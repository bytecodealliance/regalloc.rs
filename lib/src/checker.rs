//! Checker: verifies that spills/reloads/moves retain equivalent dataflow to original, vreg-based
//! code.
//!
//! The basic idea is that we track symbolic values as they flow through spills and reloads.
//! The symbolic values represent particular virtual or real registers in the original
//! function body presented to the register allocator. Any instruction in the original
//! function body (i.e., not added by the allocator) conceptually generates a symbolic
//! value "Rn" or "Vn" when storing to (or modifying) a real or virtual register. This
//! includes moves (from e.g. phi-node lowering): they also generate a new value.
//!
//! In other words, the dataflow analysis state at each program point is:
//!
//!   - map `R` of: real reg -> lattice value  (top > Rn/Vn symbols (unordered) > bottom)
//!   - map `S` of: spill slot -> lattice value (same)
//!
//! And the transfer functions for each statement type are:
//!
//!   - spill (inserted by RA):    [ store spill_i, R_j ]
//!
//!       S[spill_i] := R[R_j]
//!
//!   - reload (inserted by RA):   [ load R_i, spill_j ]
//!
//!       R[R_i] := S[spill_j]
//!
//!   - move (inserted by RA):     [ R_i := R_j ]
//!
//!       R[R_i] := R[R_j]
//!
//!   - statement in pre-regalloc function [ V_i := op V_j, V_k, ... ]
//!     with allocated form                [ R_i := op R_j, R_k, ... ]
//!
//!       R[R_i] := `V_i`
//!
//!     In other words, a statement, even after allocation, generates a symbol
//!     that corresponds to its original virtual-register def.
//!
//!     (N.B.: moves in pre-regalloc function fall into this last case -- they
//!      are "just another operation" and generate a new symbol)
//!
//!     (Slight extension for multi-def ops, and ops with "modify" args: the op
//!      generates symbol `V_i` into reg `R_i` allocated for that particular def/mod).
//!
//! The initial state is: for each real reg R_livein where R_livein is in the livein set, we set
//! R[R_livein] to `R_livein`.
//!
//! At control-flow join points, the symbols meet using a very simple lattice meet-function:
//! two different symbols in the same real-reg or spill-slot meet to "conflicted"; otherwise,
//! the symbol meets with itself to produce itself (reflexivity).
//!
//! To check correctness, we first find the dataflow fixpoint with the above lattice and
//! transfer/meet functions. Then, at each op, we examine the dataflow solution at the preceding
//! program point, and check that the real reg for each op arg (input/use) contains the symbol
//! corresponding to the original (usually virtual) register specified for this arg.

#![allow(dead_code)]

use crate::data_structures::{
  BlockIx, InstIx, InstPoint, Map, Point, RealReg, RealRegUniverse, Reg,
  SanitizedInstRegUses, SpillSlot, VirtualReg, Writable,
};
use crate::inst_stream::{InstAndPoint, InstsAndPoints};
use crate::interface::Function;

use std::collections::VecDeque;
use std::default::Default;
use std::hash::Hash;
use std::result::Result;

use log::debug;

/// A set of errors detected by the regalloc checker.
#[derive(Clone, Debug)]
pub struct CheckerErrors {
  errors: Vec<CheckerError>,
}

/// A single error detected by the regalloc checker.
#[derive(Clone, Debug)]
pub enum CheckerError {
  UnknownValueInReg {
    real_reg: RealReg,
    inst: InstIx,
  },
  IncorrectValueInReg {
    actual: Reg,
    expected: Reg,
    real_reg: RealReg,
    inst: InstIx,
  },
}

/// Abstract state for a storage slot (real register or spill slot).
///
/// Forms a lattice with \top (`Unknown`), \bot (`Conflicted`), and a number of mutually unordered
/// value-points in between, one per real or virtual register. Any two different registers
/// meet to \bot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CheckerValue {
  /// "top" value: this storage slot has no known value.
  Unknown,
  /// "bottom" value: this storage slot has a conflicted value.
  Conflicted,
  /// Reg: this storage slot has a value that originated as a def into
  /// the given register, either implicitly (RealRegs at beginning of
  /// function) or explicitly (as an instruction's def).
  Reg(Reg),
}

impl Default for CheckerValue {
  fn default() -> CheckerValue {
    CheckerValue::Unknown
  }
}

impl CheckerValue {
  /// Meet function of the abstract-interpretation value lattice.
  fn meet(&self, other: &CheckerValue) -> CheckerValue {
    match (self, other) {
      (&CheckerValue::Unknown, _) => *other,
      (_, &CheckerValue::Unknown) => *self,
      (&CheckerValue::Conflicted, _) => *self,
      (_, &CheckerValue::Conflicted) => *other,
      _ if *self == *other => *self,
      _ => CheckerValue::Conflicted,
    }
  }
}

/// State that steps through program points as we scan over the instruction stream.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CheckerState {
  /// For each RealReg, abstract state.
  reg_values: Map<RealReg, CheckerValue>,
  /// For each spill slot, abstract state.
  spill_slots: Map<SpillSlot, CheckerValue>,
}

impl Default for CheckerState {
  fn default() -> CheckerState {
    CheckerState { reg_values: Map::default(), spill_slots: Map::default() }
  }
}

fn merge_map<K: Copy + Clone + PartialEq + Eq + Hash>(
  into: &mut Map<K, CheckerValue>, from: &Map<K, CheckerValue>,
) {
  for (k, v) in from {
    let into_v = into.entry(*k).or_insert(Default::default());
    let merged = into_v.meet(v);
    *into_v = merged;
  }
}

impl CheckerState {
  /// Create a new checker state.
  fn new() -> CheckerState {
    Default::default()
  }

  /// Merge this checker state with another at a CFG join-point.
  fn meet_with(&mut self, other: &CheckerState) {
    merge_map(&mut self.reg_values, &other.reg_values);
    merge_map(&mut self.spill_slots, &other.spill_slots);
  }

  /// Check an instruction against this state.
  fn check(&self, inst: &Inst) -> Result<(), CheckerError> {
    match inst {
      &Inst::Op { inst_ix, ref uses_orig, ref uses, .. } => {
        // For each use, check the mapped RealReg's symbolic value; it must
        // be the original reg.
        assert!(uses_orig.len() == uses.len());
        for (orig, mapped) in
          uses_orig.iter().cloned().zip(uses.iter().cloned())
        {
          let val =
            self.reg_values.get(&mapped).cloned().unwrap_or(Default::default());
          debug!(
            "checker: inst {:?}: orig {:?}, mapped {:?}, checker state {:?}",
            inst, orig, mapped, val
          );
          match val {
            CheckerValue::Unknown | CheckerValue::Conflicted => {
              return Err(CheckerError::UnknownValueInReg {
                real_reg: mapped,
                inst: inst_ix,
              });
            }
            CheckerValue::Reg(r) if r != orig => {
              return Err(CheckerError::IncorrectValueInReg {
                actual: r,
                expected: orig,
                real_reg: mapped,
                inst: inst_ix,
              });
            }
            _ => {}
          }
        }
      }
      _ => {}
    }
    Ok(())
  }

  /// Update according to instruction.
  pub(crate) fn update(&mut self, inst: &Inst) {
    match inst {
      &Inst::Op { ref defs_orig, ref defs, .. } => {
        // For each def, set the symbolic value of the mapped RealReg to a
        // symbol corresponding to the original def.
        assert!(defs_orig.len() == defs.len());
        for (orig, mapped) in
          defs_orig.iter().cloned().zip(defs.iter().cloned())
        {
          self.reg_values.insert(mapped, CheckerValue::Reg(orig));
        }
      }
      &Inst::Move { into, from } => {
        let val =
          self.reg_values.get(&from).cloned().unwrap_or(Default::default());
        self.reg_values.insert(into.to_reg(), val);
      }
      &Inst::Spill { into, from } => {
        let val =
          self.reg_values.get(&from).cloned().unwrap_or(Default::default());
        self.spill_slots.insert(into, val);
      }
      &Inst::Reload { into, from } => {
        let val =
          self.spill_slots.get(&from).cloned().unwrap_or(Default::default());
        self.reg_values.insert(into.to_reg(), val);
      }
    }
  }
}

/// An instruction representation in the checker's BB summary.
#[derive(Clone, Debug)]
pub(crate) enum Inst {
  /// A register spill into memory.
  Spill { into: SpillSlot, from: RealReg },
  /// A register reload from memory.
  Reload { into: Writable<RealReg>, from: SpillSlot },
  /// A regalloc-inserted move (not a move in the original program!)
  Move { into: Writable<RealReg>, from: RealReg },
  /// A regular instruction with fixed use and def slots. Contains both
  /// the original registers (as given to the regalloc) and the allocated ones.
  Op {
    inst_ix: InstIx,
    defs_orig: Vec<Reg>,
    uses_orig: Vec<Reg>,
    defs: Vec<RealReg>,
    uses: Vec<RealReg>,
  },
}

#[derive(Debug)]
pub(crate) struct Checker {
  bb_entry: BlockIx,
  bb_in: Map<BlockIx, CheckerState>,
  bb_succs: Map<BlockIx, Vec<BlockIx>>,
  bb_insts: Map<BlockIx, Vec<Inst>>,
}

fn map_regs(map: &Map<VirtualReg, RealReg>, regs: &[Reg]) -> Vec<RealReg> {
  regs
    .iter()
    .map(|r| {
      if r.is_virtual() {
        map.get(&r.to_virtual_reg()).cloned().unwrap()
      } else {
        r.to_real_reg()
      }
    })
    .collect()
}

impl Checker {
  /// Create a new checker for the given function, initializing CFG info immediately.
  /// The client should call the `add_*()` methods to add abstract instructions to each
  /// BB before invoking `run()` to check for errors.
  pub(crate) fn new<F: Function>(f: &F) -> Checker {
    let mut bb_in = Map::default();
    let mut bb_succs = Map::default();
    let mut bb_insts = Map::default();

    for block in f.blocks() {
      bb_in.insert(block, Default::default());
      bb_succs.insert(block, f.block_succs(block));
      bb_insts.insert(block, vec![]);
    }

    Checker { bb_entry: f.entry_block(), bb_in, bb_succs, bb_insts }
  }

  /// Add an abstract instruction (spill, reload, oor move) to a BB.
  ///
  /// Can also accept an `Inst::Op`, but `add_op()` is better-suited
  /// for this.
  pub(crate) fn add_inst(&mut self, block: BlockIx, inst: Inst) {
    let insts = self.bb_insts.get_mut(&block).unwrap();
    insts.push(inst);
  }

  /// Add a "normal" instruction that uses, modifies, and/or defines certain registers. The
  /// `SanitizedInstRegUses` must be the pre-allocation state; the `pre_map` and `post_map` must be
  /// provided to give the virtual -> real mappings at the program points immediately before and
  /// after this instruction.
  pub(crate) fn add_op(
    &mut self, block: BlockIx, inst_ix: InstIx, iru: &SanitizedInstRegUses,
    pre_map: &Map<VirtualReg, RealReg>, post_map: &Map<VirtualReg, RealReg>,
  ) {
    let mut uses_set = iru.san_used.clone();
    let mut defs_set = iru.san_defined.clone();
    uses_set.union(&iru.san_modified);
    defs_set.union(&iru.san_modified);
    if uses_set.is_empty() && defs_set.is_empty() {
      return;
    }

    let uses_orig = uses_set.to_vec();
    let defs_orig = defs_set.to_vec();
    let uses = map_regs(pre_map, &uses_orig[..]);
    let defs = map_regs(post_map, &defs_orig[..]);
    let insts = self.bb_insts.get_mut(&block).unwrap();
    insts.push(Inst::Op { inst_ix, uses_orig, defs_orig, uses, defs });
  }

  /// Perform the dataflow analysis to compute checker state at each BB entry.
  fn analyze(&mut self) {
    let mut queue = VecDeque::new();
    queue.push_back(self.bb_entry);

    while !queue.is_empty() {
      let block = queue.pop_front().unwrap();
      let mut state = self.bb_in.get(&block).cloned().unwrap();
      for inst in self.bb_insts.get(&block).unwrap() {
        state.update(inst);
      }

      for succ in self.bb_succs.get(&block).unwrap() {
        let cur_succ_in = self.bb_in.get(succ).unwrap();
        state.meet_with(cur_succ_in);
        let changed = &state != cur_succ_in;
        if changed {
          self.bb_in.insert(*succ, state.clone());
          queue.push_back(*succ);
        }
      }
    }
  }

  /// Using BB-start state computed by `analyze()`, step the checker state
  /// through each BB and check each instruction's register allocations
  /// for errors.
  fn find_errors(&self) -> Result<(), CheckerErrors> {
    let mut errors = vec![];
    for (block, input) in &self.bb_in {
      let mut state = input.clone();
      for inst in self.bb_insts.get(block).unwrap() {
        if let Err(e) = state.check(inst) {
          debug!("Checker error: {:?}", e);
          errors.push(e);
        }
        state.update(inst);
      }
    }

    if errors.is_empty() {
      Ok(())
    } else {
      Err(CheckerErrors { errors })
    }
  }

  /// Find any errors, returning `Err(CheckerErrors)` with all errors found
  /// or `Ok(())` otherwise.
  pub(crate) fn run(mut self) -> Result<(), CheckerErrors> {
    self.analyze();
    self.find_errors()
  }
}

/// A wrapper around `Checker` that assists its use with `InstsAndPoints` and `Function` together.
pub(crate) struct CheckerContext {
  checker: Checker,
  checker_inst_map: Map<InstPoint, Vec<Inst>>,
}

impl CheckerContext {
  /// Create a new checker context for the given function, which is about to be edited with the
  /// given instruction insertions.
  pub(crate) fn new<F: Function>(
    f: &F, insts_to_add: &InstsAndPoints,
  ) -> CheckerContext {
    let mut checker_inst_map: Map<InstPoint, Vec<Inst>> = Map::default();
    for &InstAndPoint { ref at, ref inst } in insts_to_add {
      let checker_insts =
        checker_inst_map.entry(at.clone()).or_insert_with(|| vec![]);
      checker_insts.push(inst.to_checker_inst());
    }
    let checker = Checker::new(f);
    CheckerContext { checker, checker_inst_map }
  }

  /// Update the checker with the given instruction and the given pre- and post-maps. Instructions
  /// within a block must be visited in program order.
  pub(crate) fn handle_insn<F: Function>(
    &mut self, ru: &RealRegUniverse, func: &F, bix: BlockIx, iix: InstIx,
    pre_map: &Map<VirtualReg, RealReg>, post_map: &Map<VirtualReg, RealReg>,
  ) {
    let empty = vec![];
    let pre_point = InstPoint { iix, pt: Point::Reload };
    let post_point = InstPoint { iix, pt: Point::Spill };

    for checker_inst in self.checker_inst_map.get(&pre_point).unwrap_or(&empty)
    {
      debug!("at inst {:?}: pre checker_inst: {:?}", iix, checker_inst);
      self.checker.add_inst(bix, checker_inst.clone());
    }

    let iru = func.get_regs(func.get_insn(iix)); // AUDITED
    let sru = SanitizedInstRegUses::create_by_sanitizing(&iru, ru)
      .expect("only existing real registers at this point");
    debug!(
      "at inst {:?}: sru {:?} use-map {:?} def-map {:?}",
      iix, sru, pre_map, post_map
    );
    self.checker.add_op(bix, iix, &sru, pre_map, post_map);

    for checker_inst in self.checker_inst_map.get(&post_point).unwrap_or(&empty)
    {
      debug!("at inst {:?}: post checker_inst: {:?}", iix, checker_inst);
      self.checker.add_inst(bix, checker_inst.clone());
    }
  }

  /// Run the underlying checker, once all instructions have been added.
  pub(crate) fn run(self) -> Result<(), CheckerErrors> {
    self.checker.run()
  }
}
