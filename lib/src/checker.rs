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

use crate::data_structures::{Map, RealReg, Reg, VirtualReg, Writable};

/// Abstract state for a storage slot (real register or spill slot).
///
/// Forms a lattice with \top (`Unknown`), \bot (`Conflicted`), and a number of mutually unordered
/// value-points in between, one per real or virtual register. Any two different registers
/// meet to \bot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckerValue {
  /// "top" value: this storage slot has no known value.
  Unknown,
  /// "bottom" value: this storage slot has a conflicted value.
  Conflicted,
  /// Reg: this storage slot has a value that originated as a def into
  /// the given register, either implicitly (RealRegs at beginning of
  /// function) or explicitly (as an instruction's def).
  Reg(Reg),
}

impl CheckerValue {
  /// Meet function of the abstract-interpretation value lattice.
  pub fn meet(&self, other: &CheckerValue) -> CheckerValue {
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
pub struct CheckerState {
  /// For each RealReg or VReg, abstract state.
  reg_values: Map<Reg, CheckerValue>,
  /// For each spill slot, abstract state.
  spill_slots: Map<SpillSlot, CheckerValue>,
}

impl CheckerState {
  /// Create a new checker state.
  pub fn new() -> CheckerState {
    CheckerState { reg_values: Map::empty(), spill_slots: Map::empty() }
  }

  /// Merge this checker state with another at a CFG join-point.
  pub fn meet_with(&mut self, other: &CheckerState) {
      unimplemented!()
  }

  /// Update with a RegAlloc-inserted reload.
  pub fn process_reload(
    &mut self, into_reg: Writable<Reg>, from_slot: SpillSlot,
  ) {
    let val = self.spill_slots.get(&from_slot).unwrap_or(CheckerValue::Unknown);
    self.reg_values.insert(into_reg.to_reg(), val);
  }

  /// Update with a RegAlloc-inserted spill.
  pub fn process_spill(&mut self, into_slot: SpillSlot, from_reg: Reg) {
    let val = self.reg_values.get(&from_reg).unwrap_or(CheckerValue::Unknown);
    self.spill_slots.insert(into_slot, val);
  }

  /// Update with a reg-reg move.
  pub fn process_move(&mut self, into_reg: Writable<Reg>, from_reg: Reg) {
    let val = self.reg_values.get(&from_reg).unwrap_or(CheckerValue::Unknown);
    self.reg_values.insert(into_reg.to_reg(), val);
  }

  /// Get the checker value in a given real register.
  pub fn get_reg_value(&self, reg: RealReg) -> CheckerValue {
    self.reg_values.get(&reg).unwrap_or(CheckerValue::Unknown)
  }
}
