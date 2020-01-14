/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/
#![allow(non_snake_case)]
#![allow(unused_imports)]
#![allow(non_camel_case_types)]

// This is the top level interface for the regalloc library.

// Stuff that is defined by the library

// Sets and maps of things.  We can refine these later; but for now the
// interface needs some way to speak about them, so let's use the
// library-provided versions.

pub use crate::data_structures::Map;
pub use crate::data_structures::Set;

// Register classes

pub use crate::data_structures::RegClass;

// Registers, both real and virtual, and ways to create them

pub use crate::data_structures::mkRealReg;
pub use crate::data_structures::mkVirtualReg;
pub use crate::data_structures::Reg;

pub use crate::data_structures::RealReg;
pub use crate::data_structures::VirtualReg;

// Spill slots

pub use crate::data_structures::SpillSlot;

// The real reg universe

pub use crate::data_structures::RealRegUniverse;

/// Register uses for a given instruction.
pub struct InstRegUses {
  pub used: Set<Reg>,    // registers that are read.
  pub defined: Set<Reg>, // registers that are written.
  pub modified: Set<Reg>, // registers that are modified.
                          // Note that `modified` is distinct from just `used`+`defined` because
                          // the vreg must live in the same real reg both before and after the
                          // instruction.
}

// TypedIxVector, so that the interface can speak about vectors of blocks and
// instructions.

pub use crate::data_structures::TypedIxVec;
pub use crate::data_structures::{BlockIx, InstIx, MyRange};

/// A trait defined by the regalloc client to provide access to its machine-instruction / CFG
/// representation.
pub trait Function {
  /// Regalloc is parameterized on F: Function and so can use the projected
  /// type F::Inst.
  type Inst: Clone;

  // -------------
  // CFG traversal
  // -------------

  /// Allow access to the underlying vector of instructions.
  fn insns(&self) -> &[Self::Inst];

  /// Allow iteration over basic blocks (in instruction order).
  fn blocks(&self) -> MyRange<BlockIx>;

  /// Provide the range of instruction indices contained in each block.
  fn block_insns(&self, block: BlockIx) -> MyRange<InstIx>;

  /// Get CFG successors for a given block.
  fn block_succs(&self, block: BlockIx) -> Vec<BlockIx>;

  /// Provide the defined, used, and modified registers for an instruction.
  fn get_regs(&self, insn: &Self::Inst) -> InstRegUses;

  /// Map each register slot through a virt -> phys mapping indexed
  /// by virtual register. The two separate maps provide the
  /// mapping to use for uses (which semantically occur just prior
  /// to the instruction's effect) and defs (which semantically occur
  /// just after the instruction's effect). Regs that were "modified"
  /// can use either map; the vreg should be the same in both.
  fn map_regs(
    &self, insn: &mut Self::Inst, pre_map: &Map<VirtualReg, RealReg>,
    post_map: &Map<VirtualReg, RealReg>,
  );

  /// Allow the regalloc to query whether this is a move.
  fn is_move(&self, insn: &Self::Inst) -> Option<(Reg, Reg)>;

  /// How many logical spill slots does the given regclass require?  E.g., on a
  /// 64-bit machine, spill slots may nominally be 64-bit words, but a 128-bit
  /// vector value will require two slots.  The regalloc will always align on
  /// this size.
  fn get_spillslot_size(&self, regclass: RegClass) -> SpillSlot;

  /// Generate a spill instruction for insertion into the instruction sequence.
  fn gen_spill(&self, from_reg: RealReg, to_slot: SpillSlot) -> Self::Inst;

  /// Generate a reload instruction for insertion into the instruction sequence.
  fn gen_reload(&self, from_slot: SpillSlot, to_reg: RealReg) -> Self::Inst;

  /// Generate a register-to-register move for insertion into the instruction sequence.
  fn gen_move(&self, from_reg: RealReg, to_reg: RealReg) -> Self::Inst;

  /// Try to alter an existing instruction to use a value directly in a
  /// spillslot (accessing memory directly) instead of the given register. May
  /// be useful on ISAs that have mem/reg ops, like x86.
  ///
  /// Note that this is not *quite* just fusing a load with the op; if the
  /// value is def'd or modified, it should be written back to the spill slot
  /// as well. In other words, it is just using the spillslot as if it were a
  /// real register, for reads and/or writes.
  fn maybe_direct_reload(
    &self, insn: &Self::Inst, reg: VirtualReg, slot: SpillSlot,
  ) -> Option<Self::Inst>;
}

/// The result of register allocation.  Note that allocation can fail!
pub struct RegAllocResult<F: Function> {
  /// A new sequence of instructions with all register slots filled with real registers, and
  /// spills/fills/moves possibly inserted (and unneeded moves elided).
  pub insns: Vec<F::Inst>,

  /// Basic-block start indices for the new instruction list, indexed by the original basic block
  /// indices. May be used by the client to, e.g., remap branch targets appropriately.
  pub target_map: Map<BlockIx, InstIx>,

  /// Which real registers were overwritten? This will contain all real regs that appear as defs or
  /// modifies in register slots of the output instruction list.
  pub clobbered_registers: Set<RealReg>,

  /// How many spill slots were used?
  pub num_spill_slots: SpillSlot,
}

/// Allocate registers for a function's code, given a universe of real registers that we are
/// allowed to use. Allocate may succeed, returning a `RegAllocResult` with the new instruction
/// sequence, or it may fail, returning an error string.
///
/// TODO: better error type? Are there a few canonical errors we return (out of regs, ...)?
pub fn allocate_registers<F: Function>(
  func: &F, rreg_universe: &RealRegUniverse,
) -> Result<RegAllocResult<F>, String> {
  Err("Unimplemented".into())
}
