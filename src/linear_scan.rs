//! Implementation of the linear scan allocator algorithm.

use crate::analysis::run_analysis;
use crate::data_structures::{
    i_reload, i_spill, mkBlockIx, mkFrag, mkFragIx, mkInsnIx, mkInsnPoint, mkRReg, mkSlot, mkVLRIx,
    Block, BlockIx, Frag, FragIx, FragKind, Func, Insn, InsnIx, InsnPoint, InsnPoint_D,
    InsnPoint_R, InsnPoint_S, InsnPoint_U, Map, Point, RReg, Reg, Reg_V, Set, Show, Slot,
    SortedFragIxs, TVec, VLRIx, VReg, Vec_Block, Vec_Frag, Vec_Insn, Vec_RLR, Vec_VLR, RLR, VLR,
};

// Allocator top level.  |func| is modified so that, when this function
// returns, it will contain no VReg uses.  Allocation can fail if there are
// insufficient registers to even generate spill/reload code, or if the
// function appears to have any undefined VReg/RReg uses.
#[inline(never)]
pub fn alloc_main(func: &mut Func, nRRegs: usize) -> Result<(), String> {
    let (rlr_env, mut vlr_env, mut frag_env) = run_analysis(func, nRRegs)?;

    unimplemented!("linear scan");
}
