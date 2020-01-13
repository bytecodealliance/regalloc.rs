//! Implementation of the linear scan allocator algorithm.

use crate::analysis::run_analysis;
use crate::data_structures::{
    i_reload, i_spill, mkBlockIx, mkRangeFrag, mkRangeFragIx, mkInstIx, mkInstPoint, mkRealReg, mkSpillSlot, mkVirtualRangeIx,
    Block, BlockIx, RangeFrag, RangeFragIx, RangeFragKind, Func, Inst, InstIx, InstPoint, InstPoint_Def,
    InstPoint_Reload, InstPoint_Spill, InstPoint_Use, Map, Point, RealReg, Reg, Set, Show, SpillSlot,
    SortedRangeFragIxs, TypedIxVec, VirtualRangeIx, VirtualReg, Vec_Block, Vec_RangeFrag, Vec_Inst, Vec_RealRange, Vec_VirtualRange, RealRange, VirtualRange,
    RealRegUniverse
};

// Allocator top level.  |func| is modified so that, when this function
// returns, it will contain no VirtualReg uses.  Allocation can fail if there
// are insufficient registers to even generate spill/reload code, or if the
// function appears to have any undefined VirtualReg/RealReg uses.
#[inline(never)]
pub fn alloc_main(func: &mut Func, reg_universe: &RealRegUniverse)
                  -> Result<(), String> {
    let (rlr_env, mut vlr_env, mut frag_env) = run_analysis(func)?;

    unimplemented!("linear scan");
}
