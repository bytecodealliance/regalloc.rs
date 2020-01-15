/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/
//! Implementation of the linear scan allocator algorithm.

use crate::analysis::run_analysis;
use crate::data_structures::{
  mkBlockIx, mkInstIx, mkInstPoint, mkRangeFrag, mkRangeFragIx, mkRealReg,
  mkSpillSlot, mkVirtualRangeIx, BlockIx, InstIx, InstPoint, InstPoint_Def,
  InstPoint_Reload, InstPoint_Spill, InstPoint_Use, Map, Point, RangeFrag,
  RangeFragIx, RangeFragKind, RealRange, RealReg, RealRegUniverse, Reg, Set,
  SortedRangeFragIxs, SpillSlot, TypedIxVec, VirtualRange, VirtualRangeIx,
  VirtualReg,
};
use crate::interface::{Function, RegAllocResult};

// Allocator top level.  |func| is modified so that, when this function
// returns, it will contain no VirtualReg uses.  Allocation can fail if there
// are insufficient registers to even generate spill/reload code, or if the
// function appears to have any undefined VirtualReg/RealReg uses.
#[inline(never)]
pub fn alloc_main<F: Function>(
  func: &mut F, reg_universe: &RealRegUniverse,
) -> Result<RegAllocResult<F>, String> {
  let (rlr_env, mut vlr_env, mut frag_env) = run_analysis(func)?;

  unimplemented!("linear scan");
}
