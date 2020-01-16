/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

//! Implementation of the linear scan allocator algorithm.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;

use log::{debug, trace};

use crate::analysis::run_analysis;
use crate::backtracking::{edit_inst_stream, EditList, RangeAllocations};
use crate::data_structures::{
  cmpRangeFrags, mkBlockIx, mkInstIx, mkInstPoint, mkRangeFrag, mkRangeFragIx,
  mkRealReg, mkSpillSlot, mkVirtualRangeIx, BlockIx, InstIx, InstPoint,
  InstPoint_Def, InstPoint_Reload, InstPoint_Spill, InstPoint_Use, Map, Point,
  RangeFrag, RangeFragIx, RangeFragKind, RealRange, RealRangeIx, RealReg,
  RealRegUniverse, Reg, RegClass, Set, SortedRangeFragIxs, SpillSlot,
  TypedIxVec, VirtualRange, VirtualRangeIx, VirtualReg, NUM_REG_CLASSES,
};
use crate::interface::{Function, RegAllocResult};

// Local renamings.
type Fragments = TypedIxVec<RangeFragIx, RangeFrag>;
type VirtualRanges = TypedIxVec<VirtualRangeIx, VirtualRange>;
type RealRanges = TypedIxVec<RealRangeIx, RealRange>;

#[derive(Clone, Copy, PartialEq, Eq)]
struct LiveId(usize);

impl fmt::Debug for LiveId {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "int{}", self.0)
  }
}

enum LiveIntervalKind<'a> {
  Fixed(&'a mut RealRange),
  Virtual(&'a mut VirtualRange),
}

impl<'a> LiveIntervalKind<'a> {
  fn fragments(&self) -> &SortedRangeFragIxs {
    match &self {
      LiveIntervalKind::Fixed(r) => &r.sortedFrags,
      LiveIntervalKind::Virtual(r) => &r.sortedFrags,
    }
  }
  fn allocated_register(&self) -> Option<RealReg> {
    match &self {
      LiveIntervalKind::Fixed(r) => Some(r.rreg),
      LiveIntervalKind::Virtual(r) => r.rreg,
    }
  }
  fn is_fixed(&self) -> bool {
    match &self {
      LiveIntervalKind::Fixed(_) => true,
      _ => false,
    }
  }
  fn fixed_reg(&self) -> Option<RealReg> {
    if self.is_fixed() {
      self.allocated_register()
    } else {
      None
    }
  }
  fn start_point(&self, fragments: &Fragments) -> InstPoint {
    fragments[*self.fragments().fragIxs.first().unwrap()].first
  }
  fn end_point(&self, fragments: &Fragments) -> InstPoint {
    fragments[*self.fragments().fragIxs.last().unwrap()].last
  }
}

impl<'a> fmt::Debug for LiveIntervalKind<'a> {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      LiveIntervalKind::Fixed(range) => write!(fmt, "fixed({:?})", range),
      LiveIntervalKind::Virtual(range) => write!(fmt, "virtual({:?})", range),
    }
  }
}

struct LiveInterval<'a> {
  id: LiveId,
  kind: LiveIntervalKind<'a>,
}

impl<'a> fmt::Debug for LiveInterval<'a> {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{:?} -> {:?}", self.id, self.kind)
  }
}

impl<'a> std::ops::Deref for LiveInterval<'a> {
  type Target = LiveIntervalKind<'a>;
  fn deref(&self) -> &Self::Target {
    &self.kind
  }
}

impl<'a> LiveInterval<'a> {
  fn reg_class(&self) -> RegClass {
    match &self.kind {
      LiveIntervalKind::Fixed(r) => r.rreg.get_class(),
      LiveIntervalKind::Virtual(r) => r.vreg.get_class(),
    }
  }

  fn covers(&self, pos: &InstPoint, fragments: &Fragments) -> bool {
    self
      .fragments()
      .fragIxs
      .iter()
      .map(|&index| fragments[index])
      .any(|frag| frag.contains(pos))
  }

  fn intersects_with(
    &self, other: &LiveInterval, fragments: &Fragments,
  ) -> Option<InstPoint> {
    let frags = &self.fragments().fragIxs;
    let other_frags = &other.fragments().fragIxs;

    let mut i = 0;
    let mut other_i = 0;

    while i < frags.len() && other_i < other_frags.len() {
      let cur = &fragments[frags[i]];
      let other = &fragments[other_frags[other_i]];
      match cmpRangeFrags(cur, other) {
        None => {
          // They intersect!
          return Some(if cur.first < other.first {
            other.first
          } else {
            cur.first
          });
        }
        Some(Ordering::Less) => {
          // cur < other, go to the range following cur.
          i += 1;
        }
        Some(Ordering::Equal) => {
          // Special intersection case, at the start.
          return Some(cur.first);
        }
        Some(Ordering::Greater) => {
          // cur > other, go to the range following other.
          other_i += 1;
        }
      }
    }

    None
  }

  // Mutators.
  fn set_reg(&mut self, reg: RealReg) {
    debug_assert!(self.allocated_register().is_none());
    match &mut self.kind {
      LiveIntervalKind::Fixed(_) => unreachable!(),
      LiveIntervalKind::Virtual(ref mut r) => r.rreg = Some(reg),
    }
  }
}

fn update_state<'a>(
  cur_id: LiveId, mut state: State<'a>, fragments: &Fragments,
) -> State<'a> {
  trace!("starting update_state...");
  let start_point = state.intervals[cur_id].start_point(&fragments);

  //let mut regs = state.regs;

  let mut next_active = Vec::new();
  let mut next_inactive = Vec::new();

  for &active_int_id in &state.active {
    let active_int = &mut state.intervals[active_int_id];
    if active_int.end_point(fragments) < start_point {
      debug!("update_state: active {:?} becomes handled", active_int_id);
      // Free the register, if it was allocated one.
      //if let Some(reg) = active_int.allocated_register() {
      //regs[reg.get_class() as usize].free(&reg);
      //}
      state.handled.push(active_int_id);
    } else if active_int.covers(&start_point, fragments) {
      debug!("update_state: active {:?} stays active", active_int_id);
      next_active.push(active_int_id);
    } else {
      debug!("update_state: active {:?} becomes inactive", active_int_id);
      next_inactive.push(active_int_id);
    }
  }

  for &inactive_int_id in &state.inactive {
    let inactive_int = &mut state.intervals[inactive_int_id];
    if inactive_int.end_point(fragments) < start_point {
      debug!("update_state: inactive {:?} becomes handled", inactive_int_id);
      // Free the register, if it was allocated one.
      //if let Some(reg) = inactive_int.allocated_register() {
      //regs[reg.get_class() as usize].free(&reg);
      //}
      state.handled.push(inactive_int_id);
    } else if inactive_int.covers(&start_point, fragments) {
      debug!("update_state: inactive {:?} becomes active", inactive_int_id);
      next_active.push(inactive_int_id);
    } else {
      debug!("update_state: inactive {:?} stays inactive", inactive_int_id);
      next_inactive.push(inactive_int_id);
    }
  }

  state.active = next_active;
  state.inactive = next_inactive;
  //state.regs = regs;

  trace!("done with update_state!");
  state
}

fn try_allocate_reg(
  id: LiveId, state: &mut State, fragments: &Fragments,
  reg_universe: &RealRegUniverse,
) -> bool {
  let int = &state.intervals[id];
  let reg_class = int.reg_class();

  let mut free_until_pos = RegisterMapping::with_default(
    reg_class,
    reg_universe,
    InstPoint::max_value(),
  );

  for &id in &state.active {
    if let Some(reg) = state.intervals[id].allocated_register() {
      free_until_pos[reg].1 = InstPoint::min_value();
    }
  }

  {
    let cur_int = &state.intervals[id];
    for &id in &state.inactive {
      if let Some(reg) = state.intervals[id].allocated_register() {
        if let Some(intersect_at) =
          state.intervals[id].intersects_with(cur_int, fragments)
        {
          if intersect_at < free_until_pos[reg].1 {
            free_until_pos[reg].1 = intersect_at;
          }
        }
      }
    }
  }

  let solution = if state.intervals[id].is_fixed() {
    let reg = state.intervals[id].allocated_register().unwrap();
    let pos = free_until_pos[reg].1;
    if state.intervals[id].start_point(fragments) < pos {
      Some((reg, pos))
    } else {
      None
    }
  } else {
    let mut best_reg = None;
    let mut best_pos = InstPoint::min_value();
    // Find the register with the furthest next use.
    for &(reg, pos) in free_until_pos.iter() {
      if pos > best_pos {
        best_pos = pos;
        best_reg = Some(reg);
      }
    }
    if let Some(best_reg) = best_reg {
      Some((best_reg, best_pos))
    } else {
      None
    }
  };

  let (best_reg, best_pos) = if let Some(solution) = solution {
    solution
  } else {
    // Can't allocate, we need to spill.
    return false;
  };

  // At least a partial match: allocate.
  if let Some(fixed_reg) = state.intervals[id].fixed_reg() {
    debug!("{:?} <- {:?} (fixed)", id, fixed_reg);
  } else {
    debug!("{:?} <- {:?} (virtual)", id, best_reg);
    state.intervals[id].set_reg(best_reg);
  }
  //state.regs[reg_class as usize].take(&best_reg);

  if state.intervals[id].end_point(fragments) >= best_pos {
    // The current interval is partially covered, split it.
    split_at(state, id, SplitPosition::At(best_pos));
  }

  true
}

fn allocate_blocked_reg() {
  unimplemented!("allocate_blocked_reg");
}

enum SplitPosition {
  At(InstPoint),
}

fn split_at(_state: &mut State, _id: LiveId, _split_pos: SplitPosition) {
  unimplemented!("split_at")
}

/// A mapping from real reg to some T.
#[derive(Clone)]
struct RegisterMapping<T> {
  offset: usize,
  regs: Vec<(RealReg, T)>,
}

impl<T: Copy> RegisterMapping<T> {
  fn with_default(
    reg_class: RegClass, reg_universe: &RealRegUniverse, initial_value: T,
  ) -> Self {
    let mut regs = Vec::new();
    let mut offset = 0;
    // Collect all the registers for the current class.
    if let Some(ref range) = reg_universe.allocable_by_class[reg_class as usize]
    {
      debug_assert!(range.0 <= range.1);
      offset = range.0;
      for reg in &reg_universe.regs[range.0..=range.1] {
        debug_assert!(regs.len() == reg.0.get_index() - offset);
        regs.push((reg.0, initial_value));
      }
    };
    Self { offset, regs }
  }

  fn iter<'a>(&'a self) -> std::slice::Iter<(RealReg, T)> {
    self.regs.iter()
  }
}

impl<T> std::ops::Index<RealReg> for RegisterMapping<T> {
  type Output = (RealReg, T);
  fn index(&self, rreg: RealReg) -> &Self::Output {
    &self.regs[rreg.get_index() - self.offset]
  }
}

impl<T> std::ops::IndexMut<RealReg> for RegisterMapping<T> {
  fn index_mut(&mut self, rreg: RealReg) -> &mut Self::Output {
    &mut self.regs[rreg.get_index() - self.offset]
  }
}

// Precise implementations of RegisterMapping.

struct Intervals<'a> {
  data: Vec<LiveInterval<'a>>,
}

impl<'a> Intervals<'a> {
  fn new(
    rlrs: &'a mut RealRanges, vlrs: &'a mut VirtualRanges,
    fragments: &Fragments,
  ) -> Self {
    let mut data =
      Vec::with_capacity(rlrs.len() as usize + vlrs.len() as usize);
    for rlr in rlrs.iter_mut() {
      data.push(LiveIntervalKind::Fixed(rlr));
    }
    for vlr in vlrs.iter_mut() {
      data.push(LiveIntervalKind::Virtual(vlr));
    }
    data.sort_by_key(|live_int| live_int.start_point(&fragments));

    let data = data
      .into_iter()
      .enumerate()
      .map(|(index, kind)| LiveInterval { id: LiveId(index), kind })
      .collect();

    Self { data }
  }

  fn clear(&mut self) {
    self.data.clear()
  }
}

impl<'a> std::ops::Index<LiveId> for Intervals<'a> {
  type Output = LiveInterval<'a>;
  fn index(&self, id: LiveId) -> &Self::Output {
    &self.data[id.0]
  }
}

impl<'a> std::ops::IndexMut<LiveId> for Intervals<'a> {
  fn index_mut(&mut self, id: LiveId) -> &mut Self::Output {
    &mut self.data[id.0]
  }
}

/// State structure, which can be cleared between different calls to register allocation.
struct State<'a> {
  intervals: Intervals<'a>,

  /// Intervals that are starting after the current interval's start position.
  unhandled: Vec<LiveId>,

  /// Intervals that are covering the current interval's start position.
  active: Vec<LiveId>,

  /// Intervals that are not covering but end after the current interval's start
  /// position.
  inactive: Vec<LiveId>,

  /// Intervals that have been expired or spilled.
  handled: Vec<LiveId>,
}

impl<'a> State<'a> {
  fn new(intervals: Intervals<'a>) -> Self {
    // Trick! Keep unhandled in reverse sorted order, so we can just pop
    // unhandled ids instead of shifting the first element.
    let unhandled: Vec<LiveId> =
      intervals.data.iter().rev().map(|int| int.id).collect();

    trace!("unhandled: {:#?}", unhandled);

    Self {
      intervals,
      unhandled,
      active: Vec::new(),
      inactive: Vec::new(),
      handled: Vec::new(),
    }
  }

  #[allow(dead_code)]
  pub fn clear(&mut self) {
    self.intervals.clear();
    self.unhandled.clear();
    self.active.clear();
    self.inactive.clear();
    self.handled.clear();
  }

  fn next_unhandled(&mut self) -> Option<LiveId> {
    self.unhandled.pop()
  }
}

// Allocator top level.  |func| is modified so that, when this function
// returns, it will contain no VirtualReg uses.  Allocation can fail if there
// are insufficient registers to even generate spill/reload code, or if the
// function appears to have any undefined VirtualReg/RealReg uses.
#[inline(never)]
pub fn run<F: Function>(
  func: &mut F, reg_universe: &RealRegUniverse,
) -> Result<RegAllocResult<F>, String> {
  let (mut rlrs, mut vlrs, fragments) = run_analysis(func)?;

  let intervals = Intervals::new(&mut rlrs, &mut vlrs, &fragments);

  let mut state = State::new(intervals);

  while let Some(id) = state.next_unhandled() {
    trace!("main loop {:?}: {:?}", id, state.intervals[id]);

    state = update_state(id, state, &fragments);

    if !try_allocate_reg(id, &mut state, &fragments, reg_universe) {
      allocate_blocked_reg();
    }

    if let Some(_) = state.intervals[id].allocated_register() {
      state.active.push(id);
    }
  }

  // Prepare edit stream.
  // TODO clean up this; this is basically a shim of Julian's backtracking's
  // tail.
  let mut frag_maps_by_start = RangeAllocations::new();
  let mut frag_maps_by_end = RangeAllocations::new();

  type PerRealReg = Vec<VirtualRangeIx>;

  // Whereas this is empty.  We have to populate it "by hand", by
  // effectively cloning the allocatable part (prefix) of the universe.
  let mut per_real_reg = Vec::<PerRealReg>::new();
  for _rreg in 0..reg_universe.allocable {
    // Doing this instead of simply .resize avoids needing Clone for PerRealReg
    per_real_reg.push(PerRealReg::new());
  }

  for (i, vlr) in vlrs.iter().enumerate() {
    let rregNo = vlr.rreg.unwrap().get_index();
    let curr_vlrix = mkVirtualRangeIx(i as u32);
    per_real_reg[rregNo].push(curr_vlrix);
  }

  // For each real register under our control ..
  for i in 0..reg_universe.allocable {
    let rreg = reg_universe.regs[i].0;
    // .. look at all the VirtualRanges assigned to it.  And for each such
    // VirtualRange ..
    for vlrix_assigned in &per_real_reg[i] {
      let vlr_assigned = &vlrs[*vlrix_assigned];
      // All the RangeFrags in |vlr_assigned| require |vlr_assigned.reg|
      // to be mapped to the real reg |i|
      let vreg = vlr_assigned.vreg;
      // .. collect up all its constituent RangeFrags.
      for fix in &vlr_assigned.sortedFrags.fragIxs {
        frag_maps_by_start.push((*fix, vreg, rreg));
        frag_maps_by_end.push((*fix, vreg, rreg));
      }
    }
  }

  // TODO not spilling yet.
  let edit_list = EditList::new();
  let num_spill_slots = 0;

  edit_inst_stream(
    func,
    edit_list,
    frag_maps_by_start,
    frag_maps_by_end,
    &fragments,
    &vlrs,
    num_spill_slots,
  )
}
