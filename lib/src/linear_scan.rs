/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

//! Implementation of the linear scan allocator algorithm.
//!
//! This tries to follow the implementation as suggested by:
//!   Optimized Interval Splitting in a Linear Scan Register Allocator,
//!     by Wimmer et al., 2005
//!

// TODO brain dump:
// - (perf) in try_allocate_reg, try to implement the fixed blocked heuristics, and see
// if it improves perf.
// - (perf) try to handle different register classes in different passes.
// - (correctness) use sanitized reg uses in lieu of reg uses.

use std::cmp::Ordering;
use std::fmt;

use log::{debug, trace};

use crate::analysis::run_analysis;
use crate::data_structures::{
  cmp_range_frags, BlockIx, InstPoint, Map, PlusOne, Point, RangeFrag,
  RangeFragIx, RealRange, RealRangeIx, RealReg, RealRegUniverse, Reg, RegClass,
  Set, SortedRangeFragIxs, SpillSlot, TypedIxVec, VirtualRange, VirtualRangeIx,
  VirtualReg, Writable,
};
use crate::inst_stream::{fill_memory_moves, InstAndPoint, InstsAndPoints};
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

enum LiveIntervalKind {
  Fixed(RealRangeIx),
  Virtual(VirtualRangeIx),
}

impl fmt::Debug for LiveIntervalKind {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      LiveIntervalKind::Fixed(range) => write!(fmt, "fixed({:?})", range),
      LiveIntervalKind::Virtual(range) => write!(fmt, "virtual({:?})", range),
    }
  }
}

struct LiveInterval {
  id: LiveId,
  kind: LiveIntervalKind,
  /// Parent interval in the interval split tree.
  parent: Option<LiveId>,
  /// When used, this indicates that this interval has been split, and this is
  /// where its children must reload from.
  spill_slot: Option<SpillSlot>,
}

impl LiveInterval {
  fn unwrap_virtual(&self) -> VirtualRangeIx {
    if let LiveIntervalKind::Virtual(r) = &self.kind {
      *r
    } else {
      unreachable!();
    }
  }
}

// Live intervals.

struct Intervals {
  real_ranges: RealRanges,
  virtual_ranges: VirtualRanges,
  data: Vec<LiveInterval>,
}

impl Intervals {
  fn new(
    real_ranges: RealRanges, virtual_ranges: VirtualRanges,
    fragments: &Fragments,
  ) -> Self {
    let mut data = Vec::with_capacity(
      real_ranges.len() as usize + virtual_ranges.len() as usize,
    );

    for rlr in 0..real_ranges.len() {
      data.push(LiveIntervalKind::Fixed(RealRangeIx::new(rlr)));
    }
    for vlr in 0..virtual_ranges.len() {
      data.push(LiveIntervalKind::Virtual(VirtualRangeIx::new(vlr)));
    }

    // Sort before assigning indexes.
    data.sort_by_key(|live_int| {
      let sorted_frag_ix = match live_int {
        LiveIntervalKind::Fixed(ix) => &real_ranges[*ix].sorted_frags.frag_ixs,
        LiveIntervalKind::Virtual(ix) => {
          &virtual_ranges[*ix].sorted_frags.frag_ixs
        }
      };
      fragments[*sorted_frag_ix.first().unwrap()].first
    });

    let data = data
      .into_iter()
      .enumerate()
      .map(|(index, kind)| LiveInterval {
        id: LiveId(index),
        kind,
        parent: None,
        spill_slot: None,
      })
      .collect();

    Self { real_ranges, virtual_ranges, data }
  }

  fn fragments(&self, live_id: LiveId) -> &SortedRangeFragIxs {
    match &self.data[live_id.0].kind {
      LiveIntervalKind::Fixed(r) => &self.real_ranges[*r].sorted_frags,
      LiveIntervalKind::Virtual(r) => &self.virtual_ranges[*r].sorted_frags,
    }
  }

  fn fragments_mut(&mut self, live_id: LiveId) -> &mut SortedRangeFragIxs {
    match &mut self.data[live_id.0].kind {
      LiveIntervalKind::Fixed(r) => &mut self.real_ranges[*r].sorted_frags,
      LiveIntervalKind::Virtual(r) => &mut self.virtual_ranges[*r].sorted_frags,
    }
  }

  fn allocated_register(&self, live_id: LiveId) -> Option<RealReg> {
    match &self.data[live_id.0].kind {
      LiveIntervalKind::Fixed(r) => Some(self.real_ranges[*r].rreg),
      LiveIntervalKind::Virtual(r) => self.virtual_ranges[*r].rreg,
    }
  }

  fn is_fixed(&self, live_id: LiveId) -> bool {
    match &self.data[live_id.0].kind {
      LiveIntervalKind::Fixed(_) => true,
      LiveIntervalKind::Virtual(_) => false,
    }
  }

  fn fixed_reg(&self, live_id: LiveId) -> Option<RealReg> {
    if self.is_fixed(live_id) {
      self.allocated_register(live_id)
    } else {
      None
    }
  }

  fn vreg(&self, live_id: LiveId) -> VirtualReg {
    match &self.data[live_id.0].kind {
      LiveIntervalKind::Fixed(_) => panic!("asking for vreg of fixed interval"),
      LiveIntervalKind::Virtual(r) => self.virtual_ranges[*r].vreg,
    }
  }

  fn reg(&self, live_id: LiveId) -> Reg {
    match &self.data[live_id.0].kind {
      LiveIntervalKind::Fixed(r) => self.real_ranges[*r].rreg.to_reg(),
      LiveIntervalKind::Virtual(r) => self.virtual_ranges[*r].vreg.to_reg(),
    }
  }

  fn reg_class(&self, live_id: LiveId) -> RegClass {
    self.reg(live_id).get_class()
  }

  fn covers(
    &self, live_id: LiveId, pos: &InstPoint, fragments: &Fragments,
  ) -> bool {
    self
      .fragments(live_id)
      .frag_ixs
      .iter()
      .map(|&index| fragments[index])
      .any(|frag| frag.contains(pos))
  }

  fn intersects_with(
    &self, live_id: LiveId, other_id: LiveId, fragments: &Fragments,
  ) -> Option<InstPoint> {
    let frags = &self.fragments(live_id).frag_ixs;
    let other_frags = &self.fragments(other_id).frag_ixs;

    let mut i = 0;
    let mut other_i = 0;

    while i < frags.len() && other_i < other_frags.len() {
      let cur = &fragments[frags[i]];
      let other = &fragments[other_frags[other_i]];
      match cmp_range_frags(cur, other) {
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

  fn start_point(&self, live_id: LiveId, fragments: &Fragments) -> InstPoint {
    fragments[*self.fragments(live_id).frag_ixs.first().unwrap()].first
  }
  fn end_point(&self, live_id: LiveId, fragments: &Fragments) -> InstPoint {
    fragments[*self.fragments(live_id).frag_ixs.last().unwrap()].last
  }

  fn num_intervals(&self) -> usize {
    self.data.len()
  }

  fn display(&self, live_id: LiveId, fragments: &Fragments) -> String {
    let int = &self.data[live_id.0];
    let vreg = if self.is_fixed(live_id) {
      "fixed".to_string()
    } else {
      format!("{:?}", self.reg(live_id))
    };
    let rreg = if let Some(rreg) = self.allocated_register(live_id) {
      format!("{:?}", rreg)
    } else {
      "none".into()
    };
    let frag_ixs = &self.fragments(live_id).frag_ixs;
    let fragments = frag_ixs
      .iter()
      .map(|&ix| {
        let frag = fragments[ix];
        (ix, frag.first, frag.last)
      })
      .collect::<Vec<_>>();
    format!(
      "{:?}{}: {} {} {}{:?}",
      int.id,
      if let Some(ref p) = int.parent {
        format!(" (parent={:?}) ", p)
      } else {
        "".to_string()
      },
      vreg,
      rreg,
      if let Some(ref slot) = int.spill_slot {
        format!("({:?}), ", slot)
      } else {
        "".to_string()
      },
      fragments
    )
  }

  fn spill_slot(&self, live_id: LiveId) -> Option<SpillSlot> {
    self.data[live_id.0].spill_slot
  }

  // Mutators.
  fn set_reg(&mut self, live_id: LiveId, reg: RealReg) {
    debug_assert!(self.allocated_register(live_id).is_none());
    match self.data[live_id.0].kind {
      LiveIntervalKind::Fixed(_) => unreachable!(),
      LiveIntervalKind::Virtual(id) => self.virtual_ranges[id].rreg = Some(reg),
    }
  }

  fn assign_spill(&mut self, live_id: LiveId, slot: SpillSlot) {
    self.data[live_id.0].spill_slot = Some(slot);
  }
  fn remove_spill(&mut self, live_id: LiveId) {
    debug_assert!(self.spill_slot(live_id).is_some());
    self.data[live_id.0].spill_slot = None;
  }

  fn push_interval(&mut self, int: LiveInterval) {
    debug_assert!(int.id.0 == self.data.len());
    self.data.push(int);
  }
}

// State management.

/// State structure, which can be cleared between different calls to register allocation.
/// TODO: split this into clearable fields and non-clearable fields.
struct State<'a, F: Function> {
  func: &'a F,

  fragments: Fragments,
  intervals: Intervals,

  /// Intervals that are starting after the current interval's start position.
  unhandled: Vec<LiveId>,

  /// Intervals that are covering the current interval's start position.
  active: Vec<LiveId>,

  /// Intervals that are not covering but end after the current interval's start
  /// position.
  inactive: Vec<LiveId>,

  /// Intervals that have been expired or spilled.
  handled: Vec<LiveId>,

  /// Next available spill slot.
  next_spill_slot: SpillSlot,
}

impl<'a, F: Function> State<'a, F> {
  fn new(func: &'a F, fragments: Fragments, intervals: Intervals) -> Self {
    // Trick! Keep unhandled in reverse sorted order, so we can just pop
    // unhandled ids instead of shifting the first element.
    let unhandled: Vec<LiveId> =
      intervals.data.iter().rev().map(|int| int.id).collect();

    Self {
      func,
      fragments,
      intervals,
      unhandled,
      active: Vec::new(),
      inactive: Vec::new(),
      handled: Vec::new(),
      next_spill_slot: SpillSlot::new(0),
    }
  }

  fn next_unhandled(&mut self) -> Option<LiveId> {
    self.unhandled.pop()
  }

  fn insert_unhandled(&mut self, id: LiveId) {
    let fragments = &self.fragments;
    let start_pos = self.intervals.start_point(id, fragments);
    // Maintain reversed start_pos order by inverting the operands in the
    // comparison.
    let pos = self.unhandled.binary_search_by(|&id| {
      start_pos.cmp(&self.intervals.start_point(id, fragments))
    });
    let pos = match pos {
      Ok(index) => index,
      Err(index) => index,
    };
    self.unhandled.insert(pos, id);
  }

  fn spill(&mut self, id: LiveId) {
    debug_assert!(!self.intervals.is_fixed(id), "can't split fixed interval");
    debug_assert!(self.intervals.spill_slot(id).is_none(), "already spilled");
    debug!("spilling {}", self.intervals.display(id, &self.fragments));

    // TODO this should be per vreg instead.
    let mut spill_slot = None;

    // Try to find if there's a parent which allocated a spill slot for this
    // particular virtual register, and reuse it in this case.
    let mut cur_id = id;
    while let Some(parent) = &self.intervals.data[cur_id.0].parent {
      if let Some(parent_spill) = self.intervals.spill_slot(*parent) {
        spill_slot = Some(parent_spill);
        break;
      }
      cur_id = *parent;
    }

    let spill_slot = match spill_slot {
      None => {
        let reg_class = self.intervals.reg_class(id);
        let vreg = self.intervals.vreg(id);
        let size_slot = self.func.get_spillslot_size(reg_class, vreg);
        let spill_slot = self.next_spill_slot.round_up(size_slot);
        self.next_spill_slot = self.next_spill_slot.inc(1);
        spill_slot
      }
      Some(x) => x,
    };

    self.intervals.assign_spill(id, spill_slot);
  }
}

/// Transitions intervals from active/inactive into active/inactive/handled.
fn update_state<'a, F: Function>(cur_id: LiveId, state: &mut State<'a, F>) {
  let int = &state.intervals;
  let start_point = int.start_point(cur_id, &state.fragments);

  let mut next_active = Vec::new();
  let mut next_inactive = Vec::new();

  for &id in &state.active {
    if int.end_point(id, &state.fragments) < start_point {
      state.handled.push(id);
    } else if int.covers(id, &start_point, &state.fragments) {
      next_active.push(id);
    } else {
      next_inactive.push(id);
    }
  }

  for &id in &state.inactive {
    if int.end_point(id, &state.fragments) < start_point {
      state.handled.push(id);
    } else if int.covers(id, &start_point, &state.fragments) {
      next_active.push(id);
    } else {
      next_inactive.push(id);
    }
  }

  state.active = next_active;
  state.inactive = next_inactive;

  trace!("state active: {:?}", state.active);
  trace!("state inactive: {:?}", state.inactive);
}

/// Naive heuristic to select a register when we're not aware of any conflict.
/// Currently, it chooses the register with the furthest next use.
fn select_naive_reg<F: Function>(
  state: &State<F>, id: LiveId, reg_class: RegClass,
  reg_universe: &RealRegUniverse,
) -> Option<(RealReg, InstPoint)> {
  let mut free_until_pos = RegisterMapping::with_default(
    reg_class,
    reg_universe,
    InstPoint::max_value(),
  );

  // All registers currently in use are blocked.
  for &id in &state.active {
    if let Some(reg) = state.intervals.allocated_register(id) {
      if reg.get_class() == reg_class {
        free_until_pos[reg] = InstPoint::min_value();
      }
    }
  }

  // All registers that would be used at the same time as the current interval
  // are partially blocked, up to the point when they start being used.
  {
    let int = &state.intervals;
    let cur_id = id;
    for &id in &state.inactive {
      if let Some(reg) = int.allocated_register(id) {
        if reg.get_class() != reg_class {
          continue;
        }
        if let Some(intersect_at) =
          int.intersects_with(id, cur_id, &state.fragments)
        {
          if intersect_at < free_until_pos[reg] {
            free_until_pos[reg] = intersect_at;
          }
        }
      }
    }
  }

  // Find the register with the furthest next use, if there's any.
  let mut best_reg = None;
  let mut best_pos = InstPoint::min_value();
  for &(reg, pos) in free_until_pos.iter() {
    if pos > best_pos {
      best_pos = pos;
      best_reg = Some(reg);
    }
  }

  best_reg.and_then(|reg| Some((reg, best_pos)))
}

fn try_allocate_reg<F: Function>(
  id: LiveId, state: &mut State<F>, reg_universe: &RealRegUniverse,
) -> bool {
  let reg_class = state.intervals.reg_class(id);

  let (best_reg, best_pos) = if let Some(solution) =
    select_naive_reg(state, id, reg_class, reg_universe)
  {
    solution
  } else {
    debug!("try_allocate_reg: all registers taken, need to spill.");
    return false;
  };
  debug!(
    "try_allocate_reg: best register {:?} has next use at {:?}",
    best_reg, best_pos
  );

  if state.intervals.end_point(id, &state.fragments) >= best_pos {
    // Partial solution: the register is available until best_pos, and is
    // unavailable later. It must be split before the best position.
    let last_use = find_last_use_before(state, id, best_pos);

    // TODO theoretically, this could be anywhere in [last_use, best_pos].
    let split_pos = last_use;
    //let split_pos = find_optimal_split_pos(state, id, last_use, best_pos).unwrap();

    if split_pos <= state.intervals.start_point(id, &state.fragments) {
      debug!("try_allocate_reg: partial cover: nowhere to split");
      return false;
    }

    let new_int = split(state, id, Split::At(split_pos));
    state.insert_unhandled(new_int);
  }

  // At least a partial match: allocate.
  debug!("{:?}: {:?} <- {:?}", id, state.intervals.vreg(id), best_reg);
  state.intervals.set_reg(id, best_reg);

  true
}

/// Finds the first use for the current interval that's located after the given
/// `pos` (included), in a broad sense of use (any of use, def or mod).
///
/// Extends to the left, that is, "modified" means "used".
fn find_next_use_after<F: Function>(
  int: &Intervals, id: LiveId, pos: InstPoint, func: &F, fragments: &Fragments,
) -> Option<InstPoint> {
  trace!("find next use of {} after {:?}", int.display(id, fragments), pos);
  if int.end_point(id, fragments) < pos {
    return None;
  }

  let reg = int.reg(id);
  for &frag_id in &int.fragments(id).frag_ixs {
    let frag = &fragments[frag_id];
    if frag.last < pos {
      continue;
    }
    for inst_id in frag.first.iix.dotdot(frag.last.iix.plus_one()) {
      if inst_id < pos.iix {
        continue;
      }
      // TODO this is really inefficient; at least cache those.
      let uses = func.get_regs(func.get_insn(inst_id));
      // TODO not sure about the proper extent to use here: use or def side, for
      // modified?
      let wreg = Writable::from_reg(reg);
      if uses.used.contains(reg) || uses.modified.contains(wreg) {
        let candidate = InstPoint::new_use(inst_id);
        // This final comparison takes the side into account.
        if pos <= candidate && candidate <= frag.last {
          trace!("found next use at {:?}", candidate);
          return Some(candidate);
        }
      }
      if uses.defined.contains(wreg) {
        let candidate = InstPoint::new_def(inst_id);
        // See comment above.
        if pos <= candidate && candidate <= frag.last {
          trace!("found next use at {:?}", candidate);
          return Some(candidate);
        }
      }
    }
  }
  trace!("found no next use");
  None
}

fn allocate_blocked_reg<F: Function>(
  cur_id: LiveId, state: &mut State<F>, reg_universe: &RealRegUniverse,
) -> Result<(), String> {
  let start_pos = state.intervals.start_point(cur_id, &state.fragments);
  let reg_class = state.intervals.reg_class(cur_id);

  // Note: in this function, "use" isn't just a use as in use-def; it really
  // means a mention, so either a use or a definition.
  //
  // 1. Compute all the positions of next uses for registers of active intervals
  // and inactive intervals that might intersect with the current one.
  // 2. Then use this to select the interval with the further next use.
  // 3. Spill either the current interval or active/inactive intervals with the
  //    selected register.
  // 4. Make sure that the current interval doesn't intersect with the fixed
  //    interval for the selected register.

  // Step 1: compute all the next use positions.
  let mut next_use_pos = RegisterMapping::with_default(
    reg_class,
    reg_universe,
    InstPoint::max_value(),
  );

  trace!(
    "allocate_blocked_reg: searching reg with next use after {:?}",
    start_pos
  );

  for &id in &state.active {
    let int = &state.intervals;
    if int.reg_class(id) != reg_class {
      continue;
    }
    if let Some(reg) = int.allocated_register(id) {
      if let Some(next_use) =
        find_next_use_after(int, id, start_pos, state.func, &state.fragments)
      {
        if next_use < next_use_pos[reg] {
          next_use_pos[reg] = next_use;
        }
      }
    }
  }

  for &id in &state.inactive {
    let int = &state.intervals;
    if int.reg_class(id) != reg_class {
      continue;
    }
    if int.intersects_with(id, cur_id, &state.fragments).is_none() {
      continue;
    }
    if let Some(reg) = &int.allocated_register(id) {
      if let Some(next_use) =
        find_next_use_after(int, id, start_pos, state.func, &state.fragments)
      {
        if next_use < next_use_pos[*reg] {
          next_use_pos[*reg] = next_use;
        }
      }
    }
  }

  // Step 2: find the register with the furthest next use.
  let best_reg = {
    let mut best = None;
    for (reg, pos) in next_use_pos.iter() {
      trace!("allocate_blocked_reg: {:?} has next use at {:?}", reg, pos);
      match best {
        None => best = Some((reg, pos)),
        Some((ref mut best_reg, ref mut best_pos)) => {
          if *best_pos < pos {
            *best_pos = pos;
            *best_reg = reg;
          }
        }
      }
    }
    match best {
      Some(best) => *best.0,
      None => {
        return Err(format!(
          "no register available in this class: {:?}",
          reg_class
        ))
      }
    }
  };
  debug!(
    "selecting blocked register {:?} with furthest next use at {:?}",
    best_reg, next_use_pos[best_reg]
  );

  // Step 3: if the next use of the current interval is after the furthest use
  // of the selected register, then we should spill the current interval.
  // Otherwise, spill other intervals.
  let first_use = find_next_use_after(
    &state.intervals,
    cur_id,
    InstPoint::min_value(),
    state.func,
    &state.fragments,
  )
  .expect("an interval must have uses");

  debug!(
    "current first used at {:?}, next use of best reg at {:?}",
    first_use, next_use_pos[best_reg]
  );

  if first_use == next_use_pos[best_reg] {
    // The register is already taken at this position, there's nothing much we
    // can do.
    return Err("running out of registers".into());
  }

  if first_use > next_use_pos[best_reg] {
    debug!("spill current interval");
    let new_int = split(state, cur_id, Split::At(first_use));
    state.insert_unhandled(new_int);
    state.spill(cur_id);
  } else {
    debug!("taking over register, spilling intersecting intervals");

    // Spill intervals that currently block the selected register.
    state.intervals.set_reg(cur_id, best_reg);

    let mut next_active = Vec::new();
    let mut next_inactive = Vec::new();

    // Check that there's no interference with a fixed interval, and if so split
    // at the intersection.
    {
      let mut block_pos = InstPoint::max_value();

      for &id in &state.active {
        if state.intervals.reg_class(id) != reg_class {
          continue;
        }
        if let Some(reg) = state.intervals.fixed_reg(id) {
          if reg == best_reg {
            block_pos = InstPoint::min_value();
            // TODO this break assumes there's only one fixed interval per real
            // register. Check this assumption.
            //break;
          }
        }
      }

      for &id in &state.inactive {
        if state.intervals.reg_class(id) != reg_class {
          continue;
        }
        if let Some(reg) = state.intervals.fixed_reg(id) {
          if reg.get_index() == best_reg.get_index() {
            if let Some(intersect_pos) =
              state.intervals.intersects_with(id, cur_id, &state.fragments)
            {
              if intersect_pos < block_pos {
                block_pos = intersect_pos;
              }
            }
          }
        }
      }

      if block_pos < state.intervals.end_point(cur_id, &state.fragments) {
        debug!("allocate_blocked_reg: fixed conflict! blocked at {:?}, while ending at {:?}",
          block_pos, state.intervals.end_point(cur_id, &state.fragments));
        if let Some(child) = split_and_spill(state, cur_id, block_pos)? {
          next_inactive.push(child);
        }
      }
    }

    for &id in &state.active {
      if state.intervals.reg_class(id) != reg_class {
        continue;
      }
      if let Some(reg) = state.intervals.allocated_register(id) {
        if reg == best_reg {
          // spill it!
          debug!("allocate_blocked_reg: split and spill active stolen reg");
          if let Some(child) = split_and_spill(state, id, start_pos)? {
            next_active.push(child);
          }
          break;
        }
      }
    }

    // TODO sacrifice a goat to the borrowck gods, or have split_at take
    // intervals/fragments/func to make the conflict disappear.
    let inactive = state.inactive.clone();
    for id in inactive {
      if state.intervals.reg_class(id) != reg_class {
        continue;
      }
      if let Some(reg) = state.intervals.allocated_register(id) {
        if reg == best_reg {
          if let Some(_) =
            state.intervals.intersects_with(id, cur_id, &state.fragments)
          {
            debug!("allocate_blocked_reg: split and spill inactive stolen reg");
            // start_pos is in the middle of a hole in the split interval
            // (otherwise it'd be active), so it's a great split position.
            if let Some(child) = split_and_spill(state, id, start_pos)? {
              next_inactive.push(child);
            }
          }
          // TODO
          // break;
        }
      }
    }

    state.active.append(&mut next_active);
    state.inactive.append(&mut next_inactive);
  }

  Ok(())
}

#[derive(Debug)]
enum Split {
  At(InstPoint),
  /// Split in [left, right].
  Between(InstPoint, InstPoint),
}

/// Finds the last use of a vreg before a given target, including it in possible
/// return values.
/// Extends to the right, that is, modified means "def".
fn find_last_use_before<F: Function>(
  state: &mut State<F>, id: LiveId, target: InstPoint,
) -> InstPoint {
  debug_assert!(
    state.intervals.start_point(id, &state.fragments) <= target,
    "find_last_use_before: no intervals before the target"
  );

  let mut last_use = None;
  let reg = state.intervals.reg(id);
  for &i in &state.intervals.fragments(id).frag_ixs {
    let frag = state.fragments[i];
    for inst in frag.first.iix.dotdot(frag.last.iix.plus_one()) {
      let reg_uses = state.func.get_regs(state.func.get_insn(inst));
      let mut use_ = None;
      let wreg = Writable::from_reg(reg);
      if reg_uses.defined.contains(wreg) || reg_uses.modified.contains(wreg) {
        use_ = Some(InstPoint::new_def(inst))
      } else if reg_uses.used.contains(reg) {
        use_ = Some(InstPoint::new_use(inst));
      }
      if let Some(use_) = use_ {
        if use_ <= target {
          last_use = Some(use_);
        } else {
          break;
        }
      }
    }
  }
  trace!(
    "last use of {:?} before {:?} found at {:?}",
    id,
    target,
    last_use.as_ref().expect("couldn't find last use"),
  );
  return last_use.unwrap();

  /* TODO revisit this code later.
  // Find the first fragment which could contain candidates, then look
  // backwards until the beginning.

  let frag_ixs = &state.intervals.fragments(id).frag_ixs;

  let mut start_from = None;
  for &i in frag_ixs {
    let frag = state.fragments[i];
    if frag.contains(&target) || frag.last <= target {
      start_from = Some(i);
    } else {
      break;
    }
  }

  let mut start_from = start_from.expect("contradicts first assertion");

  // Look backwards for the last use.
  let reg = state.intervals.reg(id);
  loop {
    let frag = state.fragments[start_from];

    let mut inst = frag.last.iix;
    while inst >= frag.first.iix {
      inst = inst.minus(1);
      // TODO use the inst->uses cache.
      let reg_uses = state.func.get_regs(state.func.get_insn(inst));
      if reg_uses.defined.contains(reg) || reg_uses.modified.contains(reg) {
        trace!("find_last_use_before: found def {:?}", inst);
        return InstPoint::new_def(inst);
      }
      if reg_uses.used.contains(reg) {
        trace!("find_last_use_before: found use {:?}", inst);
        return InstPoint::new_use(inst);
      }
    }

    debug_assert!(
      start_from.get() > 0,
      "find_last_use_before: should have found use"
    );
    start_from = start_from.minus(1);
  }
  */
}

fn is_vreg_defined_at<F: Function>(
  state: &State<F>, id: LiveId, pos: InstPoint,
) -> bool {
  if pos.pt != Point::Def {
    return false;
  }
  let reg = Writable::from_reg(state.intervals.reg(id));
  state.func.get_regs(state.func.get_insn(pos.iix)).defined.contains(reg)
}

/// Finds an optimal split position, whenever we're given a range of possible
/// positions where to split.
///
/// Currently, selects:
/// - the left part of the range if it's a def or a use,
/// - or the use just next to the left part of the range.
fn find_optimal_split_pos<F: Function>(
  state: &State<F>, id: LiveId, from: InstPoint, to: InstPoint,
) -> Result<InstPoint, ()> {
  trace!("find_optimal_split_pos between {:?} and {:?}", from, to);
  // TODO Consider loop depth to avoid splitting in the middle of a loop
  // whenever possible.
  debug_assert!(from <= to, "split between positions are inconsistent");
  debug_assert!(
    state.intervals.covers(id, &from, &state.fragments),
    "split between start not in interval"
  );
  debug_assert!(
    state.intervals.covers(id, &to, &state.fragments),
    "split between end not in interval"
  );

  if from == to {
    debug_assert!(
      from.pt == Point::Use,
      "nowhere to split in between {:?} and itself",
      from
    );
    return Ok(from);
  }

  let reg = state.intervals.reg(id);
  let wreg = Writable::from_reg(reg);

  let mut found = None;
  for iix in from.iix.dotdot(to.iix.plus(1)) {
    let reg_uses = state.func.get_regs(state.func.get_insn(iix));

    let iuse = InstPoint::new_use(iix);
    if state.intervals.covers(id, &iuse, &state.fragments) {
      if !reg_uses.used.contains(reg) && !reg_uses.modified.contains(wreg) {
        found = Some(iuse);
        break;
      }
    }

    let next_use = InstPoint::new_use(iix.plus(1));
    if reg_uses.defined.contains(wreg) && next_use < to {
      found = Some(next_use);
      break;
    }
  }

  if let Some(pos) = found {
    trace!("find_optimal_split_pos: {:?}", pos);
    debug_assert!(from <= pos && pos <= to);
    return Ok(pos);
  }

  if from.pt == Point::Use {
    Ok(from)
  } else {
    Err(())
  }
}

/// Splits the interval according to the Split parameter.
///
/// If the split position is precise, then it must either be a Def of the
/// current vreg, or it must be at a Use position (otherwise there's no place to
/// put the moves created by the split).
///
/// If the split position is a interval of possible split positions, then it
/// must contain at least one position that satisfies one of these two
/// criterias.
///
/// The id of the new interval is returned, while the parent interval is mutated
/// in place. The child interval starts after (including) split_pos.
fn split<F: Function>(
  state: &mut State<F>, id: LiveId, split_pos: Split,
) -> LiveId {
  debug!(
    "split {:?} {} at {:?}",
    split_pos,
    state.intervals.display(id, &state.fragments),
    split_pos
  );

  let at_pos = match split_pos {
    Split::At(pos) => pos,
    Split::Between(from, to) => {
      find_optimal_split_pos(state, id, from, to).unwrap()
    }
  };

  // Trying to split between an use and a def means there's nowhere to put
  // spill/fill/move instructions, so don't do that.
  debug_assert!(
    is_vreg_defined_at(state, id, at_pos) || at_pos.pt == Point::Use,
    "invalid split position"
  );
  debug_assert!(
    state.intervals.covers(id, &at_pos, &state.fragments),
    "trying to split outside the interval"
  );

  let parent_start = state.intervals.start_point(id, &state.fragments);
  debug_assert!(parent_start <= at_pos, "we must split after the start");
  debug_assert!(
    state.intervals.end_point(id, &state.fragments) != parent_start,
    "no space to split"
  );

  let vreg = state
    .intervals
    .reg(id)
    .as_virtual_reg()
    .expect("must only operate on virtual intervals");

  let fragments = &state.fragments;
  let frags = state.intervals.fragments_mut(id);

  // We need to split at the first range that's before or contains the "at"
  // position, reading from the end to the start.
  let split_ranges_at = frags
    .frag_ixs
    .iter()
    .rposition(|&frag_id| {
      let frag = fragments[frag_id];
      frag.last < at_pos || frag.contains(&at_pos)
    })
    .expect("split would create an empty child");

  let mut child_frag_ixs = frags.frag_ixs.split_off(split_ranges_at);

  // The split position is either in the middle of a lifetime hole, in which
  // case we don't need to do anything. Otherwise, we might need to split a
  // range fragment into two parts.
  if let Some(&frag_ix) = child_frag_ixs.first() {
    let frag = &state.fragments[frag_ix];
    if frag.first != at_pos && frag.contains(&at_pos) {
      // We're splitting in the middle of a fragment: [L, R].
      // Split it into two fragments: parent [L, pos[ + child [pos, R].
      debug_assert!(frag.first < frag.last, "trying to split unit fragment");
      debug_assert!(frag.first <= at_pos, "no space to split fragment");

      let parent_first = frag.first;
      let parent_last = prev_pos(at_pos);
      let child_first = at_pos;
      let child_last = frag.last;

      debug!(
        "split fragment [{:?}; {:?}] into two parts: [{:?}; {:?}] to [{:?}; {:?}]",
        frag.first, frag.last,
        parent_first,
        parent_last,
        child_first,
        child_last
      );

      debug_assert!(parent_first <= parent_last);
      debug_assert!(parent_last <= child_first);
      debug_assert!(child_first <= child_last);

      let bix = frag.bix;

      // Parent range.
      let count = 1; // unused by LSRA.
      let parent_frag =
        RangeFrag::new(state.func, bix, parent_first, parent_last, count);

      let parent_frag_ix = RangeFragIx::new(state.fragments.len());
      state.fragments.push(parent_frag);

      // Child range.
      let child_frag =
        RangeFrag::new(state.func, bix, child_first, child_last, count);
      let child_frag_ix = RangeFragIx::new(state.fragments.len());
      state.fragments.push(child_frag);

      // Note the sorted order is maintained, by construction.
      frags.frag_ixs.push(parent_frag_ix);
      child_frag_ixs[0] = child_frag_ix;
    }
  }

  if frags.frag_ixs.is_empty() {
    // The only possible way is that we're trying to split [(A;B),...] at A, so
    // creating a unit [A, A] fragment. Otherwise, it's a bug and this assert
    // should catch it.
    debug_assert!(
      split_ranges_at == 0 && parent_start == at_pos,
      "no fragments in the parent interval"
    );

    let frag = &state.fragments[child_frag_ixs[0]];
    let parent_frag =
      RangeFrag::new(state.func, frag.bix, at_pos, at_pos, /* count */ 1);

    let parent_frag_ix = RangeFragIx::new(state.fragments.len());
    state.fragments.push(parent_frag);

    frags.frag_ixs.push(parent_frag_ix);
  }

  debug_assert!(!child_frag_ixs.is_empty(), "no fragments in child interval");

  let child_sorted_frags = SortedRangeFragIxs { frag_ixs: child_frag_ixs };

  let child_int = VirtualRange {
    vreg,
    rreg: None,
    sorted_frags: child_sorted_frags,
    // These two fields are not used by linear scan.
    size: 0,
    spill_cost: None,
  };

  // Insert child in virtual ranges and live intervals.
  let vreg_ix = VirtualRangeIx::new(state.intervals.virtual_ranges.len());
  state.intervals.virtual_ranges.push(child_int);

  let child_id = LiveId(state.intervals.num_intervals());
  let child_int = LiveInterval {
    id: child_id,
    kind: LiveIntervalKind::Virtual(vreg_ix),
    parent: Some(id),
    spill_slot: state.intervals.spill_slot(id),
  };
  state.intervals.push_interval(child_int);

  debug!("split results:");
  debug!("- {}", state.intervals.display(id, &state.fragments));
  debug!("- {}", state.intervals.display(child_id, &state.fragments));

  child_id
}

fn prev_pos(mut pos: InstPoint) -> InstPoint {
  match pos.pt {
    Point::Def => {
      pos.pt = Point::Use;
      pos
    }
    Point::Use => {
      pos.iix = pos.iix.minus(1);
      pos.pt = Point::Def;
      pos
    }
    _ => unreachable!(),
  }
}

/// Splits the given interval between the last use before `split_pos` and
/// `split_pos`.
///
/// In case of two-ways split (i.e. only place to split is precisely split_pos),
/// returns the live interval id for the middle child, to be added back to the
/// list of active/inactive intervals after iterating on these.
fn split_and_spill<F: Function>(
  state: &mut State<F>, id: LiveId, split_pos: InstPoint,
) -> Result<Option<LiveId>, String> {
  // First position that's the last use, or the next use just after the last def.
  let last_use = find_last_use_before(state, id, split_pos);
  debug!("split_and_spill: spill between {:?} and {:?}", last_use, split_pos);

  let mut two_ways_child = None;

  let child = if last_use == split_pos.at_use() {
    // The interval is used at last_use, but we must split there:
    // - split the parent at last_use into itself [..., prev of last use] and child: [last_use, ...]
    // - split the child into [last_use, last_use] and grandchild [succ of last_use, ...]
    debug!("two-ways split and spill");

    let child = split(state, id, Split::At(last_use));
    state
      .intervals
      .set_reg(child, state.intervals.allocated_register(id).unwrap());
    state.spill(child);
    two_ways_child = Some(child);

    split(state, child, Split::Between(last_use, split_pos))
  } else {
    state.spill(id);
    split(state, id, Split::Between(last_use, split_pos))
  };

  let child_start = state.intervals.start_point(child, &state.fragments);

  // Split until the next register use.
  match find_next_use_after(
    &state.intervals,
    child,
    split_pos,
    state.func,
    &state.fragments,
  ) {
    Some(next_use_pos) => {
      // When the next use coincides with the spill position, since this was the
      // register with the furthest next use, and we wanted to split it strictly
      // before its next use, then we can't actually split further.
      if child_start == next_use_pos {
        return Err("ran out of registers".into());
      }
      debug!("split spilled interval before next use @ {:?}", next_use_pos);

      let child = split(state, child, Split::At(next_use_pos));
      state.intervals.remove_spill(child);
      state.insert_unhandled(child);
    }
    None => {
      // Let it be spilled for the rest of its lifetime.
      // TODO do we even need to store it?
    }
  }

  // In both cases, the middle child interval can remain on the stack.
  debug!("unused split interval {:?} becomes handled", child);
  state.handled.push(child);
  Ok(two_ways_child)
}

/// A mapping from real reg to some T.
#[derive(Clone)]
struct RegisterMapping<T> {
  offset: usize,
  regs: Vec<(RealReg, T)>,
  reg_class: RegClass,
}

impl<T: Copy> RegisterMapping<T> {
  fn with_default(
    reg_class: RegClass, reg_universe: &RealRegUniverse, initial_value: T,
  ) -> Self {
    let mut regs = Vec::new();
    let mut offset = 0;
    // Collect all the registers for the current class.
    if let Some(ref info) = reg_universe.allocable_by_class[reg_class as usize]
    {
      debug_assert!(info.first <= info.last);
      offset = info.first;
      for reg in &reg_universe.regs[info.first..=info.last] {
        debug_assert!(regs.len() == reg.0.get_index() - offset);
        regs.push((reg.0, initial_value));
      }
    };
    Self { offset, regs, reg_class }
  }

  fn iter<'a>(&'a self) -> std::slice::Iter<(RealReg, T)> {
    self.regs.iter()
  }
}

impl<T> std::ops::Index<RealReg> for RegisterMapping<T> {
  type Output = T;
  fn index(&self, rreg: RealReg) -> &Self::Output {
    debug_assert!(
      rreg.get_class() == self.reg_class,
      "trying to index a reg from the wrong class"
    );
    &self.regs[rreg.get_index() - self.offset].1
  }
}

impl<T> std::ops::IndexMut<RealReg> for RegisterMapping<T> {
  fn index_mut(&mut self, rreg: RealReg) -> &mut Self::Output {
    debug_assert!(
      rreg.get_class() == self.reg_class,
      "trying to index a reg from the wrong class"
    );
    &mut self.regs[rreg.get_index() - self.offset].1
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
  let (_sanitized_reg_uses, rlrs, vlrs, fragments, liveouts, _est_freqs) =
    run_analysis(func, reg_universe).map_err(|err| err.to_string())?;

  let intervals = Intervals::new(rlrs, vlrs, &fragments);

  let (fragments, intervals, num_spill_slots) = {
    let mut state = State::new(func, fragments, intervals);

    // Put all the fixed intervals in the inactive list: they're either becoming
    // active or should be remain inactive.

    for &id in &state.unhandled {
      if state.intervals.is_fixed(id) {
        state.inactive.push(id);
      }
    }

    let mut prev_start = None;
    while let Some(id) = state.next_unhandled() {
      trace!(
        "main loop: allocating {}",
        state.intervals.display(id, &state.fragments)
      );

      {
        let start = state.intervals.start_point(id, &state.fragments);
        if let Some(ref prev) = prev_start {
          debug_assert!(*prev <= start, "main loop must make progress");
        };
        prev_start = Some(start);
      }

      update_state(id, &mut state);

      if !state.intervals.is_fixed(id)
        && state.intervals.spill_slot(id).is_none()
      {
        if !try_allocate_reg(id, &mut state, reg_universe) {
          allocate_blocked_reg(id, &mut state, reg_universe)?;
        }
        if let Some(_) = state.intervals.allocated_register(id) {
          state.active.push(id);
        }
      }

      debug!("");
    }

    debug!("linear scan results:");
    for id in 0..state.intervals.data.len() {
      debug!("{}", state.intervals.display(LiveId(id), &state.fragments));
    }
    debug!("");

    (state.fragments, state.intervals, state.next_spill_slot.get())
  };

  // Filter fixed intervals, they're already in the right place.
  let mut virtual_intervals = intervals
    .data
    .iter()
    .filter(|int| {
      if let LiveIntervalKind::Fixed(_) = &int.kind {
        false
      } else {
        true
      }
    })
    .collect::<Vec<_>>();

  // Sort by starting point, so we can plug all the different intervals
  // together.
  virtual_intervals.sort_by_key(|int| {
    let vrange = &intervals.virtual_ranges[int.unwrap_virtual()];
    let first_frag_ix = vrange.sorted_frags.frag_ixs[0];
    fragments[first_frag_ix].first
  });

  let memory_moves =
    resolve_moves(func, &intervals, &virtual_intervals, &fragments, &liveouts);

  apply_registers(func, &intervals, virtual_intervals, &fragments);

  fill_memory_moves(func, memory_moves, reg_universe, num_spill_slots)
}

fn is_block_boundary<F: Function>(func: &F, pos: InstPoint) -> bool {
  // TODO instead, create a set of block boundaries instruction, so this
  // becomes O(1)?
  for block in func.blocks() {
    let insts = func.block_insns(block);
    if (pos.iix == insts.first() && pos.pt == Point::Use)
      || (pos.iix == insts.last() && pos.pt == Point::Def)
    {
      return true;
    }
  }
  false
}

fn find_enclosing_interval(
  vreg: VirtualReg, inst: InstPoint, intervals: &Intervals,
  fragments: &Fragments, virtual_intervals: &Vec<&LiveInterval>,
) -> Option<LiveId> {
  for vint in virtual_intervals {
    if intervals.vreg(vint.id) != vreg {
      continue;
    }
    if intervals.covers(vint.id, &inst, fragments) {
      return Some(vint.id);
    }
  }
  None
}

fn resolve_moves<F: Function>(
  func: &F, intervals: &Intervals, virtual_intervals: &Vec<&LiveInterval>,
  fragments: &Fragments, liveouts: &TypedIxVec<BlockIx, Set<Reg>>,
) -> InstsAndPoints<F> {
  let mut memory_moves = InstsAndPoints::new();

  debug!("resolve_moves");
  for &interval in virtual_intervals {
    let vrange_ix = interval.unwrap_virtual();
    let vrange = &intervals.virtual_ranges[vrange_ix];

    let rreg = match vrange.rreg {
      None => {
        // Sanity checks.
        debug_assert!(
          interval.spill_slot.is_some(),
          "interval has no location"
        );
        debug_assert!(
          interval.parent.is_some(),
          "spilled interval must have a parent"
        );
        // Nothing to do in this case.
        continue;
      }
      Some(rreg) => rreg,
    };

    let vreg = intervals.vreg(interval.id);

    if let Some(parent_id) = interval.parent {
      // Reconnect with the parent location, by adding a move if needed.
      let at_inst = intervals.start_point(interval.id, &fragments);
      if !is_block_boundary(func, at_inst) {
        let mut at_inst = at_inst;
        at_inst.pt = Point::Reload;

        let wreg = Writable::from_reg(rreg);
        let reload = if let Some(spill_slot) = intervals.spill_slot(parent_id) {
          trace!(
            "inblock fixup: {:?} gen reload from {:?} to {:?} at {:?}",
            interval.id,
            spill_slot,
            rreg,
            at_inst
          );
          Some(func.gen_reload(wreg, spill_slot, vreg))
        } else {
          let from_rreg = intervals.allocated_register(parent_id).unwrap();
          if from_rreg != rreg {
            trace!(
              "inblock fixup: {:?} gen move from {:?} to {:?} at {:?}",
              interval.id,
              from_rreg,
              rreg,
              at_inst
            );
            Some(func.gen_move(wreg, from_rreg, vreg))
          } else {
            None
          }
        };
        if let Some(reload) = reload {
          memory_moves.push(InstAndPoint::new(at_inst, reload));
        }
      }
    }

    if let Some(spill_slot) = interval.spill_slot {
      // This interval has been spilled (i.e. split). Spill after the last def
      // or before the last use.
      let end = intervals.end_point(interval.id, &fragments);
      // TODO must probably make something finer grain on the last effective
      // use, def or mod of the instruction.
      let mut at_inst = end;
      at_inst.pt = if at_inst.pt == Point::Use {
        Point::Reload
      } else {
        debug_assert!(at_inst.pt == Point::Def);
        Point::Spill
      };
      if !is_block_boundary(func, end) {
        let spill = func.gen_spill(spill_slot, rreg, vreg);
        trace!(
          "inblock fixup: {:?} gen spill from {:?} to {:?} at {:?}",
          interval.id,
          rreg,
          spill_slot,
          at_inst
        );
        memory_moves.push(InstAndPoint::new(at_inst, spill));
      }
    }
  }

  // Figure the sequence of parallel moves to insert at block boundaries:
  // - for each block
  //  - for each liveout vreg in this block
  //    - for each successor of this block
  //      - if the locations allocated in the block and its successor don't
  //      match, insert a pending move from one location to the other.
  //
  // Once that's done:
  // - resolve cycles in the pending moves
  // - generate real moves from the pending moves.
  for block in func.blocks() {
    let mut parallel_moves = Vec::new();

    let successors = func.block_succs(block);

    // Where to insert the fixup move, if needed? If there's more than one
    // successor to the current block, inserting in the current block will
    // impact all the successors.
    //
    // We assume critical edges have been split, so
    // if the current block has more than one successor, then its successors
    // have at most one predecessor.
    let has_one_successor = successors.len() == 1;

    for succ in successors {
      for &reg in liveouts[block].iter() {
        let vreg =
          if let Some(vreg) = reg.as_virtual_reg() { vreg } else { continue };

        let (succ_first_inst, succ_id) = {
          let first_inst = InstPoint::new_use(func.block_insns(succ).first());
          let found = match find_enclosing_interval(
            vreg,
            first_inst,
            &intervals,
            fragments,
            &virtual_intervals,
          ) {
            Some(found) => found,
            // The vreg is unused in this successor.
            None => continue,
          };
          (first_inst, found)
        };

        // Find the interval for this (vreg, inst) pair.
        // TODO Probably need to optimized this.
        let (cur_last_inst, cur_id) = {
          let last_inst = func.block_insns(block).last();
          // see XXX above
          let last_inst = InstPoint::new_def(last_inst);
          let cur_id = find_enclosing_interval(
            vreg,
            last_inst,
            &intervals,
            fragments,
            &virtual_intervals,
          )
          .expect(&format!(
            "no interval for given {:?}:{:?} pair in current {:?}",
            vreg, last_inst, block
          ));
          (last_inst, cur_id)
        };

        let insert_pos = if has_one_successor {
          let mut pos = cur_last_inst;
          // Before the control flow instruction.
          pos.pt = Point::Reload;
          pos
        } else {
          let mut pos = succ_first_inst;
          pos.pt = Point::Reload;
          pos
        };

        let inst = match (
          intervals.allocated_register(cur_id),
          intervals.allocated_register(succ_id),
        ) {
          (Some(cur_rreg), Some(succ_rreg)) => {
            // Register to register move.
            if cur_rreg == succ_rreg {
              continue;
            }
            parallel_moves.push((cur_rreg, succ_rreg));
            trace!(
              "boundary fixup: gen move at {:?} for {:?} between {:?} and {:?}",
              insert_pos,
              vreg,
              block,
              succ
            );
            func.gen_move(Writable::from_reg(succ_rreg), cur_rreg, vreg)
          }

          (Some(cur_rreg), None) => {
            // Register to stack: spill.
            let spillslot = intervals
              .spill_slot(succ_id)
              .expect("reg->stack move without a spill slot");
            trace!(
              "boundary fixup: gen spill at {:?} for {:?} between {:?} and {:?}",
              insert_pos,
              vreg,
              block,
              succ
            );
            func.gen_spill(spillslot, cur_rreg, vreg)
          }

          (None, Some(rreg)) => {
            // Stack to register: fill.
            let spillslot = intervals
              .spill_slot(cur_id)
              .expect("stack->reg move without a spill slot");
            trace!(
              "boundary fixup: gen reload at {:?} for {:?} between {:?} and {:?}",
              insert_pos,
              vreg,
              block,
              succ
            );
            func.gen_reload(Writable::from_reg(rreg), spillslot, vreg)
          }

          (None, None) => {
            // Stack to stack: ugh.
            let left_spill_slot = intervals.spill_slot(cur_id).unwrap();
            let right_spill_slot = intervals.spill_slot(succ_id).unwrap();
            assert_eq!(
              left_spill_slot, right_spill_slot,
              "NYI: move from stack to stack."
            );
            continue;
          }
        };

        memory_moves.push(InstAndPoint::new(insert_pos, inst));
      }
    }

    // TODO consider cyclic moves here.
    {
      let mut set = Set::empty();
      for pm in &parallel_moves {
        if set.contains(pm.0) {
          unimplemented!("cyclic moves");
        }
        set.insert(pm.1);
      }
    }
  }
  debug!("");

  memory_moves
}

fn apply_registers<F: Function>(
  func: &mut F, intervals: &Intervals, virtual_intervals: Vec<&LiveInterval>,
  fragments: &Fragments,
) {
  for inst_id in func.insn_indices() {
    let inst_use = InstPoint::new_use(inst_id);
    let inst_def = InstPoint::new_def(inst_id);

    // TODO optimize this by maintaining sorted lists of active and unhandled
    // intervals.
    let mut map_uses = Map::<VirtualReg, RealReg>::default();
    let mut map_defs = Map::<VirtualReg, RealReg>::default();

    for &interval in &virtual_intervals {
      let id = interval.id;
      if intervals.is_fixed(id) {
        continue;
      }
      if intervals.covers(id, &inst_def, &fragments) {
        if let Some(rreg) = intervals.allocated_register(id) {
          let vreg = intervals.reg(id).as_virtual_reg().unwrap();
          let prev_entry = map_defs.insert(vreg, rreg);
          debug_assert!(
            prev_entry.is_none() || prev_entry.unwrap() == rreg,
            "def vreg {:?} already mapped to {:?}",
            vreg,
            prev_entry.unwrap()
          );
        }
      }
      if intervals.covers(id, &inst_use, &fragments) {
        if let Some(rreg) = intervals.allocated_register(id) {
          let vreg = intervals.reg(id).as_virtual_reg().unwrap();
          let prev_entry = map_uses.insert(vreg, rreg);
          debug_assert!(
            prev_entry.is_none() || prev_entry.unwrap() == rreg,
            "use vreg {:?} already mapped to {:?}",
            vreg,
            prev_entry.unwrap()
          );
        }
      }
    }

    trace!("map_regs for {:?}", inst_id);
    trace!("uses");
    for (k, v) in &map_uses {
      trace!("- {:?} -> {:?}", k, v);
    }
    trace!("defs");
    for (k, v) in &map_defs {
      trace!("- {:?} -> {:?}", k, v);
    }

    let mut inst = func.get_insn_mut(inst_id);
    F::map_regs(&mut inst, &map_uses, &map_defs);
    trace!("");
  }
}
