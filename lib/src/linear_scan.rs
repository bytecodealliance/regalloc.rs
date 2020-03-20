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

use log::{debug, info, trace};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use std::env;
use std::fmt;

use crate::analysis::run_analysis;
use crate::data_structures::*;
use crate::inst_stream::{
  edit_inst_stream, InstAndPoint, InstToInsert, InstsAndPoints,
  RangeAllocations,
};
use crate::interface::{Function, RegAllocError, RegAllocResult};

// Local shorthands.
type Fragments = TypedIxVec<RangeFragIx, RangeFrag>;
type VirtualRanges = TypedIxVec<VirtualRangeIx, VirtualRange>;
type RealRanges = TypedIxVec<RealRangeIx, RealRange>;
type RegUses = TypedIxVec<InstIx, SanitizedInstRegUses>;

/// A unique identifier for an interval.
#[derive(Clone, Copy, PartialEq, Eq)]
struct IntId(usize);

impl fmt::Debug for IntId {
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

#[derive(Debug, Clone, Copy)]
enum Location {
  None,
  Reg(RealReg),
  Stack(SpillSlot),
}

impl Location {
  fn reg(&self) -> Option<RealReg> {
    match self {
      Location::Reg(reg) => Some(*reg),
      _ => None,
    }
  }
  fn spill(&self) -> Option<SpillSlot> {
    match self {
      Location::Stack(slot) => Some(*slot),
      _ => None,
    }
  }
  fn is_none(&self) -> bool {
    match self {
      Location::None => true,
      _ => false,
    }
  }
}

impl fmt::Display for Location {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Location::None => write!(fmt, "none"),
      Location::Reg(reg) => write!(fmt, "{:?}", reg),
      Location::Stack(slot) => write!(fmt, "{:?}", slot),
    }
  }
}

struct LiveInterval {
  /// A unique identifier in the live interval graph.
  id: IntId,
  /// Is it fixed or virtual?
  kind: LiveIntervalKind,
  /// Parent interval in the split tree.
  parent: Option<IntId>,
  child: Option<IntId>,
  /// Location assigned to this live interval.
  location: Location,

  // Cached fields
  reg_class: RegClass,
  start: InstPoint,
  end: InstPoint,
}

impl LiveInterval {
  fn is_fixed(&self) -> bool {
    match &self.kind {
      LiveIntervalKind::Fixed(_) => true,
      LiveIntervalKind::Virtual(_) => false,
    }
  }
  fn unwrap_virtual(&self) -> VirtualRangeIx {
    if let LiveIntervalKind::Virtual(r) = &self.kind {
      *r
    } else {
      unreachable!();
    }
  }
}

/// A group of live intervals.
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
      .map(|(index, kind)| {
        let (location, start, end, reg_class) = match kind {
          LiveIntervalKind::Fixed(ix) => {
            let range = &real_ranges[ix];
            let start = fragments[range.sorted_frags.frag_ixs[0]].first;
            let end =
              fragments[*range.sorted_frags.frag_ixs.last().unwrap()].last;
            let reg_class = range.rreg.get_class();
            let location = Location::Reg(range.rreg);
            (location, start, end, reg_class)
          }
          LiveIntervalKind::Virtual(ix) => {
            let range = &virtual_ranges[ix];
            let start = fragments[range.sorted_frags.frag_ixs[0]].first;
            let end =
              fragments[*range.sorted_frags.frag_ixs.last().unwrap()].last;
            let reg_class = range.vreg.get_class();
            let location = Location::None;
            (location, start, end, reg_class)
          }
        };

        LiveInterval {
          id: IntId(index),
          kind,
          parent: None,
          child: None,
          location,
          reg_class,
          start,
          end,
        }
      })
      .collect();

    Self { real_ranges, virtual_ranges, data }
  }

  fn get(&self, int_id: IntId) -> &LiveInterval {
    &self.data[int_id.0]
  }
  fn get_mut(&mut self, int_id: IntId) -> &mut LiveInterval {
    &mut self.data[int_id.0]
  }

  fn fragments(&self, int_id: IntId) -> &SortedRangeFragIxs {
    match &self.data[int_id.0].kind {
      LiveIntervalKind::Fixed(r) => &self.real_ranges[*r].sorted_frags,
      LiveIntervalKind::Virtual(r) => &self.virtual_ranges[*r].sorted_frags,
    }
  }
  fn fragments_mut(&mut self, int_id: IntId) -> &mut SortedRangeFragIxs {
    match &mut self.data[int_id.0].kind {
      LiveIntervalKind::Fixed(r) => &mut self.real_ranges[*r].sorted_frags,
      LiveIntervalKind::Virtual(r) => &mut self.virtual_ranges[*r].sorted_frags,
    }
  }

  fn fixed_reg(&self, int_id: IntId) -> Option<RealReg> {
    let int = self.get(int_id);
    if int.is_fixed() {
      Some(int.location.reg().unwrap())
    } else {
      None
    }
  }

  fn vreg(&self, int_id: IntId) -> VirtualReg {
    match &self.data[int_id.0].kind {
      LiveIntervalKind::Fixed(_) => panic!("asking for vreg of fixed interval"),
      LiveIntervalKind::Virtual(r) => self.virtual_ranges[*r].vreg,
    }
  }

  #[inline(never)]
  fn covers(
    &self, int_id: IntId, pos: InstPoint, fragments: &Fragments,
  ) -> bool {
    // Fragments are sorted by start.
    let frag_ixs = &self.fragments(int_id).frag_ixs;

    // The binary search is useful only after some threshold number of elements;
    // This value has been determined after benchmarking a large program.
    if frag_ixs.len() <= 4 {
      for &frag_ix in frag_ixs {
        let frag = &fragments[frag_ix];
        if frag.first <= pos && pos <= frag.last {
          return true;
        }
      }
      return false;
    }

    match frag_ixs.binary_search_by_key(&pos, |&index| fragments[index].first) {
      // Either we find a precise match...
      Ok(_) => true,
      // ... or we're just after an interval that could contain it.
      Err(index) => {
        // There's at least one fragment, by construction, so no need to check
        // against fragments.len().
        index > 0 && pos <= fragments[frag_ixs[index - 1]].last
      }
    }
  }

  #[inline(never)]
  fn intersects_with(
    &self, left_id: IntId, right_id: IntId, fragments: &Fragments,
  ) -> Option<InstPoint> {
    let left = self.get(left_id);
    let right = self.get(right_id);

    if left.start == right.start {
      return Some(left.start);
    }

    let left_frags = &self.fragments(left_id).frag_ixs;
    let right_frags = &self.fragments(right_id).frag_ixs;

    let mut left_i = 0;
    let mut right_i = 0;
    let mut left_max_i = left_frags.len() - 1;
    let mut right_max_i = right_frags.len() - 1;

    if left.start < right.start {
      left_i = match left_frags
        .binary_search_by_key(&right.start, |&frag_ix| fragments[frag_ix].first)
      {
        Ok(index) => return Some(fragments[left_frags[index]].first),
        Err(index) => {
          if index == 0 {
            index
          } else {
            index - 1
          }
        }
      };
    } else {
      right_i = match right_frags
        .binary_search_by_key(&left.start, |&frag_ix| fragments[frag_ix].first)
      {
        Ok(index) => return Some(fragments[right_frags[index]].first),
        Err(index) => {
          if index == 0 {
            index
          } else {
            index - 1
          }
        }
      }
    }

    if left.end < right.end {
      right_max_i = match right_frags
        .binary_search_by_key(&left.end, |&frag_ix| fragments[frag_ix].first)
      {
        Ok(index) => index,
        Err(index) => {
          if index == 0 {
            index
          } else {
            index - 1
          }
        }
      };
    } else {
      left_max_i = match left_frags
        .binary_search_by_key(&right.end, |&frag_ix| fragments[frag_ix].first)
      {
        Ok(index) => index,
        Err(index) => {
          if index == 0 {
            index
          } else {
            index - 1
          }
        }
      };
    }

    let mut left_frag = &fragments[left_frags[left_i]];
    let mut right_frag = &fragments[right_frags[right_i]];
    loop {
      if left_frag.first == right_frag.first {
        return Some(left_frag.first);
      }
      if left_frag.last < right_frag.first {
        // left_frag < right_frag, go to the range following left_frag.
        left_i += 1;
        if left_i > left_max_i {
          break;
        }
        left_frag = &fragments[left_frags[left_i]];
      } else if right_frag.last < left_frag.first {
        // left_frag > right_frag, go to the range following right_frag.
        right_i += 1;
        if right_i > right_max_i {
          break;
        }
        right_frag = &fragments[right_frags[right_i]];
      } else {
        // They intersect!
        return Some(if left_frag.first < right_frag.first {
          right_frag.first
        } else {
          left_frag.first
        });
      }
    }

    None
  }

  fn num_intervals(&self) -> usize {
    self.data.len()
  }

  fn display(&self, int_id: IntId, fragments: &Fragments) -> String {
    let int = &self.data[int_id.0];
    let vreg = if int.is_fixed() {
      "fixed".to_string()
    } else {
      format!("{:?}", self.vreg(int_id))
    };
    let frag_ixs = &self.fragments(int_id).frag_ixs;
    let fragments = frag_ixs
      .iter()
      .map(|&ix| {
        let frag = fragments[ix];
        (ix, frag.first, frag.last)
      })
      .collect::<Vec<_>>();
    format!(
      "{:?}{}: {} {} {:?}",
      int.id,
      if let Some(ref p) = int.parent {
        format!(" (parent={:?}) ", p)
      } else {
        "".to_string()
      },
      vreg,
      int.location,
      fragments
    )
  }

  // Mutators.
  fn set_reg(&mut self, int_id: IntId, reg: RealReg) {
    let int = self.get_mut(int_id);
    debug_assert!(int.location.is_none());
    debug_assert!(!int.is_fixed());
    int.location = Location::Reg(reg);
  }
  fn set_spill(&mut self, int_id: IntId, slot: SpillSlot) {
    let int = self.get_mut(int_id);
    debug_assert!(int.location.spill().is_none());
    debug_assert!(!int.is_fixed());
    int.location = Location::Stack(slot);
  }
  fn push_interval(&mut self, int: LiveInterval) {
    debug_assert!(int.id.0 == self.data.len());
    self.data.push(int);
  }
  fn set_child(&mut self, int_id: IntId, child_id: IntId) {
    if let Some(prev_child) = self.data[int_id.0].child.clone() {
      self.data[child_id.0].child = Some(prev_child);
      self.data[prev_child.0].parent = Some(child_id);
    }
    self.data[int_id.0].child = Some(child_id);
  }
}

// State management.

/// State structure, which can be cleared between different calls to register allocation.
/// TODO: split this into clearable fields and non-clearable fields.
struct State<'a, F: Function> {
  func: &'a F,
  reg_uses: &'a RegUses,

  optimal_split_strategy: OptimalSplitStrategy,

  fragments: Fragments,
  scratches: &'a [Option<RealReg>],
  intervals: Intervals,

  /// Intervals that are starting after the current interval's start position.
  unhandled: Vec<IntId>,

  /// Intervals that are covering the current interval's start position.
  active: Vec<IntId>,

  /// Intervals that are not covering but end after the current interval's start
  /// position.
  inactive: Vec<IntId>,

  /// Next available spill slot.
  next_spill_slot: SpillSlot,

  /// Maps given virtual registers to the spill slots they should be assigned
  /// to.
  spill_map: HashMap<VirtualReg, SpillSlot>,
}

impl<'a, F: Function> State<'a, F> {
  fn new(
    func: &'a F, reg_uses: &'a RegUses, fragments: Fragments,
    intervals: Intervals, scratches: &'a [Option<RealReg>],
  ) -> Self {
    // Trick! Keep unhandled in reverse sorted order, so we can just pop
    // unhandled ids instead of shifting the first element.
    let unhandled: Vec<IntId> =
      intervals.data.iter().rev().map(|int| int.id).collect();

    // Useful for debugging.
    let optimal_split_strategy = match env::var("SPLIT") {
      Ok(s) => match s.as_str() {
        "t" | "to" => OptimalSplitStrategy::To,
        "n" => OptimalSplitStrategy::NextFrom,
        "nn" => OptimalSplitStrategy::NextNextFrom,
        "p" => OptimalSplitStrategy::PrevTo,
        "pp" => OptimalSplitStrategy::PrevPrevTo,
        "m" | "mid" => OptimalSplitStrategy::Mid,
        _ => OptimalSplitStrategy::From,
      },
      Err(_) => OptimalSplitStrategy::From,
    };

    Self {
      func,
      reg_uses,
      optimal_split_strategy,
      fragments,
      scratches,
      intervals,
      unhandled,
      active: Vec::new(),
      inactive: Vec::new(),
      next_spill_slot: SpillSlot::new(0),
      spill_map: HashMap::default(),
    }
  }

  fn next_unhandled(&mut self) -> Option<IntId> {
    self.unhandled.pop()
  }

  fn insert_unhandled(&mut self, id: IntId) {
    let start_pos = self.intervals.get(id).start;
    // Maintain reversed start_pos order by inverting the operands in the
    // comparison.
    let pos = self
      .unhandled
      .binary_search_by(|&id| start_pos.cmp(&self.intervals.get(id).start));
    let pos = match pos {
      Ok(index) => index,
      Err(index) => index,
    };
    self.unhandled.insert(pos, id);
  }

  fn spill(&mut self, id: IntId) {
    let int = self.intervals.get(id);
    debug_assert!(!int.is_fixed(), "can't split fixed interval");
    debug_assert!(int.location.spill().is_none(), "already spilled");
    debug!("spilling {}", self.intervals.display(id, &self.fragments));

    let vreg = self.intervals.vreg(id);
    let spill_slot = if let Some(spill_slot) = self.spill_map.get(&vreg) {
      *spill_slot
    } else {
      let size_slot = self.func.get_spillslot_size(int.reg_class, vreg);
      let spill_slot = self.next_spill_slot.round_up(size_slot);
      self.next_spill_slot = self.next_spill_slot.inc(1);
      self.spill_map.insert(vreg, spill_slot);
      spill_slot
    };

    self.intervals.set_spill(id, spill_slot);
  }
}

/// Transitions intervals from active/inactive into active/inactive/handled.
#[inline(never)]
fn update_state<'a, F: Function>(cur_id: IntId, state: &mut State<'a, F>) {
  let intervals = &state.intervals;

  let start_point = intervals.get(cur_id).start;

  let mut next_active = Vec::new();
  let mut next_inactive = Vec::new();

  //use log::warn;
  //warn!(
  //"update_state: {:?} {:?} {} {} (start_point/active/inactive)",
  //start_point,
  //intervals.get(cur_id).end,
  //state.active.len(),
  //state.inactive.len(),
  //);

  for &id in &state.active {
    if intervals.get(id).end < start_point {
      // It's expired, forget about it.
    } else if intervals.covers(id, start_point, &state.fragments) {
      next_active.push(id);
    } else {
      next_inactive.push(id);
    }
  }

  for &id in &state.inactive {
    if intervals.get(id).end < start_point {
      // It's expired, forget about it.
    } else if intervals.covers(id, start_point, &state.fragments) {
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
#[inline(never)]
fn select_naive_reg<F: Function>(
  state: &State<F>, id: IntId, reg_class: RegClass,
  reg_universe: &RealRegUniverse,
) -> Option<(RealReg, InstPoint)> {
  let mut free_until_pos = RegisterMapping::with_default(
    reg_class,
    reg_universe,
    state.scratches[reg_class as usize],
    InstPoint::max_value(),
  );

  // All registers currently in use are blocked.
  for &id in &state.active {
    if let Some(reg) = state.intervals.get(id).location.reg() {
      if reg.get_class() == reg_class {
        free_until_pos[reg] = InstPoint::min_value();
      }
    }
  }

  // Shortcut: if all the registers are taken, don't even bother.
  if free_until_pos.iter().all(|&(_reg, pos)| pos == InstPoint::min_value()) {
    return None;
  }

  // All registers that would be used at the same time as the current interval
  // are partially blocked, up to the point when they start being used.
  {
    let cur_id = id;
    let cur_end = state.intervals.get(id).end;

    let intervals = &state.intervals;

    for &id in &state.inactive {
      if let Some(reg) = intervals.get(id).location.reg() {
        if reg.get_class() != reg_class {
          continue;
        }
        // This is the reverse of the check in try_allocate_reg.
        if free_until_pos[reg] <= cur_end {
          // Already partially blocked, skip.
          continue;
        }
        if let Some(intersect_at) =
          intervals.intersects_with(id, cur_id, &state.fragments)
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

#[inline(never)]
fn try_allocate_reg<F: Function>(
  id: IntId, state: &mut State<F>, reg_universe: &RealRegUniverse,
) -> bool {
  let reg_class = state.intervals.get(id).reg_class;

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

  if best_pos <= state.intervals.get(id).end {
    // TODO Here, it should be possible to split the interval between the start
    // (or more precisely, the last use before best_pos) and the best_pos value.
    // See also issue #32.
    return false;
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
#[inline(never)]
fn next_use(
  intervals: &Intervals, id: IntId, pos: InstPoint, reg_uses: &RegUses,
  fragments: &Fragments,
) -> Option<InstPoint> {
  trace!(
    "find next use of {} after {:?}",
    intervals.display(id, fragments),
    pos
  );
  let int = intervals.get(id);
  if int.end < pos {
    return None;
  }

  let reg = if int.is_fixed() {
    int.location.reg().unwrap().to_reg()
  } else {
    intervals.vreg(id).to_reg()
  };

  for &frag_id in &intervals.fragments(id).frag_ixs {
    let frag = &fragments[frag_id];
    if frag.last < pos {
      continue;
    }
    for inst_id in frag.first.iix.dotdot(frag.last.iix.plus_one()) {
      if inst_id < pos.iix {
        continue;
      }

      let uses = &reg_uses[inst_id];

      let at_use = InstPoint::new_use(inst_id);
      if pos <= at_use && frag.contains(&at_use) {
        if uses.san_used.contains(reg) || uses.san_modified.contains(reg) {
          debug_assert!(intervals.covers(id, at_use, fragments));
          trace!("found next use of {:?} after {:?} at {:?}", id, pos, at_use);
          return Some(at_use);
        }
      }

      let at_def = InstPoint::new_def(inst_id);
      if pos <= at_def && frag.contains(&at_def) {
        if uses.san_defined.contains(reg) || uses.san_modified.contains(reg) {
          debug_assert!(intervals.covers(id, at_def, fragments));
          trace!("found next use of {:?} after {:?} at {:?}", id, pos, at_def);
          return Some(at_def);
        }
      }
    }
  }
  trace!("found no next use");
  None
}

#[inline(never)]
fn allocate_blocked_reg<F: Function>(
  cur_id: IntId, state: &mut State<F>, reg_universe: &RealRegUniverse,
) -> Result<(), RegAllocError> {
  // If the current interval has no uses, spill it directly.
  let first_use = match next_use(
    &state.intervals,
    cur_id,
    InstPoint::min_value(),
    &state.reg_uses,
    &state.fragments,
  ) {
    Some(u) => u,
    None => {
      state.spill(cur_id);
      return Ok(());
    }
  };

  let (start_pos, reg_class) = {
    let int = state.intervals.get(cur_id);
    (int.start, int.reg_class)
  };

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
    state.scratches[reg_class as usize],
    InstPoint::max_value(),
  );
  let mut block_pos = RegisterMapping::with_default(
    reg_class,
    reg_universe,
    state.scratches[reg_class as usize],
    InstPoint::max_value(),
  );

  trace!(
    "allocate_blocked_reg: searching reg with next use after {:?}",
    start_pos
  );

  for &id in &state.active {
    if state.intervals.get(id).reg_class != reg_class {
      continue;
    }
    if let Some(reg) = state.intervals.fixed_reg(id) {
      block_pos[reg] = InstPoint::min_value();
      next_use_pos[reg] = InstPoint::min_value();
    } else if let Some(reg) = state.intervals.get(id).location.reg() {
      if let Some(next_use) = next_use(
        &state.intervals,
        id,
        start_pos,
        &state.reg_uses,
        &state.fragments,
      ) {
        next_use_pos[reg] = InstPoint::min(next_use_pos[reg], next_use);
      }
    }
  }

  for &id in &state.inactive {
    if state.intervals.get(id).reg_class != reg_class {
      continue;
    }

    let reg = match state.intervals.get(id).location.reg() {
      Some(reg) => reg,
      None => continue,
    };

    if block_pos[reg] == InstPoint::min_value() {
      // This register is already blocked.
      debug_assert!(next_use_pos[reg] == InstPoint::min_value());
      continue;
    }

    let intervals = &state.intervals;
    let intersect_pos =
      match intervals.intersects_with(id, cur_id, &state.fragments) {
        Some(pos) => pos,
        None => continue,
      };

    if state.intervals.get(id).is_fixed() {
      block_pos[reg] = InstPoint::min(block_pos[reg], intersect_pos);
      next_use_pos[reg] = InstPoint::min(next_use_pos[reg], intersect_pos);
    } else if let Some(reg) = state.intervals.get(id).location.reg() {
      if let Some(next_use) = next_use(
        &state.intervals,
        id,
        intersect_pos,
        &state.reg_uses,
        &state.fragments,
      ) {
        next_use_pos[reg] = InstPoint::min(next_use_pos[reg], next_use);
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
        return Err(RegAllocError::Other(format!(
          "the {:?} register class has no registers!",
          reg_class
        )));
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
  debug!(
    "current first used at {:?}, next use of best reg at {:?}",
    first_use, next_use_pos[best_reg]
  );

  if first_use >= next_use_pos[best_reg] {
    if first_use == start_pos {
      return Err(RegAllocError::OutOfRegisters(reg_class));
    }
    debug!("spill current interval");
    let new_int = split(state, cur_id, first_use);
    state.insert_unhandled(new_int);
    state.spill(cur_id);
  } else {
    debug!("taking over register, spilling intersecting intervals");

    // Spill intervals that currently block the selected register.
    state.intervals.set_reg(cur_id, best_reg);

    // If there's an interference with a fixed interval, split at the
    // intersection.
    let int = state.intervals.get(cur_id);
    if block_pos[best_reg] <= int.end {
      debug!("allocate_blocked_reg: fixed conflict! blocked at {:?}, while ending at {:?}",
          block_pos[best_reg], int.end);
      // TODO Here, it should be possible to only split the interval, and not
      // spill it. See also issue #32.
      split_and_spill(state, cur_id, block_pos[best_reg]);
    }

    for &id in &state.active {
      let int = state.intervals.get(id);
      if int.reg_class != reg_class {
        continue;
      }
      if let Some(reg) = int.location.reg() {
        if reg == best_reg {
          // spill it!
          debug!("allocate_blocked_reg: split and spill active stolen reg");
          split_and_spill(state, id, start_pos);
          break;
        }
      }
    }

    // TODO sacrifice a goat to the borrowck gods, or have split_at take
    // intervals/fragments/func to make the conflict disappear.
    let inactive = state.inactive.clone();
    for id in inactive {
      let int = state.intervals.get(id);
      if int.reg_class != reg_class {
        continue;
      }
      if let Some(reg) = int.location.reg() {
        if reg == best_reg {
          if let Some(_) =
            state.intervals.intersects_with(id, cur_id, &state.fragments)
          {
            debug!("allocate_blocked_reg: split and spill inactive stolen reg");
            // start_pos is in the middle of a hole in the split interval
            // (otherwise it'd be active), so it's a great split position.
            split_and_spill(state, id, start_pos);
          }
        }
      }
    }
  }

  Ok(())
}

/// Finds the last use of a vreg before a given target, including it in possible
/// return values.
/// Extends to the right, that is, modified means "def".
#[inline(never)]
fn last_use(
  intervals: &Intervals, id: IntId, pos: InstPoint, reg_uses: &RegUses,
  fragments: &Fragments,
) -> Option<InstPoint> {
  trace!("searching last use of {:?} before {:?}", id, pos,);
  let int = intervals.get(id);
  debug_assert!(int.start <= pos);

  let reg = intervals.vreg(id).to_reg();

  for &i in intervals.fragments(id).frag_ixs.iter().rev() {
    let frag = fragments[i];
    if frag.first > pos {
      continue;
    }

    let mut inst = frag.last.iix;
    while inst >= frag.first.iix {
      let uses = &reg_uses[inst];

      let at_def = InstPoint::new_def(inst);
      if at_def <= pos && at_def <= frag.last {
        if uses.san_defined.contains(reg) || uses.san_modified.contains(reg) {
          debug_assert!(
            intervals.covers(id, at_def, fragments),
            "last use must be in interval"
          );
          trace!("last use of {:?} before {:?} found at {:?}", id, pos, at_def,);
          return Some(at_def);
        }
      }

      let at_use = InstPoint::new_use(inst);
      if at_use <= pos && at_use <= frag.last {
        if uses.san_used.contains(reg) || uses.san_modified.contains(reg) {
          debug_assert!(
            intervals.covers(id, at_use, fragments),
            "last use must be in interval"
          );
          trace!("last use of {:?} before {:?} found at {:?}", id, pos, at_use,);
          return Some(at_use);
        }
      }

      inst = inst.minus(1);
    }
  }

  None
}

/// Which strategy should we use when trying to find the best split position?
/// TODO Consider loop depth to avoid splitting in the middle of a loop
/// whenever possible.
enum OptimalSplitStrategy {
  From,
  To,
  NextFrom,
  NextNextFrom,
  PrevTo,
  PrevPrevTo,
  Mid,
}

/// Finds an optimal split position, whenever we're given a range of possible
/// positions where to split.
fn find_optimal_split_pos<F: Function>(
  state: &State<F>, id: IntId, from: InstPoint, to: InstPoint,
) -> InstPoint {
  trace!("find_optimal_split_pos between {:?} and {:?}", from, to);

  debug_assert!(from <= to, "split between positions are inconsistent");
  let int = state.intervals.get(id);
  debug_assert!(from >= int.start, "split should happen after the start");
  debug_assert!(to <= int.end, "split should happen before the end");

  if from == to {
    return from;
  }

  let candidate = match state.optimal_split_strategy {
    OptimalSplitStrategy::To => Some(to),
    OptimalSplitStrategy::NextFrom => Some(next_pos(from)),
    OptimalSplitStrategy::NextNextFrom => Some(next_pos(next_pos(from))),
    OptimalSplitStrategy::From => {
      // This is the general setting, so win some time and eagerly return here.
      return from;
    }
    OptimalSplitStrategy::PrevTo => Some(prev_pos(to)),
    OptimalSplitStrategy::PrevPrevTo => Some(prev_pos(prev_pos(to))),
    OptimalSplitStrategy::Mid => {
      Some(InstPoint::new_use(InstIx::new((from.iix.get() + to.iix.get()) / 2)))
    }
  };

  if let Some(pos) = candidate {
    if pos >= from
      && pos <= to
      && state.intervals.covers(id, pos, &state.fragments)
    {
      return pos;
    }
  }

  from
}

/// Splits the interval at the given position.
///
/// The split position must either be a Def of the current vreg, or it must be
/// at a Use position (otherwise there's no place to put the moves created by
/// the split).
///
/// The id of the new interval is returned, while the parent interval is mutated
/// in place. The child interval starts after (including) at_pos.
fn split<F: Function>(
  state: &mut State<F>, id: IntId, at_pos: InstPoint,
) -> IntId {
  debug!("split {:?} at {:?}", id, at_pos);
  trace!("interval: {}", state.intervals.display(id, &state.fragments),);

  let parent_start = state.intervals.get(id).start;
  debug_assert!(parent_start <= at_pos, "must split after the start");
  debug_assert!(
    at_pos <= state.intervals.get(id).end,
    "must split before the end"
  );

  let vreg = state.intervals.vreg(id);
  let fragments = &state.fragments;
  let frags = state.intervals.fragments_mut(id);

  // We need to split at the first range that's before or contains the "at"
  // position, reading from the end to the start.
  let split_ranges_at = frags
    .frag_ixs
    .iter()
    .position(|&frag_id| {
      let frag = fragments[frag_id];
      frag.first >= at_pos || frag.contains(&at_pos)
    })
    .expect("split would create an empty child");

  let mut child_frag_ixs = frags.frag_ixs.split_off(split_ranges_at);

  // The split position is either in the middle of a lifetime hole, in which
  // case we don't need to do anything. Otherwise, we might need to split a
  // range fragment into two parts.
  if let Some(&frag_ix) = child_frag_ixs.first() {
    let frag = &fragments[frag_ix];
    if frag.first != at_pos && frag.contains(&at_pos) {
      // We're splitting in the middle of a fragment: [L, R].
      // Split it into two fragments: parent [L, pos[ + child [pos, R].
      debug_assert!(frag.first < frag.last, "trying to split unit fragment");
      debug_assert!(frag.first <= at_pos, "no space to split fragment");

      let parent_first = frag.first;
      let parent_last = prev_pos(at_pos);
      let child_first = at_pos;
      let child_last = frag.last;

      trace!(
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
      let parent_frag = RangeFrag::new_multi_block(
        state.func,
        bix,
        parent_first,
        parent_last,
        count,
      );

      let parent_frag_ix = RangeFragIx::new(state.fragments.len());
      state.fragments.push(parent_frag);

      // Child range.
      let child_frag = RangeFrag::new_multi_block(
        state.func,
        bix,
        child_first,
        child_last,
        count,
      );
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
    let parent_frag = RangeFrag::new_multi_block(
      state.func, frag.bix, at_pos, at_pos, /* count */ 1,
    );

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
    spill_cost: SpillCost::infinite(),
  };

  let child_start = state.fragments[child_int.sorted_frags.frag_ixs[0]].first;
  let child_end =
    state.fragments[*child_int.sorted_frags.frag_ixs.last().unwrap()].last;
  let parent_end = state.fragments[*frags.frag_ixs.last().unwrap()].last;

  // Insert child in virtual ranges and live intervals.
  let vreg_ix = VirtualRangeIx::new(state.intervals.virtual_ranges.len());
  state.intervals.virtual_ranges.push(child_int);

  // TODO make a better interface out of this.
  let child_id = IntId(state.intervals.num_intervals());
  let child_int = LiveInterval {
    id: child_id,
    kind: LiveIntervalKind::Virtual(vreg_ix),
    parent: Some(id),
    child: None,
    location: Location::None,
    reg_class: state.intervals.get(id).reg_class,
    start: child_start,
    end: child_end,
  };
  state.intervals.push_interval(child_int);

  state.intervals.data[id.0].end = parent_end;
  state.intervals.set_child(id, child_id);

  trace!("split results:");
  trace!("- {}", state.intervals.display(id, &state.fragments));
  trace!("- {}", state.intervals.display(child_id, &state.fragments));

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

fn next_pos(mut pos: InstPoint) -> InstPoint {
  match pos.pt {
    Point::Use => pos.pt = Point::Def,
    Point::Def => {
      pos.pt = Point::Use;
      pos.iix = pos.iix.plus(1);
    }
    _ => unreachable!(),
  };
  pos
}

/// Splits the given interval between the last use before `split_pos` and
/// `split_pos`.
///
/// In case of two-ways split (i.e. only place to split is precisely split_pos),
/// returns the live interval id for the middle child, to be added back to the
/// list of active/inactive intervals after iterating on these.
fn split_and_spill<F: Function>(
  state: &mut State<F>, id: IntId, split_pos: InstPoint,
) {
  let child = match last_use(
    &state.intervals,
    id,
    split_pos,
    &state.reg_uses,
    &state.fragments,
  ) {
    Some(last_use) => {
      debug!(
        "split_and_spill {:?}: spill between {:?} and {:?}",
        id, last_use, split_pos
      );

      // Maintain ascending order between the min and max positions.
      let min_pos = InstPoint::min(next_pos(last_use), split_pos);

      // Make sure that if the two positions are the same, we'll be splitting in
      // a position that's in the current interval.
      let optimal_pos = find_optimal_split_pos(state, id, min_pos, split_pos);

      let child = split(state, id, optimal_pos);
      state.spill(child);
      child
    }

    None => {
      // The current interval has no uses before the split position, it can
      // safely be spilled.
      debug!(
        "split_and_spill {:?}: spilling it since no uses before split position",
        id
      );
      state.spill(id);
      id
    }
  };

  // Split until the next register use.
  match next_use(
    &state.intervals,
    child,
    split_pos,
    &state.reg_uses,
    &state.fragments,
  ) {
    Some(next_use_pos) => {
      debug!("split spilled interval before next use @ {:?}", next_use_pos);
      let child = split(state, child, next_use_pos);
      state.insert_unhandled(child);
    }
    None => {
      // Let it be spilled for the rest of its lifetime.
    }
  }

  // In both cases, the spilled child interval can remain on the stack.
  debug!("spilled split child {:?} silently expires", child);
}

/// A mapping from real reg to some T.
#[derive(Clone)]
struct RegisterMapping<T> {
  offset: usize,
  regs: Vec<(RealReg, T)>,
  reg_class: RegClass,
  scratch: Option<RealReg>,
}

impl<T: Copy> RegisterMapping<T> {
  fn with_default(
    reg_class: RegClass, reg_universe: &RealRegUniverse,
    scratch: Option<RealReg>, initial_value: T,
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
    Self { offset, regs, reg_class, scratch }
  }

  fn iter<'a>(&'a self) -> RegisterMappingIter<T> {
    RegisterMappingIter { iter: self.regs.iter(), scratch: self.scratch }
  }
}

struct RegisterMappingIter<'a, T: Copy> {
  iter: std::slice::Iter<'a, (RealReg, T)>,
  scratch: Option<RealReg>,
}

impl<'a, T: Copy> std::iter::Iterator for RegisterMappingIter<'a, T> {
  type Item = &'a (RealReg, T);
  fn next(&mut self) -> Option<Self::Item> {
    match self.iter.next() {
      Some(pair) => {
        if Some(pair.0) == self.scratch {
          // Skip to the next one.
          self.iter.next()
        } else {
          Some(pair)
        }
      }
      None => None,
    }
  }
}

impl<T> std::ops::Index<RealReg> for RegisterMapping<T> {
  type Output = T;
  fn index(&self, rreg: RealReg) -> &Self::Output {
    debug_assert!(
      rreg.get_class() == self.reg_class,
      "trying to index a reg from the wrong class"
    );
    debug_assert!(Some(rreg) != self.scratch, "trying to use the scratch");
    &self.regs[rreg.get_index() - self.offset].1
  }
}

impl<T> std::ops::IndexMut<RealReg> for RegisterMapping<T> {
  fn index_mut(&mut self, rreg: RealReg) -> &mut Self::Output {
    debug_assert!(
      rreg.get_class() == self.reg_class,
      "trying to index a reg from the wrong class"
    );
    debug_assert!(Some(rreg) != self.scratch, "trying to use the scratch");
    &mut self.regs[rreg.get_index() - self.offset].1
  }
}

fn try_compress_ranges<F: Function>(
  func: &F, rlrs: &mut RealRanges, vlrs: &mut VirtualRanges,
  fragments: &mut Fragments,
) {
  for vlr in vlrs.iter_mut() {
    let old_size = vlr.sorted_frags.frag_ixs.len();
    let mut i = vlr.sorted_frags.frag_ixs.len() - 1;
    while i > 0 {
      let cur_frag = &fragments[vlr.sorted_frags.frag_ixs[i]];
      let prev_frag = &fragments[vlr.sorted_frags.frag_ixs[i - 1]];
      if prev_frag.last.iix.get() + 1 == cur_frag.first.iix.get()
        && prev_frag.last.pt == Point::Def
        && cur_frag.first.pt == Point::Use
      {
        let new_range = RangeFrag::new_multi_block(
          func,
          prev_frag.bix,
          prev_frag.first,
          cur_frag.last,
          prev_frag.count + cur_frag.count,
        );

        let new_range_ix = RangeFragIx::new(fragments.len());
        fragments.push(new_range);
        vlr.sorted_frags.frag_ixs[i - 1] = new_range_ix;

        let _ = vlr.sorted_frags.frag_ixs.remove(i);
      }
      i -= 1;
    }

    let new_size = vlr.sorted_frags.frag_ixs.len();
    use log::warn;
    warn!(
      "compress: {} -> {}; {}",
      old_size,
      new_size,
      100. * (old_size as f64 - new_size as f64) / (old_size as f64)
    );
  }

  let mut reg_map: HashMap<RealReg, Vec<RangeFragIx>> = HashMap::default();
  for rlr in rlrs.iter_mut() {
    let reg = rlr.rreg;
    if let Some(ref mut vec) = reg_map.get_mut(&reg) {
      vec.append(&mut rlr.sorted_frags.frag_ixs);
    } else {
      // TODO clone can be avoided with an into_iter methods.
      reg_map.insert(reg, rlr.sorted_frags.frag_ixs.clone());
    }
  }

  rlrs.clear();
  for (rreg, mut sorted_frags) in reg_map {
    sorted_frags.sort_by_key(|frag_ix| fragments[*frag_ix].first);
    rlrs.push(RealRange {
      rreg,
      sorted_frags: SortedRangeFragIxs { frag_ixs: sorted_frags },
    });
  }
}

// Allocator top level.  |func| is modified so that, when this function
// returns, it will contain no VirtualReg uses.  Allocation can fail if there
// are insufficient registers to even generate spill/reload code, or if the
// function appears to have any undefined VirtualReg/RealReg uses.
#[inline(never)]
pub fn run<F: Function>(
  func: &mut F, reg_universe: &RealRegUniverse, use_checker: bool,
) -> Result<RegAllocResult<F>, RegAllocError> {
  let (reg_uses, mut rlrs, mut vlrs, mut fragments, liveouts, _est_freqs) =
    run_analysis(func, reg_universe, /* sanitize scratch */ true)
      .map_err(|err| RegAllocError::Analysis(err))?;

  let scratches_by_rc = {
    let mut scratches_by_rc = vec![None; NUM_REG_CLASSES];
    for i in 0..NUM_REG_CLASSES {
      if let Some(info) = &reg_universe.allocable_by_class[i] {
        if info.first == info.last {
          return Err(RegAllocError::Other(
            "at least 2 registers required for linear scan".into(),
          ));
        }
        let scratch = reg_universe.regs[info.suggested_scratch.unwrap()].0;
        scratches_by_rc[i] = Some(scratch);
      }
    }
    scratches_by_rc
  };

  try_compress_ranges(func, &mut rlrs, &mut vlrs, &mut fragments);

  let intervals = Intervals::new(rlrs, vlrs, &fragments);

  // Subset of fixed intervals, sorted by start point (as intervals are).
  let fixed_intervals = intervals
    .data
    .iter()
    .filter_map(|int| if int.is_fixed() { Some(int.id) } else { None })
    .collect::<Vec<_>>();

  trace!("unassigned intervals:");
  for int in &intervals.data {
    trace!("{}", intervals.display(int.id, &fragments));
  }
  trace!("");

  let (fragments, intervals, mut num_spill_slots) = {
    let mut state =
      State::new(func, &reg_uses, fragments, intervals, &scratches_by_rc);

    #[cfg(debug_assertions)]
    let mut prev_start = None;

    let mut last_fixed = 0;

    while let Some(id) = state.next_unhandled() {
      info!("main loop: allocating {:?}", id);
      trace!(
        "main loop: allocating {}",
        state.intervals.display(id, &state.fragments)
      );

      #[cfg(debug_assertions)]
      {
        let start = state.intervals.get(id).start;
        if let Some(ref prev) = prev_start {
          debug_assert!(*prev <= start, "main loop must make progress");
        };
        prev_start = Some(start);
      }

      if state.intervals.get(id).location.is_none() {
        // Lazily push all the fixed intervals that might interfere with the
        // current interval to the inactive list.
        let int = state.intervals.get(id);
        while last_fixed < fixed_intervals.len()
          && state.intervals.get(fixed_intervals[last_fixed]).start <= int.end
        {
          state.inactive.push(fixed_intervals[last_fixed]);
          last_fixed += 1;
        }

        update_state(id, &mut state);

        if !try_allocate_reg(id, &mut state, reg_universe) {
          allocate_blocked_reg(id, &mut state, reg_universe)?;
        }
        if state.intervals.get(id).location.reg().is_some() {
          state.active.push(id);
        }
      }

      debug!("");
    }

    debug!("allocation results (in order):");
    for id in 0..state.intervals.data.len() {
      debug!("{}", state.intervals.display(IntId(id), &state.fragments));
    }
    debug!("");

    (state.fragments, state.intervals, state.next_spill_slot.get())
  };

  // Filter fixed intervals, they're already in the right place.
  let mut virtual_intervals = intervals
    .data
    .iter()
    .filter_map(|int| {
      if let LiveIntervalKind::Fixed(_) = &int.kind {
        None
      } else {
        Some(int.id)
      }
    })
    .collect::<Vec<_>>();

  // Sort by vreg and starting point, so we can plug all the different intervals
  // together.
  virtual_intervals.sort_by_key(|&int_id| {
    let vrange =
      &intervals.virtual_ranges[intervals.get(int_id).unwrap_virtual()];
    let first_frag_ix = vrange.sorted_frags.frag_ixs[0];
    (vrange.vreg, fragments[first_frag_ix].first)
  });

  debug!("allocation results (by vreg)");
  for &int_id in &virtual_intervals {
    debug!("{}", intervals.display(int_id, &fragments));
  }
  debug!("");

  let memory_moves = resolve_moves(
    func,
    &reg_uses,
    &intervals,
    &virtual_intervals,
    &fragments,
    &liveouts,
    &mut num_spill_slots,
    &scratches_by_rc,
  );

  apply_registers(
    func,
    &intervals,
    virtual_intervals,
    &fragments,
    memory_moves,
    reg_universe,
    num_spill_slots,
    use_checker,
  )
}

#[inline(never)]
fn is_block_start<F: Function>(func: &F, pos: InstPoint) -> bool {
  for block in func.blocks() {
    let insts = func.block_insns(block);
    if pos.iix == insts.first() && pos.pt == Point::Use {
      return true;
    }
  }
  false
}

#[inline(never)]
fn is_block_end<F: Function>(func: &F, pos: InstPoint) -> bool {
  for block in func.blocks() {
    let insts = func.block_insns(block);
    if pos.iix == insts.last() && pos.pt == Point::Def {
      return true;
    }
  }
  false
}

#[inline(never)]
fn find_enclosing_interval(
  vreg: VirtualReg, inst: InstPoint, intervals: &Intervals,
  fragments: &Fragments, virtual_intervals: &Vec<IntId>,
) -> Option<IntId> {
  // The list of virtual intervals is sorted by vreg; find one interval for this
  // vreg.
  let index = virtual_intervals
    .binary_search_by_key(&vreg, |&int_id| intervals.vreg(int_id))
    .expect("should find at least one virtual interval for this vreg");

  // Rewind back to the first interval for this vreg, since there might be
  // several ones.
  let mut index = index;
  while index > 0 && intervals.vreg(virtual_intervals[index - 1]) == vreg {
    index -= 1;
  }

  // Now iterates on all the intervals for this virtual register, until one
  // works.
  let mut int_id = virtual_intervals[index];
  loop {
    if intervals.covers(int_id, inst, fragments) {
      return Some(int_id);
    }

    index += 1;
    if index == virtual_intervals.len() {
      return None;
    }

    int_id = virtual_intervals[index];
    if intervals.vreg(int_id) != vreg {
      return None;
    }
  }
}

#[inline(never)]
fn resolve_moves<F: Function>(
  func: &F, reg_uses: &RegUses, intervals: &Intervals,
  virtual_intervals: &Vec<IntId>, fragments: &Fragments,
  liveouts: &TypedIxVec<BlockIx, Set<Reg>>, spill_slot: &mut u32,
  scratches_by_rc: &[Option<RealReg>],
) -> InstsAndPoints {
  let mut memory_moves = HashMap::default();

  let mut parallel_reloads = HashMap::default();
  let mut spills = HashMap::default();

  info!("resolve_moves");

  for &int_id in virtual_intervals {
    let (parent_end, parent_loc, loc) = {
      let interval = intervals.get(int_id);
      let loc = interval.location;

      let parent_id = match interval.parent {
        Some(pid) => pid,
        None => {
          // In unreachable code, it's possible that a given interval has no
          // parents and is assigned to a stack location for its whole lifetime.
          //
          // In reachable code, the analysis only create intervals for virtual
          // registers with at least one register use, so a parentless interval (=
          // hasn't ever been split) can't live in a stack slot.
          debug_assert!(
            loc.spill().is_none()
              || (next_use(
                intervals,
                int_id,
                InstPoint::min_value(),
                reg_uses,
                fragments
              )
              .is_none())
          );
          continue;
        }
      };

      let parent = intervals.get(parent_id);
      if is_block_end(func, parent.end) && is_block_start(func, interval.start)
      {
        // This is a move between blocks, and should be handled as such.
        continue;
      }

      (parent.end, parent.location, loc)
    };

    let child_start = intervals.get(int_id).start;
    let vreg = intervals.vreg(int_id);

    match loc {
      Location::None => panic!("interval has no location after regalloc!"),

      Location::Reg(rreg) => {
        // Reconnect with the parent location, by adding a move if needed.
        match next_use(intervals, int_id, child_start, reg_uses, fragments) {
          Some(next_use) => {
            // No need to reload before a new definition.
            if next_use.pt == Point::Def {
              continue;
            }
          }
          None => {}
        };

        let mut at_inst = child_start;
        match at_inst.pt {
          Point::Use => {
            at_inst.pt = Point::Reload;
          }
          Point::Def => {
            at_inst.pt = Point::Spill;
          }
          _ => unreachable!(),
        }
        let entry = parallel_reloads.entry(at_inst).or_insert(Vec::new());

        match parent_loc {
          Location::None => unreachable!(),

          Location::Reg(from_rreg) => {
            if from_rreg != rreg {
              debug!(
                "inblock fixup: {:?} move {:?} -> {:?} at {:?}",
                int_id, from_rreg, rreg, at_inst
              );
              entry.push(MoveOp::new_move(from_rreg, rreg, vreg));
            }
          }

          Location::Stack(spill) => {
            debug!(
              "inblock fixup: {:?} reload {:?} -> {:?} at {:?}",
              int_id, spill, rreg, at_inst
            );
            entry.push(MoveOp::new_reload(spill, rreg, vreg));
          }
        }
      }

      Location::Stack(spill) => {
        // This interval has been spilled (i.e. split). Spill after the last def
        // or before the last use.
        let mut at_inst = parent_end;
        at_inst.pt = if at_inst.pt == Point::Use {
          Point::Reload
        } else {
          debug_assert!(at_inst.pt == Point::Def);
          Point::Spill
        };

        match parent_loc {
          Location::None => unreachable!(),

          Location::Reg(rreg) => {
            debug!(
              "inblock fixup: {:?} spill {:?} -> {:?} at {:?}",
              int_id, rreg, spill, at_inst
            );
            spills.entry(at_inst).or_insert(Vec::new()).push(
              InstToInsert::Spill {
                to_slot: spill,
                from_reg: rreg,
                for_vreg: vreg,
              },
            );
          }

          Location::Stack(parent_spill) => {
            debug_assert_eq!(parent_spill, spill);
          }
        }
      }
    }
  }

  // Flush the memory moves caused by in-block fixups. Conceptually, the spills
  // must happen after the right locations have been set, that is, after the
  // reloads. Reloads may include several moves that must happen in parallel
  // (e.g. if two real regs must be swapped), so process them first. Once all
  // the parallel assignments have been done, push forward all the spills.
  for (at_inst, mut parallel_moves) in parallel_reloads {
    let ordered_moves = schedule_moves(&mut parallel_moves);
    let insts = emit_moves(ordered_moves, spill_slot, scratches_by_rc);
    memory_moves.insert(at_inst, insts);
  }
  for (at_inst, mut spills) in spills {
    memory_moves.entry(at_inst).or_insert(Vec::new()).append(&mut spills);
  }

  let mut parallel_move_map = HashMap::default();
  enum BlockPos {
    Start,
    End,
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
  let mut seen_successors = HashSet::default();
  for block in func.blocks() {
    let successors = func.block_succs(block);
    seen_successors.clear();

    // Where to insert the fixup move, if needed? If there's more than one
    // successor to the current block, inserting in the current block will
    // impact all the successors.
    //
    // We assume critical edges have been split, so
    // if the current block has more than one successor, then its successors
    // have at most one predecessor.
    let cur_has_one_succ = successors.len() == 1;

    for succ in successors {
      if !seen_successors.insert(succ) {
        continue;
      }

      for &reg in liveouts[block].iter() {
        let vreg =
          if let Some(vreg) = reg.as_virtual_reg() { vreg } else { continue };

        // Find the interval for this (vreg, inst) pair.
        let (succ_first_inst, succ_id) = {
          let first_inst = InstPoint::new_use(func.block_insns(succ).first());
          let found = match find_enclosing_interval(
            vreg,
            first_inst,
            intervals,
            fragments,
            &virtual_intervals,
          ) {
            Some(found) => found,
            // The vreg is unused in this successor, no need to update its
            // location.
            None => continue,
          };
          (first_inst, found)
        };

        let (cur_last_inst, cur_id) = {
          let last_inst = func.block_insns(block).last();
          // see XXX above
          let last_inst = InstPoint::new_def(last_inst);
          let cur_id = find_enclosing_interval(
            vreg,
            last_inst,
            intervals,
            fragments,
            &virtual_intervals,
          )
          .expect(&format!(
            "no interval for given {:?}:{:?} pair in current {:?}",
            vreg, last_inst, block
          ));
          (last_inst, cur_id)
        };

        if succ_id == cur_id {
          continue;
        }

        let (at_inst, block_pos) = if cur_has_one_succ {
          let mut pos = cur_last_inst;
          // Before the control flow instruction.
          pos.pt = Point::Reload;
          (pos, BlockPos::End)
        } else {
          let mut pos = succ_first_inst;
          pos.pt = Point::Reload;
          (pos, BlockPos::Start)
        };

        let pending_moves =
          parallel_move_map.entry(at_inst).or_insert((Vec::new(), block_pos));

        match (intervals.get(cur_id).location, intervals.get(succ_id).location)
        {
          (Location::Reg(cur_rreg), Location::Reg(succ_rreg)) => {
            if cur_rreg == succ_rreg {
              continue;
            }
            debug!(
              "boundary fixup: move {:?} -> {:?} at {:?} for {:?} between {:?} and {:?}",
              cur_rreg,
              succ_rreg,
              at_inst,
              vreg,
              block,
              succ
            );
            pending_moves.0.push(MoveOp::new_move(cur_rreg, succ_rreg, vreg));
          }

          (Location::Reg(cur_rreg), Location::Stack(spillslot)) => {
            debug!(
              "boundary fixup: spill {:?} -> {:?} at {:?} for {:?} between {:?} and {:?}",
              cur_rreg,
              spillslot,
              at_inst,
              vreg,
              block,
              succ
            );
            pending_moves.0.push(MoveOp::new_spill(cur_rreg, spillslot, vreg));
          }

          (Location::Stack(spillslot), Location::Reg(rreg)) => {
            debug!(
              "boundary fixup: reload {:?} -> {:?} at {:?} for {:?} between {:?} and {:?}",
              spillslot,
              rreg,
              at_inst,
              vreg,
              block,
              succ
            );
            pending_moves.0.push(MoveOp::new_reload(spillslot, rreg, vreg));
          }

          (
            Location::Stack(left_spill_slot),
            Location::Stack(right_spill_slot),
          ) => {
            // Stack to stack should not happen here, since two ranges for the
            // same vreg can't be intersecting, so the same stack slot ought to
            // be reused in this case.
            debug_assert_eq!(
              left_spill_slot, right_spill_slot,
              "Moves from stack to stack only happen on the same vreg, thus the same stack slot"
            );
            continue;
          }

          (_, _) => {
            panic!("register or stack slots must have been allocated.");
          }
        };
      }
    }

    // Flush the memory moves caused by block fixups for this block.
    for (at_inst, parallel_moves) in parallel_move_map.iter_mut() {
      let ordered_moves = schedule_moves(&mut parallel_moves.0);
      let mut insts = emit_moves(ordered_moves, spill_slot, scratches_by_rc);

      // If at_inst pointed to a block start, then insert block fixups *before*
      // inblock fixups;
      // otherwise it pointed to a block end, then insert block fixups *after*
      // inblock fixups.
      let mut entry = memory_moves.entry(*at_inst).or_insert(Vec::new());
      match parallel_moves.1 {
        BlockPos::Start => {
          insts.append(&mut entry);
          *entry = insts;
        }
        BlockPos::End => {
          entry.append(&mut insts);
        }
      }
    }
    parallel_move_map.clear();
  }
  debug!("");

  let mut insts_and_points = InstsAndPoints::new();
  for (at, insts) in memory_moves {
    for inst in insts {
      insts_and_points.push(InstAndPoint::new(at, inst));
    }
  }

  insts_and_points
}

#[derive(PartialEq, Debug)]
enum MoveOperand {
  Reg(RealReg),
  Stack(SpillSlot),
}

impl MoveOperand {
  fn aliases(&self, other: &Self) -> bool {
    self == other
  }
}

struct MoveOp {
  from: MoveOperand,
  to: MoveOperand,
  vreg: VirtualReg,
  cycle_begin: Option<usize>,
  cycle_end: Option<usize>,
}

impl fmt::Debug for MoveOp {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{:?}: {:?} -> {:?}", self.vreg, self.from, self.to)?;
    if let Some(ref begin) = self.cycle_begin {
      write!(fmt, ", start of cycle #{}", begin)?;
    }
    if let Some(ref end) = self.cycle_end {
      write!(fmt, ", end of cycle #{}", end)?;
    }
    Ok(())
  }
}

impl MoveOp {
  fn new_move(from: RealReg, to: RealReg, vreg: VirtualReg) -> Self {
    Self {
      from: MoveOperand::Reg(from),
      to: MoveOperand::Reg(to),
      vreg,
      cycle_begin: None,
      cycle_end: None,
    }
  }

  fn new_spill(from: RealReg, to: SpillSlot, vreg: VirtualReg) -> Self {
    Self {
      from: MoveOperand::Reg(from),
      to: MoveOperand::Stack(to),
      vreg,
      cycle_begin: None,
      cycle_end: None,
    }
  }

  fn new_reload(from: SpillSlot, to: RealReg, vreg: VirtualReg) -> Self {
    Self {
      from: MoveOperand::Stack(from),
      to: MoveOperand::Reg(to),
      vreg,
      cycle_begin: None,
      cycle_end: None,
    }
  }

  fn gen_inst(&self) -> InstToInsert {
    match self.from {
      MoveOperand::Reg(from) => match self.to {
        MoveOperand::Reg(to) => InstToInsert::Move {
          to_reg: Writable::from_reg(to),
          from_reg: from,
          for_vreg: self.vreg,
        },
        MoveOperand::Stack(to) => InstToInsert::Spill {
          to_slot: to,
          from_reg: from,
          for_vreg: self.vreg,
        },
      },
      MoveOperand::Stack(from) => match self.to {
        MoveOperand::Reg(to) => InstToInsert::Reload {
          to_reg: Writable::from_reg(to),
          from_slot: from,
          for_vreg: self.vreg,
        },
        MoveOperand::Stack(_to) => unreachable!("stack to stack move"),
      },
    }
  }
}

fn find_blocking_move<'a>(
  pending: &'a mut Vec<MoveOp>, last: &MoveOp,
) -> Option<(usize, &'a mut MoveOp)> {
  for (i, other) in pending.iter_mut().enumerate() {
    if other.from.aliases(&last.to) {
      return Some((i, other));
    }
  }
  None
}

fn find_cycled_move<'a>(
  stack: &'a mut Vec<MoveOp>, from: &mut usize, last: &MoveOp,
) -> Option<&'a mut MoveOp> {
  for i in *from..stack.len() {
    *from += 1;
    let other = &stack[i];
    if other.from.aliases(&last.to) {
      return Some(&mut stack[i]);
    }
  }
  None
}

/// Given a pending list of moves, returns a list of moves ordered in a correct
/// way, i.e., no move clobbers another one.
#[inline(never)]
fn schedule_moves(pending: &mut Vec<MoveOp>) -> Vec<MoveOp> {
  let mut ordered_moves = Vec::new();

  let mut num_cycles = 0;
  let mut cur_cycles = 0;

  let show_debug = env::var("MOVES").is_ok();
  if show_debug {
    trace!("pending moves: {:#?}", pending);
  }

  while let Some(pm) = pending.pop() {
    if show_debug {
      trace!("handling pending move {:?}", pm);
    }
    debug_assert!(
      pm.from != pm.to,
      "spurious moves should not have been inserted"
    );

    let mut stack = vec![pm];

    while !stack.is_empty() {
      let blocking_pair = find_blocking_move(pending, stack.last().unwrap());

      if let Some((blocking_idx, blocking)) = blocking_pair {
        if show_debug {
          trace!("found blocker: {:?}", blocking);
        }
        let mut stack_cur = 0;

        let has_cycles = if let Some(mut cycled) =
          find_cycled_move(&mut stack, &mut stack_cur, blocking)
        {
          if show_debug {
            trace!("found cycle: {:?}", cycled);
          }
          debug_assert!(cycled.cycle_end.is_none());
          cycled.cycle_end = Some(cur_cycles);
          true
        } else {
          false
        };

        if has_cycles {
          loop {
            match find_cycled_move(&mut stack, &mut stack_cur, blocking) {
              Some(ref mut cycled) => {
                if show_debug {
                  trace!("found more cycles ending on blocker: {:?}", cycled);
                }
                debug_assert!(cycled.cycle_end.is_none());
                cycled.cycle_end = Some(cur_cycles);
              }
              None => break,
            }
          }

          debug_assert!(blocking.cycle_begin.is_none());
          blocking.cycle_begin = Some(cur_cycles);
          cur_cycles += 1;
        }

        let blocking = pending.remove(blocking_idx);
        stack.push(blocking);
      } else {
        // There's no blocking move! We can push this in the ordered list of
        // moves.
        // TODO IonMonkey has more optimizations for this case.
        let last = stack.pop().unwrap();
        ordered_moves.push(last);
      }
    }

    if num_cycles < cur_cycles {
      num_cycles = cur_cycles;
    }
    cur_cycles = 0;
  }

  ordered_moves
}

#[inline(never)]
fn emit_moves(
  ordered_moves: Vec<MoveOp>, num_spill_slots: &mut u32,
  scratches_by_rc: &[Option<RealReg>],
) -> Vec<InstToInsert> {
  let mut spill_slot = None;
  let mut in_cycle = false;

  let mut insts = Vec::new();

  let show_debug = env::var("MOVES").is_ok();
  if show_debug {
    trace!("emit_moves");
  }

  for mov in ordered_moves {
    if let Some(_) = &mov.cycle_end {
      debug_assert!(in_cycle);

      // There is some pattern:
      //   (A -> B)
      //   (B -> A)
      // This case handles (B -> A), which we reach last. We emit a move from
      // the saved value of B, to A.
      match mov.to {
        MoveOperand::Reg(dst_reg) => {
          let inst = InstToInsert::Reload {
            to_reg: Writable::from_reg(dst_reg),
            from_slot: spill_slot.expect("should have a cycle spill slot"),
            for_vreg: mov.vreg,
          };
          insts.push(inst);
          if show_debug {
            trace!(
              "finishing cycle: {:?} -> {:?}",
              spill_slot.unwrap(),
              dst_reg
            );
          }
        }
        MoveOperand::Stack(dst_spill) => {
          let scratch = scratches_by_rc[mov.vreg.get_class() as usize]
            .expect("missing scratch reg");
          let inst = InstToInsert::Reload {
            to_reg: Writable::from_reg(scratch),
            from_slot: spill_slot.expect("should have a cycle spill slot"),
            for_vreg: mov.vreg,
          };
          insts.push(inst);
          let inst = InstToInsert::Spill {
            to_slot: dst_spill,
            from_reg: scratch,
            for_vreg: mov.vreg,
          };
          insts.push(inst);
          if show_debug {
            trace!(
              "finishing cycle: {:?} -> {:?} -> {:?}",
              spill_slot.unwrap(),
              scratch,
              dst_spill
            );
          }
        }
      };

      in_cycle = false;
      continue;
    }

    if let Some(_) = &mov.cycle_begin {
      debug_assert!(!in_cycle);

      // There is some pattern:
      //   (A -> B)
      //   (B -> A)
      // This case handles (A -> B), which we reach first. We save B, then allow
      // the original move to continue.
      match spill_slot {
        Some(_) => {}
        None => {
          spill_slot = Some(SpillSlot::new(*num_spill_slots));
          *num_spill_slots += 1;
        }
      }

      match mov.to {
        MoveOperand::Reg(src_reg) => {
          let inst = InstToInsert::Spill {
            to_slot: spill_slot.unwrap(),
            from_reg: src_reg,
            for_vreg: mov.vreg,
          };
          insts.push(inst);
          if show_debug {
            trace!(
              "starting cycle: {:?} -> {:?}",
              src_reg,
              spill_slot.unwrap()
            );
          }
        }
        MoveOperand::Stack(src_spill) => {
          let scratch = scratches_by_rc[mov.vreg.get_class() as usize]
            .expect("missing scratch reg");
          let inst = InstToInsert::Reload {
            to_reg: Writable::from_reg(scratch),
            from_slot: src_spill,
            for_vreg: mov.vreg,
          };
          insts.push(inst);
          let inst = InstToInsert::Spill {
            to_slot: spill_slot.expect("should have a cycle spill slot"),
            from_reg: scratch,
            for_vreg: mov.vreg,
          };
          insts.push(inst);
          if show_debug {
            trace!(
              "starting cycle: {:?} -> {:?} -> {:?}",
              src_spill,
              scratch,
              spill_slot.unwrap()
            );
          }
        }
      };

      in_cycle = true;
    }

    // A normal move which is not part of a cycle.
    insts.push(mov.gen_inst());
    if show_debug {
      trace!("moving {:?} -> {:?}", mov.from, mov.to);
    }
  }

  insts
}

/// Fills in the register assignments into instructions.
#[inline(never)]
fn apply_registers<F: Function>(
  func: &mut F, intervals: &Intervals, virtual_intervals: Vec<IntId>,
  fragments: &Fragments, memory_moves: InstsAndPoints,
  reg_universe: &RealRegUniverse, num_spill_slots: u32, use_checker: bool,
) -> Result<RegAllocResult<F>, RegAllocError> {
  info!("apply_registers");

  let mut frag_map = RangeAllocations::new();
  for int_id in virtual_intervals {
    if let Some(rreg) = intervals.get(int_id).location.reg() {
      let vreg = intervals.vreg(int_id);
      for &range_ix in &intervals.fragments(int_id).frag_ixs {
        frag_map.push((range_ix, vreg, rreg));
      }
    }
  }

  edit_inst_stream(
    func,
    memory_moves,
    frag_map,
    fragments,
    reg_universe,
    num_spill_slots,
    true, // multiple blocks per frag
    use_checker,
  )
}
