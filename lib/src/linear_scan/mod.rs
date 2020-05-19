//! Implementation of the linear scan allocator algorithm.
//!
//! This tries to follow the implementation as suggested by:
//!   Optimized Interval Splitting in a Linear Scan Register Allocator,
//!     by Wimmer et al., 2005

use log::{debug, info, log_enabled, trace, Level};

use std::default;
use std::env;
use std::fmt;

use crate::analysis_main::{run_analysis, AnalysisInfo};
use crate::data_structures::*;
use crate::inst_stream::{add_spills_reloads_and_moves, InstToInsertAndPoint};
use crate::{
    checker::CheckerContext, reg_maps::MentionRegUsageMapper, Function, RegAllocError,
    RegAllocResult,
};

mod assign_registers;
mod resolve_moves;

#[derive(Default)]
pub(crate) struct Statistics {
    num_fixed: usize,
    num_vregs: usize,
    num_virtual_ranges: usize,

    peak_active: usize,
    peak_inactive: usize,

    num_try_allocate_reg: usize,
    num_try_allocate_reg_partial: usize,
    num_try_allocate_reg_success: usize,
}

impl Drop for Statistics {
    fn drop(&mut self) {
        println!(
            "stats: {} fixed / {} vreg / {} vranges, peak active {} / inactive {}, 1st try alloc: {}+{}/{}",
            self.num_fixed,
            self.num_vregs,
            self.num_virtual_ranges,
            self.peak_active,
            self.peak_inactive,
            self.num_try_allocate_reg_success,
            self.num_try_allocate_reg_partial,
            self.num_try_allocate_reg
        );
    }
}

/// Which strategy should we use when trying to find the best split position?
/// TODO Consider loop depth to avoid splitting in the middle of a loop
/// whenever possible.
#[derive(Copy, Clone, Debug)]
enum OptimalSplitStrategy {
    From,
    To,
    NextFrom,
    NextNextFrom,
    PrevTo,
    PrevPrevTo,
    Mid,
}

#[derive(Clone)]
pub struct LinearScanOptions {
    split_strategy: OptimalSplitStrategy,
    stats: bool,
}

impl default::Default for LinearScanOptions {
    fn default() -> Self {
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

        let stats = env::var("STATS").is_ok();

        Self {
            split_strategy: optimal_split_strategy,
            stats,
        }
    }
}

impl fmt::Debug for LinearScanOptions {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        writeln!(fmt, "linear scan")?;
        write!(fmt, "  split: {:?}", self.split_strategy)
    }
}

// Local shorthands.
type Fragments = TypedIxVec<RangeFragIx, RangeFrag>;
type VirtualRanges = TypedIxVec<VirtualRangeIx, VirtualRange>;
type RealRanges = TypedIxVec<RealRangeIx, RealRange>;
type RegUses = RegVecsAndBounds;

/// A unique identifier for an interval.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct IntId(usize);

impl fmt::Debug for IntId {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "int{}", self.0)
    }
}

#[derive(Clone)]
struct FixedInterval {
    reg: RealReg,
    frags: Vec<RangeFrag>,
}

impl fmt::Display for FixedInterval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fixed {:?} [", self.reg)?;
        for (i, frag) in self.frags.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "({:?}, {:?})", frag.first, frag.last)?;
        }
        write!(f, "]")
    }
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct Mention(u8);

impl fmt::Debug for Mention {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut comma = false;
        if self.0 & 1 == 1 {
            write!(fmt, "use")?;
            comma = true;
        }
        if (self.0 >> 1) & 1 == 1 {
            if comma {
                write!(fmt, ",")?;
            }
            write!(fmt, "mod")?;
            comma = true;
        }
        if (self.0 >> 2) & 1 == 1 {
            if comma {
                write!(fmt, ",")?;
            }
            write!(fmt, "def")?;
        }
        Ok(())
    }
}

impl Mention {
    fn new() -> Self {
        Self(0)
    }

    // Setters.
    fn add_use(&mut self) {
        self.0 |= 1 << 0;
    }
    fn add_mod(&mut self) {
        self.0 |= 1 << 1;
    }
    fn add_def(&mut self) {
        self.0 |= 1 << 2;
    }

    fn remove_use(&mut self) {
        self.0 &= !(1 << 0);
    }

    // Getters.
    fn is_use(&self) -> bool {
        (self.0 & 0b001) != 0
    }
    fn is_mod(&self) -> bool {
        (self.0 & 0b010) != 0
    }
    fn is_def(&self) -> bool {
        (self.0 & 0b100) != 0
    }
    fn is_use_or_mod(&self) -> bool {
        (self.0 & 0b011) != 0
    }
    fn is_mod_or_def(&self) -> bool {
        (self.0 & 0b110) != 0
    }
}

pub(crate) type MentionMap = Vec<(InstIx, Mention)>;

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

#[derive(Clone)]
pub(crate) struct VirtualInterval {
    id: IntId,
    vix: VirtualRangeIx,
    vreg: VirtualReg,

    /// Parent interval in the split tree.
    parent: Option<IntId>,
    child: Option<IntId>,

    /// Location assigned to this live interval.
    location: Location,

    mentions: MentionMap,
    start: InstPoint,
    end: InstPoint,
}

impl fmt::Display for VirtualInterval {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "virtual {:?}", self.id)?;
        if let Some(ref p) = self.parent {
            write!(fmt, " (parent={:?})", p)?;
        }
        write!(
            fmt,
            ": {:?} {} [{:?}; {:?}]",
            self.vreg, self.location, self.start, self.end
        )
    }
}

impl VirtualInterval {
    fn virtual_range_ix(&self) -> VirtualRangeIx {
        self.vix
    }
    fn mentions(&self) -> &MentionMap {
        &self.mentions
    }
    fn covers(&self, pos: InstPoint) -> bool {
        self.start <= pos && pos <= self.end
    }
}

/// A group of live intervals.
pub(crate) struct Intervals {
    virtuals: Vec<VirtualInterval>,
    fixeds: Vec<FixedInterval>,
}

impl Intervals {
    fn new(
        reg_universe: &RealRegUniverse,
        reg_uses: &RegUses,
        real_ranges: &RealRanges,
        virtual_ranges: VirtualRanges,
        fragments: &Fragments,
        stats: &mut Option<Statistics>,
    ) -> Self {
        let mut virtual_ints = Vec::with_capacity(virtual_ranges.len() as usize);
        let mut fixed_ints = Vec::with_capacity(reg_universe.regs.len() as usize);

        // Create fixed intervals first.
        for rreg in reg_universe.regs.iter() {
            stats.as_mut().map(|stats| stats.num_fixed += 1);
            fixed_ints.push(FixedInterval {
                reg: rreg.0,
                frags: Vec::new(),
            });
        }

        for rlr in real_ranges.iter() {
            let i = rlr.rreg.get_index();
            fixed_ints[i]
                .frags
                .extend(rlr.sorted_frags.frag_ixs.iter().map(|fix| fragments[*fix]));
            fixed_ints[i].frags.sort_unstable_by_key(|frag| frag.first);
        }

        // Create virtual intervals then.
        let mut int_id = 0;

        let mut regsets = RegSets::new(true);
        for (vlr_ix, vlr) in virtual_ranges.iter().enumerate() {
            let vreg = vlr.vreg;
            let reg = vreg.to_reg();

            stats.as_mut().map(|stats| {
                stats.num_virtual_ranges += 1;
                stats.num_vregs = usize::max(stats.num_vregs, vreg.get_index());
            });

            // Compute mentions.
            // TODO this is probably quite expensive, and could be done earlier during analysis.
            let mut mentions = MentionMap::new();

            let vlr_frags = &vlr.sorted_frags.frags;
            for &frag in vlr_frags {
                for iix in frag
                    .first
                    .iix()
                    .dotdot(InstIx::new(frag.last.iix().get() + 1))
                {
                    reg_uses.get_reg_sets_for_iix_reuse(iix, &mut regsets);

                    debug_assert!(regsets.is_sanitized());
                    if (iix != frag.first.iix() || frag.first.pt() == Point::Use)
                        && regsets.uses.contains(reg)
                    {
                        if mentions.is_empty() || mentions.last().unwrap().0 != iix {
                            mentions.push((iix, Mention::new()));
                        }
                        mentions.last_mut().unwrap().1.add_use();
                    }
                    if regsets.mods.contains(reg) {
                        if mentions.is_empty() || mentions.last().unwrap().0 != iix {
                            mentions.push((iix, Mention::new()));
                        }
                        mentions.last_mut().unwrap().1.add_mod();
                    }
                    if iix == frag.last.iix() && frag.last.pt() == Point::Use {
                        continue;
                    }
                    if regsets.defs.contains(reg) {
                        if mentions.is_empty() || mentions.last().unwrap().0 != iix {
                            mentions.push((iix, Mention::new()));
                        }
                        mentions.last_mut().unwrap().1.add_def();
                    }
                }
            }

            let start = vlr_frags[0].first;
            let end = vlr_frags.last().unwrap().last;

            virtual_ints.push(VirtualInterval {
                id: IntId(int_id),
                vix: VirtualRangeIx::new(vlr_ix as u32),
                vreg,
                mentions,
                start,
                end,
                parent: None,
                child: None,
                location: Location::None,
            });
            int_id += 1;
        }

        Self {
            virtuals: virtual_ints,
            fixeds: fixed_ints,
        }
    }

    fn get(&self, int_id: IntId) -> &VirtualInterval {
        &self.virtuals[int_id.0]
    }
    fn get_mut(&mut self, int_id: IntId) -> &mut VirtualInterval {
        &mut self.virtuals[int_id.0]
    }
    fn num_virtual_intervals(&self) -> usize {
        self.virtuals.len()
    }

    // Mutators.
    fn set_reg(&mut self, int_id: IntId, reg: RealReg) {
        let int = self.get_mut(int_id);
        debug_assert!(int.location.is_none());
        int.location = Location::Reg(reg);
    }
    fn set_spill(&mut self, int_id: IntId, slot: SpillSlot) {
        let int = self.get_mut(int_id);
        debug_assert!(int.location.spill().is_none());
        int.location = Location::Stack(slot);
    }
    fn push_interval(&mut self, int: VirtualInterval) {
        debug_assert!(int.id.0 == self.virtuals.len());
        self.virtuals.push(int);
    }
    fn set_child(&mut self, int_id: IntId, child_id: IntId) {
        if let Some(prev_child) = self.virtuals[int_id.0].child.clone() {
            self.virtuals[child_id.0].child = Some(prev_child);
            self.virtuals[prev_child.0].parent = Some(child_id);
        }
        self.virtuals[int_id.0].child = Some(child_id);
    }
}

/// Finds the first use for the current interval that's located after the given
/// `pos` (included), in a broad sense of use (any of use, def or mod).
///
/// Extends to the left, that is, "modified" means "used".
#[inline(never)]
fn next_use(interval: &VirtualInterval, pos: InstPoint, _reg_uses: &RegUses) -> Option<InstPoint> {
    if log_enabled!(Level::Trace) {
        trace!("find next use of {} after {:?}", interval, pos);
    }

    let mentions = interval.mentions();
    let target = InstPoint::max(pos, interval.start);

    let ret = match mentions.binary_search_by_key(&target.iix(), |mention| mention.0) {
        Ok(index) => {
            // Either the selected index is a perfect match, or the next mention is
            // the correct answer.
            let mention = &mentions[index];
            if target.pt() == Point::Use {
                if mention.1.is_use_or_mod() {
                    Some(InstPoint::new_use(mention.0))
                } else {
                    Some(InstPoint::new_def(mention.0))
                }
            } else if target.pt() == Point::Def && mention.1.is_mod_or_def() {
                Some(target)
            } else if index == mentions.len() - 1 {
                None
            } else {
                let mention = &mentions[index + 1];
                if mention.1.is_use_or_mod() {
                    Some(InstPoint::new_use(mention.0))
                } else {
                    Some(InstPoint::new_def(mention.0))
                }
            }
        }

        Err(index) => {
            if index == mentions.len() {
                None
            } else {
                let mention = &mentions[index];
                if mention.1.is_use_or_mod() {
                    Some(InstPoint::new_use(mention.0))
                } else {
                    Some(InstPoint::new_def(mention.0))
                }
            }
        }
    };

    // TODO once the mentions are properly split, this could be removed, in
    // theory.
    let ret = match ret {
        Some(pos) => {
            if pos <= interval.end {
                Some(pos)
            } else {
                None
            }
        }
        None => None,
    };

    ret
}

/// Finds the last use of a vreg before a given target, including it in possible
/// return values.
/// Extends to the right, that is, modified means "def".
fn last_use(interval: &VirtualInterval, pos: InstPoint, _reg_uses: &RegUses) -> Option<InstPoint> {
    if log_enabled!(Level::Trace) {
        trace!("searching last use of {} before {:?}", interval, pos,);
    }

    let mentions = interval.mentions();

    let target = InstPoint::min(pos, interval.end);

    let ret = match mentions.binary_search_by_key(&target.iix(), |mention| mention.0) {
        Ok(index) => {
            // Either the selected index is a perfect match, or the previous mention
            // is the correct answer.
            let mention = &mentions[index];
            if target.pt() == Point::Def {
                if mention.1.is_mod_or_def() {
                    Some(InstPoint::new_def(mention.0))
                } else {
                    Some(InstPoint::new_use(mention.0))
                }
            } else if target.pt() == Point::Use && mention.1.is_use() {
                Some(target)
            } else if index == 0 {
                None
            } else {
                let mention = &mentions[index - 1];
                if mention.1.is_mod_or_def() {
                    Some(InstPoint::new_def(mention.0))
                } else {
                    Some(InstPoint::new_use(mention.0))
                }
            }
        }

        Err(index) => {
            if index == 0 {
                None
            } else {
                let mention = &mentions[index - 1];
                if mention.1.is_mod_or_def() {
                    Some(InstPoint::new_def(mention.0))
                } else {
                    Some(InstPoint::new_use(mention.0))
                }
            }
        }
    };

    // TODO once the mentions are properly split, this could be removed, in
    // theory.
    let ret = match ret {
        Some(pos) => {
            if pos >= interval.start {
                Some(pos)
            } else {
                None
            }
        }
        None => None,
    };

    trace!("mentions: {:?}", mentions);
    trace!("found: {:?}", ret);

    ret
}

/// Checks that each register class has its own scratch register in addition to one available
/// register, and creates a mapping of register class -> scratch register.
fn compute_scratches(
    reg_universe: &RealRegUniverse,
) -> Result<Vec<Option<RealReg>>, RegAllocError> {
    let mut scratches_by_rc = vec![None; NUM_REG_CLASSES];
    for i in 0..NUM_REG_CLASSES {
        if let Some(info) = &reg_universe.allocable_by_class[i] {
            if info.first == info.last {
                return Err(RegAllocError::Other(
                    "at least 2 registers required for linear scan".into(),
                ));
            }
            let scratch = if let Some(suggested_reg) = info.suggested_scratch {
                reg_universe.regs[suggested_reg].0
            } else {
                return Err(RegAllocError::MissingSuggestedScratchReg(
                    RegClass::rc_from_u32(i as u32),
                ));
            };
            scratches_by_rc[i] = Some(scratch);
        }
    }
    Ok(scratches_by_rc)
}

/// Allocator top level.
///
/// `func` is modified so that, when this function returns, it will contain no VirtualReg uses.
///
/// Allocation can fail if there are insufficient registers to even generate spill/reload code, or
/// if the function appears to have any undefined VirtualReg/RealReg uses.
#[inline(never)]
pub(crate) fn run<F: Function>(
    func: &mut F,
    reg_universe: &RealRegUniverse,
    use_checker: bool,
    opts: &LinearScanOptions,
) -> Result<RegAllocResult<F>, RegAllocError> {
    let AnalysisInfo {
        reg_vecs_and_bounds: reg_uses,
        real_ranges: rlrs,
        virtual_ranges: vlrs,
        range_frags: fragments,
        liveins,
        liveouts,
        ..
    } = run_analysis(func, reg_universe).map_err(|err| RegAllocError::Analysis(err))?;

    let scratches_by_rc = compute_scratches(reg_universe)?;

    let mut stats = if opts.stats {
        Some(Statistics::default())
    } else {
        None
    };

    let intervals = Intervals::new(
        &reg_universe,
        &reg_uses,
        &rlrs,
        vlrs,
        &fragments,
        &mut stats,
    );

    if log_enabled!(Level::Trace) {
        trace!("fixed intervals:");
        for int in &intervals.fixeds {
            trace!("{}", int);
        }
        trace!("");
        trace!("unassigned intervals:");
        for int in &intervals.virtuals {
            trace!("{}", int);
            for mention in &int.mentions {
                trace!("  mention @ {:?}: {:?}", mention.0, mention.1);
            }
        }
        trace!("");
    }

    let (intervals, mut num_spill_slots) = assign_registers::run(
        opts,
        func,
        &reg_uses,
        reg_universe,
        &scratches_by_rc,
        intervals,
        stats,
    )?;

    // TODO avoid this clone.
    let mut sorted_virtuals = intervals.virtuals.clone();
    let virtuals = intervals.virtuals;

    // Sort by vreg and starting point, so we can plug all the different intervals
    // together.
    sorted_virtuals.sort_unstable_by_key(|int| (int.vreg, int.start));

    if log_enabled!(Level::Debug) {
        debug!("allocation results (by vreg)");
        for int in sorted_virtuals.iter() {
            debug!("{}", int);
        }
        debug!("");
    }

    let memory_moves = resolve_moves::run(
        func,
        &reg_uses,
        &virtuals,
        &sorted_virtuals,
        &liveins,
        &liveouts,
        &mut num_spill_slots,
        &scratches_by_rc,
    );

    apply_registers(
        func,
        &virtuals,
        memory_moves,
        reg_universe,
        num_spill_slots,
        use_checker,
    )
}

#[inline(never)]
fn set_registers<F: Function>(
    func: &mut F,
    virtual_intervals: &Vec<VirtualInterval>,
    reg_universe: &RealRegUniverse,
    use_checker: bool,
    memory_moves: &Vec<InstToInsertAndPoint>,
) -> Set<RealReg> {
    info!("set_registers");

    // Set up checker state, if indicated by our configuration.
    let mut checker: Option<CheckerContext> = None;
    let mut insn_blocks: Vec<BlockIx> = vec![];
    if use_checker {
        checker = Some(CheckerContext::new(func, reg_universe, memory_moves));
        insn_blocks.resize(func.insns().len(), BlockIx::new(0));
        for block_ix in func.blocks() {
            for insn_ix in func.block_insns(block_ix) {
                insn_blocks[insn_ix.get() as usize] = block_ix;
            }
        }
    }

    let mut clobbered_registers = Set::empty();

    // Collect all the regs per instruction and mention set.
    let capacity = virtual_intervals
        .iter()
        .map(|int| int.mentions.len())
        .fold(0, |a, b| a + b);

    if capacity == 0 {
        // No virtual registers have been allocated, exit early.
        return clobbered_registers;
    }

    let mut mention_map = Vec::with_capacity(capacity);

    for int in virtual_intervals {
        let rreg = match int.location.reg() {
            Some(rreg) => rreg,
            _ => continue,
        };
        trace!("int: {}", int);
        trace!("  {:?}", int.mentions);
        for &mention in &int.mentions {
            mention_map.push((mention.0, mention.1, int.vreg, rreg));
        }
    }

    // Sort by instruction index.
    mention_map.sort_unstable_by_key(|quad| quad.0);

    // Iterate over all the mentions.
    let mut mapper = MentionRegUsageMapper::new();

    let flush_inst = |func: &mut F,
                      mapper: &mut MentionRegUsageMapper,
                      iix: InstIx,
                      checker: Option<&mut CheckerContext>| {
        trace!("map_regs for {:?}", iix);
        let mut inst = func.get_insn_mut(iix);
        F::map_regs(&mut inst, mapper);

        if let Some(checker) = checker {
            let block_ix = insn_blocks[iix.get() as usize];
            checker
                .handle_insn(reg_universe, func, block_ix, iix, mapper)
                .unwrap();
        }

        mapper.clear();
    };

    let mut prev_iix = mention_map[0].0;
    for (iix, mention_set, vreg, rreg) in mention_map {
        if prev_iix != iix {
            // Flush previous instruction.
            flush_inst(func, &mut mapper, prev_iix, checker.as_mut());
            prev_iix = iix;
        }

        trace!(
            "{:?}: {:?} is in {:?} at {:?}",
            iix,
            vreg,
            rreg,
            mention_set
        );

        // Fill in new information at the given index.
        if mention_set.is_use() {
            if let Some(prev_rreg) = mapper.lookup_use(vreg) {
                debug_assert_eq!(prev_rreg, rreg, "different use allocs for {:?}", vreg);
            }
            mapper.set_use(vreg, rreg);
        }

        if mention_set.is_mod() {
            if let Some(prev_rreg) = mapper.lookup_use(vreg) {
                debug_assert_eq!(prev_rreg, rreg, "different use allocs for {:?}", vreg);
            }
            if let Some(prev_rreg) = mapper.lookup_def(vreg) {
                debug_assert_eq!(prev_rreg, rreg, "different def allocs for {:?}", vreg);
            }

            mapper.set_use(vreg, rreg);
            mapper.set_def(vreg, rreg);
            clobbered_registers.insert(rreg);
        }

        if mention_set.is_def() {
            if let Some(prev_rreg) = mapper.lookup_def(vreg) {
                debug_assert_eq!(prev_rreg, rreg, "different def allocs for {:?}", vreg);
            }

            mapper.set_def(vreg, rreg);
            clobbered_registers.insert(rreg);
        }
    }

    // Flush last instruction.
    flush_inst(func, &mut mapper, prev_iix, checker.as_mut());

    clobbered_registers
}

/// Fills in the register assignments into instructions.
#[inline(never)]
fn apply_registers<F: Function>(
    func: &mut F,
    virtual_intervals: &Vec<VirtualInterval>,
    memory_moves: Vec<InstToInsertAndPoint>,
    reg_universe: &RealRegUniverse,
    num_spill_slots: u32,
    use_checker: bool,
) -> Result<RegAllocResult<F>, RegAllocError> {
    info!("apply_registers");

    let clobbered_registers = set_registers(
        func,
        virtual_intervals,
        reg_universe,
        use_checker,
        &memory_moves,
    );

    let (final_insns, target_map, orig_insn_map) =
        add_spills_reloads_and_moves(func, memory_moves).map_err(|e| RegAllocError::Other(e))?;

    // And now remove from the clobbered registers set, all those not available to the allocator.
    // But not removing the reserved regs, since we might have modified those.
    clobbered_registers.filter_map(|&reg| {
        if reg.get_index() >= reg_universe.allocable {
            None
        } else {
            Some(reg)
        }
    });

    Ok(RegAllocResult {
        insns: final_insns,
        target_map,
        orig_insn_map,
        clobbered_registers,
        num_spill_slots,
        block_annotations: None,
    })
}
