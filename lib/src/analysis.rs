/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

use log::debug;
use rustc_hash::FxHashSet as HashSet;
use std::fmt;

use crate::data_structures::{
  BlockIx, InstIx, InstPoint, Map, Queue, RangeFrag, RangeFragIx,
  RangeFragKind, RealRange, RealRangeIx, RealReg, RealRegUniverse, Reg,
  SanitizedInstRegUses, Set, SortedRangeFragIxs, SpillCost, TypedIxVec,
  VirtualRange, VirtualRangeIx,
};
use crate::interface::Function;

#[derive(Clone, Debug)]
pub enum AnalysisError {
  /// A critical edge from "from" to "to" has been found, and should have been
  /// removed by the caller in the first place.
  CriticalEdge { from: BlockIx, to: BlockIx },

  /// Some values in the entry block are livein to the function, while not being
  /// marked as such.
  EntryLiveinValues,

  /// A non-existing real register has been seen in the code.
  NonExistingRealReg(RealReg),

  /// At least one block is dead.
  UnreachableBlocks,
}

impl ToString for AnalysisError {
  fn to_string(&self) -> String {
    match self {
      AnalysisError::CriticalEdge { from, to } => {
        format!("critical edge detected, from {:?} to {:?}", from, to)
      }
      AnalysisError::EntryLiveinValues => {
        "entry block has live-in value not present in function liveins".into()
      }
      AnalysisError::NonExistingRealReg(reg) => {
        format!("instructions mention real register {:?}, which isn't defined in the register universe", reg)
      }
      AnalysisError::UnreachableBlocks => {
        "at least one block is unreachable".to_string()
      }
    }
  }
}

//=============================================================================
// Control-flow analysis results for a Func: predecessors, successors,
// dominators and loop depths.

// CFGInfo contains CFG-related info computed from a Func.
struct CFGInfo {
  // All these TypedIxVecs contain one element per Block in the Func.

  // Predecessor and successor maps.
  pred_map: TypedIxVec<BlockIx, Set<BlockIx>>,
  succ_map: TypedIxVec<BlockIx, Set<BlockIx>>,

  // This maps from a Block to the set of Blocks it is dominated by
  dom_map: TypedIxVec<BlockIx, Set<BlockIx>>,

  // This maps from a Block to the loop depth that it is at
  depth_map: TypedIxVec<BlockIx, u32>,

  // Pre- and post-order sequences.  Iterating forwards through these
  // vectors enumerates the blocks in preorder and postorder respectively.
  pre_ord: Vec<BlockIx>,
  _post_ord: Vec<BlockIx>,
}

impl CFGInfo {
  #[inline(never)]
  fn create<F: Function>(func: &F) -> Result<Self, AnalysisError> {
    let nBlocks = func.blocks().len() as u32;

    // === BEGIN compute successor and predecessor maps ===
    //
    // First calculate the succ map, since we can do that directly from
    // the Func.
    //
    // Func::finish() ensures that all blocks are non-empty, and that only
    // the last instruction is a control flow transfer.  Hence the
    // following won't miss any edges.
    let mut succ_map = TypedIxVec::<BlockIx, Set<BlockIx>>::new();
    for b in func.blocks() {
      let succs = func.block_succs(b);
      let mut bixSet = Set::<BlockIx>::empty();
      for bix in succs.iter() {
        bixSet.insert(*bix);
      }
      succ_map.push(bixSet);
    }

    // Now invert the mapping
    let mut pred_map = TypedIxVec::<BlockIx, Set<BlockIx>>::new();
    pred_map.resize(nBlocks, Set::empty());
    for (src, dst_set) in (0..).zip(succ_map.iter()) {
      for dst in dst_set.iter() {
        pred_map[*dst].insert(BlockIx::new(src));
      }
    }

    // Stay sane ..
    assert!(pred_map.len() == nBlocks);
    assert!(succ_map.len() == nBlocks);
    //
    // === END compute successor and predecessor maps ===

    // === BEGIN check that critical edges have been split ===
    //
    for (src, dst_set) in (0..).zip(succ_map.iter()) {
      if dst_set.card() < 2 {
        continue;
      }
      for dst in dst_set.iter() {
        if pred_map[*dst].card() >= 2 {
          return Err(AnalysisError::CriticalEdge {
            from: BlockIx::new(src),
            to: *dst,
          });
        }
      }
    }
    //
    // === END check that critical edges have been split ===

    // === BEGIN compute preord/postord sequences ===
    //
    // This is per Fig 7.12 of Muchnick 1997
    //
    let mut pre_ord = Vec::<BlockIx>::new();
    let mut post_ord = Vec::<BlockIx>::new();

    let mut visited = TypedIxVec::<BlockIx, bool>::new();
    visited.resize(nBlocks, false);

    // FIXME: change this to use an explicit stack.
    fn dfs(
      pre_ord: &mut Vec<BlockIx>, post_ord: &mut Vec<BlockIx>,
      visited: &mut TypedIxVec<BlockIx, bool>,
      succ_map: &TypedIxVec<BlockIx, Set<BlockIx>>, bix: BlockIx,
    ) {
      debug_assert!(!visited[bix]);
      visited[bix] = true;
      pre_ord.push(bix);
      for succ in succ_map[bix].iter() {
        if !visited[*succ] {
          dfs(pre_ord, post_ord, visited, succ_map, *succ);
        }
      }
      post_ord.push(bix);
    }

    dfs(
      &mut pre_ord,
      &mut post_ord,
      &mut visited,
      &succ_map,
      func.entry_block(),
    );

    assert!(pre_ord.len() == post_ord.len());
    assert!(pre_ord.len() <= nBlocks as usize);
    if pre_ord.len() < nBlocks as usize {
      // This can happen if the graph contains nodes unreachable from
      // the entry point.  In which case, deal with any leftovers.
      for bix in BlockIx::new(0).dotdot(BlockIx::new(nBlocks)) {
        if !visited[bix] {
          dfs(&mut pre_ord, &mut post_ord, &mut visited, &succ_map, bix);
        }
      }
    }

    // Check that all blocks are reachable.
    {
      let mut visited_blocks = HashSet::default();
      let mut stack = vec![func.entry_block()];
      while let Some(block) = stack.pop() {
        if !visited_blocks.contains(&block) {
          visited_blocks.insert(block);

          use std::iter::FromIterator;
          let mut succ = Vec::from_iter(succ_map[block].iter().cloned());

          stack.append(&mut succ);
        }
      }

      // cfallin 2020-03-12: disable this check -- we want to do the right
      // thing in regalloc in the case of dead blocks, rather than error
      // on them.
      //if visited_blocks.len() as u32 != nBlocks {
      //  return Err(AnalysisError::UnreachableBlocks);
      //}
    }

    assert!(pre_ord.len() == nBlocks as usize);
    assert!(post_ord.len() == nBlocks as usize);
    #[cfg(debug_assertions)]
    {
      let mut pre_ord_sorted: Vec<BlockIx> = pre_ord.clone();
      let mut post_ord_sorted: Vec<BlockIx> = post_ord.clone();
      pre_ord_sorted
        .sort_by(|bix1, bix2| bix1.get().partial_cmp(&bix2.get()).unwrap());
      post_ord_sorted
        .sort_by(|bix1, bix2| bix1.get().partial_cmp(&bix2.get()).unwrap());
      let expected: Vec<BlockIx> =
        (0..nBlocks).map(|u| BlockIx::new(u)).collect();
      debug_assert!(pre_ord_sorted == expected);
      debug_assert!(post_ord_sorted == expected);
    }
    //
    // === END compute preord/postord sequences ===

    // === BEGIN compute dominator sets ===
    //
    let dom_map = calc_dominators(&pred_map, &post_ord, func.entry_block());

    // Stay sane ..
    assert!(dom_map.len() == nBlocks);
    //
    // === END compute dominator sets ===

    // === BEGIN compute loop depth of all Blocks
    //
    // Find the loops.  First, find the "loop header nodes", and from
    // those, derive the loops.
    //
    // Loop headers:
    // A "back edge" m->n is some edge m->n where n dominates m.  'n' is
    // the loop header node.
    //
    // |back_edges| is a set rather than a vector so as to avoid
    // complications that might later arise if the same loop is enumerated
    // more than once.
    //
    // Iterate over all edges (m->n)
    let mut back_edges = Set::<(BlockIx, BlockIx)>::empty();
    for bixM in BlockIx::new(0).dotdot(BlockIx::new(nBlocks)) {
      for bixN in succ_map[bixM].iter() {
        if dom_map[bixM].contains(*bixN) {
          //println!("QQQQ back edge {} -> {}",
          //         bixM.show(), bixN.show());
          back_edges.insert((bixM, *bixN));
        }
      }
    }

    // Now collect the sets of Blocks for each loop.  For each back edge,
    // collect up all the blocks in the natural loop defined by the back
    // edge M->N.  This algorithm is from Fig 7.21 of Muchnick 1997 (an
    // excellent book).  Order in |natural_loops| has no particular
    // meaning.
    let mut natural_loops = Vec::<Set<BlockIx>>::new();
    for (bixM, bixN) in back_edges.iter() {
      let mut Loop: Set<BlockIx>;
      let mut Stack: Vec<BlockIx>;
      Stack = Vec::<BlockIx>::new();
      Loop = Set::<BlockIx>::two(*bixM, *bixN);
      if bixM != bixN {
        // The next line is missing in the Muchnick description.
        // Without it the algorithm doesn't make any sense, though.
        Stack.push(*bixM);
        while let Some(bixP) = Stack.pop() {
          for bixQ in pred_map[bixP].iter() {
            if !Loop.contains(*bixQ) {
              Loop.insert(*bixQ);
              Stack.push(*bixQ);
            }
          }
        }
      }
      //println!("QQQQ back edge {} -> {} has loop {}",
      //         bixM.show(), bixN.show(), Loop.show());
      natural_loops.push(Loop);
    }

    // Here is a kludgey way to compute the depth of each loop.  First,
    // order |natural_loops| by increasing size, so the largest loops are
    // at the end.  Then, repeatedly scan forwards through the vector, in
    // "upper triangular matrix" style.  For each scan, remember the
    // "current loop".  Initially the "current loop is the start point of
    // each scan.  If, during the scan, we encounter a loop which is a
    // superset of the "current loop", change the "current loop" to this
    // new loop, and increment a counter associated with the start point
    // of the scan.  The effect is that the counter records the nesting
    // depth of the loop at the start of the scan.  For this to be
    // completely accurate, I _think_ this requires the property that
    // loops are either disjoint or nested, but are in no case
    // intersecting.

    natural_loops.sort_by(|blockSet1, blockSet2| {
      blockSet1.card().partial_cmp(&blockSet2.card()).unwrap()
    });

    let nLoops = natural_loops.len();
    let mut loop_depths = Vec::<u32>::new();
    loop_depths.resize(nLoops, 0);

    for i in 0..nLoops {
      let mut curr = i;
      let mut depth = 1;
      for j in i + 1..nLoops {
        debug_assert!(curr < j);
        if natural_loops[curr].is_subset_of(&natural_loops[j]) {
          depth += 1;
          curr = j;
        }
      }
      loop_depths[i] = depth;
    }

    // Now that we have a depth for each loop, we can finally compute the
    // depth for each block.
    let mut depth_map = TypedIxVec::<BlockIx, u32>::new();
    depth_map.resize(nBlocks, 0);
    for (loopBixs, depth) in natural_loops.iter().zip(loop_depths) {
      //println!("QQQQ4 {} {}", depth.show(), loopBixs.show());
      for loopBix in loopBixs.iter() {
        if depth_map[*loopBix] < depth {
          depth_map[*loopBix] = depth;
        }
      }
    }

    debug_assert!(depth_map.len() == nBlocks);
    //
    // === END compute loop depth of all Blocks

    //println!("QQQQ pre_ord  {}", pre_ord.show());
    //println!("QQQQ post_ord {}", post_ord.show());
    Ok(CFGInfo {
      pred_map,
      succ_map,
      dom_map,
      depth_map,
      pre_ord,
      _post_ord: post_ord,
    })
  }
}

// Calculate the dominance relationship, given |pred_map| and a start node
// |start|.  The resulting vector maps each block to the set of blocks that
// dominate it. This algorithm is from Fig 7.14 of Muchnick 1997. The
// algorithm is described as simple but not as performant as some others.
#[inline(never)]
fn calc_dominators(
  pred_map: &TypedIxVec<BlockIx, Set<BlockIx>>, post_ord: &Vec<BlockIx>,
  start: BlockIx,
) -> TypedIxVec<BlockIx, Set<BlockIx>> {
  debug!("");
  debug!("calc_dominators: begin");
  // FIXME: nice up the variable names (D, T, etc) a bit.
  let nBlocks = pred_map.len();
  let mut dom_map = TypedIxVec::<BlockIx, Set<BlockIx>>::new();
  {
    let r: BlockIx = start;
    let N: Set<BlockIx> =
      Set::from_vec((0..nBlocks).map(|bixNo| BlockIx::new(bixNo)).collect());
    let mut D: Set<BlockIx>;
    let mut T: Set<BlockIx>;
    dom_map.resize(nBlocks, Set::<BlockIx>::empty());
    dom_map[r] = Set::unit(r);
    for ixnoN in 0..nBlocks {
      let bixN = BlockIx::new(ixnoN);
      if bixN != r {
        dom_map[bixN] = N.clone();
      }
    }
    let mut nnn = 0;
    loop {
      nnn += 1;
      debug!("calc_dominators:   outer loop {}", nnn);
      let mut change = false;
      for i in 0..nBlocks {
        // bixN travels in "reverse preorder"
        let bixN = post_ord[(nBlocks - 1 - i) as usize];
        if bixN == r {
          continue;
        }
        T = N.clone();
        for bixP in pred_map[bixN].iter() {
          T.intersect(&dom_map[*bixP]);
        }
        D = T.clone();
        D.insert(bixN);
        if !D.equals(&dom_map[bixN]) {
          change = true;
          dom_map[bixN] = D;
        }
      }
      if !change {
        break;
      }
    }
  }
  debug!("calc_dominators: end");
  dom_map
}

//=============================================================================
// Extraction and sanitization of reg-use information.
//
// This calls the client's |get_regs| function on each instruction, then
// "sanitizes" the sets.  See definition of |SanitizedInstRegUses| for meaning
// of "sanitized".

fn get_sanitized_reg_uses<F: Function>(
  f: &F, reg_universe: &RealRegUniverse, sanitize_scratch: bool,
) -> Result<TypedIxVec<InstIx, SanitizedInstRegUses>, RealReg> {
  let mut san_reg_uses = TypedIxVec::new();

  let mut scratch_set: Set<Reg> = Set::empty();
  if sanitize_scratch {
    for reg_info in &reg_universe.allocable_by_class {
      if let Some(reg_info) = reg_info {
        if let Some(scratch_idx) = &reg_info.suggested_scratch {
          let scratch_reg = reg_universe.regs[*scratch_idx].0;
          scratch_set.insert(scratch_reg.to_reg());
        }
      }
    }
  }

  for inst in f.insns() {
    let iru = f.get_regs(inst); // AUDITED
    let mut sru =
      SanitizedInstRegUses::create_by_sanitizing(&iru, reg_universe)?;
    sru.san_modified.remove(&scratch_set);
    san_reg_uses.push(sru);
  }
  Ok(san_reg_uses)
}

//=============================================================================
// Computation of live-in and live-out sets

// Returned TypedIxVecs contain one element per block
#[inline(never)]
fn calc_def_and_use<F: Function>(
  f: &F, san_reg_uses: &TypedIxVec<InstIx, SanitizedInstRegUses>,
) -> (TypedIxVec<BlockIx, Set<Reg>>, TypedIxVec<BlockIx, Set<Reg>>) {
  debug!("");
  debug!("calc_def_and_use: begin");
  let mut def_sets = TypedIxVec::new();
  let mut use_sets = TypedIxVec::new();
  for b in f.blocks() {
    let mut def = Set::empty();
    let mut uce = Set::empty();
    for iix in f.block_insns(b) {
      let sru = &san_reg_uses[iix];
      // Add to |uce|, any registers for which the first event
      // in this block is a read.  Dealing with the "first event"
      // constraint is a bit tricky.
      for u in sru.san_used.iter().chain(sru.san_modified.iter()) {
        // |u| is used (either read or modified) by the
        // instruction.  Whether or not we should consider it
        // live-in for the block depends on whether it was been
        // written earlier in the block.  We can determine that by
        // checking whether it is already in the def set for the
        // block.
        if !def.contains(*u) {
          uce.insert(*u);
        }
      }
      // Now add to |def|, all registers written by the instruction.
      // This is simpler.
      // FIXME: isn't this just: defs union= (regs_d union regs_m) ?
      // (Similar comment applies for the |uce| update too)
      for d in sru.san_defined.iter().chain(sru.san_modified.iter()) {
        def.insert(*d);
      }
    }
    def_sets.push(def);
    use_sets.push(uce);
  }
  debug!("calc_def_and_use: end");
  (def_sets, use_sets)
}

// Returned vectors contain one element per block
#[inline(never)]
fn calc_livein_and_liveout<F: Function>(
  f: &F, def_sets_per_block: &TypedIxVec<BlockIx, Set<Reg>>,
  use_sets_per_block: &TypedIxVec<BlockIx, Set<Reg>>, cfg_info: &CFGInfo,
) -> (TypedIxVec<BlockIx, Set<Reg>>, TypedIxVec<BlockIx, Set<Reg>>) {
  debug!("");
  debug!("calc_livein_and_liveout: begin");
  let nBlocks = f.blocks().len() as u32;
  let empty = Set::<Reg>::empty();

  let mut nEvals = 0;
  let mut liveouts = TypedIxVec::<BlockIx, Set<Reg>>::new();
  liveouts.resize(nBlocks, empty.clone());

  // Initialise the work queue so as to do a reverse preorder traversal
  // through the graph, after which blocks are re-evaluated on demand.
  let mut workQ = Queue::<BlockIx>::new();
  for i in 0..nBlocks {
    // bixI travels in "reverse preorder"
    let bixI = cfg_info.pre_ord[(nBlocks - 1 - i) as usize];
    workQ.push_back(bixI);
  }

  while let Some(bixI) = workQ.pop_front() {
    // Compute a new value for liveouts[bixI]
    let mut set = Set::<Reg>::empty();
    for bixJ in cfg_info.succ_map[bixI].iter() {
      let mut liveinJ = liveouts[*bixJ].clone();
      liveinJ.remove(&def_sets_per_block[*bixJ]);
      liveinJ.union(&use_sets_per_block[*bixJ]);
      set.union(&liveinJ);
    }
    nEvals += 1;

    if !set.equals(&liveouts[bixI]) {
      liveouts[bixI] = set;
      // Add |bixI|'s predecessors to the work queue, since their
      // liveout values might be affected.
      //
      // FIXME JRS 2020Feb06: only add preds to the work queue if they are not
      // already in it (possible speedup).
      for bixJ in cfg_info.pred_map[bixI].iter() {
        workQ.push_back(*bixJ);
      }
    }
  }

  // The liveout values are done, but we need to compute the liveins
  // too.
  let mut liveins = TypedIxVec::<BlockIx, Set<Reg>>::new();
  liveins.resize(nBlocks, empty.clone());
  for bixI in BlockIx::new(0).dotdot(BlockIx::new(nBlocks)) {
    let mut liveinI = liveouts[bixI].clone();
    liveinI.remove(&def_sets_per_block[bixI]);
    liveinI.union(&use_sets_per_block[bixI]);
    liveins[bixI] = liveinI;
  }

  if false {
    let mut sum_card_LI = 0;
    let mut sum_card_LO = 0;
    for bix in BlockIx::new(0).dotdot(BlockIx::new(nBlocks)) {
      sum_card_LI += liveins[bix].card();
      sum_card_LO += liveouts[bix].card();
    }
    println!(
      "QQQQ calc_LI/LO: nEvals {}, tot LI {}, tot LO {}",
      nEvals, sum_card_LI, sum_card_LO
    );
  }

  debug!("calc_livein_and_liveout: end");
  (liveins, liveouts)
}

//=============================================================================
// Computation of RangeFrags (Live Range Fragments)

// This is surprisingly complex, in part because of the need to correctly
// handle (1) live-in and live-out Regs, (2) dead writes, and (3) instructions
// that modify registers rather than merely reading or writing them.

// Calculate all the RangeFrags for |bix|.  Add them to |outFEnv| and add to
// |outMap|, the associated RangeFragIxs, segregated by Reg.  |bix|, |livein|,
// |liveout| and |san_reg_uses| are expected to be valid in the context of the
// Func |f| (duh!)
fn get_RangeFrags_for_block<F: Function>(
  f: &F, bix: BlockIx, livein: &Set<Reg>, liveout: &Set<Reg>,
  san_reg_uses: &TypedIxVec<InstIx, SanitizedInstRegUses>,
  outMap: &mut Map<Reg, Vec<RangeFragIx>>,
  outFEnv: &mut TypedIxVec<RangeFragIx, RangeFrag>,
) {
  //println!("QQQQ --- block {}", bix.show());
  // BEGIN ProtoRangeFrag
  // A ProtoRangeFrag carries information about a write .. read range,
  // within a Block, which we will later turn into a fully-fledged
  // RangeFrag.  It basically records the first and last-known
  // InstPoints for appearances of a Reg.
  //
  // ProtoRangeFrag also keeps count of the number of appearances of
  // the Reg to which it pertains, using |uses|.  The counts get rolled
  // into the resulting RangeFrags, and later are used to calculate
  // spill costs.
  //
  // The running state of this function is a map from Reg to
  // ProtoRangeFrag.  Only Regs that actually appear in the Block (or are
  // live-in to it) are mapped.  This has the advantage of economy, since
  // most Regs will not appear in (or be live-in to) most Blocks.
  //
  struct ProtoRangeFrag {
    // The InstPoint in this Block at which the associated Reg most
    // recently became live (when moving forwards though the Block).
    // If this value is the first InstPoint for the Block (the U point
    // for the Block's lowest InstIx), that indicates the associated
    // Reg is live-in to the Block.
    first: InstPoint,

    // And this is the InstPoint which is the end point (most recently
    // observed read, in general) for the current RangeFrag under
    // construction.  In general we will move |last| forwards as we
    // discover reads of the associated Reg.  If this is the last
    // InstPoint for the Block (the D point for the Block's highest
    // InstInx), that indicates that the associated reg is live-out
    // from the Block.
    last: InstPoint,

    // Number of mentions of the associated Reg in this ProtoRangeFrag.
    uses: u16,
  }
  impl fmt::Debug for ProtoRangeFrag {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
      write!(fmt, "{:?}x {:?} - {:?}", self.uses, self.first, self.last)
    }
  }
  // END ProtoRangeFrag

  fn plus1(n: u16) -> u16 {
    if n == 0xFFFFu16 {
      n
    } else {
      n + 1
    }
  }

  // Some handy constants.
  debug_assert!(f.block_insns(bix).len() >= 1);
  let first_iix_in_block = f.block_insns(bix).first();
  let last_iix_in_block = f.block_insns(bix).last();
  let first_pt_in_block = InstPoint::new_use(first_iix_in_block);
  let last_pt_in_block = InstPoint::new_def(last_iix_in_block);

  // The running state.
  let mut state = Map::<Reg, ProtoRangeFrag>::default();

  // The generated RangeFrags are initially are dumped in here.  We
  // group them by Reg at the end of this function.
  let mut tmpResultVec = Vec::<(Reg, RangeFrag)>::new();

  // First, set up |state| as if all of |livein| had been written just
  // prior to the block.
  for r in livein.iter() {
    state.insert(
      *r,
      ProtoRangeFrag {
        uses: 0,
        first: first_pt_in_block,
        last: first_pt_in_block,
      },
    );
  }

  // Now visit each instruction in turn, examining first the registers
  // it reads, then those it modifies, and finally those it writes.
  for iix in f.block_insns(bix) {
    let sru = &san_reg_uses[iix];

    // Examine reads.  This is pretty simple.  They simply extend an
    // existing ProtoRangeFrag to the U point of the reading insn.
    for r in sru.san_used.iter() {
      let new_pf: ProtoRangeFrag;
      match state.get(r) {
        // First event for |r| is a read, but it's not listed in
        // |livein|, since otherwise |state| would have an entry
        // for it.
        None => {
          panic!("get_RangeFrags_for_block: fail #1");
        }
        // This the first or subsequent read after a write.  Note
        // that the "write" can be either a real write, or due to
        // the fact that |r| is listed in |livein|.  We don't care
        // here.
        Some(ProtoRangeFrag { uses, first, last }) => {
          let new_last = InstPoint::new_use(iix);
          debug_assert!(last <= &new_last);
          new_pf = ProtoRangeFrag {
            uses: plus1(*uses),
            first: *first,
            last: new_last,
          };
        }
      }
      state.insert(*r, new_pf);
    }

    // Examine modifies.  These are handled almost identically to
    // reads, except that they extend an existing ProtoRangeFrag down to
    // the D point of the modifying insn.
    for r in sru.san_modified.iter() {
      let new_pf: ProtoRangeFrag;
      match state.get(r) {
        // First event for |r| is a read (really, since this insn
        // modifies |r|), but it's not listed in |livein|, since
        // otherwise |state| would have an entry for it.
        None => {
          panic!("get_RangeFrags_for_block: fail #2");
        }
        // This the first or subsequent modify after a write.
        Some(ProtoRangeFrag { uses, first, last }) => {
          let new_last = InstPoint::new_def(iix);
          debug_assert!(last <= &new_last);
          new_pf = ProtoRangeFrag {
            uses: plus1(*uses),
            first: *first,
            last: new_last,
          };
        }
      }
      state.insert(*r, new_pf);
    }

    // Examine writes (but not writes implied by modifies).  The
    // general idea is that a write causes us to terminate the
    // existing ProtoRangeFrag, if any, add it to |tmpResultVec|,
    // and start a new frag.
    for r in sru.san_defined.iter() {
      let new_pf: ProtoRangeFrag;
      match state.get(r) {
        // First mention of a Reg we've never heard of before.
        // Start a new ProtoRangeFrag for it and keep going.
        None => {
          let new_pt = InstPoint::new_def(iix);
          new_pf = ProtoRangeFrag { uses: 1, first: new_pt, last: new_pt };
        }
        // There's already a ProtoRangeFrag for |r|.  This write
        // will start a new one, so flush the existing one and
        // note this write.
        Some(ProtoRangeFrag { uses, first, last }) => {
          if first == last {
            debug_assert!(*uses == 1);
          }
          let frag = RangeFrag::new(f, bix, *first, *last, *uses);
          tmpResultVec.push((*r, frag));
          let new_pt = InstPoint::new_def(iix);
          new_pf = ProtoRangeFrag { uses: 1, first: new_pt, last: new_pt };
        }
      }
      state.insert(*r, new_pf);
    }
    //println!("QQQQ state after  {}",
    //         id(state.iter().collect()).show());
  }

  // We are at the end of the block.  We still have to deal with
  // live-out Regs.  We must also deal with ProtoRangeFrags in |state|
  // that are for registers not listed as live-out.

  // Deal with live-out Regs.  Treat each one as if it is read just
  // after the block.
  for r in liveout.iter() {
    //println!("QQQQ post: liveout:  {}", r.show());
    match state.get(r) {
      // This can't happen.  |r| is in |liveout|, but this implies
      // that it is neither defined in the block nor present in
      // |livein|.
      None => {
        panic!("get_RangeFrags_for_block: fail #3");
      }
      // |r| is written (or modified), either literally or by virtue
      // of being present in |livein|, and may or may not
      // subsequently be read -- we don't care, because it must be
      // read "after" the block.  Create a |LiveOut| or |Thru| frag
      // accordingly.
      Some(ProtoRangeFrag { uses, first, last: _ }) => {
        let frag = RangeFrag::new(f, bix, *first, last_pt_in_block, *uses);
        tmpResultVec.push((*r, frag));
      }
    }
    // Remove the entry from |state| so that the following loop
    // doesn't process it again.
    state.remove(r);
  }

  // Finally, round up any remaining ProtoRangeFrags left in |state|.
  for (r, pf) in state.iter() {
    //println!("QQQQ post: leftover: {} {}", r.show(), pf.show());
    if pf.first == pf.last {
      debug_assert!(pf.uses == 1);
    }
    let frag = RangeFrag::new(f, bix, pf.first, pf.last, pf.uses);
    //println!("QQQQ post: leftover: {}", (r,frag).show());
    tmpResultVec.push((*r, frag));
  }

  // Copy the entries in |tmpResultVec| into |outMap| and |outVec|.
  // TODO: do this as we go along, so as to avoid the use of a temporary
  // vector.
  for (r, frag) in tmpResultVec {
    // Allocate a new RangeFragIx for |frag|, except, make some minimal effort
    // to avoid huge numbers of duplicates by inspecting the previous two
    // entries, and using them if possible.
    let outFEnv_len = outFEnv.len();
    let new_fix: RangeFragIx;
    if outFEnv_len >= 2 {
      let back_0 = RangeFragIx::new(outFEnv_len - 1);
      let back_1 = RangeFragIx::new(outFEnv_len - 2);
      if outFEnv[back_0] == frag {
        new_fix = back_0;
      } else if outFEnv[back_1] == frag {
        new_fix = back_1;
      } else {
        // No match; create a new one.
        outFEnv.push(frag);
        new_fix = RangeFragIx::new(outFEnv.len() as u32 - 1);
      }
    } else {
      // We can't look back; create a new one.
      outFEnv.push(frag);
      new_fix = RangeFragIx::new(outFEnv.len() as u32 - 1);
    }
    // And use the new RangeFragIx.
    match outMap.get_mut(&r) {
      None => {
        outMap.insert(r, vec![new_fix]);
      }
      Some(fragVec) => {
        fragVec.push(new_fix);
      }
    }
  }
}

#[inline(never)]
fn get_RangeFrags<F: Function>(
  f: &F, livein_sets_per_block: &TypedIxVec<BlockIx, Set<Reg>>,
  liveout_sets_per_block: &TypedIxVec<BlockIx, Set<Reg>>,
  san_reg_uses: &TypedIxVec<InstIx, SanitizedInstRegUses>,
) -> (Map<Reg, Vec<RangeFragIx>>, TypedIxVec<RangeFragIx, RangeFrag>) {
  debug_assert!(livein_sets_per_block.len() == f.blocks().len() as u32);
  debug_assert!(liveout_sets_per_block.len() == f.blocks().len() as u32);
  let mut resMap = Map::<Reg, Vec<RangeFragIx>>::default();
  let mut resFEnv = TypedIxVec::<RangeFragIx, RangeFrag>::new();
  for bix in f.blocks() {
    get_RangeFrags_for_block(
      f,
      bix,
      &livein_sets_per_block[bix],
      &liveout_sets_per_block[bix],
      &san_reg_uses,
      &mut resMap,
      &mut resFEnv,
    );
  }
  (resMap, resFEnv)
}

//=============================================================================
// Merging of RangeFrags, producing the final LRs, minus metrics

#[inline(never)]
fn merge_RangeFrags(
  fragIx_vecs_per_reg: &Map<Reg, Vec<RangeFragIx>>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>, cfg_info: &CFGInfo,
) -> (
  TypedIxVec<RealRangeIx, RealRange>,
  TypedIxVec<VirtualRangeIx, VirtualRange>,
) {
  debug!("");
  debug!("merge_RangeFrags: begin");
  let mut resR = TypedIxVec::<RealRangeIx, RealRange>::new();
  let mut resV = TypedIxVec::<VirtualRangeIx, VirtualRange>::new();
  for (reg, all_frag_ixs_for_reg) in fragIx_vecs_per_reg.iter() {
    // BEGIN merge |all_frag_ixs_for_reg| entries as much as possible.
    // Each |state| entry has four components:
    //    (1) An is-this-entry-still-valid flag
    //    (2) A set of RangeFragIxs.  These should refer to disjoint
    //        RangeFrags.
    //    (3) A set of blocks, which are those corresponding to (2)
    //        that are LiveIn or Thru (== have an inbound value)
    //    (4) A set of blocks, which are the union of the successors of
    //        blocks corresponding to the (2) which are LiveOut or Thru
    //        (== have an outbound value)
    struct MergeGroup {
      valid: bool,
      frag_ixs: Set<RangeFragIx>,
      live_in_blocks: Set<BlockIx>,
      succs_of_live_out_blocks: Set<BlockIx>,
    }

    let mut state = Vec::<MergeGroup>::new();

    // Create the initial state by giving each RangeFragIx its own Vec, and
    // tagging it with its interface blocks.
    for fix in all_frag_ixs_for_reg {
      let mut live_in_blocks = Set::<BlockIx>::empty();
      let mut succs_of_live_out_blocks = Set::<BlockIx>::empty();
      let frag = &frag_env[*fix];
      let frag_bix = frag.bix;
      let frag_succ_bixes = &cfg_info.succ_map[frag_bix];
      match frag.kind {
        RangeFragKind::Local => {}
        RangeFragKind::LiveIn => {
          live_in_blocks.insert(frag_bix);
        }
        RangeFragKind::LiveOut => {
          succs_of_live_out_blocks.union(frag_succ_bixes);
        }
        RangeFragKind::Thru => {
          live_in_blocks.insert(frag_bix);
          succs_of_live_out_blocks.union(frag_succ_bixes);
        }
      }

      let valid = true;
      let frag_ixs = Set::unit(*fix);
      let mg = MergeGroup {
        valid,
        frag_ixs,
        live_in_blocks,
        succs_of_live_out_blocks,
      };
      state.push(mg);
    }

    // Iterate over |state|, merging entries as much as possible.  This
    // is, unfortunately, quadratic.
    let state_len = state.len();
    loop {
      let mut changed = false;

      for i in 0..state_len {
        if !state[i].valid {
          continue;
        }
        for j in i + 1..state_len {
          if !state[j].valid {
            continue;
          }
          let do_merge = // frag group i feeds a value to group j
                        state[i].succs_of_live_out_blocks
                                .intersects(&state[j].live_in_blocks)
                        || // frag group j feeds a value to group i
                        state[j].succs_of_live_out_blocks
                                .intersects(&state[i].live_in_blocks);
          if do_merge {
            let mut tmp_frag_ixs = state[i].frag_ixs.clone();
            state[j].frag_ixs.union(&mut tmp_frag_ixs);
            let tmp_libs = state[i].live_in_blocks.clone();
            state[j].live_in_blocks.union(&tmp_libs);
            let tmp_solobs = state[i].succs_of_live_out_blocks.clone();
            state[j].succs_of_live_out_blocks.union(&tmp_solobs);
            state[i].valid = false;
            changed = true;
          }
        }
      }

      if !changed {
        break;
      }
    }

    // Harvest the merged RangeFrag sets from |state|, and turn them into
    // RealRanges or VirtualRanges.
    for MergeGroup { valid, frag_ixs, .. } in state {
      if !valid {
        continue;
      }
      let sorted_frags = SortedRangeFragIxs::new(&frag_ixs.to_vec(), &frag_env);
      let size = 0;
      // Set zero spill cost for now.  We'll fill it in for real later.
      let spill_cost = SpillCost::zero();
      if reg.is_virtual() {
        resV.push(VirtualRange {
          vreg: reg.to_virtual_reg(),
          rreg: None,
          sorted_frags,
          size,
          spill_cost,
        });
      } else {
        resR.push(RealRange { rreg: reg.to_real_reg(), sorted_frags });
      }
    }

    // END merge |all_frag_ixs_for_reg| entries as much as possible
  }

  debug!("merge_RangeFrags: end");
  (resR, resV)
}

//=============================================================================
// Finalising of VirtualRanges, by setting the |size| and |spill_cost| metrics.

// |size|: this is simple.  Simply sum the size of the individual fragments.
// Note that this must produce a value > 0 for a dead write, hence the "+1".
//
// |spill_cost|: try to estimate the number of spills and reloads that would
// result from spilling the VirtualRange, thusly:
//    sum, for each frag
//        # mentions of the VirtualReg in the frag
//            (that's the per-frag, per pass spill spill_cost)
//        *
//        the estimated execution count of the containing block
//
// all the while being very careful to avoid overflow.
#[inline(never)]
fn set_VirtualRange_metrics(
  vlrs: &mut TypedIxVec<VirtualRangeIx, VirtualRange>,
  fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  estFreq: &TypedIxVec<BlockIx, u32>,
) {
  debug!("");
  debug!("set_VirtualRange_metrics: begin");
  for vlr in vlrs.iter_mut() {
    debug_assert!(vlr.size == 0 && vlr.spill_cost.is_zero());
    debug_assert!(vlr.rreg.is_none());
    let mut tot_size: u32 = 0;
    let mut tot_cost: f32 = 0.0;

    for fix in &vlr.sorted_frags.frag_ixs {
      let frag = &fenv[*fix];

      // Add on the size of this fragment, but make sure we can't
      // overflow a u32 no matter how many fragments there are.
      let mut frag_size: u32 = frag.last.iix.get() - frag.first.iix.get() + 1;
      if frag_size > 0xFFFF {
        frag_size = 0xFFFF;
      }
      tot_size += frag_size;
      if tot_size > 0xFFFF {
        tot_size = 0xFFFF;
      }

      // tot_cost is a float, so no such paranoia there.
      tot_cost += frag.count as f32 * estFreq[frag.bix] as f32;
    }

    debug_assert!(tot_cost >= 0.0);
    debug_assert!(tot_size >= 1 && tot_size <= 0xFFFF);
    vlr.size = tot_size as u16;

    // Divide tot_cost by the total length, so as to increase the apparent
    // spill cost of short LRs.  This is so as to give the advantage to
    // short LRs in competition for registers.  This seems a bit of a hack
    // to me, but hey ..
    tot_cost /= tot_size as f32;
    vlr.spill_cost = SpillCost::finite(tot_cost);
  }
  debug!("set_VirtualRange_metrics: end");
}

#[inline(never)]
pub fn run_analysis<F: Function>(
  func: &F, reg_universe: &RealRegUniverse, sanitize_scratch: bool,
) -> Result<
  (
    // The sanitized per-insn reg-use info
    TypedIxVec<InstIx, SanitizedInstRegUses>,
    // The real-reg live ranges
    TypedIxVec<RealRangeIx, RealRange>,
    // The virtual-reg live ranges
    TypedIxVec<VirtualRangeIx, VirtualRange>,
    // The fragment table
    TypedIxVec<RangeFragIx, RangeFrag>,
    // Liveouts per block
    TypedIxVec<BlockIx, Set<Reg>>,
    // Estimated execution frequency per block
    TypedIxVec<BlockIx, u32>,
  ),
  AnalysisError,
> {
  // See |get_sanitized_reg_uses| for the meaning of "sanitized".
  let san_reg_uses =
    get_sanitized_reg_uses(func, reg_universe, sanitize_scratch)
      .map_err(|reg| AnalysisError::NonExistingRealReg(reg))?;

  let (def_sets_per_block, use_sets_per_block) =
    calc_def_and_use(func, &san_reg_uses);
  debug_assert!(def_sets_per_block.len() == func.blocks().len() as u32);
  debug_assert!(use_sets_per_block.len() == func.blocks().len() as u32);

  let mut n = 0;
  debug!("");
  for (def, uce) in def_sets_per_block.iter().zip(use_sets_per_block.iter()) {
    debug!("{:<3?}   def {:<16?}  use {:?}", BlockIx::new(n), def, uce);
    n += 1;
  }

  let cfg_info = CFGInfo::create(func)?;

  n = 0;
  debug!("");
  for (preds, succs) in cfg_info.pred_map.iter().zip(cfg_info.succ_map.iter()) {
    debug!("{:<3?}   preds {:<16?}  succs {:?}", BlockIx::new(n), preds, succs);
    n += 1;
  }

  n = 0;
  debug!("");
  for (depth, dom_by) in cfg_info.depth_map.iter().zip(cfg_info.dom_map.iter())
  {
    debug!(
      "{:<3?}   depth {}   dom_by {:<16?}",
      BlockIx::new(n),
      depth,
      dom_by
    );
    n += 1;
  }

  // Annotate each Block with its estimated execution frequency
  let mut estFreqs = TypedIxVec::new();
  for bix in func.blocks() {
    let mut estFreq = 1;
    let mut depth = cfg_info.depth_map[bix];
    if depth > 3 {
      depth = 3;
    }
    for _ in 0..depth {
      estFreq *= 10;
    }
    assert!(bix == BlockIx::new(estFreqs.len()));
    estFreqs.push(estFreq);
  }

  // |liveout_sets_per_block| is amended below for return blocks, hence `mut`.
  let (livein_sets_per_block, mut liveout_sets_per_block) =
    calc_livein_and_liveout(
      func,
      &def_sets_per_block,
      &use_sets_per_block,
      &cfg_info,
    );
  debug_assert!(livein_sets_per_block.len() == func.blocks().len() as u32);
  debug_assert!(liveout_sets_per_block.len() == func.blocks().len() as u32);

  n = 0;
  debug!("");
  for (livein, liveout) in
    livein_sets_per_block.iter().zip(liveout_sets_per_block.iter())
  {
    debug!(
      "{:<3?}   livein {:<16?}  liveout {:<16?}",
      BlockIx::new(n),
      livein,
      liveout
    );
    n += 1;
  }

  // Verify livein set of entry block against liveins specified by function
  // (e.g., ABI params).
  let func_liveins = Set::from_vec(
    func
      .func_liveins()
      .to_vec()
      .into_iter()
      .map(|rreg| rreg.to_reg())
      .collect(),
  );
  if !livein_sets_per_block[func.entry_block()].is_subset_of(&func_liveins) {
    return Err(AnalysisError::EntryLiveinValues);
  }

  // Add function liveouts to every block ending in a return.
  let func_liveouts = Set::from_vec(
    func
      .func_liveouts()
      .to_vec()
      .into_iter()
      .map(|rreg| rreg.to_reg())
      .collect(),
  );
  for block in func.blocks() {
    let last_iix = func.block_insns(block).last();
    if func.is_ret(last_iix) {
      liveout_sets_per_block[block].union(&func_liveouts);
    }
  }

  let (frag_ixs_per_reg, frag_env) = get_RangeFrags(
    func,
    &livein_sets_per_block,
    &liveout_sets_per_block,
    &san_reg_uses,
  );

  debug!("");
  n = 0;
  for frag in frag_env.iter() {
    debug!("{:<3?}   {:?}", RangeFragIx::new(n), frag);
    n += 1;
  }

  debug!("");
  for (reg, frag_ixs) in frag_ixs_per_reg.iter() {
    debug!("frags for {:?}   {:?}", reg, frag_ixs);
  }

  let (rlr_env, mut vlr_env) =
    merge_RangeFrags(&frag_ixs_per_reg, &frag_env, &cfg_info);
  set_VirtualRange_metrics(&mut vlr_env, &frag_env, &estFreqs);

  debug!("");
  n = 0;
  for rlr in rlr_env.iter() {
    debug!("{:<4?}   {:?}", RealRangeIx::new(n), rlr);
    n += 1;
  }

  debug!("");
  n = 0;
  for vlr in vlr_env.iter() {
    debug!("{:<4?}   {:?}", VirtualRangeIx::new(n), vlr);
    n += 1;
  }

  debug_assert!(liveout_sets_per_block.len() == estFreqs.len());

  Ok((
    san_reg_uses,
    rlr_env,
    vlr_env,
    frag_env,
    liveout_sets_per_block,
    estFreqs,
  ))
}
