/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

use log::{debug, info};
//use rustc_hash::FxHashSet as HashSet;
use std::fmt;

use crate::data_structures::{
  BlockIx, InstIx, InstPoint, Map, Queue, RangeFrag, RangeFragIx,
  RangeFragKind, RealRange, RealRangeIx, RealReg, RealRegUniverse, Reg,
  SanitizedInstRegUses, Set, SortedRangeFragIxs, SpillCost, TypedIxVec,
  VirtualRange, VirtualRangeIx,
};
use crate::interface::Function;
use crate::trees_maps_sets::{ToFromU32, UnionFind};

// DEBUGGING: set to true to cross-check the merge_RangeFrags machinery.

const CROSSCHECK_MERGE: bool = false;

//=============================================================================
// Overall analysis return results, for both control- and data-flow analyses.

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

  /// Implementation limits exceeded
  ImplementationLimitsExceeded,
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
      AnalysisError::ImplementationLimitsExceeded => {
        "implementation limits exceeded (too many blocks, insns, etc)".to_string()
      }
    }
  }
}

//===========================================================================//
//                                                                           //
// CONTROL FLOW ANALYSIS                                                     //
//                                                                           //
//===========================================================================//

//=============================================================================
// Control flow analysis: calculation of block successor and predecessor maps

// Returned TypedIxVecs contain one element per block
#[inline(never)]
fn calc_preds_and_succs<F: Function>(
  func: &F, nBlocks: u32,
) -> (TypedIxVec<BlockIx, Set<BlockIx>>, TypedIxVec<BlockIx, Set<BlockIx>>) {
  info!("      calc_preds_and_succs: begin");

  assert!(func.blocks().len() == nBlocks as usize);

  // First calculate the succ map, since we can do that directly from the
  // Func.
  //
  // Func::finish() ensures that all blocks are non-empty, and that only the
  // last instruction is a control flow transfer.  Hence the following won't
  // miss any edges.
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

  let mut n = 0;
  debug!("");
  for (preds, succs) in pred_map.iter().zip(succ_map.iter()) {
    debug!("{:<3?}   preds {:<16?}  succs {:?}", BlockIx::new(n), preds, succs);
    n += 1;
  }

  info!("      calc_preds_and_succs: end");
  (pred_map, succ_map)
}

//=============================================================================
// Control flow analysis: calculation of block preorder and postorder sequences

// Returned Vecs contain one element per block.
#[inline(never)]
fn calc_preord_and_postord<F: Function>(
  func: &F, nBlocks: u32, succ_map: &TypedIxVec<BlockIx, Set<BlockIx>>,
) -> (Vec<BlockIx>, Vec<BlockIx>) {
  info!("      calc_preord_and_postord: begin");

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

  dfs(&mut pre_ord, &mut post_ord, &mut visited, &succ_map, func.entry_block());

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

  info!("      calc_preord_and_postord: begin");
  (pre_ord, post_ord)
}

//=============================================================================
// Computation of per-block dominator sets.  Note, this is slow, and will be
// removed at some point.

// Calculate the dominance relationship, given |pred_map| and a start node
// |start|.  The resulting vector maps each block to the set of blocks that
// dominate it. This algorithm is from Fig 7.14 of Muchnick 1997. The
// algorithm is described as simple but not as performant as some others.
#[inline(never)]
fn calc_dom_sets(
  nBlocks: u32, pred_map: &TypedIxVec<BlockIx, Set<BlockIx>>,
  post_ord: &Vec<BlockIx>, start: BlockIx,
) -> TypedIxVec<BlockIx, Set<BlockIx>> {
  info!("        calc_dom_sets: begin");
  // FIXME: nice up the variable names (D, T, etc) a bit.
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
      info!("        calc_dom_sets:   outer loop {}", nnn);
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
  info!("        calc_dom_sets: end");
  dom_map
}

//=============================================================================
// Computation of per-block loop-depths

#[inline(never)]
fn calc_loop_depths(
  nBlocks: u32, pred_map: &TypedIxVec<BlockIx, Set<BlockIx>>,
  succ_map: &TypedIxVec<BlockIx, Set<BlockIx>>, post_ord: &Vec<BlockIx>,
  start: BlockIx,
) -> TypedIxVec<BlockIx, u32> {
  info!("      calc_loop_depths: begin");
  let dom_map = calc_dom_sets(nBlocks, pred_map, post_ord, start);

  // Find the loops.  First, find the "loop header nodes", and from those,
  // derive the loops.
  //
  // Loop headers:
  // A "back edge" m->n is some edge m->n where n dominates m.  'n' is
  // the loop header node.
  //
  // |back_edges| is a set rather than a vector so as to avoid complications
  // that might later arise if the same loop is enumerated more than once.
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
  // collect up all the blocks in the natural loop defined by the back edge
  // M->N.  This algorithm is from Fig 7.21 of Muchnick 1997 (an excellent
  // book).  Order in |natural_loops| has no particular meaning.
  let mut natural_loops = Vec::<Set<BlockIx>>::new();
  for (bixM, bixN) in back_edges.iter() {
    let mut Loop: Set<BlockIx>;
    let mut Stack: Vec<BlockIx>;
    Stack = Vec::<BlockIx>::new();
    Loop = Set::<BlockIx>::two(*bixM, *bixN);
    if bixM != bixN {
      // The next line is missing in the Muchnick description.  Without it the
      // algorithm doesn't make any sense, though.
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

  // Here is a kludgey way to compute the depth of each loop.  First, order
  // |natural_loops| by increasing size, so the largest loops are at the end.
  // Then, repeatedly scan forwards through the vector, in "upper triangular
  // matrix" style.  For each scan, remember the "current loop".  Initially
  // the "current loop is the start point of each scan.  If, during the scan,
  // we encounter a loop which is a superset of the "current loop", change the
  // "current loop" to this new loop, and increment a counter associated with
  // the start point of the scan.  The effect is that the counter records the
  // nesting depth of the loop at the start of the scan.  For this to be
  // completely accurate, I _think_ this requires the property that loops are
  // either disjoint or nested, but are in no case intersecting.

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

  // Now that we have a depth for each loop, we can finally compute the depth
  // for each block.
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

  let mut n = 0;
  debug!("");
  for (depth, dom_by) in depth_map.iter().zip(dom_map.iter()) {
    debug!(
      "{:<3?}   depth {}   dom_by {:<16?}",
      BlockIx::new(n),
      depth,
      dom_by
    );
    n += 1;
  }

  info!("      calc_loop_depths: end");
  depth_map
}

//=============================================================================
// Control-flow analysis top level: For a Func: predecessors, successors,
// preord and postord sequences, and loop depths.

// CFGInfo contains CFG-related info computed from a Func.
struct CFGInfo {
  // All these TypedIxVecs and plain Vecs contain one element per Block in the
  // Func.

  // Predecessor and successor maps.
  pred_map: TypedIxVec<BlockIx, Set<BlockIx>>,
  succ_map: TypedIxVec<BlockIx, Set<BlockIx>>,

  // Pre- and post-order sequences.  Iterating forwards through these
  // vectors enumerates the blocks in preorder and postorder respectively.
  pre_ord: Vec<BlockIx>,
  _post_ord: Vec<BlockIx>,

  // This maps from a Block to the loop depth that it is at
  depth_map: TypedIxVec<BlockIx, u32>,
}

impl CFGInfo {
  #[inline(never)]
  fn create<F: Function>(func: &F) -> Result<Self, AnalysisError> {
    info!("    CFGInfo::create: begin");

    // Throw out insanely large inputs.  They'll probably cause failure later
    // on.
    let nBlocksUSize = func.blocks().len();
    if nBlocksUSize >= 1 * 1024 * 1024 {
      // 1 million blocks should be enough for anyone.  That will soak up 20
      // index bits, leaving a "safety margin" of 12 bits for indices for
      // induced structures (RangeFragIx, InstIx, VirtualRangeIx, RealRangeIx,
      // etc).
      return Err(AnalysisError::ImplementationLimitsExceeded);
    }
    // Similarly, limit the number of instructions to 16 million.  This allows
    // 16 insns per block with the worst-case number of blocks.  Because each
    // insn typically generates somewhat less than one new value, this check
    // also has the effect of limiting the number of virtual registers to
    // roughly the same amount (16 million).
    if func.insns().len() >= 16 * 1024 * 1024 {
      return Err(AnalysisError::ImplementationLimitsExceeded);
    }

    // Now we know we're safe to narrow it to u32.
    let nBlocks = func.blocks().len() as u32;

    // === BEGIN compute successor and predecessor maps ===
    //
    let (pred_map, succ_map) = calc_preds_and_succs(func, nBlocks);
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
    let (pre_ord, post_ord) = calc_preord_and_postord(func, nBlocks, &succ_map);
    assert!(pre_ord.len() == nBlocks as usize);
    assert!(post_ord.len() == nBlocks as usize);
    //
    // === END compute preord/postord sequences ===

    // sewardj 2020Mar19: if we do have to reinstate this, which I hope we
    // don't, at least redo it to use a Vec::<bool> rather than a HashSet.
    //
    // Check that all blocks are reachable.
    //{
    //  let mut visited_blocks = HashSet::default();
    //  let mut stack = vec![func.entry_block()];
    //  while let Some(block) = stack.pop() {
    //    if !visited_blocks.contains(&block) {
    //      visited_blocks.insert(block);
    //
    //      use std::iter::FromIterator;
    //      let mut succ = Vec::from_iter(succ_map[block].iter().cloned());
    //
    //      stack.append(&mut succ);
    //    }
    //  }
    //
    //  // cfallin 2020-03-12: disable this check -- we want to do the right
    //  // thing in regalloc in the case of dead blocks, rather than error
    //  // on them.
    //  if visited_blocks.len() as u32 != nBlocks {
    //    return Err(AnalysisError::UnreachableBlocks);
    //  }
    //}

    // === BEGIN compute loop depth of all Blocks
    //
    let depth_map = calc_loop_depths(
      nBlocks,
      &pred_map,
      &succ_map,
      &post_ord,
      func.entry_block(),
    );
    debug_assert!(depth_map.len() == nBlocks);
    //
    // === END compute loop depth of all Blocks

    info!("    CFGInfo::create: end");
    Ok(CFGInfo { pred_map, succ_map, pre_ord, _post_ord: post_ord, depth_map })
  }
}

//===========================================================================//
//                                                                           //
// DATA FLOW AND LIVENESS ANALYSIS                                           //
//                                                                           //
//===========================================================================//

//=============================================================================
// Extraction and sanitization of reg-use information.
//
// This calls the client's |get_regs| function on each instruction, then
// "sanitizes" the sets.  See definition of |SanitizedInstRegUses| for meaning
// of "sanitized".

#[inline(never)]
fn get_sanitized_reg_uses<F: Function>(
  func: &F, reg_universe: &RealRegUniverse, sanitize_scratch: bool,
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

  for inst in func.insns() {
    let iru = func.get_regs(inst); // AUDITED
    let mut sru =
      SanitizedInstRegUses::create_by_sanitizing(&iru, reg_universe)?;
    sru.san_defined.remove(&scratch_set);
    san_reg_uses.push(sru);
  }
  Ok(san_reg_uses)
}

//=============================================================================
// Data flow analysis: calculation of per-block register def and use sets

// Returned TypedIxVecs contain one element per block
#[inline(never)]
fn calc_def_and_use<F: Function>(
  func: &F, san_reg_uses: &TypedIxVec<InstIx, SanitizedInstRegUses>,
) -> (TypedIxVec<BlockIx, Set<Reg>>, TypedIxVec<BlockIx, Set<Reg>>) {
  info!("    calc_def_and_use: begin");
  let mut def_sets = TypedIxVec::new();
  let mut use_sets = TypedIxVec::new();
  for b in func.blocks() {
    let mut def = Set::empty();
    let mut uce = Set::empty();
    for iix in func.block_insns(b) {
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

  assert!(def_sets.len() == use_sets.len());

  let mut n = 0;
  debug!("");
  for (def, uce) in def_sets.iter().zip(use_sets.iter()) {
    debug!("{:<3?}   def {:<16?}  use {:?}", BlockIx::new(n), def, uce);
    n += 1;
  }

  info!("    calc_def_and_use: end");
  (def_sets, use_sets)
}

//=============================================================================
// Data flow analysis: computation of per-block register live-in and live-out
// sets

// Returned vectors contain one element per block
#[inline(never)]
fn calc_livein_and_liveout<F: Function>(
  func: &F, def_sets_per_block: &TypedIxVec<BlockIx, Set<Reg>>,
  use_sets_per_block: &TypedIxVec<BlockIx, Set<Reg>>, cfg_info: &CFGInfo,
) -> (TypedIxVec<BlockIx, Set<Reg>>, TypedIxVec<BlockIx, Set<Reg>>) {
  info!("    calc_livein_and_liveout: begin");
  let nBlocks = func.blocks().len() as u32;
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

  // inQ is an optimisation -- this routine works fine without it.  inQ is
  // used to avoid inserting duplicate work items in workQ.  This avoids some
  // number of duplicate re-evaluations and gets us to a fixed point faster.
  // Very roughly, it reduces the number of evaluations per block from around
  // 3 to around 2.
  let mut inQ = Vec::<bool>::new();
  inQ.resize(nBlocks as usize, true);

  while let Some(bixI) = workQ.pop_front() {
    let i = bixI.get() as usize;
    assert!(inQ[i]);
    inQ[i] = false;

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
        let j = bixJ.get() as usize;
        if !inQ[j] {
          workQ.push_back(*bixJ);
          inQ[j] = true;
        }
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

  let ratio: f32 =
    (nEvals as f32) / ((if nBlocks == 0 { 1 } else { nBlocks }) as f32);
  info!(
    "    calc_livein_and_liveout:   {} blocks, {} evals ({:<.2} per block)",
    nBlocks, nEvals, ratio
  );

  let mut n = 0;
  debug!("");
  for (livein, liveout) in liveins.iter().zip(liveouts.iter()) {
    debug!(
      "{:<3?}   livein {:<16?}  liveout {:<16?}",
      BlockIx::new(n),
      livein,
      liveout
    );
    n += 1;
  }

  info!("    calc_livein_and_liveout: end");
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
#[inline(never)]
fn get_RangeFrags_for_block<F: Function>(
  func: &F, bix: BlockIx, livein: &Set<Reg>, liveout: &Set<Reg>,
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
  debug_assert!(func.block_insns(bix).len() >= 1);
  let first_iix_in_block = func.block_insns(bix).first();
  let last_iix_in_block = func.block_insns(bix).last();
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
  for iix in func.block_insns(bix) {
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
          let frag = RangeFrag::new(func, bix, *first, *last, *uses);
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
        let frag = RangeFrag::new(func, bix, *first, last_pt_in_block, *uses);
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
    let frag = RangeFrag::new(func, bix, pf.first, pf.last, pf.uses);
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
  func: &F, livein_sets_per_block: &TypedIxVec<BlockIx, Set<Reg>>,
  liveout_sets_per_block: &TypedIxVec<BlockIx, Set<Reg>>,
  san_reg_uses: &TypedIxVec<InstIx, SanitizedInstRegUses>,
) -> (Map<Reg, Vec<RangeFragIx>>, TypedIxVec<RangeFragIx, RangeFrag>) {
  info!("    get_RangeFrags: begin");
  debug_assert!(livein_sets_per_block.len() == func.blocks().len() as u32);
  debug_assert!(liveout_sets_per_block.len() == func.blocks().len() as u32);
  let mut resMap = Map::<Reg, Vec<RangeFragIx>>::default();
  let mut resFEnv = TypedIxVec::<RangeFragIx, RangeFrag>::new();
  for bix in func.blocks() {
    get_RangeFrags_for_block(
      func,
      bix,
      &livein_sets_per_block[bix],
      &liveout_sets_per_block[bix],
      &san_reg_uses,
      &mut resMap,
      &mut resFEnv,
    );
  }

  debug!("");
  let mut n = 0;
  for frag in resFEnv.iter() {
    debug!("{:<3?}   {:?}", RangeFragIx::new(n), frag);
    n += 1;
  }

  debug!("");
  for (reg, frag_ixs) in resMap.iter() {
    debug!("frags for {:?}   {:?}", reg, frag_ixs);
  }

  info!("    get_RangeFrags: end");
  (resMap, resFEnv)
}

//=============================================================================
// Merging of RangeFrags, producing the final LRs, minus metrics
// (SLOW reference implementation)

#[inline(never)]
fn merge_RangeFrags_SLOW(
  fragIx_vecs_per_reg: &Map<Reg, Vec<RangeFragIx>>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>, cfg_info: &CFGInfo,
) -> (
  TypedIxVec<RealRangeIx, RealRange>,
  TypedIxVec<VirtualRangeIx, VirtualRange>,
) {
  let mut n_total_incoming_frags = 0;
  for (_reg, all_frag_ixs_for_reg) in fragIx_vecs_per_reg.iter() {
    n_total_incoming_frags += all_frag_ixs_for_reg.len();
  }
  info!("      merge_RangeFrags_SLOW: begin");
  info!("        in: {} in frag_env", frag_env.len());
  info!(
    "        in: {} regs containing in total {} frags",
    fragIx_vecs_per_reg.len(),
    n_total_incoming_frags
  );

  let mut resR = TypedIxVec::<RealRangeIx, RealRange>::new();
  let mut resV = TypedIxVec::<VirtualRangeIx, VirtualRange>::new();
  for (reg, all_frag_ixs_for_reg) in fragIx_vecs_per_reg.iter() {
    let n_for_this_reg = all_frag_ixs_for_reg.len();
    assert!(n_for_this_reg > 0);

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

  info!("        out: {} VLRs, {} RLRs", resV.len(), resR.len());
  info!("      merge_RangeFrags_SLOW: end");
  (resR, resV)
}

//=============================================================================
// Merging of RangeFrags, producing the final LRs, minus metrics

// HELPER FUNCTION
fn create_and_add_Range(
  resR: &mut TypedIxVec<RealRangeIx, RealRange>,
  resV: &mut TypedIxVec<VirtualRangeIx, VirtualRange>, reg: Reg,
  sorted_frags: SortedRangeFragIxs,
) {
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

// We need this in order to construct a UnionFind<usize>.
impl ToFromU32 for usize {
  // 64 bit
  #[cfg(target_pointer_width = "64")]
  fn to_u32(x: usize) -> u32 {
    if x < 0x1_0000_0000usize {
      x as u32
    } else {
      panic!("impl ToFromU32 for usize: to_u32: out of range")
    }
  }
  #[cfg(target_pointer_width = "64")]
  fn from_u32(x: u32) -> usize {
    x as usize
  }
  // 32 bit
  #[cfg(target_pointer_width = "32")]
  fn to_u32(x: usize) -> u32 {
    x as u32
  }
  #[cfg(target_pointer_width = "32")]
  fn from_u32(x: u32) -> usize {
    x as usize
  }
}

#[inline(never)]
fn merge_RangeFrags(
  fragIx_vecs_per_reg: &Map<Reg, Vec<RangeFragIx>>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>, cfg_info: &CFGInfo,
) -> (
  TypedIxVec<RealRangeIx, RealRange>,
  TypedIxVec<VirtualRangeIx, VirtualRange>,
) {
  let mut n_total_incoming_frags = 0;
  for (_reg, all_frag_ixs_for_reg) in fragIx_vecs_per_reg.iter() {
    n_total_incoming_frags += all_frag_ixs_for_reg.len();
  }
  info!("    merge_RangeFrags: begin");
  info!("      in: {} in frag_env", frag_env.len());
  info!(
    "      in: {} regs containing in total {} frags",
    fragIx_vecs_per_reg.len(),
    n_total_incoming_frags
  );

  let mut n_single_grps = 0;
  let mut n_local_frags = 0;

  let mut n_multi_grps_small = 0;
  let mut n_multi_grps_large = 0;
  let mut sz_multi_grps_small = 0;
  let mut sz_multi_grps_large = 0;

  let mut resR = TypedIxVec::<RealRangeIx, RealRange>::new();
  let mut resV = TypedIxVec::<VirtualRangeIx, VirtualRange>::new();

  // BEGIN per_reg_loop
  'per_reg_loop: for (reg, all_frag_ixs_for_reg) in fragIx_vecs_per_reg.iter() {
    let n_frags_for_this_reg = all_frag_ixs_for_reg.len();
    assert!(n_frags_for_this_reg > 0);

    // Do some shortcutting.  First off, if there's only one frag for this
    // reg, we can directly give it its own live range, and have done.
    if n_frags_for_this_reg == 1 {
      create_and_add_Range(
        &mut resR,
        &mut resV,
        *reg,
        SortedRangeFragIxs::unit(all_frag_ixs_for_reg[0], frag_env),
      );
      n_single_grps += 1;
      continue 'per_reg_loop;
    }

    // BEGIN merge |all_frag_ixs_for_reg| entries as much as possible.
    //
    // but .. if we come across independents (RangeKind::Local), pull them out
    // immediately.

    let mut triples = Vec::<(RangeFragIx, RangeFragKind, BlockIx)>::new();

    // Create |triples|.  We will use it to guide the merging phase, but it is
    // immutable there.
    'per_frag_loop: for fix in all_frag_ixs_for_reg {
      let frag = &frag_env[*fix];
      // This frag is Local (standalone).  Give it its own Range and move on.
      // This is an optimisation, but it's also necessary: the main
      // fragment-merging logic below relies on the fact that the
      // fragments it is presented with are all either LiveIn, LiveOut or
      // Thru.
      if frag.kind == RangeFragKind::Local {
        create_and_add_Range(
          &mut resR,
          &mut resV,
          *reg,
          SortedRangeFragIxs::unit(*fix, frag_env),
        );
        n_local_frags += 1;
        continue 'per_frag_loop;
      }
      // This frag isn't Local (standalone) so we have process it the slow way.
      assert!(frag.kind != RangeFragKind::Local);
      triples.push((*fix, frag.kind, frag.bix));
    }

    let triples_len = triples.len();

    // This is the core of the merging algorithm.
    //
    // For each ix@(fix, kind, bix) in |triples| (order unimportant):
    //
    // (1) "Merge with blocks that are live 'downstream' from here":
    //     if fix is live-out or live-through:
    //        for b in succs[bix]
    //           for each ix2@(fix2, kind2, bix2) in |triples|
    //              if bix2 == b && kind2 is live-in or live-through:
    //                  merge(ix, ix2)
    //
    // (2) "Merge with blocks that are live 'upstream' from here":
    //     if fix is live-in or live-through:
    //        for b in preds[bix]
    //           for each ix2@(fix2, kind2, bix2) in |triples|
    //              if bix2 == b && kind2 is live-out or live-through:
    //                  merge(ix, ix2)
    //
    // |triples| remains unchanged.  The equivalence class info is accumulated
    // in |eclasses_uf| instead.  |eclasses_uf| entries are indices into
    // |triples|.
    //
    // Now, you might think it necessary to do both (1) and (2).  But no, they
    // are mutually redundant, since if two blocks are connected by a live
    // flow from one to the other, then they are also connected in the other
    // direction.  Hence checking one of the directions is enough.
    let mut eclasses_uf = UnionFind::<usize>::new(triples_len);

    // We have two schemes for group merging, one of which is N^2 in the
    // length of triples, the other is N-log-N, but with higher constant
    // factors.  Some experimentation with the bz2 test on a Cortex A57 puts
    // the optimal crossover point between 200 and 300; it's not critical.
    // Having this protects us against bad behaviour for huge inputs whilst
    // still being fast for small inputs.
    if triples_len <= 250 {
      // The simple way, which is N^2 in the length of |triples|.
      for ((_fix, kind, bix), ix) in triples.iter().zip(0..) {
        // Deal with liveness flows outbound from |fix|.  Meaning, (1) above.
        if *kind == RangeFragKind::LiveOut || *kind == RangeFragKind::Thru {
          for b in cfg_info.succ_map[*bix].iter() {
            // Visit all entries in |triples| that are for |b|
            for ((_fix2, kind2, bix2), ix2) in triples.iter().zip(0..) {
              if *bix2 != *b || *kind2 == RangeFragKind::LiveOut {
                continue;
              }
              // Now we know that liveness for this reg "flows" from
              // |triples[ix]| to |triples[ix2]|.  So those two frags must be
              // part of the same live range.  Note this.
              debug_assert!(ix != ix2);
              eclasses_uf.union(ix, ix2); // Order of args irrelevant
            }
          }
        }
      } // outermost iteration over |triples|
      n_multi_grps_small += 1;
      sz_multi_grps_small += triples_len;
    } else {
      // The more complex way, which is N-log-N in the length of |triples|.
      // This is the same as the simple way, except that the innermost loop,
      // which is a linear search in |triples| to find entries for some block
      // |b|, is replaced by a binary search.  This means that |triples| first
      // needs to be sorted by block index.
      triples.sort_unstable_by(|(_, _, bix1), (_, _, bix2)| {
        bix1.partial_cmp(bix2).unwrap()
      });
      for ((_fix, kind, bix), ix) in triples.iter().zip(0..) {
        // Deal with liveness flows outbound from |fix|.  Meaning, (1) above.
        if *kind == RangeFragKind::LiveOut || *kind == RangeFragKind::Thru {
          for b in cfg_info.succ_map[*bix].iter() {
            //println!("QQQ looking for {:?}", b);
            // Visit all entries in |triples| that are for |b|.  Binary search
            // |triples| to find the lowest-indexed entry for |b|.
            let mut ixL = 0;
            let mut ixR = triples_len;
            while ixL < ixR {
              let m = (ixL + ixR) >> 1;
              if triples[m].2 < *b {
                ixL = m + 1;
              } else {
                ixR = m;
              }
            }
            // It might be that there is no block for |b| in the sequence.
            // That's legit; it just means that block |bix| jumps to a
            // successor where the associated register isn't live-in/thru.  A
            // failure to find |b| can be indicated one of two ways:
            //
            // * ixL == triples_len
            // * ixL < triples_len and b < triples[ixL].b
            //
            // In both cases I *think* the 'loop_over_entries_for_b below will
            // not do anything.  But this is all a bit hairy, so let's convert
            // the second variant into the first, so as to make it obvious
            // that the loop won't do anything.

            // ixL now holds the lowest index of any |triples| entry for block
            // |b|.  Assert this.
            if ixL < triples_len && *b < triples[ixL].2 {
              ixL = triples_len;
            }
            if ixL < triples_len {
              assert!(ixL == 0 || triples[ixL - 1].2 < *b);
            }
            // ix2 plays the same role as in the quadratic version.  ixL and
            // ixR are not used after this point.
            let mut ix2 = ixL;
            'loop_over_entries_for_b: loop {
              if ix2 >= triples_len {
                break;
              }
              let (_fix2, kind2, bix2) = triples[ix2];
              if *b < bix2 {
                // We've come to the end of the sequence of |b|-blocks.
                break;
              }
              debug_assert!(*b == bix2);
              if kind2 == RangeFragKind::LiveOut {
                ix2 += 1;
                continue 'loop_over_entries_for_b;
              }
              // Now we know that liveness for this reg "flows" from
              // |triples[ix]| to |triples[ix2]|.  So those two frags must be
              // part of the same live range.  Note this.
              if ix != ix2 {
                eclasses_uf.union(ix, ix2); // Order of args irrelevant
              }
              ix2 += 1;
            }
            if ix2 + 1 < triples_len {
              debug_assert!(*b < triples[ix2 + 1].2);
            }
          }
        }
      }
      n_multi_grps_large += 1;
      sz_multi_grps_large += triples_len;
    }

    // Now |eclasses_uf| contains the results of the merging-search.  Visit
    // each of its equivalence classes in turn, and convert each into a
    // virtual or real live range as appropriate.
    let eclasses = eclasses_uf.get_equiv_classes();
    for leader_triple_ix in eclasses.equiv_class_leaders_iter() {
      // |leader_triple_ix| is an eclass leader.  Enumerate the whole eclass.
      let mut frag_ixs = Vec::<RangeFragIx>::new();
      for triple_ix in eclasses.equiv_class_elems_iter(leader_triple_ix) {
        frag_ixs.push(triples[triple_ix].0 /*first field is frag ix*/);
      }
      let sorted_frags = SortedRangeFragIxs::new(&frag_ixs.to_vec(), &frag_env);
      create_and_add_Range(&mut resR, &mut resV, *reg, sorted_frags);
    }
    // END merge |all_frag_ixs_for_reg| entries as much as possible
  } // 'per_reg_loop
    // END per_reg_loop

  info!("      in: {} single groups", n_single_grps);
  info!("      in: {} local frags in multi groups", n_local_frags);
  info!(
    "      in: {} small multi groups, {} small multi group total size",
    n_multi_grps_small, sz_multi_grps_small
  );
  info!(
    "      in: {} large multi groups, {} large multi group total size",
    n_multi_grps_large, sz_multi_grps_large
  );
  info!("      out: {} VLRs, {} RLRs", resV.len(), resR.len());
  info!("    merge_RangeFrags: end");

  if CROSSCHECK_MERGE {
    info!("    merge_RangeFrags: crosscheck: begin");
    let (resRref, resVref) =
      merge_RangeFrags_SLOW(fragIx_vecs_per_reg, frag_env, cfg_info);
    assert!(resR.len() == resRref.len());
    assert!(resV.len() == resVref.len());

    // We need to check that resR comprises an identical set of RealRanges to
    // resRref.  Problem is they are presented in some arbitrary order.  Hence
    // we need to sort both, per some arbitrary total order, before comparing.
    let mut resRc = resR.clone();
    let mut resRrefc = resRref.clone();
    resRc.sort_by(|x, y| RealRange::cmp_debug_only(x, y));
    resRrefc.sort_by(|x, y| RealRange::cmp_debug_only(x, y));
    for i in 0..resR.len() {
      let rlrix = RealRangeIx::new(i);
      assert!(resRc[rlrix].rreg == resRrefc[rlrix].rreg);
      assert!(
        resRc[rlrix].sorted_frags.frag_ixs
          == resRrefc[rlrix].sorted_frags.frag_ixs
      );
    }
    // Same deal for the VirtualRanges.
    let mut resVc = resV.clone();
    let mut resVrefc = resVref.clone();
    resVc.sort_by(|x, y| VirtualRange::cmp_debug_only(x, y));
    resVrefc.sort_by(|x, y| VirtualRange::cmp_debug_only(x, y));
    for i in 0..resV.len() {
      let vlrix = VirtualRangeIx::new(i);
      assert!(resVc[vlrix].vreg == resVrefc[vlrix].vreg);
      assert!(resVc[vlrix].rreg == resVrefc[vlrix].rreg);
      assert!(
        resVc[vlrix].sorted_frags.frag_ixs
          == resVrefc[vlrix].sorted_frags.frag_ixs
      );
      assert!(resVc[vlrix].size == resVrefc[vlrix].size);
      assert!(resVc[vlrix].spill_cost.is_zero());
      assert!(resVrefc[vlrix].spill_cost.is_zero());
    }
    info!("    merge_RangeFrags: crosscheck: end");
  }

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
  info!("    set_VirtualRange_metrics: begin");
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
  info!("    set_VirtualRange_metrics: end");
}

//=============================================================================
// Top level for all analysis activities.

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
  info!("run_analysis: begin");
  info!(
    "  run_analysis: {} blocks, {} insns",
    func.blocks().len(),
    func.insns().len()
  );
  info!("  run_analysis: begin control flow analysis");

  // First do control flow analysis.  This is (relatively) simple.  Note that
  // this can fail, for various reasons; we propagate the failure if so.
  let cfg_info = CFGInfo::create(func)?;

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

  info!("  run_analysis: end control flow analysis");

  // Now perform dataflow analysis.  This is somewhat more complex.
  info!("  run_analysis: begin data flow analysis");

  // See |get_sanitized_reg_uses| for the meaning of "sanitized".
  let san_reg_uses =
    get_sanitized_reg_uses(func, reg_universe, sanitize_scratch)
      .map_err(|reg| AnalysisError::NonExistingRealReg(reg))?;

  // Calculate block-local def/use sets.
  let (def_sets_per_block, use_sets_per_block) =
    calc_def_and_use(func, &san_reg_uses);
  debug_assert!(def_sets_per_block.len() == func.blocks().len() as u32);
  debug_assert!(use_sets_per_block.len() == func.blocks().len() as u32);

  // Calculate live-in and live-out sets per block, using the traditional
  // iterate-to-a-fixed-point scheme.

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

  info!("  run_analysis: end data flow analysis");

  // Dataflow analysis is now complete.  Now compute the virtual and real live
  // ranges, in two steps: (1) compute RangeFrags, and (2) merge them
  // together, guided by flow and liveness info, so as to create the final
  // VirtualRanges and RealRanges.
  info!("  run_analysis: begin liveness analysis");

  let (frag_ixs_per_reg, frag_env) = get_RangeFrags(
    func,
    &livein_sets_per_block,
    &liveout_sets_per_block,
    &san_reg_uses,
  );

  let (rlr_env, mut vlr_env) =
    merge_RangeFrags(&frag_ixs_per_reg, &frag_env, &cfg_info);

  set_VirtualRange_metrics(&mut vlr_env, &frag_env, &estFreqs);

  debug_assert!(liveout_sets_per_block.len() == estFreqs.len());

  debug!("");
  let mut n = 0;
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

  info!("  run_analysis: end liveness analysis");
  info!("run_analysis: end");

  Ok((
    san_reg_uses,
    rlr_env,
    vlr_env,
    frag_env,
    liveout_sets_per_block,
    estFreqs,
  ))
}
