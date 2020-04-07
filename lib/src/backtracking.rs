/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

//! Core implementation of the backtracking allocator.

use log::{debug, info, log_enabled, Level};
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::fmt;

use crate::analysis::{does_inst_use_def_or_mod_reg, run_analysis};
use crate::avl_tree::{AVLTag, AVLTree, AVL_NULL};
use crate::data_structures::{
  cmp_range_frags, BlockIx, InstIx, InstPoint, Point, RangeFrag, RangeFragIx,
  RangeFragKind, RealRange, RealRangeIx, RealReg, RealRegUniverse, Reg,
  RegVecsAndBounds, Set, SortedRangeFragIxs, SpillCost, SpillSlot, TypedIxVec,
  VirtualRange, VirtualRangeIx, VirtualReg, Writable,
};
use crate::inst_stream::{
  edit_inst_stream, InstAndPoint, InstToInsert, InstsAndPoints,
  RangeAllocations,
};
use crate::interface::{Function, RegAllocError, RegAllocResult};
use crate::trees_maps_sets::{ToFromU32, UnionFind, UnionFindEquivClasses};

// DEBUGGING: set to true to cross-check the CommitmentMap machinery.

const CROSSCHECK_CM: bool = false;

//=============================================================================
// A spill slot allocator.  This could be implemented more simply than it is.
// The reason for the extra complexity is to support copy-coalescing at the
// spill-slot level.  That is, it tries make it possible to allocate all
// members of a VirtualRange group to the same spill slot, so that moves
// between two spilled members of the same group can be turned into no-ops.
//
// All of the |size| metrics in this bit are in terms of "logical spill slot
// units", per the interface's description for |get_spillslot_size|.

// We keep one of these for every "logical spill slot" in use.
enum LogicalSpillSlot {
  // This slot is in use and can hold values of size |size| (only).  Note that
  // |InUse| may only appear in |SpillSlotAllocator::slots| positions that
  // have indices that are 0 % |size|.  Furthermore, after such an entry in
  // |SpillSlotAllocator::slots|, the next |size| - 1 entries must be
  // |Unavail|.  This is a hard invariant, violation of which will cause
  // overlapping spill slots and potential chaos.
  InUse { size: u32, tree: AVLTree<RangeFragIx> },
  // This slot is unavailable, as described above.  It's unavailable because
  // it holds some part of the values associated with the nearest lower
  // numbered entry which isn't |Unavail|, and that entry must be an |InUse|
  // entry.
  Unavail,
}
impl LogicalSpillSlot {
  fn is_Unavail(&self) -> bool {
    match self {
      LogicalSpillSlot::Unavail => true,
      _ => false,
    }
  }
  fn is_InUse(&self) -> bool {
    !self.is_Unavail()
  }
  fn get_tree(&self) -> &AVLTree<RangeFragIx> {
    match self {
      LogicalSpillSlot::InUse { ref tree, .. } => tree,
      LogicalSpillSlot::Unavail => panic!("LogicalSpillSlot::get_tree"),
    }
  }
  fn get_mut_tree(&mut self) -> &mut AVLTree<RangeFragIx> {
    match self {
      LogicalSpillSlot::InUse { ref mut tree, .. } => tree,
      LogicalSpillSlot::Unavail => panic!("LogicalSpillSlot::get_mut_tree"),
    }
  }
  fn get_size(&self) -> u32 {
    match self {
      LogicalSpillSlot::InUse { size, .. } => *size,
      LogicalSpillSlot::Unavail => panic!("LogicalSpillSlot::get_size"),
    }
  }
}

// HELPER FUNCTION
// The custom comparator
fn cmp_tree_entries_for_SpillSlotAllocator(
  fix1: RangeFragIx, fix2: RangeFragIx,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
) -> Option<Ordering> {
  cmp_range_frags(&frag_env[fix1], &frag_env[fix2])
}

// HELPER FUNCTION
// Find out whether it is possible to add all of |frags| to |tree|.  Returns
// true if possible, false if not.  This routine relies on the fact that
// SortedFrags is non-overlapping.  However, this is a bit subtle.  We know
// that both |tree| and |frags| individually are non-overlapping, but there's
// no guarantee that elements of |frags| don't overlap |tree|.  Hence we have
// to do a custom walk of |tree| to check for overlap; we can't just use
// |AVLTree::contains|.
fn ssal_is_add_possible(
  tree: &AVLTree<RangeFragIx>, frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  frags: &SortedRangeFragIxs,
) -> bool {
  // Figure out whether all the frags will go in.
  for fix in &frags.frag_ixs {
    // BEGIN check |fix| for any overlap against |tree|.
    let frag = &frag_env[*fix];
    let mut root = tree.root;
    while root != AVL_NULL {
      let root_node = &tree.pool[root as usize];
      let root_fix = root_node.item;
      let root_frag = &frag_env[root_fix];
      if frag.last < root_frag.first {
        // |frag| is entirely to the left of the |root|.  So there's no
        // overlap with root.  Continue by inspecting the left subtree.
        root = root_node.left;
      } else if root_frag.last < frag.first {
        // Ditto for the right subtree.
        root = root_node.right;
      } else {
        // |frag| overlaps the |root|.  Give up.
        return false;
      }
    }
    // END check |fix| for any overlap against |tree|.
    // |fix| doesn't overlap.  Move on to the next one.
  }
  true
}

// HELPER FUNCTION
// Try to add all of |frags| to |tree|.  Return |true| if possible, |false| if
// not possible.  If |false| is returned, |tree| is unchanged (this is
// important).  This routine relies on the fact that SortedFrags is
// non-overlapping.
fn ssal_add_if_possible(
  tree: &mut AVLTree<RangeFragIx>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>, frags: &SortedRangeFragIxs,
) -> bool {
  // Check if all the frags will go in.
  if !ssal_is_add_possible(tree, frag_env, frags) {
    return false;
  }
  // They will.  So now insert them.
  for fix in &frags.frag_ixs {
    let inserted = tree.insert(
      *fix,
      Some(&|fix1, fix2| {
        cmp_tree_entries_for_SpillSlotAllocator(fix1, fix2, frag_env)
      }),
    );
    // This can't fail
    assert!(inserted);
  }
  true
}

struct SpillSlotAllocator {
  slots: Vec<LogicalSpillSlot>,
}
impl SpillSlotAllocator {
  fn new() -> Self {
    Self { slots: vec![] }
  }

  // This adds a new, empty slot, for items of the given size, and returns its
  // index.  This isn't clever, in the sense that it fails to use some slots
  // that it could use, but at least it's simple.
  fn add_new_slot(&mut self, req_size: u32) -> u32 {
    assert!(req_size == 1 || req_size == 2 || req_size == 4 || req_size == 8);
    // Satisfy alignment constraints.  These entries will unfortunately be
    // wasted (never used).
    while self.slots.len() % (req_size as usize) != 0 {
      self.slots.push(LogicalSpillSlot::Unavail);
    }
    // And now the new slot.
    let dflt = RangeFragIx::new(0xFFFF_FFFF); // value is unimportant
    let tree = AVLTree::<RangeFragIx>::new(dflt);
    let res = self.slots.len() as u32;
    self.slots.push(LogicalSpillSlot::InUse { size: req_size, tree });
    // And now "block out subsequent slots that |req_size| implies.
    // viz: req_size == 1  ->  block out 0 more
    // viz: req_size == 2  ->  block out 1 more
    // viz: req_size == 4  ->  block out 3 more
    // viz: req_size == 8  ->  block out 7 more
    for _ in 1..req_size {
      self.slots.push(LogicalSpillSlot::Unavail);
    }
    assert!(self.slots.len() % (req_size as usize) == 0);
    //println!("QQQQ   add_new_slot {} for size {}", res, req_size);
    res
  }

  // Allocate spill slots for all the VirtualRanges in |vlrix|s eclass,
  // including |vlrix| itself.  Since we are allocating spill slots for
  // complete eclasses at once, none of the members of the class should
  // currently have any allocation.  This routine will try to allocate all
  // class members the same slot, but it can only guarantee to do so if the
  // class members are mutually non-overlapping.  Hence it can't guarantee that
  // in general.
  fn alloc_spill_slots<F: Function>(
    &mut self,
    vlr_slot_env: &mut TypedIxVec<VirtualRangeIx, Option<SpillSlot>>, func: &F,
    frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
    vlrEquivClasses: &UnionFindEquivClasses<VirtualRangeIx>,
    vlrix: VirtualRangeIx,
  ) {
    //println!("QQQQ alloc_spill_slots: BEGIN");
    for cand_vlrix in vlrEquivClasses.equiv_class_elems_iter(vlrix) {
      assert!(vlr_slot_env[cand_vlrix].is_none());
    }
    // Do this in two passes.  It's a bit cumbersome.
    //
    // In the first pass, find a spill slot which can take all of the
    // candidates when we try them *individually*, but don't update the tree
    // yet.  We will always find such a slot, because if none of the existing
    // slots can do it, we can always start a new one.
    //
    // Now, that doesn't guarantee that all the candidates can *together* can
    // be assigned to the chosen slot.  That's only possible when they are
    // non-overlapping.  Rather than laboriously try to determine that, simply
    // proceed with the second pass, the assignment pass, as follows.  For
    // each candidate, try to allocate it to our chosen slot.  If it goes in
    // without interference, fine.  If not, that means it overlaps with some
    // other member of the class -- in which case we must find some other slot
    // for it.  It's too bad.
    //
    // The result is: all members will get a valid spill slot.  And if they
    // were all non overlapping then we are guaranteed that they all get the
    // same slot.  Which is as good as we can hope for.

    // We need to know what regclass, and hence what slot size, we're looking
    // for.  Just look at the representative; all VirtualRanges in the eclass
    // must have the same regclass.  (If they don't, the client's is_move
    // function has been giving us wrong information.)
    let vlrix_vreg = vlr_env[vlrix].vreg;
    let req_size = func.get_spillslot_size(vlrix_vreg.get_class(), vlrix_vreg);
    assert!(req_size == 1 || req_size == 2 || req_size == 4 || req_size == 8);

    // Pass 1: find a slot which can take VirtualRange when tested
    // individually.
    //
    // 1a: search existing slots
    let mut mb_chosen_slotno: Option<u32> = None;
    'pass1_search_existing_slots: for cand_slot_no in 0..self.slots.len() as u32
    {
      let cand_slot = &self.slots[cand_slot_no as usize];
      if !cand_slot.is_InUse() {
        continue 'pass1_search_existing_slots;
      }
      if cand_slot.get_size() != req_size {
        continue 'pass1_search_existing_slots;
      }
      let tree = &cand_slot.get_tree();
      assert!(mb_chosen_slotno.is_none());

      // BEGIN see if |cand_slot| can hold all eclass members individually
      let mut all_cands_fit_individually = true;
      for cand_vlrix in vlrEquivClasses.equiv_class_elems_iter(vlrix) {
        let cand_vlr = &vlr_env[cand_vlrix];
        let this_cand_fits =
          ssal_is_add_possible(&tree, &frag_env, &cand_vlr.sorted_frags);
        if !this_cand_fits {
          all_cands_fit_individually = false;
          break;
        }
      }
      // END see if |cand_slot| can hold all eclass members individually
      if !all_cands_fit_individually {
        continue 'pass1_search_existing_slots;
      }

      // Ok.  All eclass members will fit individually in |cand_slot_no|.
      mb_chosen_slotno = Some(cand_slot_no);
      break;
    } /* 'pass1_search_existing_slots */
    // 1b. If we didn't find a usable slot, allocate a new one.
    let chosen_slotno: u32 = if mb_chosen_slotno.is_none() {
      //println!(
      //    "QQQQ   alloc_spill_slots: no existing slot works.  Alloc new.");
      self.add_new_slot(req_size)
    } else {
      //println!("QQQQ   alloc_spill_slots: use existing {} (for eclass)",
      //         mb_chosen_slotno.unwrap());
      mb_chosen_slotno.unwrap()
    };
    //println!("QQQQ   alloc_spill_slots: chosen = {}", chosen_slotno);

    // Pass 2.  Try to allocate each eclass member individually to the chosen
    // slot.  If that fails, just allocate them anywhere.
    let mut _all_in_chosen = true;
    'pass2_per_equiv_class: for cand_vlrix in
      vlrEquivClasses.equiv_class_elems_iter(vlrix)
    {
      let cand_vlr = &vlr_env[cand_vlrix];
      let mut tree = self.slots[chosen_slotno as usize].get_mut_tree();
      let added =
        ssal_add_if_possible(&mut tree, &frag_env, &cand_vlr.sorted_frags);
      if added {
        vlr_slot_env[cand_vlrix] = Some(SpillSlot::new(chosen_slotno));
        continue 'pass2_per_equiv_class;
      }
      // It won't fit in |chosen_slotno|, so try somewhere (anywhere) else.
      for alt_slotno in 0..self.slots.len() as u32 {
        let alt_slot = &self.slots[alt_slotno as usize];
        if !alt_slot.is_InUse() {
          continue;
        }
        if alt_slot.get_size() != req_size {
          continue;
        }
        if alt_slotno == chosen_slotno {
          // We already know this won't work.
          continue;
        }
        let mut tree = self.slots[alt_slotno as usize].get_mut_tree();
        let added =
          ssal_add_if_possible(&mut tree, &frag_env, &cand_vlr.sorted_frags);
        if added {
          vlr_slot_env[cand_vlrix] = Some(SpillSlot::new(alt_slotno));
          continue 'pass2_per_equiv_class;
        }
      }
      // If we get here, it means it won't fit in any slot we currently have.
      // So allocate a new one and use that.
      _all_in_chosen = false;
      let new_slotno = self.add_new_slot(req_size);
      let mut tree = self.slots[new_slotno as usize].get_mut_tree();
      let added =
        ssal_add_if_possible(&mut tree, &frag_env, &cand_vlr.sorted_frags);
      if added {
        vlr_slot_env[cand_vlrix] = Some(SpillSlot::new(new_slotno));
        continue 'pass2_per_equiv_class;
      }
      // We failed to allocate it to any empty slot!  This can't happen.
      panic!("SpillSlotAllocator: alloc_spill_slots: failed?!?!");
      /*NOTREACHED*/
    } /* 'pass2_per_equiv_class */

    for eclass_vlrix in vlrEquivClasses.equiv_class_elems_iter(vlrix) {
      assert!(vlr_slot_env[eclass_vlrix].is_some());
      debug!(
        "--     alloc_spill_sls  {:?} -> {:?}",
        eclass_vlrix,
        vlr_slot_env[eclass_vlrix].unwrap()
      );
    }
    //println!("QQQQ alloc_spill_slots: END, all in same = {}",
    //         if all_in_chosen { "YES" } else { "no" });
    //println!("QQQQ");
  }
}

//=============================================================================
// Analysis in support of copy coalescing.
//
// This detects and collects information about, all copy coalescing
// opportunities in the incoming function.  It does not use that information
// at all -- that is for the main allocation loop to do.

// A coalescing hint for a virtual live range.  The u32 is an arbitrary
// "weight" value which indicates a relative strength-of-preference for the
// hint.  It exists because a VLR can have arbitrarily many copy
// instructions at its "boundary", and hence arbitrarily many hints.  Of
// course the allocator core can honour at most one of them, so it needs a
// way to choose between them.  In this implementation, the u32s are simply
// the estimated execution count of the associated copy instruction.
#[derive(Clone)]
enum Hint {
  // I would like to have the same real register as some other virtual range.
  SameAs(VirtualRangeIx, u32),
  // I would like to have exactly this real register.
  Exactly(RealReg, u32),
}
fn show_hint(h: &Hint) -> String {
  match h {
    Hint::SameAs(vlrix, weight) => {
      format!("(SameAs {:?}, weight={})", vlrix, weight)
    }
    Hint::Exactly(rreg, weight) => {
      format!("(Exactly {:?}, weight={})", rreg, weight)
    }
  }
}
impl Hint {
  fn get_weight(&self) -> u32 {
    match self {
      Hint::SameAs(_vlrix, weight) => *weight,
      Hint::Exactly(_rreg, weight) => *weight,
    }
  }
}

// We need this in order to construct a UnionFind<VirtualRangeIx>.
impl ToFromU32 for VirtualRangeIx {
  fn to_u32(x: VirtualRangeIx) -> u32 {
    x.get()
  }
  fn from_u32(x: u32) -> VirtualRangeIx {
    VirtualRangeIx::new(x)
  }
}

#[inline(never)]
fn do_coalescing_analysis<F: Function>(
  func: &F, reg_vecs_and_bounds: &RegVecsAndBounds,
  rlr_env: &TypedIxVec<RealRangeIx, RealRange>,
  vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  est_freqs: &TypedIxVec<BlockIx, u32>,
) -> (
  TypedIxVec<VirtualRangeIx, Vec<Hint>>,
  UnionFindEquivClasses<VirtualRangeIx>,
  TypedIxVec<InstIx, bool>,
) {
  info!("");
  info!("do_coalescing_analysis: begin");
  // We have in hand the virtual live ranges.  Each of these carries its
  // associated vreg.  So in effect we have a VLR -> VReg mapping.  We now
  // invert that, so as to generate a mapping from VRegs to their containing
  // VLRs.
  //
  // Note that multiple VLRs may map to the same VReg.  So the inverse mapping
  // will actually be from VRegs to a set of VLRs.  In most cases, we expect
  // the virtual-registerised-code given to this allocator to be derived from
  // SSA, in which case each VReg will have only one VLR.  So in this case,
  // the cost of first creating the mapping, and then looking up all the VRegs
  // in moves in it, will have cost linear in the size of the input function.
  //
  // It would be convenient here to know how many VRegs there are ahead of
  // time, but until then we'll discover it dynamically.
  // NB re the SmallVec.  That has set semantics (no dups)
  // FIXME use SmallVec for the VirtualRangeIxs.  Or even a sparse set.
  let mut vreg_to_vlrs_map = Vec::</*vreg index,*/ Vec<VirtualRangeIx>>::new();

  for (vlr, n) in vlr_env.iter().zip(0..) {
    let vlrix = VirtualRangeIx::new(n);
    let vreg: VirtualReg = vlr.vreg;
    // Now we know that there's a VLR |vlr| that is for VReg |vreg|.  Update
    // the inverse mapping accordingly.  That may involve resizing it, since
    // we have no idea of the order in which we will first encounter VRegs.
    // By contrast, we know we are stepping sequentially through the VLR
    // (index) space, and we'll never see the same VLRIx twice.  So there's no
    // need to check for dups when adding a VLR index to an existing binding
    // for a VReg.
    let vreg_ix = vreg.get_index();

    while vreg_to_vlrs_map.len() <= vreg_ix {
      vreg_to_vlrs_map.push(vec![]); // This is very un-clever
    }

    vreg_to_vlrs_map[vreg_ix].push(vlrix);
  }

  // Same for the real live ranges
  let mut rreg_to_rlrs_map = Vec::</*rreg index,*/ Vec<RealRangeIx>>::new();

  for (rlr, n) in rlr_env.iter().zip(0..) {
    let rlrix = RealRangeIx::new(n);
    let rreg: RealReg = rlr.rreg;
    let rreg_ix = rreg.get_index();

    while rreg_to_rlrs_map.len() <= rreg_ix {
      rreg_to_rlrs_map.push(vec![]); // This is very un-clever
    }

    rreg_to_rlrs_map[rreg_ix].push(rlrix);
  }

  // And what do we got?
  //for (vlrixs, vreg) in vreg_to_vlrs_map.iter().zip(0..) {
  //  println!("QQQQ vreg v{:?} -> vlrixs {:?}", vreg, vlrixs);
  //}
  //for (rlrixs, rreg) in rreg_to_rlrs_map.iter().zip(0..) {
  //  println!("QQQQ rreg r{:?} -> rlrixs {:?}", rreg, rlrixs);
  //}

  // Range end checks for VRegs
  let doesVRegHaveXXat
  // true = "last use" false = "first def"
    = |xxIsLastUse: bool, vreg: VirtualReg, iix: InstIx|
    -> Option<VirtualRangeIx> {
      let vreg_no = vreg.get_index();
      let vlrixs = &vreg_to_vlrs_map[vreg_no];
      for vlrix in vlrixs {
        let frags = &vlr_env[*vlrix].sorted_frags;
        for fix in &frags.frag_ixs {
          let frag = &frag_env[*fix];
          if xxIsLastUse {
            // We're checking to see if |vreg| has a last use in this block
            // (well, technically, a fragment end in the block; we don't care if
            // it is later redefined in the same block) .. anyway ..
            // We're checking to see if |vreg| has a last use in this block
            // at |iix|.u
            if frag.last == InstPoint::new_use(iix) {
              return Some(*vlrix);
            }
          } else {
            // We're checking to see if |vreg| has a first def in this block
            // at |iix|.d
            if frag.first == InstPoint::new_def(iix) {
              return Some(*vlrix);
            }
          }
        }
      }
      None
    };

  // Range end checks for RRegs
  let doesRRegHaveXXat
  // true = "last use" false = "first def"
    = |xxIsLastUse: bool, rreg: RealReg, iix: InstIx|
    -> Option<RealRangeIx> {
      let rreg_no = rreg.get_index();
      let rlrixs = &rreg_to_rlrs_map[rreg_no];
      for rlrix in rlrixs {
        let frags = &rlr_env[*rlrix].sorted_frags;
        for fix in &frags.frag_ixs {
          let frag = &frag_env[*fix];
          if xxIsLastUse {
            // We're checking to see if |rreg| has a last use in this block
            // at |iix|.u
            if frag.last == InstPoint::new_use(iix) {
              return Some(*rlrix);
            }
          } else {
            // We're checking to see if |rreg| has a first def in this block
            // at |iix|.d
            if frag.first == InstPoint::new_def(iix) {
              return Some(*rlrix);
            }
          }
        }
      }
      None
    };

  // Make up a vector of registers that are connected by moves:
  //
  //    (dstReg, srcReg, transferring insn, estimated execution count)
  //
  // This can contain real-to-real moves, which we obviously can't do anything
  // about.  We'll remove them in the next pass.
  let mut connectedByMoves = Vec::<(Reg, Reg, InstIx, u32)>::new();
  for b in func.blocks() {
    let block_eef = est_freqs[b];
    for iix in func.block_insns(b) {
      let insn = &func.get_insn(iix);
      let im = func.is_move(insn);
      match im {
        None => {}
        Some((wreg, reg)) => {
          let iix_bounds = &reg_vecs_and_bounds.bounds[iix];
          // It might seem strange to assert that defs_len is <= 1 rather than
          // == 1.  But -- as fuzzing shows -- it might be that the
          // destination of a copy is a real reg that is one of the
          // RealRegUniverse |suggested_scratch| registers.  It is allowable
          // for such a register to be defined, but not used or modified.
          // However, sanitisation will ensure it is not present in any of the
          // three register sets.  Hence the assertions and the following
          // conditional block.  If any of the following five assertions fail,
          // the client's |is_move| is probably lying to us.
          assert!(iix_bounds.uses_len == 1);
          assert!(iix_bounds.defs_len <= 1);
          assert!(iix_bounds.mods_len == 0);
          if iix_bounds.uses_len == 1 && iix_bounds.defs_len == 1 {
            let reg_vecs = &reg_vecs_and_bounds.vecs;
            assert!(reg_vecs.uses[iix_bounds.uses_start as usize] == reg);
            assert!(
              reg_vecs.defs[iix_bounds.defs_start as usize] == wreg.to_reg()
            );
            connectedByMoves.push((wreg.to_reg(), reg, iix, block_eef));
          }
        }
      }
    }
  }

  // FIXME SmallVec!
  // XX these sub-vectors could contain duplicates, I suppose, for example if
  // there are two identical copy insns at different points on the "boundary"
  // for some VLR.  I don't think it matters though since we're going to rank
  // the hints by strength and then choose at most one.
  let mut hints = TypedIxVec::<VirtualRangeIx, Vec<Hint>>::new();
  hints.resize(vlr_env.len(), vec![]);

  let mut is_vv_boundary_move = TypedIxVec::<InstIx, bool>::new();
  is_vv_boundary_move.resize(func.insns().len() as u32, false);

  let mut vlrEquivClassesUF =
    UnionFind::<VirtualRangeIx>::new(vlr_env.len() as usize);

  for (rDst, rSrc, iix, eef) in connectedByMoves {
    //println!("QQQQ at {:?} {:?} <- {:?} (eef {})", iix, rDst, rSrc, eef);
    match (rDst.is_virtual(), rSrc.is_virtual()) {
      (true, true) => {
        // Check for a V <- V hint.
        let rSrcV = rSrc.to_virtual_reg();
        let rDstV = rDst.to_virtual_reg();
        let mb_vlrSrc =
          doesVRegHaveXXat(/*xxIsLastUse=*/ true, rSrcV, iix);
        let mb_vlrDst =
          doesVRegHaveXXat(/*xxIsLastUse=*/ false, rDstV, iix);
        if mb_vlrSrc.is_some() && mb_vlrDst.is_some() {
          let vlrSrc = mb_vlrSrc.unwrap();
          let vlrDst = mb_vlrDst.unwrap();
          // Add hints for both VLRs, since we don't know which one will
          // assign first.  Indeed, a VLR may be assigned and un-assigned
          // arbitrarily many times.
          hints[vlrSrc].push(Hint::SameAs(vlrDst, eef));
          hints[vlrDst].push(Hint::SameAs(vlrSrc, eef));
          vlrEquivClassesUF.union(vlrDst, vlrSrc);
          is_vv_boundary_move[iix] = true;
        }
      }
      (true, false) => {
        // Check for a V <- R hint.
        let rSrcR = rSrc.to_real_reg();
        let rDstV = rDst.to_virtual_reg();
        let mb_rlrSrc =
          doesRRegHaveXXat(/*xxIsLastUse=*/ true, rSrcR, iix);
        let mb_vlrDst =
          doesVRegHaveXXat(/*xxIsLastUse=*/ false, rDstV, iix);
        if mb_rlrSrc.is_some() && mb_vlrDst.is_some() {
          let vlrDst = mb_vlrDst.unwrap();
          hints[vlrDst].push(Hint::Exactly(rSrcR, eef));
        }
      }
      (false, true) => {
        // Check for a R <- V hint.
        let rSrcV = rSrc.to_virtual_reg();
        let rDstR = rDst.to_real_reg();
        let mb_vlrSrc =
          doesVRegHaveXXat(/*xxIsLastUse=*/ true, rSrcV, iix);
        let mb_rlrDst =
          doesRRegHaveXXat(/*xxIsLastUse=*/ false, rDstR, iix);
        if mb_vlrSrc.is_some() && mb_rlrDst.is_some() {
          let vlrSrc = mb_vlrSrc.unwrap();
          hints[vlrSrc].push(Hint::Exactly(rDstR, eef));
        }
      }
      (false, false) => {
        // This is a real-to-real move.  There's nothing we can do.  Ignore it.
      }
    }
  }

  // For the convenience of the allocator core, sort the hints for each VLR so
  // as to move the most preferred to the front.
  for hints_for_one_vlr in hints.iter_mut() {
    hints_for_one_vlr
      .sort_by(|h1, h2| h2.get_weight().partial_cmp(&h1.get_weight()).unwrap());
  }

  let vlrEquivClasses: UnionFindEquivClasses<VirtualRangeIx> =
    vlrEquivClassesUF.get_equiv_classes();

  if log_enabled!(Level::Debug) {
    debug!("Coalescing hints:");
    let mut n = 0;
    for hints_for_one_vlr in hints.iter() {
      let mut s = "".to_string();
      for hint in hints_for_one_vlr {
        s = s + &show_hint(hint) + &" ".to_string();
      }
      debug!("  hintsfor {:<4?} = {}", VirtualRangeIx::new(n), s);
      n += 1;
    }

    for n in 0..vlr_env.len() {
      let vlrix = VirtualRangeIx::new(n);
      let mut tmpvec = vec![];
      for elem in vlrEquivClasses.equiv_class_elems_iter(vlrix) {
        tmpvec.reverse();
        tmpvec.push(elem);
      }
      debug!("  eclassof {:?} = {:?}", vlrix, tmpvec);
    }

    for (b, i) in is_vv_boundary_move.iter().zip(0..) {
      if *b {
        debug!("  vv_boundary_move at {:?}", InstIx::new(i));
      }
    }
  }

  info!("do_coalescing_analysis: end");
  info!("");

  (hints, vlrEquivClasses, is_vv_boundary_move)
}

//=============================================================================
// The as-yet-unallocated VirtualReg LR prio queue, |VirtualRangePrioQ|.
//
// Relevant methods are parameterised by a VirtualRange env.

// What we seek to do with |VirtualRangePrioQ| is to implement a priority
// queue of as-yet unallocated virtual live ranges.  For each iteration of the
// main allocation loop, we pull out the highest-priority unallocated
// VirtualRange, and either allocate it (somehow), or spill it.
//
// The Rust standard type BinaryHeap gives us an efficient way to implement
// the priority queue.  However, it requires that the queue items supply the
// necessary cost-comparisons by implementing |Ord| on that type.  Hence we
// have to wrap up the items we fundamentally want in the queue, viz,
// |VirtualRangeIx|, into a new type |VirtualRangeIxAndSize| that also carries
// the relevant cost field, |size|.  Then we implement |Ord| for
// |VirtualRangeIxAndSize| so as to only look at the |size| fields.
//
// There is a small twist, however.  Most virtual ranges are small and so will
// have a small |size| field (less than 20, let's say).  For such cases,
// |BinaryHeap| will presumably choose between contenders with the same |size|
// field in some arbitrary way.  This has two disadvantages:
//
// * it makes the exact allocation order, and hence allocation results,
//   dependent on |BinaryHeap|'s arbitrary-choice scheme.  This seems
//   undesirable, and given recent shenanigans resulting from |HashMap| being
//   nondeterministic even in a single-threaded scenario, I don't entirely
//   trust |BinaryHeap| even to be deterministic.
//
// * experimentation with the "qsort" test case shows that breaking ties by
//   selecting the entry that has been in the queue the longest, rather than
//   choosing arbitrarily, gives slightly better allocations (slightly less
//   spilling) in spill-heavy situations (where there are few registers).
//   When there is not much spilling, it makes no difference.
//
// For these reasons, |VirtualRangeIxAndSize| also contains a |tiebreaker|
// field.  The |VirtualRangePrioQ| logic gives a different value of this for
// each |VirtualRangeIxAndSize| it creates.  These numbers start off at 2^32-1
// and decrease towards zero.  They are used as a secondary comparison key in
// the case where the |size| fields are equal.  The effect is that (1)
// tiebreaking is made completely deterministic, and (2) it breaks ties in
// favour of the oldest entry (since that will have the highest |tiebreaker|
// field).
//
// The tiebreaker field will wrap around when it hits zero, but that can only
// happen after processing 2^32-1 virtual live ranges.  In such cases I would
// expect that the allocator would have run out of memory long before, so it's
// academic in practice.  Even if it does wrap around there is no danger to
// the correctness of the allocations.

// Wrap up a VirtualRangeIx and its size, so that we can implement Ord for it
// on the basis of the |size| and |tiebreaker| fields.
//
// NB! Do not derive {,Partial}{Eq,Ord} for this.  It has its own custom
// implementations.
struct VirtualRangeIxAndSize {
  vlrix: VirtualRangeIx,
  size: u16,
  tiebreaker: u32,
}
impl VirtualRangeIxAndSize {
  fn new(vlrix: VirtualRangeIx, size: u16, tiebreaker: u32) -> Self {
    assert!(size > 0);
    Self { vlrix, size, tiebreaker }
  }
}
impl PartialEq for VirtualRangeIxAndSize {
  fn eq(&self, other: &Self) -> bool {
    self.size == other.size && self.tiebreaker == other.tiebreaker
  }
}
impl Eq for VirtualRangeIxAndSize {}
impl PartialOrd for VirtualRangeIxAndSize {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl Ord for VirtualRangeIxAndSize {
  fn cmp(&self, other: &Self) -> Ordering {
    match self.size.cmp(&other.size) {
      Ordering::Less => Ordering::Less,
      Ordering::Greater => Ordering::Greater,
      Ordering::Equal => self.tiebreaker.cmp(&other.tiebreaker),
    }
  }
}

struct VirtualRangePrioQ {
  // The set of as-yet unallocated VirtualRangeIxs.  These are indexes into a
  // VirtualRange env that is not stored here.  The VirtualRangeIxs are tagged
  // with the VirtualRange size and a tiebreaker field.
  heap: BinaryHeap<VirtualRangeIxAndSize>,
  tiebreaker_ctr: u32,
}
impl VirtualRangePrioQ {
  fn new(vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>) -> Self {
    let mut res =
      Self { heap: BinaryHeap::new(), tiebreaker_ctr: 0xFFFF_FFFFu32 };
    for vlrix in
      VirtualRangeIx::new(0).dotdot(VirtualRangeIx::new(vlr_env.len()))
    {
      let to_add = VirtualRangeIxAndSize::new(
        vlrix,
        vlr_env[vlrix].size,
        res.tiebreaker_ctr,
      );
      res.heap.push(to_add);
      res.tiebreaker_ctr -= 1;
    }
    res
  }

  #[inline(never)]
  fn is_empty(&self) -> bool {
    self.heap.is_empty()
  }

  #[inline(never)]
  fn len(&self) -> usize {
    self.heap.len()
  }

  // Add a VirtualRange index.
  #[inline(never)]
  fn add_VirtualRange(
    &mut self, vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
    vlrix: VirtualRangeIx,
  ) {
    let to_add = VirtualRangeIxAndSize::new(
      vlrix,
      vlr_env[vlrix].size,
      self.tiebreaker_ctr,
    );
    self.tiebreaker_ctr -= 1;
    self.heap.push(to_add);
  }

  // Look in |unallocated| to locate the entry referencing the VirtualRange
  // with the largest |size| value.  Remove the ref from |unallocated| and
  // return the VLRIx for said entry.
  #[inline(never)]
  fn get_longest_VirtualRange(&mut self) -> Option<VirtualRangeIx> {
    match self.heap.pop() {
      None => None,
      Some(VirtualRangeIxAndSize { vlrix, size: _, tiebreaker: _ }) => {
        Some(vlrix)
      }
    }
  }

  #[inline(never)]
  fn show_with_envs(
    &self, vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) -> Vec<String> {
    let mut resV = vec![];
    for VirtualRangeIxAndSize { vlrix, size: _, tiebreaker: _ } in
      self.heap.iter()
    {
      let mut res = "TODO  ".to_string();
      res += &format!("{:?} = {:?}", vlrix, &vlr_env[*vlrix]);
      resV.push(res);
    }
    resV
  }
}

//=============================================================================
// Per-real-register commitment maps
//

// Something that pairs a fragment index with the index of the virtual range
// to which this fragment conceptually "belongs", at least for the purposes of
// this commitment map.  Alternatively, the |vlrix| field may be None, which
// indicates that the associated fragment belongs to a real-reg live range and
// is therefore non-evictable.
//
// (A fragment merely denotes a sequence of instruction (points), but within
// the context of a commitment map for a real register, obviously any
// particular fragment can't be part of two different virtual live ranges.)
//
// Note that we don't intend to actually use the PartialOrd methods for
// FIxAndVLRix.  However, they need to exist since we want to construct an
// AVLTree<FIxAndVLRix>, and that requires PartialOrd for its element type.
// For working with such trees we will supply our own comparison function;
// hence PartialOrd here serves only to placate the typechecker.  It should
// never actually be used.
#[derive(Clone, Copy)]
struct FIxAndVLRIx {
  fix: RangeFragIx,
  mb_vlrix: Option<VirtualRangeIx>,
}
impl FIxAndVLRIx {
  fn new(fix: RangeFragIx, mb_vlrix: Option<VirtualRangeIx>) -> Self {
    Self { fix, mb_vlrix }
  }
}
impl PartialEq for FIxAndVLRIx {
  fn eq(&self, _other: &Self) -> bool {
    // See comments above.
    panic!("impl PartialEq for FIxAndVLRIx: should never be used");
  }
}
impl PartialOrd for FIxAndVLRIx {
  fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
    // See comments above.
    panic!("impl PartialOrd for FIxAndVLRIx: should never be used");
  }
}
impl fmt::Debug for FIxAndVLRIx {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    let vlrix_string = match self.mb_vlrix {
      None => "NONE".to_string(),
      Some(vlrix) => format!("{:?}", vlrix),
    };
    write!(fmt, "(FnV {:?} {})", self.fix, vlrix_string)
  }
}

// This indicates the current set of fragments to which some real register is
// currently "committed".  The fragments *must* be non-overlapping.  Hence
// they form a total order, and so they must appear in the vector sorted by
// that order.
//
// Overall this is identical to SortedRangeFragIxs, except extended so that
// each FragIx is tagged with an Option<VirtualRangeIx>.
#[derive(Clone)]
struct CommitmentMap {
  pairs: Vec<FIxAndVLRIx>,
}
impl fmt::Debug for CommitmentMap {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    self.pairs.fmt(fmt)
  }
}
impl CommitmentMap {
  pub fn show_with_fenv(
    &self, _fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> String {
    //let mut frags = TypedIxVec::<RangeFragIx, RangeFrag>::new();
    //for fix in &self.frag_ixs {
    //  frags.push(fenv[*fix]);
    //}
    format!("(CommitmentMap {:?})", &self.pairs)
  }
}

impl CommitmentMap {
  pub fn new() -> Self {
    CommitmentMap { pairs: vec![] }
  }

  fn check(
    &self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    let mut ok = true;
    for i in 1..self.pairs.len() {
      let prev_pair = &self.pairs[i - 1];
      let this_pair = &self.pairs[i - 0];
      let prev_fix = prev_pair.fix;
      let this_fix = this_pair.fix;
      let prev_frag = &fenv[prev_fix];
      let this_frag = &fenv[this_fix];
      // Check in-orderness
      if cmp_range_frags(prev_frag, this_frag) != Some(Ordering::Less) {
        ok = false;
        break;
      }
      // Check that, if this frag specifies an owner VirtualRange, that the
      // VirtualRange lists this frag as one of its components.
      let this_mb_vlrix = this_pair.mb_vlrix;
      if let Some(this_vlrix) = this_mb_vlrix {
        ok = vlr_env[this_vlrix]
          .sorted_frags
          .frag_ixs
          .iter()
          .any(|fix| *fix == this_fix);
        if !ok {
          break;
        }
      }
    }
    // Also check the first entry for a correct back-link.
    if ok && self.pairs.len() > 0 {
      let this_pair = &self.pairs[0];
      let this_fix = this_pair.fix;
      let this_mb_vlrix = this_pair.mb_vlrix;
      if let Some(this_vlrix) = this_mb_vlrix {
        ok = vlr_env[this_vlrix]
          .sorted_frags
          .frag_ixs
          .iter()
          .any(|fix| *fix == this_fix);
      }
    }
    if !ok {
      panic!("CommitmentMap::check: vector not ok");
    }
  }

  pub fn add(
    &mut self, to_add_frags: &SortedRangeFragIxs,
    to_add_mb_vlrix: Option<VirtualRangeIx>,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    self.check(fenv, vlr_env);
    to_add_frags.check(fenv);
    let pairs_x = &self;
    let frags_y = &to_add_frags;
    let mut ix = 0;
    let mut iy = 0;
    let mut res = Vec::<FIxAndVLRIx>::new();
    while ix < pairs_x.pairs.len() && iy < frags_y.frag_ixs.len() {
      let fx = fenv[pairs_x.pairs[ix].fix];
      let fy = fenv[frags_y.frag_ixs[iy]];
      match cmp_range_frags(&fx, &fy) {
        Some(Ordering::Less) => {
          res.push(pairs_x.pairs[ix]);
          ix += 1;
        }
        Some(Ordering::Greater) => {
          res.push(FIxAndVLRIx::new(frags_y.frag_ixs[iy], to_add_mb_vlrix));
          iy += 1;
        }
        Some(Ordering::Equal) | None => {
          panic!("CommitmentMap::add: vectors intersect")
        }
      }
    }
    // At this point, one or the other or both vectors are empty.  Hence
    // it doesn't matter in which order the following two while-loops
    // appear.
    assert!(ix == pairs_x.pairs.len() || iy == frags_y.frag_ixs.len());
    while ix < pairs_x.pairs.len() {
      res.push(pairs_x.pairs[ix]);
      ix += 1;
    }
    while iy < frags_y.frag_ixs.len() {
      res.push(FIxAndVLRIx::new(frags_y.frag_ixs[iy], to_add_mb_vlrix));
      iy += 1;
    }
    self.pairs = res;
    self.check(fenv, vlr_env);
  }

  pub fn del(
    &mut self, to_del_frags: &SortedRangeFragIxs,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    self.check(fenv, vlr_env);
    to_del_frags.check(fenv);
    let pairs_x = &self;
    let frags_y = &to_del_frags;
    let mut ix = 0;
    let mut iy = 0;
    let mut res = Vec::<FIxAndVLRIx>::new();
    while ix < pairs_x.pairs.len() && iy < frags_y.frag_ixs.len() {
      let fx = fenv[pairs_x.pairs[ix].fix];
      let fy = fenv[frags_y.frag_ixs[iy]];
      match cmp_range_frags(&fx, &fy) {
        Some(Ordering::Less) => {
          res.push(pairs_x.pairs[ix]);
          ix += 1;
        }
        Some(Ordering::Equal) => {
          ix += 1;
          iy += 1;
        }
        Some(Ordering::Greater) => {
          iy += 1;
        }
        None => panic!("CommitmentMap::del: partial overlap"),
      }
    }
    assert!(ix == pairs_x.pairs.len() || iy == frags_y.frag_ixs.len());
    // Handle leftovers
    while ix < pairs_x.pairs.len() {
      res.push(pairs_x.pairs[ix]);
      ix += 1;
    }
    self.pairs = res;
    self.check(fenv, vlr_env);
  }
}

//=============================================================================
// Per-real-register commitment maps FAST
//

// This indicates the current set of fragments to which some real register is
// currently "committed".  The fragments *must* be non-overlapping.  Hence
// they form a total order, and so they must appear in the vector sorted by
// that order.
//
// Overall this is identical to SortedRangeFragIxs, except extended so that
// each FragIx is tagged with an Option<VirtualRangeIx>.
struct CommitmentMapFAST {
  tree: AVLTree<FIxAndVLRIx>,
}
impl fmt::Debug for CommitmentMapFAST {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    let as_vec = self.tree.to_vec();
    as_vec.fmt(fmt)
  }
}

// The custom comparator
fn cmp_tree_entries_for_CommitmentMapFAST(
  e1: FIxAndVLRIx, e2: FIxAndVLRIx,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
) -> Option<Ordering> {
  cmp_range_frags(&frag_env[e1.fix], &frag_env[e2.fix])
}

impl CommitmentMapFAST {
  pub fn new() -> Self {
    // The AVL tree constructor needs a default value for the elements.  It
    // will never be used.  To be on the safe side, give it something that
    // will show as obviously bogus if we ever try to "dereference" any part
    // of it.
    let dflt = FIxAndVLRIx::new(
      RangeFragIx::new(0xFFFF_FFFF),
      Some(VirtualRangeIx::new(0xFFFF_FFFF)),
    );
    Self { tree: AVLTree::<FIxAndVLRIx>::new(dflt) }
  }

  pub fn add(
    &mut self, to_add_frags: &SortedRangeFragIxs,
    to_add_mb_vlrix: Option<VirtualRangeIx>,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    _vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    for fix in &to_add_frags.frag_ixs {
      let to_add = FIxAndVLRIx::new(*fix, to_add_mb_vlrix);
      let added = self.tree.insert(
        to_add,
        Some(&|pair1, pair2| {
          cmp_tree_entries_for_CommitmentMapFAST(pair1, pair2, fenv)
        }),
      );
      // If this fails, it means the fragment overlaps one that has already
      // been committed to.  That's a serious error.
      assert!(added);
    }
  }

  pub fn del(
    &mut self, to_del_frags: &SortedRangeFragIxs,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    _vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    for fix in &to_del_frags.frag_ixs {
      // re None: we don't care what the VLRIx is, since we're deleting by
      // RangeFrags alone.
      let to_del = FIxAndVLRIx::new(*fix, None);
      let deleted = self.tree.delete(
        to_del,
        Some(&|pair1, pair2| {
          cmp_tree_entries_for_CommitmentMapFAST(pair1, pair2, fenv)
        }),
      );
      // If this fails, it means the fragment wasn't already committed to.
      // That's also a serious error.
      assert!(deleted);
    }
  }
}

//=============================================================================
// The per-real-register state
//
// Relevant methods are expected to be parameterised by the same VirtualRange
// env as used in calls to |VirtualRangePrioQ|.

struct PerRealReg {
  // The current committed fragments for this RealReg.
  committed: CommitmentMap,
  committedFAST: CommitmentMapFAST,

  // The set of VirtualRanges which have been assigned to this RealReg.  The
  // union of their frags will be equal to |committed| only if this RealReg
  // has no RealRanges.  If this RealReg does have RealRanges the
  // aforementioned union will be exactly the subset of |committed| not used
  // by the RealRanges.
  vlrixs_assigned: Set<VirtualRangeIx>,
}
impl PerRealReg {
  fn new() -> Self {
    Self {
      committed: CommitmentMap::new(),
      committedFAST: CommitmentMapFAST::new(),
      vlrixs_assigned: Set::<VirtualRangeIx>::empty(),
    }
  }

  #[inline(never)]
  fn add_RealRange(
    &mut self, to_add: &RealRange, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    // Commit this register to |to_add|, irrevocably.  Don't add it to
    // |vlrixs_assigned| since we will never want to later evict the
    // assignment.
    self.committedFAST.add(&to_add.sorted_frags, None, fenv, vlr_env);
    if CROSSCHECK_CM {
      self.committed.add(&to_add.sorted_frags, None, fenv, vlr_env);
    }
  }

  #[inline(never)]
  fn add_VirtualRange(
    &mut self, to_add_vlrix: VirtualRangeIx,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    let to_add_vlr = &vlr_env[to_add_vlrix];
    self.committedFAST.add(
      &to_add_vlr.sorted_frags,
      Some(to_add_vlrix),
      fenv,
      vlr_env,
    );
    if CROSSCHECK_CM {
      self.committed.add(
        &to_add_vlr.sorted_frags,
        Some(to_add_vlrix),
        fenv,
        vlr_env,
      );
    }
    assert!(!self.vlrixs_assigned.contains(to_add_vlrix));
    self.vlrixs_assigned.insert(to_add_vlrix);
  }

  #[inline(never)]
  fn del_VirtualRange(
    &mut self, to_del_vlrix: VirtualRangeIx,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    // Remove it from |vlrixs_assigned|
    if self.vlrixs_assigned.contains(to_del_vlrix) {
      self.vlrixs_assigned.delete(to_del_vlrix);
    } else {
      panic!("PerRealReg: del_VirtualRange on VR not in vlrixs_assigned");
    }
    // Remove it from |committed|
    let to_del_vlr = &vlr_env[to_del_vlrix];
    self.committedFAST.del(&to_del_vlr.sorted_frags, fenv, vlr_env);
    if CROSSCHECK_CM {
      self.committed.del(&to_del_vlr.sorted_frags, fenv, vlr_env);
    }
  }
}

// HELPER FUNCTION
// In order to allocate |would_like_to_add| for this real reg, we will
// need to evict |pairs[pairs_ix]|.  That may or may not be possible,
// given the rules of the game.  If it is possible, update |evict_set| and
// |evict_cost| accordingly, and return |true|.  If it isn't possible,
// return |false|; |evict_set| and |evict_cost| must not be changed.
fn handle_CM_entry(
  evict_set: &mut Set<VirtualRangeIx>, evict_cost: &mut SpillCost,
  pairs: &Vec<FIxAndVLRIx>, pairs_ix: usize, spill_cost_budget: SpillCost,
  do_not_evict: &Set<VirtualRangeIx>,
  vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>, _who: &'static str,
) -> bool {
  let FIxAndVLRIx { fix: _fix_to_evict, mb_vlrix: mb_vlrix_to_evict } =
    pairs[pairs_ix];
  //debug!("handle_CM_entry({}): to_evict = {:?}, set = {:?}",
  //       who, mb_vlrix_to_evict, evict_set);
  // Work through our list of reasons why evicting this frag isn't
  // possible or allowed.
  if mb_vlrix_to_evict.is_none() {
    // This frag has no associated VirtualRangeIx, so it is part of a
    // RealRange, and hence not evictable.
    return false;
  }
  // The |unwrap| is guarded by the previous |if|.
  let vlrix_to_evict = mb_vlrix_to_evict.unwrap();
  if do_not_evict.contains(vlrix_to_evict) {
    // Our caller asks that we do not evict this one.
    return false;
  }
  let vlr_to_evict = &vlr_env[vlrix_to_evict];
  if vlr_to_evict.spill_cost.is_infinite() {
    // This is a spill/reload range, so we can't evict it.
    return false;
  }
  // It's at least plausible.  Check the costs.  Note that because a
  // VirtualRange may contain arbitrarily many RangeFrags, and we're
  // visiting RangeFrags here, the |evict_set| may well already contain
  // |vlrix_to_evict|, in the case where we've already visited a different
  // fragment that "belongs" to |vlrix_to_evict|.  Hence we must be sure
  // not to add it again -- if only as as not to mess up the evict cost
  // calculations.

  if !evict_set.contains(vlrix_to_evict) {
    let mut new_evict_cost = *evict_cost;
    new_evict_cost.add(&vlr_to_evict.spill_cost);
    // Are we still within our spill-cost "budget"?
    if !new_evict_cost.is_less_than(&spill_cost_budget) {
      // No.  Give up.
      return false;
    }
    // We're committing to this entry.  So update the running state.
    evict_set.insert(vlrix_to_evict);
    *evict_cost = new_evict_cost;
  }
  true
}

// HELPER FUNCTION
// For a given RangeFrag, traverse the commitment sub-tree rooted at |root|,
// adding to |running_set| the set of VLRIxs that the frag intersects, and
// adding their spill costs to |running_cost|.  Return false if, for one of
// the 4 reasons documented below, the traversal has been abandoned, and true
// if the search completed successfully.
fn rec_helper(
  // The running state, threaded through the tree traversal.  These accumulate
  // ranges and costs as we traverse the tree.
  running_set: &mut Set<VirtualRangeIx>,
  running_cost: &mut SpillCost,
  // The root of the subtree to search.  This changes as we recurse down.
  root: u32,
  // === All the other args stay constant as we recurse ===
  tree: &AVLTree<FIxAndVLRIx>,
  // The FIxAndVLRIx we want to accommodate, in its components.
  pair_frag: &RangeFrag,
  spill_cost_budget: &SpillCost,
  do_not_evict: &Set<VirtualRangeIx>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
) -> bool {
  let root_node = &tree.pool[root as usize];
  let root_node_FnV = &root_node.item;
  assert!(root_node.tag != AVLTag::Free);
  let root_frag = &frag_env[root_node_FnV.fix];
  // Now figure out:
  // - whether we need to search the left subtree
  // - whether we need to search the right subtree
  // - whether |pair_frag| overlaps the root of the subtree
  let go_left = pair_frag.first < root_frag.first;
  let go_right = pair_frag.last > root_frag.last;
  let overlaps_root =
    pair_frag.last >= root_frag.first && pair_frag.first <= root_frag.last;

  // Let's first consider the root node.  If we need it but it's not
  // evictable, we might as well stop now.
  if overlaps_root {
    // This frag has no associated VirtualRangeIx, so it is part of a
    // RealRange, and hence not evictable.
    if root_node_FnV.mb_vlrix.is_none() {
      return false;
    }
    // Maybe this one is a spill range, in which case, it can't be evicted.
    let vlrix_to_evict = root_node_FnV.mb_vlrix.unwrap();
    let vlr_to_evict = &vlr_env[vlrix_to_evict];
    if vlr_to_evict.spill_cost.is_infinite() {
      return false;
    }
    // Check that this range alone doesn't exceed our total spill cost.
    // NB: given the check XXX below, I don't think this is necessary.
    if !vlr_to_evict.spill_cost.is_less_than(spill_cost_budget) {
      return false;
    }
    // Maybe our caller asked us not to evict this one.
    if do_not_evict.contains(vlrix_to_evict) {
      return false;
    }
    // Ok!  We can evict the root node.  Update the running state accordingly.
    // Note that we may be presented with the same VLRIx to evict multiple
    // times, so we must be careful to add the cost of it only once.
    if !running_set.contains(vlrix_to_evict) {
      let mut tmp_cost = *running_cost;
      tmp_cost.add(&vlr_to_evict.spill_cost);
      // See above XXX
      if !tmp_cost.is_less_than(spill_cost_budget) {
        return false;
      }
      *running_cost = tmp_cost;
      running_set.insert(vlrix_to_evict);
    }
  }

  // Now consider contributions from the left subtree.  Whether we visit the
  // left or right subtree first is unimportant.
  let left_root = tree.pool[root as usize].left;
  if go_left && left_root != AVL_NULL {
    let ok_left = rec_helper(
      running_set,
      running_cost,
      left_root,
      tree,
      pair_frag,
      spill_cost_budget,
      do_not_evict,
      frag_env,
      vlr_env,
    );
    if !ok_left {
      return false;
    }
  }

  let right_root = tree.pool[root as usize].right;
  if go_right && right_root != AVL_NULL {
    let ok_right = rec_helper(
      running_set,
      running_cost,
      right_root,
      tree,
      pair_frag,
      spill_cost_budget,
      do_not_evict,
      frag_env,
      vlr_env,
    );
    if !ok_right {
      return false;
    }
  }

  // If we get here, it means that |pair_frag| can be accommodated if we evict
  // all the frags it overlaps in the entire subtree rooted at |root|.
  // Propagate that (good) news upwards.
  //
  // Stay sane ..
  assert!(running_cost.is_finite());
  assert!(running_cost.is_less_than(spill_cost_budget));
  true
}

impl PerRealReg {
  // Find the set of VirtualRangeIxs that would need to be evicted in order to
  // allocate |would_like_to_add| to this register.  Virtual ranges mentioned
  // in |do_not_evict| must not be considered as candidates for eviction.
  // Also returns the total associated spill cost.  That spill cost cannot be
  // infinite.
  //
  // This can fail (return None) for four different reasons:
  //
  // - |would_like_to_add| interferes with a real-register-live-range
  //   commitment, so the register would be unavailable even if we evicted
  //   *all* virtual ranges assigned to it.
  //
  // - |would_like_to_add| interferes with a virtual range which is a spill
  //   range (has infinite cost).  We cannot evict those without risking
  //   non-termination of the overall allocation algorithm.
  //
  // - |would_like_to_add| interferes with a virtual range listed in
  //   |do_not_evict|.  Our caller uses this mechanism when trying to do
  //   coalesing, to avoid the nonsensicality of evicting some part of a
  //   virtual live range group in order to allocate a member of the same
  //   group.
  //
  // - The total spill cost of the candidate set exceeds the spill cost of
  //   |would_like_to_add|.  This means that spilling them would be a net loss
  //   per our cost model.  Note that |would_like_to_add| may have an infinite
  //   spill cost, in which case it will "win" over all other
  //   non-infinite-cost eviction candidates.  This is by design (so as to
  //   guarantee that we can always allocate spill/reload bridges).
  #[inline(never)]
  fn find_Evict_Set_FAST(
    &self, would_like_to_add: VirtualRangeIx,
    do_not_evict: &Set<VirtualRangeIx>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
    frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> Option<(Set<VirtualRangeIx>, SpillCost)> {
    // Firstly, if the commitment tree is for this reg is empty, we can
    // declare success immediately.
    if self.committedFAST.tree.root == AVL_NULL {
      let evict_set = Set::<VirtualRangeIx>::empty();
      let evict_cost = SpillCost::zero();
      return Some((evict_set, evict_cost));
    }

    // The tree isn't empty, so we will have to do this the hard way: iterate
    // over all fragments in |would_like_to_add| and check them against the
    // tree.

    // Useful constants for the main loop
    let would_like_to_add_vlr = &vlr_env[would_like_to_add];
    let evict_cost_budget = would_like_to_add_vlr.spill_cost;
    // Note that |evict_cost_budget| can be infinite because
    // |would_like_to_add| might be a spill/reload range.

    // The overall evict set and cost so far.  These are updated as we iterate
    // over the fragments that make up |would_like_to_add|.
    let mut running_set = Set::<VirtualRangeIx>::empty();
    let mut running_cost = SpillCost::zero();

    // "wlta" = would like to add
    for wlta_fix in &would_like_to_add_vlr.sorted_frags.frag_ixs {
      //debug!("fESF: considering {:?}", *wlta_fix);
      let wlta_frag = &frag_env[*wlta_fix];
      let wlta_frag_ok = rec_helper(
        &mut running_set,
        &mut running_cost,
        self.committedFAST.tree.root,
        &self.committedFAST.tree,
        &wlta_frag,
        &evict_cost_budget,
        do_not_evict,
        frag_env,
        vlr_env,
      );
      if !wlta_frag_ok {
        return None;
      }
      // And move on to the next fragment.
    }

    // If we got here, it means that |would_like_to_add| can be accommodated \o/
    assert!(running_cost.is_finite());
    assert!(running_cost.is_less_than(&evict_cost_budget));
    Some((running_set, running_cost))
  }

  // This should compute exactly the same results as find_Evict_Set_FAST,
  // using a slow but much-easier-to-get-correct algorithm.  It has been used
  // to debug find_Evict_Set_FAST.
  #[inline(never)]
  fn find_Evict_Set_CROSSCHECK(
    &self, would_like_to_add: VirtualRangeIx,
    do_not_evict: &Set<VirtualRangeIx>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
    frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> Option<(Set<VirtualRangeIx>, SpillCost)> {
    fn step_ip(ip: InstPoint) -> InstPoint {
      match ip.pt {
        Point::Reload => InstPoint::new(ip.iix, Point::Use),
        Point::Use => InstPoint::new(ip.iix, Point::Def),
        Point::Def => InstPoint::new(ip.iix, Point::Spill),
        Point::Spill => InstPoint::new(ip.iix.plus(1), Point::Reload),
      }
    }

    // Useful constants for the loop
    let would_like_to_add_vlr = &vlr_env[would_like_to_add];
    let evict_cost_budget = would_like_to_add_vlr.spill_cost;
    // Note that |evict_cost_budget| can be infinite because
    // |would_like_to_add| might be a spill/reload range.

    let vr_ip_first =
      frag_env[would_like_to_add_vlr.sorted_frags.frag_ixs[0]].first;
    let vr_ip_last = frag_env[would_like_to_add_vlr.sorted_frags.frag_ixs
      [would_like_to_add_vlr.sorted_frags.frag_ixs.len() - 1]]
      .last;
    // assert that wlta is in order
    for fix in &would_like_to_add_vlr.sorted_frags.frag_ixs {
      let frag = &frag_env[*fix];
      assert!(vr_ip_first <= frag.first && frag.first <= vr_ip_last);
      assert!(vr_ip_first <= frag.last && frag.last <= vr_ip_last);
    }

    // if the CM is empty, we can always accept the assignment.  Otherwise:

    // State updated by the loop
    let mut evict_set = Set::<VirtualRangeIx>::empty();
    let mut evict_cost = SpillCost::zero();

    if self.committed.pairs.len() > 0 {
      // iterate over all points in wlta (the VR)
      let mut vr_ip = vr_ip_first;
      loop {
        if vr_ip > vr_ip_last {
          break;
        }

        // Find out any vr entry contains |vr_ip|, if any.  If not, move on.
        let mut found_in_vr = false;
        for fix in &would_like_to_add_vlr.sorted_frags.frag_ixs {
          let frag = &frag_env[*fix];
          if frag.first <= vr_ip && vr_ip <= frag.last {
            found_in_vr = true;
            break;
          }
        }
        if !found_in_vr {
          vr_ip = step_ip(vr_ip);
          continue; // there can't be any intersection at |vr_ip|
        }

        // Find the cm entry containing |vr_ip|
        let mut pair_ix = 0;
        let mut found = false;
        for pair in &self.committed.pairs {
          let FIxAndVLRIx { fix, mb_vlrix: _ } = pair;
          let frag = &frag_env[*fix];
          if frag.first <= vr_ip && vr_ip <= frag.last {
            found = true;
            break;
          }
          pair_ix += 1;
        }
        if found {
          //debug!("findXX: must evict {:?}", &self.committed.pairs[pair_ix]);
          let evict_possible = handle_CM_entry(
            &mut evict_set,
            &mut evict_cost,
            &self.committed.pairs,
            pair_ix,
            evict_cost_budget,
            &do_not_evict,
            &vlr_env,
            "CX",
          );
          if !evict_possible {
            return None;
          }
        }

        vr_ip = step_ip(vr_ip);
      }
    } // if self.committed.pairs.len() > 0 {

    assert!(evict_cost.is_finite());
    assert!(evict_cost.is_less_than(&evict_cost_budget));
    Some((evict_set, evict_cost))
  }

  #[inline(never)]
  fn find_Evict_Set(
    &self, would_like_to_add: VirtualRangeIx,
    do_not_evict: &Set<VirtualRangeIx>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
    frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> Option<(Set<VirtualRangeIx>, SpillCost)> {
    //let s1 = format!("{:?}", self.committed);
    //let s2 = format!("{:?}", self.committedFAST);
    //debug!("fESF: self.cm  = {}", s1);
    //debug!("fESF: self.cmF = {}", s2);
    //assert!(s1 == s2);

    let result_fast = self.find_Evict_Set_FAST(
      would_like_to_add,
      do_not_evict,
      vlr_env,
      frag_env,
    );

    if CROSSCHECK_CM {
      let result_crosscheck = self.find_Evict_Set_CROSSCHECK(
        would_like_to_add,
        do_not_evict,
        vlr_env,
        frag_env,
      );
      // Big hack.  Note that this hack depends on <Debug for Set> printing
      // set elements in some fixed sequence that depends only on what is in
      // the set, and not on any other factors (eg, the history of how it
      // was constructed.)
      let str_fast: String = format!("{:?}", result_fast);
      let str_crosscheck: String = format!("{:?}", result_crosscheck);
      if str_fast != str_crosscheck {
        println!(
          "QQQQ find_Evict_Set: fast {}, crosscheck {}",
          str_fast, str_crosscheck
        );
        println!("");
        println!("self.commitments = {:?}", self.committed);
        println!("");
        println!("wlta = {:?}", vlr_env[would_like_to_add]);
        println!("");
        println!("");
        panic!("find_Evict_Set: crosscheck failed");
      }
    }

    result_fast
  }

  #[inline(never)]
  fn show1_with_envs(
    &self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> String {
    "in_use:   ".to_string() + &self.committed.show_with_fenv(&fenv)
  }
  #[inline(never)]
  fn show2_with_envs(
    &self, _fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> String {
    "assigned: ".to_string() + &format!("{:?}", &self.vlrixs_assigned)
  }
}

//=============================================================================
// Printing the allocator's top level state

#[inline(never)]
fn print_RA_state(
  who: &str,
  universe: &RealRegUniverse,
  // State components
  prioQ: &VirtualRangePrioQ,
  perRealReg: &Vec<PerRealReg>,
  edit_list_move: &Vec<EditListItem>,
  edit_list_other: &Vec<EditListItem>,
  // The context (environment)
  vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
) {
  debug!("<<<<====---- RA state at '{}' ----====", who);
  for ix in 0..perRealReg.len() {
    if !&perRealReg[ix].committed.pairs.is_empty() {
      debug!(
        "{:<5}  {}",
        universe.regs[ix].1,
        &perRealReg[ix].show1_with_envs(&frag_env)
      );
      debug!("       {}", &perRealReg[ix].show2_with_envs(&frag_env));
      debug!("");
    }
  }
  if !prioQ.is_empty() {
    for s in prioQ.show_with_envs(&vlr_env) {
      debug!("{}", s);
    }
  }
  for eli in edit_list_move {
    debug!("ELI MOVE: {:?}", eli);
  }
  for eli in edit_list_other {
    debug!("ELI other: {:?}", eli);
  }
  debug!(">>>>");
}

//=============================================================================
// Allocator top level

/* (const) For each virtual live range
   - its sorted RangeFrags
   - its total size
   - its spill cost
   - (eventually) its assigned real register
   New VirtualRanges are created as we go, but existing ones are unchanged,
   apart from being tagged with its assigned real register.

   (mut) For each real register
   - the sorted RangeFrags assigned to it (todo: rm the M)
   - the virtual LR indices assigned to it.  This is so we can eject
     a VirtualRange from the commitment, as needed

   (mut) the set of VirtualRanges not yet allocated, prioritised by total size

   (mut) the edit list that is produced
*/
/*
fn show_commit_tab(commit_tab: &Vec::<SortedRangeFragIxs>,
                   who: &str,
                   context: &TypedIxVec::<RangeFragIx, RangeFrag>) -> String {
    let mut res = "Commit Table at '".to_string()
                  + &who.to_string() + &"'\n".to_string();
    let mut rregNo = 0;
    for smf in commit_tab.iter() {
        res += &"  ".to_string();
        res += &mkRealReg(rregNo).show();
        res += &" ".to_string();
        res += &smf.show_with_fenv(&context);
        res += &"\n".to_string();
        rregNo += 1;
    }
    res
}
*/

// VirtualRanges created by spilling all pertain to a single InstIx.  But
// within that InstIx, there are three kinds of "bridges":
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum BridgeKind {
  RtoU, // A bridge for a USE.  This connects the reload to the use.
  RtoS, // a bridge for a MOD.  This connects the reload, the use/def
  // and the spill, since the value must first be reloade, then
  // operated on, and finally re-spilled.
  DtoS, // A bridge for a DEF.  This connects the def to the spill.
}

impl fmt::Debug for BridgeKind {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      BridgeKind::RtoU => write!(fmt, "R->U"),
      BridgeKind::RtoS => write!(fmt, "R->S"),
      BridgeKind::DtoS => write!(fmt, "D->S"),
    }
  }
}

#[derive(Clone, Copy)]
struct EditListItem {
  // This holds enough information to create a spill or reload instruction,
  // or both, and also specifies where in the instruction stream it/they
  // should be added.  Note that if the edit list as a whole specifies
  // multiple items for the same location, then it is assumed that the order
  // in which they execute isn't important.
  //
  // Some of the relevant info can be found via the VirtualRangeIx link:
  // (1) the real reg involved
  // (2) the place where the insn should go, since the VirtualRange should
  //    only have one RangeFrag, and we can deduce the correct location
  //    from that.
  // Despite (2) we also carry here the InstIx of the affected instruction
  // (there should be only one) since computing it via (2) is expensive.
  // This however gives a redundancy in representation against (2).  Beware!
  slot: SpillSlot,
  vlrix: VirtualRangeIx,
  kind: BridgeKind,
  iix: InstIx,
}

impl fmt::Debug for EditListItem {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt,
      "(ELI: at {:?} for {:?} add {:?}, slot={:?})",
      self.iix, self.vlrix, self.kind, self.slot
    )
  }
}

// Allocator top level.  This function returns a result struct that contains
// the final sequence of instructions, possibly with fills/spills/moves
// spliced in and redundant moves elided, and with all virtual registers
// replaced with real registers. Allocation can fail if there are insufficient
// registers to even generate spill/reload code, or if the function appears to
// have any undefined VirtualReg/RealReg uses.

#[inline(never)]
pub fn alloc_main<F: Function>(
  func: &mut F, reg_universe: &RealRegUniverse, use_checker: bool,
) -> Result<RegAllocResult<F>, RegAllocError> {
  // -------- Perform initial liveness analysis --------
  // Note that the analysis phase can fail; hence we propagate any error.
  let (
    reg_vecs_and_bounds,
    rlr_env,
    mut vlr_env,
    mut frag_env,
    _liveouts,
    est_freqs,
  ) = run_analysis(func, reg_universe)
    .map_err(|err| RegAllocError::Analysis(err))?;
  assert!(reg_vecs_and_bounds.is_sanitized());

  // Also perform analysis that finds all coalesing opportunities.
  let coalescing_info = do_coalescing_analysis(
    func,
    &reg_vecs_and_bounds,
    &rlr_env,
    &vlr_env,
    &frag_env,
    &est_freqs,
  );
  let hints: TypedIxVec<VirtualRangeIx, Vec<Hint>> = coalescing_info.0;
  let vlrEquivClasses: UnionFindEquivClasses<VirtualRangeIx> =
    coalescing_info.1;
  let is_vv_boundary_move: TypedIxVec<InstIx, bool> = coalescing_info.2;
  debug_assert!(hints.len() == vlr_env.len());

  // -------- Alloc main --------

  // Create initial state
  info!("alloc_main: begin");
  info!(
    "alloc_main:   in: {} insns in {} blocks",
    func.insns().len(),
    func.blocks().len()
  );
  let num_vlrs_initial = vlr_env.len(); // stats only
  info!("alloc_main:   in: {} VLRs, {} RLRs", num_vlrs_initial, rlr_env.len());

  // This is fully populated by the ::new call.
  let mut prioQ = VirtualRangePrioQ::new(&vlr_env);

  // Whereas this is empty.  We have to populate it "by hand", by
  // effectively cloning the allocatable part (prefix) of the universe.
  let mut per_real_reg = Vec::<PerRealReg>::new();
  for _ in 0..reg_universe.allocable {
    // Doing this instead of simply .resize avoids needing Clone for
    // PerRealReg
    per_real_reg.push(PerRealReg::new());
  }
  for rlr in rlr_env.iter() {
    let rregIndex = rlr.rreg.get_index();
    // Ignore RealRanges for RealRegs that are not part of the allocatable
    // set.  As far as the allocator is concerned, such RealRegs simply
    // don't exist.
    if rregIndex >= reg_universe.allocable {
      continue;
    }
    per_real_reg[rregIndex].add_RealRange(&rlr, &frag_env, &vlr_env);
  }

  let mut edit_list_move = Vec::<EditListItem>::new();
  let mut edit_list_other = Vec::<EditListItem>::new();
  if log_enabled!(Level::Debug) {
    debug!("");
    print_RA_state(
      "Initial",
      &reg_universe,
      &prioQ,
      &per_real_reg,
      &edit_list_move,
      &edit_list_other,
      &vlr_env,
      &frag_env,
    );
  }

  // This is also part of the running state.  |vlr_slot_env| tells us the
  // assigned spill slot for each VirtualRange, if any.
  // |spill_slot_allocator| decides on the assignments and writes them into
  // |vlr_slot_env|.
  let mut vlr_slot_env = TypedIxVec::<VirtualRangeIx, Option<SpillSlot>>::new();
  vlr_slot_env.resize(num_vlrs_initial, None);
  let mut spill_slot_allocator = SpillSlotAllocator::new();

  // Main allocation loop.  Each time round, pull out the longest
  // unallocated VirtualRange, and do one of three things:
  //
  // * allocate it to a RealReg, possibly by ejecting some existing
  //   allocation, but only one with a lower spill cost than this one, or
  //
  // * spill it.  This causes the VirtualRange to disappear.  It is replaced
  //   by a set of very short VirtualRanges to carry the spill and reload
  //   values.  Or,
  //
  // * split it.  This causes it to disappear but be replaced by two
  //   VirtualRanges which together constitute the original.
  debug!("");
  debug!("-- MAIN ALLOCATION LOOP (DI means 'direct', CO means 'coalesced'):");

  // A handy constant
  let empty_Set_VirtualRangeIx = Set::<VirtualRangeIx>::empty();

  info!("alloc_main:   main allocation loop: begin");

  // ======== BEGIN Main allocation loop ========
  let mut num_vlrs_processed = 0; // stats only
  let mut num_vlrs_spilled = 0; // stats only
  let mut num_vlrs_evicted = 0; // stats only

  'main_allocation_loop: loop {
    debug!("-- still TODO          {}", prioQ.len());
    if false {
      if log_enabled!(Level::Debug) {
        debug!("");
        print_RA_state(
          "Loop Top",
          &reg_universe,
          &prioQ,
          &per_real_reg,
          &edit_list_move,
          &edit_list_other,
          &vlr_env,
          &frag_env,
        );
        debug!("");
      }
    }

    let mb_curr_vlrix = prioQ.get_longest_VirtualRange();
    if mb_curr_vlrix.is_none() {
      break 'main_allocation_loop;
    }

    num_vlrs_processed += 1;
    let curr_vlrix = mb_curr_vlrix.unwrap();
    let curr_vlr = &vlr_env[curr_vlrix];

    debug!("--   considering       {:?}:  {:?}", curr_vlrix, curr_vlr);

    assert!(curr_vlr.vreg.to_reg().is_virtual());
    assert!(curr_vlr.rreg.is_none());
    let curr_vlr_regclass = curr_vlr.vreg.get_class();
    let curr_vlr_rc = curr_vlr_regclass.rc_to_usize();

    // ====== BEGIN Try to do coalescing ======
    //
    // First, look through the hints for |curr_vlr|, collecting up candidate
    // real regs, in decreasing order of preference, in |hinted_regs|.  Note
    // that we don't have to consider the weights here, because the coalescing
    // analysis phase has already sorted the hints for the VLR so as to
    // present the most favoured (weighty) first, so we merely need to retain
    // that ordering when copying into |hinted_regs|.
    // FIXME (very) SmallVec
    let mut hinted_regs = Vec::<RealReg>::new();
    let mut mb_curr_vlr_eclass: Option<Set<VirtualRangeIx>> = None;

    // === BEGIN collect all hints for |curr_vlr| ===
    // |hints| has one entry per VLR, but only for VLRs which existed
    // initially (viz, not for any created by spilling/splitting/whatever).
    // Similarly, |vlrEquivClasses| can only map VLRs that existed initially,
    // and will panic otherwise.  Hence the following check:
    if curr_vlrix.get() < hints.len() {
      for hint in &hints[curr_vlrix] {
        // BEGIN for each hint
        let mb_cand = match hint {
          Hint::SameAs(other_vlrix, _weight) => {
            // It wants the same reg as some other VLR, but we can only honour
            // that if the other VLR actually *has* a reg at this point.  Its
            // |rreg| field will tell us exactly that.
            vlr_env[*other_vlrix].rreg
          }
          Hint::Exactly(rreg, _weight) => Some(*rreg),
        };
        // So now |mb_cand| might have a preferred real reg.  If so, add it to
        // the list of cands.  De-dup as we go, since that is way cheaper than
        // effectively doing the same via repeated lookups in the
        // CommitmentMaps.
        if let Some(rreg) = mb_cand {
          if !hinted_regs.iter().any(|r| *r == rreg) {
            hinted_regs.push(rreg);
          }
        }
        // END for each hint
      }

      // At this point, we have in |hinted_regs|, the hint candidates that
      // arise from copies between |curr_vlr| and its immediate neighbouring
      // VLRs or RLRs, in order of declining preference.  And that is a good
      // start.  However, it may be the case that there is some other VLR
      // which is in the same equivalence class as |curr_vlr|, but is not a
      // direct neighbour, and which has already been assigned a register.  We
      // really ought to take those into account too, as the least-preferred
      // candidates.  Hence we need to iterate over the equivalence class and
      // "round up the secondary candidates."
      let n_primary_cands = hinted_regs.len();

      // Find the equivalence class set for |curr_vlrix|.  We'll need it
      // later.
      let mut curr_vlr_eclass = Set::<VirtualRangeIx>::empty();
      for vlrix in vlrEquivClasses.equiv_class_elems_iter(curr_vlrix) {
        curr_vlr_eclass.insert(vlrix);
      }
      assert!(curr_vlr_eclass.contains(curr_vlrix));
      mb_curr_vlr_eclass = Some(curr_vlr_eclass);

      // And work through it to pick up any rreg hints now.
      for vlrix in vlrEquivClasses.equiv_class_elems_iter(curr_vlrix) {
        if vlrix != curr_vlrix {
          if let Some(rreg) = vlr_env[vlrix].rreg {
            // Add |rreg| as a cand, if we don't already have it.
            if !hinted_regs.iter().any(|r| *r == rreg) {
              hinted_regs.push(rreg);
            }
          }
        }
      }

      // Sort the secondary cands, so as to try and impose more consistency
      // across the group.  I don't know if this is worthwhile, but it seems
      // sensible.
      hinted_regs[n_primary_cands..].sort_by(|rreg1, rreg2| {
        rreg1.get_index().partial_cmp(&rreg2.get_index()).unwrap()
      });

      if log_enabled!(Level::Debug) {
        if !hinted_regs.is_empty() {
          let mut candStr = "pri {".to_string();
          for (rreg, n) in hinted_regs.iter().zip(0..) {
            if n == n_primary_cands {
              candStr = candStr + &" } sec {".to_string();
            }
            candStr = candStr
              + &" ".to_string()
              + &reg_universe.regs[rreg.get_index()].1;
          }
          candStr = candStr + &" }";
          debug!("--   CO candidates     {}", candStr);
        }
      }
    }
    // === END collect all hints for |curr_vlr| ===

    // === BEGIN try to use the hints for |curr_vlr| ===
    // Now work through the list of preferences, to see if we can honour any
    // of them.
    for rreg in &hinted_regs {
      let rregNo = rreg.get_index();

      // Find the set of ranges which we'd have to evict in order to honour
      // this hint.  In the best case the set will be empty.  In the worst
      // case, we will get None either because (1) it would require evicting a
      // spill range, which is disallowed so as to guarantee termination of
      // the algorithm, or (2) because it would require evicting a real reg
      // live range, which we can't do.
      //
      // We take care not to evict any range which is in the same equivalence
      // class as |curr_vlr| since those are (by definition) connected to
      // |curr_vlr| via V-V copies, and so evicting any of them would be
      // counterproductive from the point of view of removing copies.

      let do_not_evict = if let Some(ref curr_vlr_eclass) = mb_curr_vlr_eclass {
        curr_vlr_eclass
      } else {
        &empty_Set_VirtualRangeIx
      };
      let mb_evict_info: Option<(Set<VirtualRangeIx>, SpillCost)> =
        per_real_reg[rregNo].find_Evict_Set(
          curr_vlrix,
          do_not_evict, // these are not to be considered for eviction
          &vlr_env,
          &frag_env,
        );
      if let Some((vlrixs_to_evict, total_evict_cost)) = mb_evict_info {
        // Stay sane #1
        assert!(curr_vlr.rreg.is_none());
        // Stay sane #2
        assert!(vlrixs_to_evict.is_empty() == total_evict_cost.is_zero());
        // Can't evict if any in the set are spill ranges
        assert!(total_evict_cost.is_finite());
        // Ensure forward progress
        assert!(total_evict_cost.is_less_than(&curr_vlr.spill_cost));
        // Evict all evictees in the set
        for vlrix_to_evict in vlrixs_to_evict.iter() {
          // Ensure we're not evicting anything in |curr_vlrix|'s eclass.
          // This should be guaranteed us by find_Evict_Set.
          assert!(!do_not_evict.contains(*vlrix_to_evict));
          // Evict ..
          debug!(
            "--   CO evict          {:?}:  {:?}",
            *vlrix_to_evict, &vlr_env[*vlrix_to_evict]
          );
          per_real_reg[rregNo].del_VirtualRange(
            *vlrix_to_evict,
            &frag_env,
            &vlr_env,
          );
          prioQ.add_VirtualRange(&vlr_env, *vlrix_to_evict);
          // Directly modify bits of vlr_env.  This means we have to abandon
          // the immutable borrow for curr_vlr, but that's OK -- we won't need
          // it again (in this loop iteration).
          debug_assert!(vlr_env[*vlrix_to_evict].rreg.is_some());
          vlr_env[*vlrix_to_evict].rreg = None;
          num_vlrs_evicted += 1;
        }
        // .. and reassign.
        debug!("--   CO alloc to       {}", reg_universe.regs[rregNo].1);
        per_real_reg[rregNo].add_VirtualRange(curr_vlrix, &frag_env, &vlr_env);
        vlr_env[curr_vlrix].rreg = Some(*rreg);
        // We're done!
        continue 'main_allocation_loop;
      }
    } /* for rreg in hinted_regs */
    // === END try to use the hints for |curr_vlr| ===

    // ====== END Try to do coalescing ======

    // We get here if we failed to find a viable assignment by the process of
    // looking at the coalescing hints.
    //
    // So: do almost exactly as we did in the "try for coalescing" stage
    // above.  Except, instead of trying each coalescing candidate
    // individually, iterate over all the registers in the class, to find the
    // one (if any) that has the lowest total evict cost.  If we find one that
    // has zero cost -- that is, we can make the assignment without evicting
    // anything -- then stop the search at that point, since searching further
    // is pointless.

    let (first_in_rc, last_in_rc) =
      match &reg_universe.allocable_by_class[curr_vlr_rc] {
        &None => {
          return Err(RegAllocError::OutOfRegisters(curr_vlr_regclass));
        }
        &Some(ref info) => (info.first, info.last),
      };

    let mut best_so_far: Option<(
      /*rreg index*/ usize,
      Set<VirtualRangeIx>,
      SpillCost,
    )> = None;

    'search_through_cand_rregs_loop: for rregNo in first_in_rc..last_in_rc + 1 {
      //debug!("--   Cand              {} ...",
      //       reg_universe.regs[rregNo].1);

      let mb_evict_info: Option<(Set<VirtualRangeIx>, SpillCost)> =
        per_real_reg[rregNo].find_Evict_Set(
          curr_vlrix,
          &empty_Set_VirtualRangeIx,
          &vlr_env,
          &frag_env,
        );
      //
      //match mb_evict_info {
      //  None => debug!("--   Cand              {}: Unavail",
      //                 reg_universe.regs[rregNo].1),
      //  Some((ref evict_set, ref evict_cost)) =>
      //    debug!("--   Cand              {}: Avail, evict cost {:?}, set {:?}",
      //            reg_universe.regs[rregNo].1, evict_cost, evict_set)
      //}
      //
      if let Some((cand_vlrixs_to_evict, cand_total_evict_cost)) = mb_evict_info
      {
        // Stay sane ..
        assert!(
          cand_vlrixs_to_evict.is_empty() == cand_total_evict_cost.is_zero()
        );
        // We can't evict if any in the set are spill ranges, and
        // find_Evict_Set should not offer us that possibility.
        assert!(cand_total_evict_cost.is_finite());
        // Ensure forward progress
        assert!(cand_total_evict_cost.is_less_than(&curr_vlr.spill_cost));
        // Update the "best so far".  First, if the evict set is empty, then
        // the candidate is by definition better than all others, and we will
        // quit searching just below.
        let mut cand_is_better = cand_vlrixs_to_evict.is_empty();
        if !cand_is_better {
          if let Some((_, _, best_spill_cost)) = best_so_far {
            // If we've already got a candidate, this one is better if it has
            // a lower total spill cost.
            if cand_total_evict_cost.is_less_than(&best_spill_cost) {
              cand_is_better = true;
            }
          } else {
            // We don't have any candidate so far, so what we just got is
            // better (than nothing).
            cand_is_better = true;
          }
        }
        // Remember the candidate if required.
        let cand_vlrixs_to_evict_is_empty = cand_vlrixs_to_evict.is_empty();
        if cand_is_better {
          best_so_far =
            Some((rregNo, cand_vlrixs_to_evict, cand_total_evict_cost));
        }
        // If we've found a no-evictions-necessary candidate, quit searching
        // immediately.  We won't find anything better.
        if cand_vlrixs_to_evict_is_empty {
          break 'search_through_cand_rregs_loop;
        }
      }
    } // for rregNo in first_in_rc..last_in_rc + 1 {

    // Examine the results of the search.  Did we find any usable candidate?
    if let Some((rregNo, vlrixs_to_evict, total_spill_cost)) = best_so_far {
      // We are still Totally Paranoid (tm)
      // Stay sane #1
      debug_assert!(curr_vlr.rreg.is_none());
      // Can't spill a spill range
      assert!(total_spill_cost.is_finite());
      // Ensure forward progress
      assert!(total_spill_cost.is_less_than(&curr_vlr.spill_cost));
      // Now the same evict-reassign section as with the coalescing logic above.
      // Evict all evictees in the set
      for vlrix_to_evict in vlrixs_to_evict.iter() {
        // Evict ..
        debug!(
          "--   DI evict          {:?}:  {:?}",
          *vlrix_to_evict, &vlr_env[*vlrix_to_evict]
        );
        per_real_reg[rregNo].del_VirtualRange(
          *vlrix_to_evict,
          &frag_env,
          &vlr_env,
        );
        prioQ.add_VirtualRange(&vlr_env, *vlrix_to_evict);
        debug_assert!(vlr_env[*vlrix_to_evict].rreg.is_some());
        vlr_env[*vlrix_to_evict].rreg = None;
        num_vlrs_evicted += 1;
      }
      // .. and reassign.
      debug!("--   DI alloc to       {}", reg_universe.regs[rregNo].1);
      per_real_reg[rregNo].add_VirtualRange(curr_vlrix, &frag_env, &vlr_env);
      let rreg = reg_universe.regs[rregNo].0;
      vlr_env[curr_vlrix].rreg = Some(rreg);
      // We're done!
      continue 'main_allocation_loop;
    }

    // Still no luck.  We can't find a register to put it in, so we'll
    // have to spill it, since splitting it isn't yet implemented.
    debug!("--   spill");

    // If the live range already pertains to a spill or restore, then
    // it's Game Over.  The constraints (availability of RealRegs vs
    // requirement for them) are impossible to fulfill, and so we cannot
    // generate any valid allocation for this function.
    if curr_vlr.spill_cost.is_infinite() {
      return Err(RegAllocError::OutOfRegisters(curr_vlr_regclass));
    }

    // Generate a new spill slot number, S
    /* Spilling vreg V with virtual live range VirtualRange to slot S:
          for each frag F in VirtualRange {
             for each insn I in F.first.iix .. F.last.iix {
                if I does not mention V
                   continue
                if I mentions V in a Read role {
                   // invar: I cannot mention V in a Mod role
                   add new VirtualRange I.reload -> I.use,
                                        vreg V, spillcost Inf
                   add eli @ I.reload V SpillSlot
                }
                if I mentions V in a Mod role {
                   // invar: I cannot mention V in a Read or Write Role
                   add new VirtualRange I.reload -> I.spill,
                                        Vreg V, spillcost Inf
                   add eli @ I.reload V SpillSlot
                   add eli @ I.spill  SpillSlot V
                }
                if I mentions V in a Write role {
                   // invar: I cannot mention V in a Mod role
                   add new VirtualRange I.def -> I.spill,
                                        vreg V, spillcost Inf
                   add eli @ I.spill V SpillSlot
                }
             }
          }
    */

    // We will be spilling vreg |curr_vlr.reg| with VirtualRange |curr_vlr| to
    // a spill slot that the spill slot allocator will choose for us, just a
    // bit further down this function.

    // This holds enough info to create reload or spill (or both)
    // instructions around an instruction that references a VirtualReg
    // that has been spilled.
    struct SpillAndOrReloadInfo {
      bix: BlockIx,     // that |iix| is in
      iix: InstIx,      // this is the Inst we are spilling/reloading for
      kind: BridgeKind, // says whether to create a spill or reload or both
    }
    let mut sri_vec = Vec::<SpillAndOrReloadInfo>::new();
    let curr_vlr_vreg = curr_vlr.vreg;
    let curr_vlr_reg = curr_vlr_vreg.to_reg();

    for fix in &curr_vlr.sorted_frags.frag_ixs {
      let frag: &RangeFrag = &frag_env[*fix];
      for iix in frag.first.iix.dotdot(frag.last.iix.plus(1)) {
        let (
          iix_uses_curr_vlr_reg,
          iix_defs_curr_vlr_reg,
          iix_mods_curr_vlr_reg,
        ) =
          does_inst_use_def_or_mod_reg(&reg_vecs_and_bounds, iix, curr_vlr_reg);
        // If this insn doesn't mention the vreg we're spilling for,
        // move on.
        if !iix_defs_curr_vlr_reg
          && !iix_mods_curr_vlr_reg
          && !iix_uses_curr_vlr_reg
        {
          continue;
        }
        // USES: Do we need to create a reload-to-use bridge
        // (VirtualRange) ?
        if iix_uses_curr_vlr_reg && frag.contains(&InstPoint::new_use(iix)) {
          debug_assert!(!iix_mods_curr_vlr_reg);
          // Stash enough info that we can create a new VirtualRange
          // and a new edit list entry for the reload.
          let sri =
            SpillAndOrReloadInfo { bix: frag.bix, iix, kind: BridgeKind::RtoU };
          sri_vec.push(sri);
        }
        // MODS: Do we need to create a reload-to-spill bridge?  This
        // can only happen for instructions which modify a register.
        // Note this has to be a single VirtualRange, since if it were
        // two (one for the reload, one for the spill) they could
        // later end up being assigned to different RealRegs, which is
        // obviously nonsensical.
        if iix_mods_curr_vlr_reg
          && frag.contains(&InstPoint::new_use(iix))
          && frag.contains(&InstPoint::new_def(iix))
        {
          debug_assert!(!iix_uses_curr_vlr_reg);
          debug_assert!(!iix_defs_curr_vlr_reg);
          let sri =
            SpillAndOrReloadInfo { bix: frag.bix, iix, kind: BridgeKind::RtoS };
          sri_vec.push(sri);
        }
        // DEFS: Do we need to create a def-to-spill bridge?
        if iix_defs_curr_vlr_reg && frag.contains(&InstPoint::new_def(iix)) {
          debug_assert!(!iix_mods_curr_vlr_reg);
          let sri =
            SpillAndOrReloadInfo { bix: frag.bix, iix, kind: BridgeKind::DtoS };
          sri_vec.push(sri);
        }
      }
    }

    // Now that we no longer need to access |frag_env| or |vlr_env| for
    // the remainder of this iteration of the main allocation loop, we can
    // actually generate the required spill/reload artefacts.

    // First off, poke the spill slot allocator to get an intelligent choice
    // of slot.  Note that this will fail for "non-initial" VirtualRanges; but
    // the only non-initial ones will have been created by spilling anyway,
    // any we definitely shouldn't be trying to spill them again.  Hence we
    // can assert.
    assert!(vlr_slot_env.len() == num_vlrs_initial);
    assert!(curr_vlrix < VirtualRangeIx::new(num_vlrs_initial));
    if vlr_slot_env[curr_vlrix].is_none() {
      // It hasn't been decided yet.  Cause it to be so by asking for an
      // allocation for the entire eclass that |curr_vlrix| belongs to.
      spill_slot_allocator.alloc_spill_slots(
        &mut vlr_slot_env,
        func,
        &frag_env,
        &vlr_env,
        &vlrEquivClasses,
        curr_vlrix,
      );
      assert!(vlr_slot_env[curr_vlrix].is_some());
    }
    let spill_slot_to_use = vlr_slot_env[curr_vlrix].unwrap();

    for sri in sri_vec {
      // For a spill for a MOD use, the new value will be referenced
      // three times.  For DEF and USE uses, it'll only be ref'd twice.
      // (I think we don't care about metrics for the new RangeFrags,
      // though)
      let new_vlr_count = if sri.kind == BridgeKind::RtoS { 3 } else { 2 };
      let (new_vlr_first_pt, new_vlr_last_pt) = match sri.kind {
        BridgeKind::RtoU => (Point::Reload, Point::Use),
        BridgeKind::RtoS => (Point::Reload, Point::Spill),
        BridgeKind::DtoS => (Point::Def, Point::Spill),
      };
      let new_vlr_frag = RangeFrag {
        bix: sri.bix,
        kind: RangeFragKind::Local,
        first: InstPoint::new(sri.iix, new_vlr_first_pt),
        last: InstPoint::new(sri.iix, new_vlr_last_pt),
        count: new_vlr_count,
      };
      let new_vlr_fix = RangeFragIx::new(frag_env.len() as u32);
      frag_env.push(new_vlr_frag);
      debug!(
        "--     new RangeFrag    {:?}  :=  {:?}",
        &new_vlr_fix, &new_vlr_frag
      );
      let new_vlr_sfixs = SortedRangeFragIxs::unit(new_vlr_fix, &frag_env);
      let new_vlr = VirtualRange {
        vreg: curr_vlr_vreg,
        rreg: None,
        sorted_frags: new_vlr_sfixs,
        size: 1,
        spill_cost: SpillCost::infinite(),
      };
      let new_vlrix = VirtualRangeIx::new(vlr_env.len() as u32);
      debug!("--     new VirtRange    {:?}  :=  {:?}", new_vlrix, &new_vlr);
      vlr_env.push(new_vlr);
      prioQ.add_VirtualRange(&vlr_env, new_vlrix);

      let new_eli = EditListItem {
        slot: spill_slot_to_use,
        vlrix: new_vlrix,
        kind: sri.kind,
        iix: sri.iix,
      };
      if is_vv_boundary_move[sri.iix] {
        debug!("--     new ELI MOVE     {:?}", &new_eli);
        edit_list_move.push(new_eli);
      } else {
        debug!("--     new ELI other    {:?}", &new_eli);
        edit_list_other.push(new_eli);
      }
    }

    num_vlrs_spilled += 1;
    // And implicitly "continue 'main_allocation_loop"
  }
  // ======== END Main allocation loop ========

  info!("alloc_main:   main allocation loop: end");

  if log_enabled!(Level::Debug) {
    debug!("");
    print_RA_state(
      "Final",
      &reg_universe,
      &prioQ,
      &per_real_reg,
      &edit_list_move,
      &edit_list_other,
      &vlr_env,
      &frag_env,
    );
  }

  // ======== BEGIN Do spill slot coalescing ========

  debug!("");
  info!("alloc_main:   create spills_n_reloads for MOVE insns");

  // Sort |edit_list_move| by the insn with which each item is associated.
  edit_list_move.sort_unstable_by(|eli1, eli2| eli1.iix.cmp(&eli2.iix));

  // Now go through |edit_list_move| and find pairs which constitute a
  // spillslot-to-the-same-spillslot move.  What we have in |edit_list_move| is
  // heavily constrained, as follows:
  //
  // * each entry should reference an InstIx which the coalescing analysis
  //   identified as a virtual-to-virtual copy which exists at the boundary
  //   between two VirtualRanges.  The "boundary" aspect is important; we
  //   can't coalesce out moves in which the source vreg is not the "last use"
  //   or for which the destination vreg is not the "first def".  (The same is
  //   true for coalescing of unspilled moves).
  //
  // * the each entry must reference a VirtualRange which has only a single
  //   RangeFrag, and that frag must exist entirely "within" the referenced
  //   instruction.  Specifically, it may only be a R->U frag (bridge) or a
  //   D->S frag.
  //
  // * For a referenced instruction, there may be at most two entries in this
  //   list: one that references the R->U frag and one that references the
  //   D->S frag.  Furthermore, the two entries must carry values of the same
  //   RegClass; if that isn't true, the client's |is_move| function is
  //   defective.
  //
  // For any such pair identified, if both frags mention the same spill slot,
  // we skip generating both the reload and the spill instruction.  We also
  // note that the instruction itself is to be deleted (converted to a
  // zero-len nop).  In a sense we have "cancelled out" a reload/spill pair.
  // Entries that can't be cancelled out are handled the same way as for
  // entries in |edit_list_other|, by simply copying them there.
  //
  // Since |edit_list_move| is sorted by insn ix, we can scan linearly over
  // it, looking for adjacent pairs.  We'll have to accept them in either
  // order though (first R->U then D->S, or the other way round).  There's no
  // fixed ordering since there is no particular ordering in the way
  // VirtualRanges are allocated.

  // As a result of spill slot coalescing, we'll need to delete the move
  // instructions leading to a mergable spill slot move.  The insn stream
  // editor can't delete instructions, so instead it'll replace them with zero
  // len nops obtained from the client.  |iixs_to_nop_out| records the insns
  // that this has to happen to.  It is in increasing order of InstIx (because
  // |edit_list_sorted| is), and the indices in it refer to the original
  // virtual-registerised code.
  let mut iixs_to_nop_out = Vec::<InstIx>::new();

  let n_edit_list_move = edit_list_move.len();
  let mut n_edit_list_move_processed = 0; // for assertions only
  let mut i_min = 0;
  loop {
    if i_min >= n_edit_list_move {
      break;
    }
    // Find the bounds of the current group.
    debug!("editlist entry (MOVE): min: {:?}", &edit_list_move[i_min]);
    let i_min_iix = edit_list_move[i_min].iix;
    let mut i_max = i_min;
    while i_max + 1 < n_edit_list_move
      && edit_list_move[i_max + 1].iix == i_min_iix
    {
      i_max += 1;
      debug!("editlist entry (MOVE): max: {:?}", &edit_list_move[i_max]);
    }
    // Current group is from i_min to i_max inclusive.  At most 2 entries are
    // allowed per group.
    assert!(i_max - i_min <= 1);
    // Check for a mergeable pair.
    if i_max - i_min == 1 {
      assert!(is_vv_boundary_move[i_min_iix]);
      let vlrix1 = edit_list_move[i_min].vlrix;
      let vlrix2 = edit_list_move[i_max].vlrix;
      assert!(vlrix1 != vlrix2);
      let vlr1 = &vlr_env[vlrix1];
      let vlr2 = &vlr_env[vlrix2];
      let fixs1 = &vlr1.sorted_frags;
      let fixs2 = &vlr2.sorted_frags;
      assert!(fixs1.frag_ixs.len() == 1);
      assert!(fixs2.frag_ixs.len() == 1);
      let frag1 = &frag_env[fixs1.frag_ixs[0]];
      let frag2 = &frag_env[fixs2.frag_ixs[0]];
      assert!(frag1.first.iix == i_min_iix);
      assert!(frag1.last.iix == i_min_iix);
      assert!(frag2.first.iix == i_min_iix);
      assert!(frag2.last.iix == i_min_iix);
      // frag1 must be R->U and frag2 must be D->S, or vice versa
      match (frag1.first.pt, frag1.last.pt, frag2.first.pt, frag2.last.pt) {
        (Point::Reload, Point::Use, Point::Def, Point::Spill)
        | (Point::Def, Point::Spill, Point::Reload, Point::Use) => {
          let slot1 = edit_list_move[i_min].slot;
          let slot2 = edit_list_move[i_max].slot;
          if slot1 == slot2 {
            // Yay.  We've found a coalescable pair.  We can just ignore the
            // two entries and move on.  Except we have to mark the insn
            // itself for deletion.
            debug!("editlist entry (MOVE): delete {:?}", i_min_iix);
            iixs_to_nop_out.push(i_min_iix);
            i_min = i_max + 1;
            n_edit_list_move_processed += 2;
            continue;
          }
        }
        (_, _, _, _) => {
          panic!("spill slot coalescing, edit_list_move: unexpected frags");
        }
      }
    }
    // If we get here for whatever reason, this group is uninteresting.  Copy
    // in to |edit_list_other| so that it gets processed in the normal way.
    for i in i_min..=i_max {
      edit_list_other.push(edit_list_move[i]);
      n_edit_list_move_processed += 1;
    }
    i_min = i_max + 1;
  }
  assert!(n_edit_list_move_processed == n_edit_list_move);

  // ======== END Do spill slot coalescing ========

  // ======== BEGIN Create all other spills and reloads ========

  debug!("");
  info!("alloc_main:   create spills_n_reloads for other insns");

  // Reload and spill instructions are missing.  To generate them, go through
  // the "edit list", which contains info on both how to generate the
  // instructions, and where to insert them.
  let mut spills_n_reloads = InstsAndPoints::new();
  let mut num_spills = 0; // stats only
  let mut num_reloads = 0; // stats only
  for eli in &edit_list_other {
    debug!("editlist entry (other): {:?}", eli);
    let vlr = &vlr_env[eli.vlrix];
    let vlr_sfrags = &vlr.sorted_frags;
    debug_assert!(vlr.sorted_frags.frag_ixs.len() == 1);
    let vlr_frag = frag_env[vlr_sfrags.frag_ixs[0]];
    let rreg = vlr.rreg.expect("Gen of spill/reload: reg not assigned?!");
    let vreg = vlr.vreg;
    match eli.kind {
      BridgeKind::RtoU => {
        debug_assert!(vlr_frag.first.pt.is_reload());
        debug_assert!(vlr_frag.last.pt.is_use());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnR = InstToInsert::Reload {
          to_reg: Writable::from_reg(rreg),
          from_slot: eli.slot,
          for_vreg: vreg,
        };
        let whereToR = vlr_frag.first;
        spills_n_reloads.push(InstAndPoint::new(whereToR, insnR));
        num_reloads += 1;
      }
      BridgeKind::RtoS => {
        debug_assert!(vlr_frag.first.pt.is_reload());
        debug_assert!(vlr_frag.last.pt.is_spill());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnR = InstToInsert::Reload {
          to_reg: Writable::from_reg(rreg),
          from_slot: eli.slot,
          for_vreg: vreg,
        };
        let whereToR = vlr_frag.first;
        let insnS = InstToInsert::Spill {
          to_slot: eli.slot,
          from_reg: rreg,
          for_vreg: vreg,
        };
        let whereToS = vlr_frag.last;
        spills_n_reloads.push(InstAndPoint::new(whereToR, insnR));
        spills_n_reloads.push(InstAndPoint::new(whereToS, insnS));
        num_reloads += 1;
        num_spills += 1;
      }
      BridgeKind::DtoS => {
        debug_assert!(vlr_frag.first.pt.is_def());
        debug_assert!(vlr_frag.last.pt.is_spill());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnS = InstToInsert::Spill {
          to_slot: eli.slot,
          from_reg: rreg,
          for_vreg: vreg,
        };
        let whereToS = vlr_frag.last;
        spills_n_reloads.push(InstAndPoint::new(whereToS, insnS));
        num_spills += 1;
      }
    }
  }

  // ======== END Create all other spills and reloads ========

  //for pair in &spillsAndReloads {
  //    debug!("spill/reload: {}", pair.show());
  //}

  // Gather up a vector of (RangeFrag, VirtualReg, RealReg) resulting from
  // the previous phase.  This fundamentally is the result of the allocation
  // and tells us how the instruction stream must be edited.  Note it does
  // not take account of spill or reload instructions.  Dealing with those
  // is relatively simple and happens later.

  info!("alloc_main:   create frag_map");

  let mut frag_map = RangeAllocations::new();
  // For each real register under our control ..
  for i in 0..reg_universe.allocable {
    let rreg = reg_universe.regs[i].0;
    // .. look at all the VirtualRanges assigned to it.  And for each such
    // VirtualRange ..
    for vlrix_assigned in per_real_reg[i].vlrixs_assigned.iter() {
      let VirtualRange { vreg, sorted_frags, .. } = &vlr_env[*vlrix_assigned];
      // All the RangeFrags in |vlr_assigned| require |vlr_assigned.reg|
      // to be mapped to the real reg |i|
      // .. collect up all its constituent RangeFrags.
      for fix in &sorted_frags.frag_ixs {
        frag_map.push((*fix, *vreg, rreg));
      }
    }
  }

  info!("alloc_main:   edit_inst_stream");

  let res = edit_inst_stream(
    func,
    spills_n_reloads,
    &iixs_to_nop_out,
    frag_map,
    &frag_env,
    &reg_universe,
    spill_slot_allocator.slots.len() as u32,
    false, // multiple blocks per frag
    use_checker,
  );

  match res {
    Ok(ref rar) => {
      info!(
        "alloc_main:   out: VLRs: {} initially, {} processed",
        num_vlrs_initial, num_vlrs_processed
      );
      info!(
        "alloc_main:   out: VLRs: {} evicted, {} spilled",
        num_vlrs_evicted, num_vlrs_spilled
      );
      info!(
        "alloc_main:   out: insns: {} total, {} spills, {} reloads, {} nopzs",
        rar.insns.len(),
        num_spills,
        num_reloads,
        iixs_to_nop_out.len()
      );
      info!(
        "alloc_main:   out: spill slots: {} used",
        spill_slot_allocator.slots.len()
      );
    }
    Err(_) => {
      info!("alloc_main:   allocation failed!");
    }
  }

  info!("alloc_main: end");

  res
}
