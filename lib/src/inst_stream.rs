/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

use log::debug;
use std::fmt;

use crate::data_structures::{
  mkBlockIx, mkInstIx, BlockIx, InstIx, InstPoint, InstPoint_Reload,
  InstPoint_Spill, Map, RangeFrag, RangeFragIx, RealReg, Set, SpillSlot,
  TypedIxVec, VirtualRange, VirtualRangeIx, VirtualReg,
};
use crate::interface::{Function, RegAllocResult};

//=============================================================================
// Edit list items

// VirtualRanges created by spilling all pertain to a single InstIx.  But
// within that InstIx, there are three kinds of "bridges":
#[derive(PartialEq)]
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

pub(crate) struct EditListItem {
  // This holds enough information to create a spill or reload instruction,
  // or both, and also specifies where in the instruction stream it/they
  // should be added.  Note that if the edit list as a whole specifies
  // multiple items for the same location, then it is assumed that the order
  // in which they execute isn't important.
  //
  // Some of the relevant info can be found via the VirtualRangeIx link:
  // * the real reg involved
  // * the place where the insn should go, since the VirtualRange should only
  //   have one RangeFrag, and we can deduce the correct location from that.
  pub slot: SpillSlot,
  pub vlrix: VirtualRangeIx,
  pub kind: BridgeKind,
}

impl fmt::Debug for EditListItem {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt,
      "ELI {{ for {:?} add '{:?}' {:?} }}",
      self.vlrix, self.kind, self.slot
    )
  }
}

pub(crate) type EditList = Vec<EditListItem>;

pub(crate) type RangeAllocations = Vec<(RangeFragIx, VirtualReg, RealReg)>;

pub(crate) fn edit_inst_stream<F: Function>(
  func: &mut F, edit_list: EditList, frag_map: RangeAllocations,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>, num_spill_slots: u32,
) -> Result<RegAllocResult<F>, String> {
  // Make two copies of the fragment mapping, one sorted by the fragment start
  // points (just the InstIx numbers, ignoring the Point), and one sorted by
  // fragment end points.
  let mut frag_maps_by_start = frag_map.clone();
  let mut frag_maps_by_end = frag_map;

  // -------- Edit the instruction stream --------
  frag_maps_by_start.sort_unstable_by(
    |(frag_ix, _, _), (other_frag_ix, _, _)| {
      frag_env[*frag_ix]
        .first
        .iix
        .partial_cmp(&frag_env[*other_frag_ix].first.iix)
        .unwrap()
    },
  );

  frag_maps_by_end.sort_unstable_by(
    |(frag_ix, _, _), (other_frag_ix, _, _)| {
      frag_env[*frag_ix]
        .last
        .iix
        .partial_cmp(&frag_env[*other_frag_ix].last.iix)
        .unwrap()
    },
  );

  //debug!("Firsts: {}", fragMapsByStart.show());
  //debug!("Lasts:  {}", fragMapsByEnd.show());

  let mut cursor_starts = 0;
  let mut cursor_ends = 0;

  let mut map = Map::<VirtualReg, RealReg>::default();

  //fn showMap(m: &Map<VirtualReg, RealReg>) -> String {
  //  let mut vec: Vec<(&VirtualReg, &RealReg)> = m.iter().collect();
  //  vec.sort_by(|p1, p2| p1.0.partial_cmp(p2.0).unwrap());
  //  format!("{:?}", vec)
  //}

  fn is_sane(frag: &RangeFrag) -> bool {
    // "Normal" frag (unrelated to spilling).  No normal frag may start or
    // end at a .s or a .r point.
    if frag.first.pt.isUseOrDef()
      && frag.last.pt.isUseOrDef()
      && frag.first.iix <= frag.last.iix
    {
      return true;
    }
    // A spill-related ("bridge") frag.  There are three possibilities,
    // and they correspond exactly to |BridgeKind|.
    if frag.first.pt.isReload()
      && frag.last.pt.isUse()
      && frag.last.iix == frag.first.iix
    {
      // BridgeKind::RtoU
      return true;
    }
    if frag.first.pt.isReload()
      && frag.last.pt.isSpill()
      && frag.last.iix == frag.first.iix
    {
      // BridgeKind::RtoS
      return true;
    }
    if frag.first.pt.isDef()
      && frag.last.pt.isSpill()
      && frag.last.iix == frag.first.iix
    {
      // BridgeKind::DtoS
      return true;
    }
    // None of the above apply.  This RangeFrag is insane \o/
    false
  }

  for insnIx in func.insn_indices() {
    //debug!("");
    //debug!("QQQQ insn {}: {}",
    //         insnIx, func.insns[insnIx].show());
    //debug!("QQQQ init map {}", showMap(&map));
    // advance [cursorStarts, +numStarts) to the group for insnIx
    while cursor_starts < frag_maps_by_start.len()
      && frag_env[frag_maps_by_start[cursor_starts].0].first.iix < insnIx
    {
      cursor_starts += 1;
    }
    let mut numStarts = 0;
    while cursor_starts + numStarts < frag_maps_by_start.len()
      && frag_env[frag_maps_by_start[cursor_starts + numStarts].0].first.iix
        == insnIx
    {
      numStarts += 1;
    }

    // advance [cursorEnds, +numEnds) to the group for insnIx
    while cursor_ends < frag_maps_by_end.len()
      && frag_env[frag_maps_by_end[cursor_ends].0].last.iix < insnIx
    {
      cursor_ends += 1;
    }
    let mut numEnds = 0;
    while cursor_ends + numEnds < frag_maps_by_end.len()
      && frag_env[frag_maps_by_end[cursor_ends + numEnds].0].last.iix == insnIx
    {
      numEnds += 1;
    }

    // So now, fragMapsByStart[cursorStarts, +numStarts) are the mappings
    // for fragments that begin at this instruction, in no particular
    // order.  And fragMapsByEnd[cursorEnd, +numEnd) are the RangeFragIxs
    // for fragments that end at this instruction.

    //debug!("insn no {}:", insnIx);
    //for j in cursorStarts .. cursorStarts + numStarts {
    //    debug!("   s: {} {}",
    //             (fragMapsByStart[j].1, fragMapsByStart[j].2).show(),
    //             frag_env[ fragMapsByStart[j].0 ]
    //             .show());
    //}
    //for j in cursorEnds .. cursorEnds + numEnds {
    //    debug!("   e: {} {}",
    //             (fragMapsByEnd[j].1, fragMapsByEnd[j].2).show(),
    //             frag_env[ fragMapsByEnd[j].0 ]
    //             .show());
    //}

    // Sanity check all frags.  In particular, reload and spill frags are
    // heavily constrained.  No functional effect.
    for j in cursor_starts..cursor_starts + numStarts {
      let frag = &frag_env[frag_maps_by_start[j].0];
      // "It really starts here, as claimed."
      debug_assert!(frag.first.iix == insnIx);
      debug_assert!(is_sane(&frag));
    }
    for j in cursor_ends..cursor_ends + numEnds {
      let frag = &frag_env[frag_maps_by_end[j].0];
      // "It really ends here, as claimed."
      debug_assert!(frag.last.iix == insnIx);
      debug_assert!(is_sane(frag));
    }

    // Here's the plan, in summary:
    // Update map for I.r:
    //   add frags starting at I.r
    //   no frags should end at I.r (it's a reload insn)
    // Update map for I.u:
    //   add frags starting at I.u
    //   mapU := map
    //   remove frags ending at I.u
    // Update map for I.d:
    //   add frags starting at I.d
    //   mapD := map
    //   remove frags ending at I.d
    // Update map for I.s:
    //   no frags should start at I.s (it's a spill insn)
    //   remove frags ending at I.s
    // apply mapU/mapD to I

    //debug!("QQQQ mapping insn {:?}", insnIx);
    //debug!("QQQQ current map {}", showMap(&map));

    // Update map for I.r:
    //   add frags starting at I.r
    //   no frags should end at I.r (it's a reload insn)
    for j in cursor_starts..cursor_starts + numStarts {
      let frag = &frag_env[frag_maps_by_start[j].0];
      if frag.first.pt.isReload() {
        //////// STARTS at I.r
        map.insert(frag_maps_by_start[j].1, frag_maps_by_start[j].2);
        //debug!(
        //  "QQQQ inserted frag from reload: {:?} -> {:?}",
        //  fragMapsByStart[j].1, fragMapsByStart[j].2
        //);
      }
    }

    // Update map for I.u:
    //   add frags starting at I.u
    //   mapU := map
    //   remove frags ending at I.u
    for j in cursor_starts..cursor_starts + numStarts {
      let frag = &frag_env[frag_maps_by_start[j].0];
      if frag.first.pt.isUse() {
        //////// STARTS at I.u
        map.insert(frag_maps_by_start[j].1, frag_maps_by_start[j].2);
        //debug!(
        //  "QQQQ inserted frag from use: {:?} -> {:?}",
        //  fragMapsByStart[j].1, fragMapsByStart[j].2
        //);
      }
    }
    let mapU = map.clone();
    for j in cursor_ends..cursor_ends + numEnds {
      let frag = &frag_env[frag_maps_by_end[j].0];
      if frag.last.pt.isUse() {
        //////// ENDS at I.U
        map.remove(&frag_maps_by_end[j].1);
        //debug!("QQQQ removed frag after use: {:?}", fragMapsByStart[j].1);
      }
    }

    // Update map for I.d:
    //   add frags starting at I.d
    //   mapD := map
    //   remove frags ending at I.d
    for j in cursor_starts..cursor_starts + numStarts {
      let frag = &frag_env[frag_maps_by_start[j].0];
      if frag.first.pt.isDef() {
        //////// STARTS at I.d
        map.insert(frag_maps_by_start[j].1, frag_maps_by_start[j].2);
        //debug!(
        //  "QQQQ inserted frag from def: {:?} -> {:?}",
        //  fragMapsByStart[j].1, fragMapsByStart[j].2
        //);
      }
    }
    let mapD = map.clone();
    for j in cursor_ends..cursor_ends + numEnds {
      let frag = &frag_env[frag_maps_by_end[j].0];
      if frag.last.pt.isDef() {
        //////// ENDS at I.d
        map.remove(&frag_maps_by_end[j].1);
        //debug!("QQQQ ended frag from def: {:?}", fragMapsByEnd[j].1);
      }
    }

    // Update map for I.s:
    //   no frags should start at I.s (it's a spill insn)
    //   remove frags ending at I.s
    for j in cursor_ends..cursor_ends + numEnds {
      let frag = &frag_env[frag_maps_by_end[j].0];
      if frag.last.pt.isSpill() {
        //////// ENDS at I.s
        map.remove(&frag_maps_by_end[j].1);
        //debug!("QQQQ ended frag from spill: {:?}", fragMapsByEnd[j].1);
      }
    }

    //debug!("QQQQ mapU {}", showMap(&mapU));
    //debug!("QQQQ mapD {}", showMap(&mapD));

    // Finally, we have mapU/mapD set correctly for this instruction.
    // Apply it.
    let mut insn = func.get_insn_mut(insnIx);
    F::map_regs(&mut insn, &mapU, &mapD);

    // Update cursorStarts and cursorEnds for the next iteration
    cursor_starts += numStarts;
    cursor_ends += numEnds;

    for b in func.blocks() {
      if func.block_insns(b).last() == insnIx {
        //debug!("Block end");
        debug_assert!(map.is_empty());
      }
    }
  }

  debug_assert!(map.is_empty());

  // At this point, we've successfully pushed the vreg->rreg assignments
  // into the original instructions.  But the reload and spill instructions
  // are missing.  To generate them, go through the "edit list", which
  // contains info on both how to generate the instructions, and where to
  // insert them.
  let mut spills_and_reloads = Vec::<(InstPoint, F::Inst)>::new();
  for eli in &edit_list {
    debug!("editlist entry: {:?}", eli);
    let vlr = &vlr_env[eli.vlrix];
    let vlr_sfrags = &vlr.sorted_frags;
    debug_assert!(vlr.sorted_frags.fragIxs.len() == 1);
    let vlr_frag = frag_env[vlr_sfrags.fragIxs[0]];
    let rreg = vlr.rreg.expect("Gen of spill/reload: reg not assigned?!");
    match eli.kind {
      BridgeKind::RtoU => {
        debug_assert!(vlr_frag.first.pt.isReload());
        debug_assert!(vlr_frag.last.pt.isUse());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnR = func.gen_reload(rreg, eli.slot);
        let whereToR = vlr_frag.first;
        spills_and_reloads.push((whereToR, insnR));
      }
      BridgeKind::RtoS => {
        debug_assert!(vlr_frag.first.pt.isReload());
        debug_assert!(vlr_frag.last.pt.isSpill());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnR = func.gen_reload(rreg, eli.slot);
        let whereToR = vlr_frag.first;
        let insnS = func.gen_spill(eli.slot, rreg);
        let whereToS = vlr_frag.last;
        spills_and_reloads.push((whereToR, insnR));
        spills_and_reloads.push((whereToS, insnS));
      }
      BridgeKind::DtoS => {
        debug_assert!(vlr_frag.first.pt.isDef());
        debug_assert!(vlr_frag.last.pt.isSpill());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnS = func.gen_spill(eli.slot, rreg);
        let whereToS = vlr_frag.last;
        spills_and_reloads.push((whereToS, insnS));
      }
    }
  }

  //for pair in &spillsAndReloads {
  //    debug!("spill/reload: {}", pair.show());
  //}

  // Construct the final code by interleaving the mapped code with the
  // spills and reloads.  To do that requires having the latter sorted by
  // InstPoint.
  //
  // We also need to examine and update Func::blocks.  This is assumed to
  // be arranged in ascending order of the Block::start fields.

  spills_and_reloads
    .sort_unstable_by(|(ip1, _), (ip2, _)| ip1.partial_cmp(ip2).unwrap());

  let mut curSnR = 0; // cursor in |spillsAndReloads|
  let mut curB = mkBlockIx(0); // cursor in Func::blocks

  let mut insns: Vec<F::Inst> = vec![];
  let mut target_map: TypedIxVec<BlockIx, InstIx> = TypedIxVec::new();
  let mut clobbered_registers: Set<RealReg> = Set::empty();

  for iix in func.insn_indices() {
    // Is |iix| the first instruction in a block?  Meaning, are we
    // starting a new block?
    debug_assert!(curB.get() < func.blocks().len() as u32);
    if func.block_insns(curB).start() == iix {
      assert!(curB.get() == target_map.len());
      target_map.push(mkInstIx(insns.len() as u32));
    }

    // Copy reloads for this insn
    while curSnR < spills_and_reloads.len()
      && spills_and_reloads[curSnR].0 == InstPoint_Reload(iix)
    {
      insns.push(spills_and_reloads[curSnR].1.clone());
      curSnR += 1;
    }
    // And the insn itself
    insns.push(func.get_insn(iix).clone());
    // Copy spills for this insn
    while curSnR < spills_and_reloads.len()
      && spills_and_reloads[curSnR].0 == InstPoint_Spill(iix)
    {
      insns.push(spills_and_reloads[curSnR].1.clone());
      curSnR += 1;
    }

    // Is |iix| the last instruction in a block?
    if iix == func.block_insns(curB).last() {
      debug_assert!(curB.get() < func.blocks().len() as u32);
      curB = curB.plus(1);
    }
  }

  debug_assert!(curSnR == spills_and_reloads.len());
  debug_assert!(curB.get() == func.blocks().len() as u32);

  // Compute clobbered registers with one final, quick pass.
  //
  // TODO: derive this information directly from the allocation data
  // structures used above.
  for insn in insns.iter() {
    let reg_usage = func.get_regs(insn);
    for reg in reg_usage.modified.iter().chain(reg_usage.defined.iter()) {
      assert!(reg.is_real());
      clobbered_registers.insert(reg.to_real_reg());
    }
  }

  // And we're done!

  Ok(RegAllocResult { insns, target_map, clobbered_registers, num_spill_slots })
}
