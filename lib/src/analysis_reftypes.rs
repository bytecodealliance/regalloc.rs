//! Performs a simple taint analysis, to find all live ranges that are reftyped.

use crate::data_structures::{
    MoveInfo, MoveInfoElem, RangeId, RealRange, RealRangeIx, RegClass, RegToRangesMaps, TypedIxVec,
    VirtualRange, VirtualRangeIx, VirtualReg,
};
use crate::sparse_set::SparseSet;

pub fn do_reftypes_analysis(
    // From dataflow/liveness analysis.  Modified by setting their is_ref bit.
    rlr_env: &mut TypedIxVec<RealRangeIx, RealRange>,
    vlr_env: &mut TypedIxVec<VirtualRangeIx, VirtualRange>,
    // From dataflow analysis
    reg_to_ranges_maps: &RegToRangesMaps,
    move_info: &MoveInfo,
    // As supplied by the client
    reftype_class: RegClass,
    reftyped_vregs: &Vec<VirtualReg>,
) {
    // The game here is: starting with `reftyped_vregs`, find *all* the VirtualRanges and
    // RealRanges to which that refness can flow, via instructions which the client's `is_move`
    // function considers to be moves.

    // We have `move_info`, which tells us which regs (both real and virtual) are connected by
    // moves.  However, that's not directly useful -- we need to know which *ranges* are
    // connected by moves.  So first, convert `move_info` into a set of range-pairs.

    let mut range_pairs = Vec::<(RangeId, RangeId)>::new(); // (DST, SRC)

    for MoveInfoElem {
        dst: dst_reg,
        src: src_reg,
        iix: _,
        est_freq: _,
    } in &move_info.moves
    {
        debug_assert!(dst_reg.get_class() == src_reg.get_class());

        // Don't waste time processing moves which can't possibly be of reftyped values.
        if dst_reg.get_class() != reftype_class {
            continue;
        }

        // This is kinda tiresome because of the differing representations, but .. construct the
        // cartesian product of the range indicies for both the source and destination of the
        // move.

        let dst_reg_ix = dst_reg.get_index();
        let src_reg_ix = src_reg.get_index();
        match (dst_reg.is_real(), src_reg.is_real()) {
            (true, true) => {
                // R <- R
                for dst_ix in &reg_to_ranges_maps.rreg_to_rlrs_map[dst_reg_ix] {
                    for src_ix in &reg_to_ranges_maps.rreg_to_rlrs_map[src_reg_ix] {
                        range_pairs.push((RangeId::new_real(*dst_ix), RangeId::new_real(*src_ix)));
                    }
                }
            }
            (true, false) => {
                // R <- V
                for dst_ix in &reg_to_ranges_maps.rreg_to_rlrs_map[dst_reg_ix] {
                    for src_ix in &reg_to_ranges_maps.vreg_to_vlrs_map[src_reg_ix] {
                        range_pairs
                            .push((RangeId::new_real(*dst_ix), RangeId::new_virtual(*src_ix)));
                    }
                }
            }
            (false, true) => {
                // V <- R
                for dst_ix in &reg_to_ranges_maps.vreg_to_vlrs_map[dst_reg_ix] {
                    for src_ix in &reg_to_ranges_maps.rreg_to_rlrs_map[src_reg_ix] {
                        range_pairs
                            .push((RangeId::new_virtual(*dst_ix), RangeId::new_real(*src_ix)));
                    }
                }
            }
            (false, false) => {
                // V <- V
                for dst_ix in &reg_to_ranges_maps.vreg_to_vlrs_map[dst_reg_ix] {
                    for src_ix in &reg_to_ranges_maps.vreg_to_vlrs_map[src_reg_ix] {
                        range_pairs
                            .push((RangeId::new_virtual(*dst_ix), RangeId::new_virtual(*src_ix)));
                    }
                }
            }
        }
    }

    // We have to hand the range-pairs that must be a superset of the moves that could possibly
    // carry reftyped values.  Now compute the starting set of reftyped virtual ranges.  This
    // can serve as the starting value for the following fixpoint iteration.

    let mut reftyped_ranges = SparseSet::<RangeId>::empty();
    for vreg in reftyped_vregs {
        // If this fails, the client has been telling is that some virtual reg is reftyped, yet
        // it doesn't belong to the class of regs that it claims can carry refs.  So the client
        // is buggy.
        debug_assert!(vreg.get_class() == reftype_class);
        for vlrix in &reg_to_ranges_maps.vreg_to_vlrs_map[vreg.get_index()] {
            reftyped_ranges.insert(RangeId::new_virtual(*vlrix));
        }
    }

    // Now, finally, compute the fixpoint resulting from repeatedly mapping `reftyped_ranges`
    // through `range_pairs`. XXXX this looks dangerously expensive .. reimplement.
    //
    // Later .. this is overkill.  All that is needed is a DFS of the directed graph in which
    // the nodes are the union of the RealRange(Ixs) and the VirtualRange(Ixs), and whose edges
    // are exactly what we computed into `range_pairs`.  This graph then needs to be searched
    // from each root in `reftyped_ranges`.
    loop {
        let card_before = reftyped_ranges.card();

        for (dst_lr_id, src_lr_id) in &range_pairs {
            if reftyped_ranges.contains(*src_lr_id) {
                reftyped_ranges.insert(*dst_lr_id);
            }
        }

        let card_after = reftyped_ranges.card();
        if card_after == card_before {
            // Since we're only ever adding items to `reftyped_ranges`, and it has set
            // semantics, checking that the cardinality is unchanged is an adequate check for
            // having reached a (the minimal?) fixpoint.
            break;
        }
    }

    // Finally, annotate rlr_env/vlr_env with the results of the analysis.  (That was the whole
    // point!)
    for lr_id in reftyped_ranges.iter() {
        if lr_id.is_real() {
            let rrange = &mut rlr_env[lr_id.to_real()];
            debug_assert!(!rrange.is_ref);
            rrange.is_ref = true;
        } else {
            let vrange = &mut vlr_env[lr_id.to_virtual()];
            debug_assert!(!vrange.is_ref);
            vrange.is_ref = true;
        }
    }
}
