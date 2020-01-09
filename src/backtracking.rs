//! Core implementation of the backtracking allocator.

use crate::data_structures::{
    BlockIx, Set, Func, Map, TVec, mkBlockIx, Reg, FragIx, Vec_Frag, InsnPoint, Show, mkInsnIx, InsnPoint_U, InsnPoint_D, Frag, mkFrag, mkFragIx, Vec_RLR, Vec_VLR, FragKind,
    SortedFragIxs, RLR, VLR, Vec_Block,
    VLRIx, mkVLRIx, Slot, mkRReg, InsnIx, Reg_V, Insn, Point, mkInsnPoint, mkSlot, RReg, VReg, i_spill, i_reload, Vec_Insn, Block, InsnPoint_R, InsnPoint_S
};
use crate::analysis::run_analysis;

fn cost_is_less(cost1: Option<f32>, cost2: Option<f32>) -> bool {
    // None denotes "infinity", while Some(_) is some number less than
    // infinity.  No matter that the enclosed f32 can denote its own infinity
    // :-/ (they never actually should be infinity, nor negative, nor any
    // denormal either).
    match (cost1, cost2) {
        (None,     None)     => false,
        (Some(_),  None)     => true,
        (None,     Some(_))  => false,
        (Some(f1), Some(f2)) => f1 < f2
    }
}

//=============================================================================
// The as-yet-unallocated VReg LR prio queue
//
// Relevant methods are parameterised by a VLR env.

struct VLRPrioQ {
    // The set of as-yet unallocated VLRs.  These are indexes into a VLR env
    // that is not stored here.  These indices can come and go.
    unallocated: Vec::<VLRIx>
}
impl VLRPrioQ {
    fn new(vlr_env: &Vec_VLR) -> Self {
        let mut res = Self { unallocated: Vec::new() };
        for vlrix in mkVLRIx(0) .dotdot( mkVLRIx(vlr_env.len()) ) {
            assert!(vlr_env[vlrix].size > 0);
            res.unallocated.push(vlrix);
        }
        res
    }

    #[inline(never)]
    fn is_empty(&self) -> bool {
        self.unallocated.is_empty()
    }

    // Add a VLR index.
    #[inline(never)]
    fn add_VLR(&mut self, vlr_ix: VLRIx) {
        self.unallocated.push(vlr_ix);
    }

    // Look in |unallocated| to locate the entry referencing the VLR with the
    // largest |size| value.  Remove the ref from |unallocated| and return the
    // LRIx for said entry.
    #[inline(never)]
    fn get_longest_VLR(&mut self, vlr_env: &Vec_VLR) -> Option<VLRIx> {
        if self.unallocated.len() == 0 {
            return None;
        }
        let mut largestIx   = self.unallocated.len(); /*INVALID*/
        let mut largestSize = 0; /*INVALID*/
        for i in 0 .. self.unallocated.len() {
            let cand_vlrix = self.unallocated[i];
            let cand_vlr = &vlr_env[cand_vlrix];
            if cand_vlr.size > largestSize {
                largestSize = cand_vlr.size;
                largestIx   = i;
            }
        }
        // We must have found *something* since there was at least one
        // unallocated VLR still available.
        debug_assert!(largestIx < self.unallocated.len());
        debug_assert!(largestSize > 0);
        // What we will return
        let res = self.unallocated[largestIx];
        // Remove the selected |unallocated| entry in constant time.
        self.unallocated[largestIx] =
            self.unallocated[self.unallocated.len() - 1];
        self.unallocated.remove(self.unallocated.len() - 1);
        Some(res)
    }

    #[inline(never)]
    fn show_with_envs(&self, vlr_env: &Vec_VLR) -> String {
        let mut res = "".to_string();
        let mut first = true;
        for vlrix in self.unallocated.iter() {
            if !first { res += &"\n".to_string(); }
            first = false;
            res += &"TODO  ".to_string();
            res += &vlr_env[*vlrix].show();
        }
        res
    }
}

//=============================================================================
// The per-real-register state
//
// Relevant methods are expected to be parameterised by the same VLR env as
// used in calls to |VLRPrioQ|.

struct PerRReg {
    // The current committed fragments for this RReg.
    frags_in_use: SortedFragIxs,

    // The VLRs which have been assigned to this RReg, in no particular order.
    // The union of their frags will be equal to |frags_in_use| only if this
    // RReg has no RLRs.  If this RReg does have RLRs the aforementioned union
    // will be exactly the subset of |frags_in_use| not used by the RLRs.
    vlrixs_assigned: Vec::<VLRIx>
}
impl PerRReg {
    fn new(fenv: &Vec_Frag) -> Self {
        Self {
            frags_in_use: SortedFragIxs::new(&vec![], fenv),
            vlrixs_assigned: Vec::<VLRIx>::new()
        }
    }

    #[inline(never)]
    fn add_RLR(&mut self, to_add: &RLR, fenv: &Vec_Frag) {
        // Commit this register to |to_add|, irrevocably.  Don't add it to
        // |vlrixs_assigned| since we will never want to later evict the
        // assignment.
        self.frags_in_use.add(&to_add.sfrags, fenv);
    }

    #[inline(never)]
    fn can_add_VLR_without_eviction(&self, to_add: &VLR,
                                    fenv: &Vec_Frag) -> bool {
        self.frags_in_use.can_add(&to_add.sfrags, fenv)
    }

    #[inline(never)]
    fn add_VLR(&mut self, to_add_vlrix: VLRIx,
               vlr_env: &Vec_VLR, fenv: &Vec_Frag) {
        let vlr = &vlr_env[to_add_vlrix];
        self.frags_in_use.add(&vlr.sfrags, fenv);
        self.vlrixs_assigned.push(to_add_vlrix);
    }

    #[inline(never)]
    fn del_VLR(&mut self, to_del_vlrix: VLRIx,
               vlr_env: &Vec_VLR, fenv: &Vec_Frag) {
        debug_assert!(self.vlrixs_assigned.len() > 0);
        // Remove it from |vlrixs_assigned|
        let mut found = None;
        for i in 0 .. self.vlrixs_assigned.len() {
            if self.vlrixs_assigned[i] == to_del_vlrix {
                found = Some(i);
                break;
            }
        }
        if let Some(i) = found {
            self.vlrixs_assigned[i]
                = self.vlrixs_assigned[self.vlrixs_assigned.len() - 1];
            self.vlrixs_assigned.remove(self.vlrixs_assigned.len() - 1);
        } else {
            panic!("PerRReg: del_VLR on VLR that isn't in vlrixs_assigned");
        }
        // Remove it from |frags_in_use|
        let vlr = &vlr_env[to_del_vlrix];
        self.frags_in_use.del(&vlr.sfrags, fenv);
    }

    #[inline(never)]
    fn find_best_evict_VLR(&self, would_like_to_add: &VLR,
                           vlr_env: &Vec_VLR,
                           frag_env: &Vec_Frag)
                           -> Option<(VLRIx, f32)> {
        // |would_like_to_add| presumably doesn't fit here.  See if eviction
        // of any of the existing LRs would make it allocable, and if so
        // return that LR and its cost.  Valid candidates VLRs must meet
        // the following criteria:
        // - must be assigned to this register (obviously)
        // - must have a non-infinite spill cost
        //   (since we don't want to eject spill/reload LRs)
        // - must have a spill cost less than that of |would_like_to_add|
        //   (so as to guarantee forward progress)
        // - removal of it must actually make |would_like_to_add| allocable
        //   (otherwise all this is pointless)
        let mut best_so_far: Option<(VLRIx, f32)> = None;
        for cand_vlrix in &self.vlrixs_assigned {
            let cand_vlr = &vlr_env[*cand_vlrix];
            if cand_vlr.cost.is_none() {
                continue;
            }
            let cand_cost = cand_vlr.cost.unwrap();
            if !cost_is_less(Some(cand_cost), would_like_to_add.cost) {
                continue;
            }
            if !self.frags_in_use
                    .can_add_if_we_first_del(&cand_vlr.sfrags,
                                             &would_like_to_add.sfrags,
                                             frag_env) {
                continue;
            }
            // Ok, it's at least a valid candidate.  But is it better than
            // any candidate we might already have?
            let mut cand_is_better = true;
            if let Some((_, best_cost)) = best_so_far {
                if cost_is_less(Some(best_cost), Some(cand_cost)) {
                    cand_is_better = false;
                }
            }
            if cand_is_better {
                // Either this is the first possible candidate we've seen, or
                // it's better than any previous one.  In either case, make
                // note of it.
                best_so_far = Some((*cand_vlrix, cand_cost));
            }
        }
        best_so_far
    }

    #[inline(never)]
    fn show1_with_envs(&self, fenv: &Vec_Frag) -> String {
        "in_use:   ".to_string() + &self.frags_in_use.show_with_fenv(&fenv)
    }
    #[inline(never)]
    fn show2_with_envs(&self, fenv: &Vec_Frag) -> String {
        "assigned: ".to_string() + &self.vlrixs_assigned.show()
    }
}

//=============================================================================
// Edit list items

// VLRs created by spilling all pertain to a single InsnIx.  But within that
// InsnIx, there are three kinds of "bridges":
#[derive(PartialEq)]
enum BridgeKind {
    RtoU, // A bridge for a USE.  This connects the reload to the use.
    RtoS, // a bridge for a MOD.  This connects the reload, the use/def
          // and the spill, since the value must first be reloade, then
          // operated on, and finally re-spilled.
    DtoS  // A bridge for a DEF.  This connects the def to the spill.
}
impl Show for BridgeKind {
    fn show(&self) -> String {
        match self {
            BridgeKind::RtoU => "R->U".to_string(),
            BridgeKind::RtoS => "R->S".to_string(),
            BridgeKind::DtoS => "D->S".to_string()
        }
    }
}


struct EditListItem {
    // This holds enough information to create a spill or reload instruction,
    // or both, and also specifies where in the instruction stream it/they
    // should be added.  Note that if the edit list as a whole specifies
    // multiple items for the same location, then it is assumed that the order
    // in which they execute isn't important.
    //
    // Some of the relevant info can be found via the VLRIx link:
    // * the real reg involved
    // * the place where the insn should go, since the VLR should only have
    //   one Frag, and we can deduce the correct location from that.
    slot:  Slot,
    vlrix: VLRIx,
    kind:  BridgeKind
}
impl Show for EditListItem {
    fn show(&self) -> String {
        "ELI { for ".to_string() + &self.vlrix.show() + &" add '".to_string()
            + &self.kind.show() + &"' ".to_string() + &self.slot.show()
            + &" }".to_string()
    }
}

//=============================================================================
// Printing the allocator's top level state

#[inline(never)]
fn print_RA_state(who: &str,
                  // State components
                  prioQ: &VLRPrioQ, perRReg: &Vec::<PerRReg>,
                  editList: &Vec::<EditListItem>,
                  // The context (environment)
                  vlr_env: &Vec_VLR, frag_env: &Vec_Frag)
{
    println!("<<<<====---- RA state at '{}' ----====", who);
    for ix in 0 .. perRReg.len() {
        println!("{:<3}   {}\n      {}",
                 mkRReg(ix as u32).show(),
                 &perRReg[ix].show1_with_envs(&frag_env),
                 &perRReg[ix].show2_with_envs(&frag_env));
        println!("");
    }
    if !prioQ.is_empty() {
        println!("{}", prioQ.show_with_envs(&vlr_env));
    }
    for eli in editList {
        println!("{}", eli.show());
    }
    println!(">>>>");
}

//=============================================================================
// Allocator top level

/* (const) For each virtual live range
   - its sorted Frags
   - its total size
   - its spill cost
   - (eventually) its assigned real register
   New VLRs are created as we go, but existing ones are unchanged, apart from
   being tagged with its assigned real register.

   (mut) For each real register
   - the sorted Frags assigned to it (todo: rm the M)
   - the virtual LR indices assigned to it.  This is so we can eject
     a VLR from the commitment, as needed

   (mut) the set of VLRs not yet allocated, prioritised by total size

   (mut) the edit list that is produced
*/
/*
fn show_commit_tab(commit_tab: &Vec::<SortedFragIxs>,
                   who: &str,
                   context: &Vec_Frag) -> String {
    let mut res = "Commit Table at '".to_string()
                  + &who.to_string() + &"'\n".to_string();
    let mut rregNo = 0;
    for smf in commit_tab.iter() {
        res += &"  ".to_string();
        res += &mkRReg(rregNo).show();
        res += &" ".to_string();
        res += &smf.show_with_fenv(&context);
        res += &"\n".to_string();
        rregNo += 1;
    }
    res
}
*/



// Allocator top level.  |func| is modified so that, when this function
// returns, it will contain no VReg uses.  Allocation can fail if there are
// insufficient registers to even generate spill/reload code, or if the
// function appears to have any undefined VReg/RReg uses.
#[inline(never)]
pub fn alloc_main(func: &mut Func, nRRegs: usize) -> Result<(), String> {
    let (rlr_env, mut vlr_env, mut frag_env) = run_analysis(func)?;

    // -------- Alloc main --------

    // Create initial state

    // This is fully populated by the ::new call.
    let mut prioQ = VLRPrioQ::new(&vlr_env);

    // Whereas this is empty.  We have to populate it "by hand".
    let mut perRReg = Vec::<PerRReg>::new();
    for _ in 0 .. nRRegs {
        // Doing this instead of simply .resize avoids needing Clone for PerRReg
        perRReg.push(PerRReg::new(&frag_env));
    }
    for rlr in rlr_env.iter() {
        let rregNo = rlr.rreg.get_usize();
        // Ignore RLRs for RRegs outside its allocation domain.  As far as the
        // allocator is concerned, such RRegs simply don't exist.
        if rregNo >= nRRegs {
            continue;
        }
        perRReg[rregNo].add_RLR(&rlr, &frag_env);
    }

    let mut editList = Vec::<EditListItem>::new();
    println!("");
    print_RA_state("Initial", &prioQ, &perRReg, &editList, &vlr_env, &frag_env);

    // This is technically part of the running state, at least for now.
    let mut spillSlotCtr: u32 = 0;

    // Main allocation loop.  Each time round, pull out the longest
    // unallocated VLR, and do one of three things:
    //
    // * allocate it to a RReg, possibly by ejecting some existing allocation,
    //   but only one with a lower spill cost than this one, or
    //
    // * spill it.  This causes the VLR to disappear.  It is replaced by a set
    //   of very short VLRs to carry the spill and reload values.  Or,
    //
    // * split it.  This causes it to disappear but be replaced by two VLRs
    //   which together constitute the original.
    println!("");
    println!("-- MAIN ALLOCATION LOOP:");
    while let Some(curr_vlrix) = prioQ.get_longest_VLR(&vlr_env) {
        let curr_vlr = &vlr_env[curr_vlrix];

        println!("-- considering        {}:  {}",
                 curr_vlrix.show(), curr_vlr.show());

        // See if we can find a RReg to which we can assign this VLR without
        // evicting any previous assignment.
        let mut rreg_to_use = None;
        for i in 0 .. nRRegs {
            if perRReg[i].can_add_VLR_without_eviction(curr_vlr, &frag_env) {
                rreg_to_use = Some(i);
                break;
            }
        }
        if let Some(rregNo) = rreg_to_use {
            // Yay!
            let rreg = mkRReg(rregNo as u32);
            println!("--   direct alloc to  {}", rreg.show());
            perRReg[rregNo].add_VLR(curr_vlrix, &vlr_env, &frag_env);
            debug_assert!(curr_vlr.rreg.is_none());
            // Directly modify bits of vlr_env.  This means we have to abandon
            // the immutable borrow for curr_vlr, but that's OK -- we won't
            // need it again (in this loop iteration).
            vlr_env[curr_vlrix].rreg = Some(rreg);
            continue;
        }

        // That didn't work out.  Next, try to see if we can allocate it by
        // evicting some existing allocation that has a lower spill weight.
        // Search all RRegs to find the candidate with the lowest spill
        // weight.  This could be expensive.

        // (rregNo for best cand, its VLRIx, and its spill cost)
        let mut best_so_far: Option<(usize, VLRIx, f32)> = None;
        for i in 0 .. nRRegs {
            let mb_better_cand: Option<(VLRIx, f32)>;
            mb_better_cand =
                perRReg[i].find_best_evict_VLR(&curr_vlr, &vlr_env, &frag_env);
            if let Some((cand_vlrix, cand_cost)) = mb_better_cand {
                // See if this is better than the best so far, and if so take
                // it.  First some sanity checks:
                //
                // If the cand to be evicted is the current one,
                // something's seriously wrong.
                debug_assert!(cand_vlrix != curr_vlrix);
                // We can only evict a LR with lower spill cost than the LR
                // we're trying to allocate.  This is really important, if only
                // to show that the algorithm will actually terminate.
                debug_assert!(cost_is_less(Some(cand_cost), curr_vlr.cost));
                let mut cand_is_better = true;
                if let Some((_, _, best_cost)) = best_so_far {
                    if cost_is_less(Some(best_cost), Some(cand_cost)) {
                        cand_is_better = false;
                    }
                }
                if cand_is_better {
                    // Either this is the first possible candidate we've seen,
                    // or it's better than any previous one.  In either case,
                    // make note of it.
                    best_so_far = Some((i, cand_vlrix, cand_cost));
                }
            }
        }
        if let Some((rregNo, vlrix_to_evict, _)) = best_so_far {
            // Evict ..
            println!("--   evict            {}:  {}",
                     vlrix_to_evict.show(),
                     &vlr_env[vlrix_to_evict].show());
            debug_assert!(vlrix_to_evict != curr_vlrix);
            perRReg[rregNo].del_VLR(vlrix_to_evict, &vlr_env, &frag_env);
            prioQ.add_VLR(vlrix_to_evict);
            debug_assert!(vlr_env[vlrix_to_evict].rreg.is_some());
            // .. and reassign.
            let rreg = mkRReg(rregNo as u32);
            println!("--   then alloc to    {}", rreg.show());
            perRReg[rregNo].add_VLR(curr_vlrix, &vlr_env, &frag_env);
            debug_assert!(curr_vlr.rreg.is_none());
            // Directly modify bits of vlr_env.  This means we have to abandon
            // the immutable borrow for curr_vlr, but that's OK -- we won't
            // need it again again (in this loop iteration).
            vlr_env[curr_vlrix].rreg = Some(rreg);
            vlr_env[vlrix_to_evict].rreg = None;
            continue;
        }

        // Still no luck.  We can't find a register to put it in, so we'll
        // have to spill it, since splitting it isn't yet implemented.
        println!("--   spill");

        // If the live range already pertains to a spill or restore, then
        // it's Game Over.  The constraints (availability of RRegs vs
        // requirement for them) are impossible to fulfill, and so we cannot
        // generate any valid allocation for this function.
        if curr_vlr.cost.is_none() {
            return Err("out of registers".to_string());
        }

        // Generate a new spill slot number, S
        /* Spilling vreg V with virtual live range VLR to slot S:
              for each frag F in VLR {
                 for each insn I in F.first.iix .. F.last.iix {
                    if I does not mention V
                       continue
                    if I mentions V in a Read role {
                       // invar: I cannot mention V in a Mod role
                       add new VLR I.reload -> I.use, vreg V, spillcost Inf
                       add eli @ I.reload V Slot
                    }
                    if I mentions V in a Mod role {
                       // invar: I cannot mention V in a Read or Write Role
                       add new VLR I.reload -> I.spill, Vreg V, spillcost Inf
                       add eli @ I.reload V Slot
                       add eli @ I.spill  Slot V
                    }
                    if I mentions V in a Write role {
                       // invar: I cannot mention V in a Mod role
                       add new VLR I.def -> I.spill, vreg V, spillcost Inf
                       add eli @ I.spill V Slot
                    }
                 }
              }
        */
        /* We will be spilling vreg |curr_vlr.reg| with VLR |curr_vlr| to ..
           well, we better invent a new spill slot number.  Just hand them out
           sequentially for now. */

        // This holds enough info to create reload or spill (or both)
        // instructions around an instruction that references a VReg that has
        // been spilled.
        struct SpillAndOrReloadInfo {
            bix:  BlockIx, // that |iix| is in
            iix:  InsnIx,  // this is the Insn we are spilling/reloading for
            kind: BridgeKind // says whether to create a spill or reload or both
        }
        let mut sri_vec = Vec::<SpillAndOrReloadInfo>::new();
        let curr_vlr_vreg = curr_vlr.vreg;
        let curr_vlr_reg = Reg_V(curr_vlr_vreg);

        for fix in &curr_vlr.sfrags.fragIxs {
            let frag: &Frag = &frag_env[*fix];
            for iix in frag.first.iix .dotdot( frag.last.iix.plus(1) ) {
                let insn: &Insn = &func.insns[iix];
                let (regs_d, regs_m, regs_u) = insn.getRegUsage();
                // If this insn doesn't mention the vreg we're spilling for,
                // move on.
                if !regs_d.contains(curr_vlr_reg)
                   && !regs_m.contains(curr_vlr_reg)
                   && !regs_u.contains(curr_vlr_reg) {
                    continue;
                }
                // USES: Do we need to create a reload-to-use bridge (VLR) ?
                if regs_u.contains(curr_vlr_reg)
                   && frag.contains(&InsnPoint_U(iix)) {
                    debug_assert!(!regs_m.contains(curr_vlr_reg));
                    // Stash enough info that we can create a new VLR and a
                    // new edit list entry for the reload.
                    let sri = SpillAndOrReloadInfo { bix: frag.bix, iix: iix,
                                                     kind: BridgeKind::RtoU };
                    sri_vec.push(sri);
                }
                // MODS: Do we need to create a reload-to-spill bridge?  This
                // can only happen for instructions which modify a register.
                // Note this has to be a single VLR, since if it were two (one
                // for the reload, one for the spill) they could later end up
                // being assigned to different RRegs, which is obviously
                // nonsensical.
                if regs_m.contains(curr_vlr_reg)
                   && frag.contains(&InsnPoint_U(iix))
                   && frag.contains(&InsnPoint_D(iix)) {
                    debug_assert!(!regs_u.contains(curr_vlr_reg));
                    debug_assert!(!regs_d.contains(curr_vlr_reg));
                    let sri = SpillAndOrReloadInfo { bix: frag.bix, iix: iix,
                                                     kind: BridgeKind::RtoS };
                    sri_vec.push(sri);
                }
                // DEFS: Do we need to create a def-to-spill bridge?
                if regs_d.contains(curr_vlr_reg)
                   && frag.contains(&InsnPoint_D(iix)) {
                    debug_assert!(!regs_m.contains(curr_vlr_reg));
                    let sri = SpillAndOrReloadInfo { bix: frag.bix, iix: iix,
                                                     kind: BridgeKind::DtoS };
                    sri_vec.push(sri);
                }
            }
        }

        // Now that we no longer need to access |frag_env| or |vlr_env| for
        // the remainder of this iteration of the main allocation loop, we can
        // actually generate the required spill/reload artefacts.
        for sri in sri_vec {
            // For a spill for a MOD use, the new value will be referenced
            // three times.  For DEF and USE uses, it'll only be ref'd twice.
            // (I think we don't care about metrics for the new Frags, though)
            let new_vlr_count =
                if sri.kind == BridgeKind::RtoS { 3 } else { 2 };
            let (new_vlr_first_pt, new_vlr_last_pt) =
                match sri.kind {
                    BridgeKind::RtoU => (Point::R, Point::U),
                    BridgeKind::RtoS => (Point::R, Point::S),
                    BridgeKind::DtoS => (Point::D, Point::S)
                };
            let new_vlr_frag
                = Frag { bix:   sri.bix,
                         kind:  FragKind::Local,
                         first: mkInsnPoint(sri.iix, new_vlr_first_pt),
                         last:  mkInsnPoint(sri.iix, new_vlr_last_pt),
                         count: new_vlr_count };
            let new_vlr_fix = mkFragIx(frag_env.len() as u32);
            frag_env.push(new_vlr_frag);
            println!("--     new Frag       {}  :=  {}",
                     &new_vlr_fix.show(), &new_vlr_frag.show());
            let new_vlr_sfixs = SortedFragIxs::unit(new_vlr_fix, &frag_env);
            let new_vlr = VLR { vreg: curr_vlr_vreg, rreg: None,
                                sfrags: new_vlr_sfixs,
                                size: 1, cost: None/*infinity*/ };
            let new_vlrix = mkVLRIx(vlr_env.len() as u32);
            println!("--     new VLR        {}  :=  {}",
                     new_vlrix.show(), &new_vlr.show());
            vlr_env.push(new_vlr);
            prioQ.add_VLR(new_vlrix);

            let new_eli
                = EditListItem { slot:  mkSlot(spillSlotCtr),
                                 vlrix: new_vlrix,
                                 kind:  sri.kind };
            println!("--     new ELI        {}", &new_eli.show());
            editList.push(new_eli);
        }

        spillSlotCtr += 1;
    }

    println!("");
    print_RA_state("Final", &prioQ, &perRReg, &editList, &vlr_env, &frag_env);

    // -------- Edit the instruction stream --------

    // Gather up a vector of (Frag, VReg, RReg) resulting from the previous
    // phase.  This fundamentally is the result of the allocation and tells us
    // how the instruction stream must be edited.  Note it does not take
    // account of spill or reload instructions.  Dealing with those is
    // relatively simple and happens later.
    //
    // Make two copies of this list, one sorted by the fragment start points
    // (just the InsnIx numbers, ignoring the Point), and one sorted by
    // fragment end points.

    let mut fragMapsByStart = Vec::<(FragIx, VReg, RReg)>::new();
    let mut fragMapsByEnd   = Vec::<(FragIx, VReg, RReg)>::new();
    // For each real register ..
    for i in 0 .. nRRegs {
        let rreg = mkRReg(i as u32);
        // .. look at all the VLRs assigned to it.  And for each such VLR ..
        for vlrix_assigned in &perRReg[i].vlrixs_assigned {
            let vlr_assigned = &vlr_env[*vlrix_assigned];
            // All the Frags in |vlr_assigned| require |vlr_assigned.reg| to
            // be mapped to the real reg |i|
            let vreg = vlr_assigned.vreg;
            // .. collect up all its constituent Frags.
            for fix in &vlr_assigned.sfrags.fragIxs {
                let frag = &frag_env[*fix];
                fragMapsByStart.push((*fix, vreg, rreg));
                fragMapsByEnd.push((*fix, vreg, rreg));
            }
        }
    }

    fragMapsByStart.sort_unstable_by(
        |(fixNo1, _, _), (fixNo2, _, _)|
        frag_env[*fixNo1].first.iix.partial_cmp(&frag_env[*fixNo2].first.iix)
                         .unwrap());

    fragMapsByEnd.sort_unstable_by(
        |(fixNo1, _, _), (fixNo2, _, _)|
        frag_env[*fixNo1].last.iix.partial_cmp(&frag_env[*fixNo2].last.iix)
                         .unwrap());

    //println!("Firsts: {}", fragMapsByStart.show());
    //println!("Lasts:  {}", fragMapsByEnd.show());

    let mut cursorStarts = 0;
    let mut numStarts = 0;
    let mut cursorEnds = 0;
    let mut numEnds = 0;

    let mut map = Map::<VReg, RReg>::default();

    fn showMap(m: &Map::<VReg, RReg>) -> String {
        let mut vec: Vec::<(&VReg, &RReg)> = m.iter().collect();
        vec.sort_by(|p1, p2| p1.0.partial_cmp(p2.0).unwrap());
        vec.show()
    }

    fn is_sane(frag: &Frag) -> bool {
        // "Normal" frag (unrelated to spilling).  No normal frag may start or
        // end at a .s or a .r point.
        if frag.first.pt.isUorD() && frag.last.pt.isUorD()
           && frag.first.iix <= frag.last.iix {
               return true;
        }
        // A spill-related ("bridge") frag.  There are three possibilities,
        // and they correspond exactly to |BridgeKind|.
        if frag.first.pt.isR() && frag.last.pt.isU()
           && frag.last.iix == frag.first.iix {
            // BridgeKind::RtoU
            return true;
        }
        if frag.first.pt.isR() && frag.last.pt.isS()
           && frag.last.iix == frag.first.iix {
            // BridgeKind::RtoS
            return true;
        }
        if frag.first.pt.isD() && frag.last.pt.isS()
           && frag.last.iix == frag.first.iix {
            // BridgeKind::DtoS
            return true;
        }
        // None of the above apply.  This Frag is insane \o/
        false
    }

    for insnIx in mkInsnIx(0) .dotdot( mkInsnIx(func.insns.len()) ) {
        //println!("");
        //println!("QQQQ insn {}: {}",
        //         insnIx, func.insns[insnIx].show());
        //println!("QQQQ init map {}", showMap(&map));
        // advance [cursorStarts, +numStarts) to the group for insnIx
        while cursorStarts < fragMapsByStart.len()
              && frag_env[ fragMapsByStart[cursorStarts].0 ]
                 .first.iix < insnIx {
            cursorStarts += 1;
        }
        numStarts = 0;
        while cursorStarts + numStarts < fragMapsByStart.len()
              && frag_env[ fragMapsByStart[cursorStarts + numStarts].0 ]
                 .first.iix == insnIx {
            numStarts += 1;
        }

        // advance [cursorEnds, +numEnds) to the group for insnIx
        while cursorEnds < fragMapsByEnd.len()
              && frag_env[ fragMapsByEnd[cursorEnds].0 ]
                 .last.iix < insnIx {
            cursorEnds += 1;
        }
        numEnds = 0;
        while cursorEnds + numEnds < fragMapsByEnd.len()
              && frag_env[ fragMapsByEnd[cursorEnds + numEnds].0 ]
                 .last.iix == insnIx {
            numEnds += 1;
        }

        // So now, fragMapsByStart[cursorStarts, +numStarts) are the mappings
        // for fragments that begin at this instruction, in no particular
        // order.  And fragMapsByEnd[cursorEnd, +numEnd) are the FragIxs for
        // fragments that end at this instruction.

        //println!("insn no {}:", insnIx);
        //for j in cursorStarts .. cursorStarts + numStarts {
        //    println!("   s: {} {}",
        //             (fragMapsByStart[j].1, fragMapsByStart[j].2).show(),
        //             frag_env[ fragMapsByStart[j].0 ]
        //             .show());
        //}
        //for j in cursorEnds .. cursorEnds + numEnds {
        //    println!("   e: {} {}",
        //             (fragMapsByEnd[j].1, fragMapsByEnd[j].2).show(),
        //             frag_env[ fragMapsByEnd[j].0 ]
        //             .show());
        //}

        // Sanity check all frags.  In particular, reload and spill frags are
        // heavily constrained.  No functional effect.
        for j in cursorStarts .. cursorStarts + numStarts {
            let frag = &frag_env[ fragMapsByStart[j].0 ];
            // "It really starts here, as claimed."
            debug_assert!(frag.first.iix == insnIx);
            debug_assert!(is_sane(&frag));
        }
        for j in cursorEnds .. cursorEnds + numEnds {
            let frag = &frag_env[ fragMapsByEnd[j].0 ];
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

        // Update map for I.r:
        //   add frags starting at I.r
        //   no frags should end at I.r (it's a reload insn)
        for j in cursorStarts .. cursorStarts + numStarts {
            let frag = &frag_env[ fragMapsByStart[j].0 ];
            if frag.first.pt.isR() { //////// STARTS at I.r
                map.insert(fragMapsByStart[j].1, fragMapsByStart[j].2);
            }
        }

        // Update map for I.u:
        //   add frags starting at I.u
        //   mapU := map
        //   remove frags ending at I.u
        for j in cursorStarts .. cursorStarts + numStarts {
            let frag = &frag_env[ fragMapsByStart[j].0 ];
            if frag.first.pt.isU() { //////// STARTS at I.u
                map.insert(fragMapsByStart[j].1, fragMapsByStart[j].2);
            }
        }
        let mapU = map.clone();
        for j in cursorEnds .. cursorEnds + numEnds {
            let frag = &frag_env[ fragMapsByEnd[j].0 ];
            if frag.last.pt.isU() { //////// ENDS at I.U
                map.remove(&fragMapsByEnd[j].1);
            }
        }

        // Update map for I.d:
        //   add frags starting at I.d
        //   mapD := map
        //   remove frags ending at I.d
        for j in cursorStarts .. cursorStarts + numStarts {
            let frag = &frag_env[ fragMapsByStart[j].0 ];
            if frag.first.pt.isD() { //////// STARTS at I.d
                map.insert(fragMapsByStart[j].1, fragMapsByStart[j].2);
            }
        }
        let mapD = map.clone();
        for j in cursorEnds .. cursorEnds + numEnds {
            let frag = &frag_env[ fragMapsByEnd[j].0 ];
            if frag.last.pt.isD() { //////// ENDS at I.d
                map.remove(&fragMapsByEnd[j].1);
            }
        }

        // Update map for I.s:
        //   no frags should start at I.s (it's a spill insn)
        //   remove frags ending at I.s
        for j in cursorEnds .. cursorEnds + numEnds {
            let frag = &frag_env[ fragMapsByEnd[j].0 ];
            if frag.last.pt.isS() { //////// ENDS at I.s
                map.remove(&fragMapsByEnd[j].1);
            }
        }

        //println!("QQQQ mapU {}", showMap(&mapU));
        //println!("QQQQ mapD {}", showMap(&mapD));

        // Finally, we have mapU/mapD set correctly for this instruction.
        // Apply it.
        func.insns[insnIx].mapRegs_D_U(&mapD, &mapU);

        // Update cursorStarts and cursorEnds for the next iteration
        cursorStarts += numStarts;
        cursorEnds += numEnds;

        if func.blocks.iter().any(|b| b.start.plus(b.len).minus(1) == insnIx) {
            //println!("Block end");
            debug_assert!(map.is_empty());
        }
    }

    debug_assert!(map.is_empty());

    // At this point, we've successfully pushed the vreg->rreg assignments
    // into the original instructions.  But the reload and spill instructions
    // are missing.  To generate them, go through the "edit list", which
    // contains info on both how to generate the instructions, and where to
    // insert them.
    let mut spillsAndReloads = Vec::<(InsnPoint, Insn)>::new();
    for eli in &editList {
        let vlr = &vlr_env[eli.vlrix];
        let vlr_sfrags = &vlr.sfrags;
        debug_assert!(vlr.sfrags.fragIxs.len() == 1);
        let vlr_frag = frag_env[ vlr_sfrags.fragIxs[0] ];
        let rreg = vlr.rreg.expect("Gen of spill/reload: reg not assigned?!");
        match eli.kind {
            BridgeKind::RtoU => {
                debug_assert!(vlr_frag.first.pt.isR());
                debug_assert!(vlr_frag.last.pt.isU());
                debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
                let insnR    = i_reload(rreg, eli.slot);
                let whereToR = vlr_frag.first;
                spillsAndReloads.push((whereToR, insnR));
            },
            BridgeKind::RtoS => {
                debug_assert!(vlr_frag.first.pt.isR());
                debug_assert!(vlr_frag.last.pt.isS());
                debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
                let insnR    = i_reload(rreg, eli.slot);
                let whereToR = vlr_frag.first;
                let insnS    = i_spill(eli.slot, rreg);
                let whereToS = vlr_frag.last;
                spillsAndReloads.push((whereToR, insnR));
                spillsAndReloads.push((whereToS, insnS));
            },
            BridgeKind::DtoS => {
                debug_assert!(vlr_frag.first.pt.isD());
                debug_assert!(vlr_frag.last.pt.isS());
                debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
                let insnS = i_spill(eli.slot, rreg);
                let whereToS = vlr_frag.last;
                spillsAndReloads.push((whereToS, insnS));
            }
        }
    }

    //for pair in &spillsAndReloads {
    //    println!("spill/reload: {}", pair.show());
    //}

    // Construct the final code by interleaving the mapped code with the
    // spills and reloads.  To do that requires having the latter sorted by
    // InsnPoint.
    //
    // We also need to examine and update Func::blocks.  This is assumed to
    // be arranged in ascending order of the Block::start fields.

    spillsAndReloads.sort_unstable_by(
        |(ip1, _), (ip2, _)| ip1.partial_cmp(ip2).unwrap());

    let mut curSnR = 0; // cursor in |spillsAndReloads|
    let mut curB = mkBlockIx(0); // cursor in Func::blocks

    let mut newInsns = Vec_Insn::new();
    let mut newBlocks = Vec_Block::new();

    for iix in mkInsnIx(0) .dotdot( mkInsnIx(func.insns.len()) ) {

        // Is |iix| the first instruction in a block?  Meaning, are we
        // starting a new block?
        debug_assert!(curB.get() < func.blocks.len());
        if func.blocks[curB].start == iix {
            let oldBlock = &func.blocks[curB];
            let newBlock = Block { name: oldBlock.name.clone(),
                                   start: mkInsnIx(newInsns.len() as u32),
                                   len: 0, eef: oldBlock.eef };
            newBlocks.push(newBlock);

        }

        // Copy reloads for this insn
        while curSnR < spillsAndReloads.len()
              && spillsAndReloads[curSnR].0 == InsnPoint_R(iix) {
            newInsns.push(spillsAndReloads[curSnR].1.clone());
            curSnR += 1;
        }
        // And the insn itself
        newInsns.push(func.insns[iix].clone());
        // Copy spills for this insn
        while curSnR < spillsAndReloads.len()
              && spillsAndReloads[curSnR].0 == InsnPoint_S(iix) {
            newInsns.push(spillsAndReloads[curSnR].1.clone());
            curSnR += 1;
        }

        // Is |iix| the last instruction in a block?
        if iix.plus(1) == func.blocks[curB].start.plus(func.blocks[curB].len) {
            debug_assert!(curB.get() < func.blocks.len());
            debug_assert!(newBlocks.len() > 0);
            debug_assert!(curB.get() == newBlocks.len() - 1);
            newBlocks[curB].len = newInsns.len() as u32
                                  - newBlocks[curB].start.get();
            curB = curB.plus(1);
        }
    }

    debug_assert!(curSnR == spillsAndReloads.len());
    debug_assert!(curB.get() == func.blocks.len());
    debug_assert!(curB.get() == newBlocks.len());

    func.insns = newInsns;
    func.blocks = newBlocks;

    // And we're done!
    //
    // Curiously, there's no need to fix up Labels after having merged the
    // spill and original instructions.  That's because Labels refer to
    // Blocks, not to individual Insns.  Obviously in a real system things are
    // different :-/
    Ok(())
}
