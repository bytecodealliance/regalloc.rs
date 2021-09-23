//! Compatibility layer that allows us to use regalloc2.

#![allow(dead_code)]

use crate::analysis_main::AnalysisError;
use crate::checker::{CheckerContext, CheckerErrors};
use crate::data_structures::RegVecs;
use crate::inst_stream::{ExtPoint, InstExtPoint, InstToInsert, InstToInsertAndExtPoint};
use crate::{
    BlockIx, Function, InstIx, RealReg, RealRegUniverse, Reg, RegAllocError, RegAllocResult,
    RegClass, RegEnv, RegUsageCollector, RegUsageMapper, Set, SpillSlot, StackmapRequestInfo,
    TypedIxVec, VirtualReg, Writable,
};
use smallvec::{smallvec, SmallVec};
use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub(crate) struct Regalloc2Env {
    env: regalloc2::MachineEnv,
    rregs_by_preg_index: Vec<RealReg>,
    pregs_by_rreg_index: Vec<regalloc2::PReg>,
    pinned_vregs: Vec<regalloc2::VReg>,
    vreg_offset: usize,
    // regalloc2 uses only Float and Int classes. If the regalloc.rs
    // client uses F64, we map that to Float; otherwise, V128 maps to
    // Float. We don't support the case where both regalloc.rs classes
    // are used. This is sufficient to cover existing use-cases until
    // they can migrate directly to regalloc2.
    float_regclass: RegClass,
}

pub(crate) struct Shim<'a, F: Function> {
    // Register environment state.
    env: &'a RegEnv,

    // Function-specific state.
    func: &'a mut F,
    succs: Vec<regalloc2::Block>,
    succ_ranges: Vec<(u32, u32)>,
    preds: Vec<regalloc2::Block>,
    pred_ranges: Vec<(u32, u32)>,
    operands: Vec<regalloc2::Operand>,
    operand_ranges: Vec<(u32, u32)>,
    reftype_vregs: Vec<regalloc2::VReg>,
    safepoints: regalloc2::indexset::IndexSet,
}

pub(crate) fn build_machine_env(rru: &RealRegUniverse, opts: &Regalloc2Options) -> Regalloc2Env {
    let mut regs = vec![];
    let mut preferred_regs_by_class = [vec![], vec![]];
    let mut non_preferred_regs_by_class = [vec![], vec![]];
    let mut scratch_by_class = [regalloc2::PReg::invalid(), regalloc2::PReg::invalid()];

    // For each reg in the RRU, create a PReg. Its hw_enc index is its
    // index in the class; note that we must have <= 32 regs per class
    // due to the bitpacking internal to regalloc2.

    // We only support I64 and V128 regclasses in this shim.
    assert_eq!(crate::NUM_REG_CLASSES, 5);
    assert!(rru.allocable_by_class[RegClass::rc_to_usize(RegClass::I32)].is_none());
    assert!(rru.allocable_by_class[RegClass::rc_to_usize(RegClass::F32)].is_none());

    let float_regclass = if rru.allocable_by_class[RegClass::rc_to_usize(RegClass::V128)].is_some()
    {
        assert!(rru.allocable_by_class[RegClass::rc_to_usize(RegClass::F64)].is_none());
        RegClass::V128
    } else {
        assert!(rru.allocable_by_class[RegClass::rc_to_usize(RegClass::V128)].is_none());
        RegClass::F64
    };

    // PReg is limited to 64 (32 int, 32 float) regs due to
    // bitpacking, so just build full lookup tables in both
    // directions.
    let mut rregs_by_preg_index = vec![RealReg::invalid(); 64];
    let mut pregs_by_rreg_index = vec![regalloc2::PReg::invalid(); 64];
    let mut pinned_vregs = vec![];

    let int_info = rru.allocable_by_class[RegClass::rc_to_usize(RegClass::I64)]
        .as_ref()
        .unwrap();
    assert!(int_info.suggested_scratch.is_some());
    let float_info = rru.allocable_by_class[RegClass::rc_to_usize(float_regclass)]
        .as_ref()
        .unwrap();
    assert!(float_info.suggested_scratch.is_some());

    let mut int_idx = 0;
    let mut float_idx = 0;
    for (rreg, _) in &rru.regs {
        let preg = match rreg.get_class() {
            RegClass::I64 => {
                let i = int_idx;
                int_idx += 1;
                regalloc2::PReg::new(i, regalloc2::RegClass::Int)
            }
            x if x == float_regclass => {
                let i = float_idx;
                float_idx += 1;
                regalloc2::PReg::new(i, regalloc2::RegClass::Float)
            }
            _ => unreachable!(),
        };
        log::debug!("RealReg {:?} <-> PReg {:?}", rreg, preg);

        // We'll sort these by index below.
        regs.push(preg);

        pinned_vregs.push(regalloc2::VReg::new(preg.hw_enc() as usize, preg.class()));

        rregs_by_preg_index[preg.index()] = *rreg;
        pregs_by_rreg_index[rreg.get_index()] = preg;

        if rreg.get_index() == int_info.suggested_scratch.unwrap() {
            scratch_by_class[0] = preg;
        } else if rreg.get_index() == float_info.suggested_scratch.unwrap() {
            scratch_by_class[1] = preg;
        } else if rreg.get_index() < rru.allocable {
            match preg.class() {
                regalloc2::RegClass::Int => {
                    if int_idx <= opts.num_int_preferred {
                        preferred_regs_by_class[0].push(preg);
                    } else {
                        non_preferred_regs_by_class[0].push(preg);
                    }
                }
                regalloc2::RegClass::Float => {
                    if float_idx <= opts.num_float_preferred {
                        preferred_regs_by_class[1].push(preg);
                    } else {
                        non_preferred_regs_by_class[1].push(preg);
                    }
                }
            }
        }
    }

    log::debug!("preferred_regs int: {:?}", preferred_regs_by_class[0]);
    log::debug!("preferred_regs float: {:?}", preferred_regs_by_class[1]);
    log::debug!(
        "non_preferred_regs int: {:?}",
        non_preferred_regs_by_class[0]
    );
    log::debug!(
        "non_preferred_regs float: {:?}",
        non_preferred_regs_by_class[1]
    );
    log::debug!("scratch: {:?}", scratch_by_class);

    regs.sort_by_key(|preg| preg.index());

    let machenv = regalloc2::MachineEnv {
        regs,
        preferred_regs_by_class,
        non_preferred_regs_by_class,
        scratch_by_class,
    };
    let vreg_offset = rregs_by_preg_index.len();

    Regalloc2Env {
        env: machenv,
        rregs_by_preg_index,
        pregs_by_rreg_index,
        pinned_vregs,
        vreg_offset,
        float_regclass,
    }
}

pub(crate) fn create_shim<'a, F: Function>(
    func: &'a mut F,
    env: &'a RegEnv,
    sri: Option<&StackmapRequestInfo>,
    opts: &Regalloc2Options,
) -> Result<Shim<'a, F>, RegAllocError> {
    let mut shim = Shim {
        env,
        func,
        succs: vec![],
        succ_ranges: vec![],
        preds: vec![],
        pred_ranges: vec![],
        operands: vec![],
        operand_ranges: vec![],
        reftype_vregs: vec![],
        safepoints: regalloc2::indexset::IndexSet::new(),
    };

    // Compute preds and succs in a regalloc2-compatible format.
    let mut edges: Vec<(usize, usize)> = vec![];
    for block in shim.func.blocks() {
        let start = shim.succs.len();
        for &succ in shim.func.block_succs(block).iter() {
            shim.succs.push(regalloc2::Block::new(succ.get() as usize));
            edges.push((block.get() as usize, succ.get() as usize));
        }
        // Remove duplicates.
        let end = shim.succs.len();
        shim.succs[start..end].sort_unstable();
        let mut out = start;
        for i in start..end {
            if i == start || shim.succs[i] != shim.succs[i - 1] {
                shim.succs[out] = shim.succs[i];
                out += 1;
            }
        }
        shim.succs.truncate(out);
        let end = shim.succs.len();
        shim.succ_ranges.push((start as u32, end as u32));
    }
    edges.sort_unstable_by_key(|(_from, to)| *to);
    let mut i = 0;
    for block in shim.func.blocks() {
        while i < edges.len() && edges[i].1 < block.get() as usize {
            i += 1;
        }
        let first_edge = i;
        while i < edges.len() && edges[i].1 == block.get() as usize {
            i += 1;
        }
        let edges = &edges[first_edge..i];

        let start = shim.preds.len();
        let mut last = None;
        for &(from, _) in edges {
            if Some(from) == last {
                continue;
            }
            shim.preds.push(regalloc2::Block::new(from));
            last = Some(from);
        }
        let end = shim.preds.len();
        shim.pred_ranges.push((start as u32, end as u32));
    }

    // Reject CFGs with unreachable blocks; the fuzzer likes to
    // generate these and we must reject them to keep the checker
    // happy.
    let mut reachable = Set::empty();
    reachable.insert(shim.func.entry_block());
    let mut queue = VecDeque::new();
    let mut queue_set = Set::empty();
    queue.push_back(shim.func.entry_block());
    queue_set.insert(shim.func.entry_block());
    while let Some(b) = queue.pop_front() {
        queue_set.delete(b);
        for &succ in shim.func.block_succs(b).iter() {
            if !reachable.contains(succ) && !queue_set.contains(succ) {
                reachable.insert(succ);
                queue.push_back(succ);
                queue_set.insert(succ);
            }
        }
    }
    for block in shim.func.blocks() {
        if !reachable.contains(block) {
            return Err(RegAllocError::Analysis(AnalysisError::UnreachableBlocks));
        }
    }

    // Create a virtual entry instruction with livein defs.
    for &livein in shim.func.func_liveins().iter() {
        let vreg = shim.translate_realreg_to_vreg(livein);
        let preg = shim.translate_realreg_to_preg(livein);
        shim.operands
            .push(regalloc2::Operand::reg_fixed_def(vreg, preg));
    }
    shim.operand_ranges.push((0, shim.operands.len() as u32));

    let disallowed: SmallVec<[RealReg; 4]> = smallvec![
        shim.ra2_env().rregs_by_preg_index[shim.ra2_env().env.scratch_by_class[0].index()],
        shim.ra2_env().rregs_by_preg_index[shim.ra2_env().env.scratch_by_class[1].index()],
    ];
    log::debug!("disallowed: {:?}", disallowed);

    // Create Operands for each reg use/def/mod in the function.
    let mut reg_vecs = RegVecs::new(false);
    let mut moves = 0;
    for (i, insn) in shim.func.insns().iter().enumerate() {
        reg_vecs.clear();
        let mut coll = RegUsageCollector::new(&mut reg_vecs);
        F::get_regs(insn, &mut coll);
        let start = shim.operands.len();
        if let Some((dst, src)) = shim.func.is_move(insn) {
            for r in &[dst.to_reg(), src] {
                if let Some(rreg) = r.as_real_reg() {
                    if disallowed.contains(&rreg) {
                        log::debug!(
                            "illegal use of disallowed register {:?} in inst {:?}",
                            rreg,
                            insn
                        );
                        return Err(RegAllocError::Analysis(AnalysisError::IllegalRealReg(rreg)));
                    }
                }
            }

            moves += 1;
            // Moves are handled specially by the regalloc. We don't
            // need to generate any operands at all.
            shim.operand_ranges.push((start as u32, start as u32));
            continue;
        }

        if !opts.ignore_scratch_reg_mentions {
            // Reject programs that use a scratch or extra-scratch
            // register. The former is a requirement at the regalloc.rs API
            // level; the latter is something that we impose because we need
            // another scratch register for stack-to-stack moves.
            for &r in reg_vecs
                .uses
                .iter()
                .chain(reg_vecs.defs.iter())
                .chain(reg_vecs.mods.iter())
            {
                if let Some(reg) = r.as_real_reg() {
                    if disallowed.contains(&reg) {
                        log::debug!(
                            "illegal use of disallowed register {:?} in inst {:?}",
                            reg,
                            i
                        );
                        return Err(RegAllocError::Analysis(AnalysisError::IllegalRealReg(reg)));
                    }
                }
            }
        }

        for &u in &reg_vecs.uses {
            if let Some(reg) = u.as_real_reg() {
                if reg.get_index() >= shim.env.rru.allocable {
                    continue;
                }
            }
            let vreg = shim.translate_reg_to_vreg(u);
            let constraint = shim.translate_reg_to_constraint(u);
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                constraint,
                regalloc2::OperandKind::Use,
                regalloc2::OperandPos::Early,
            ));
        }
        let mut def_rregs: u64 = 0;
        for &d in &reg_vecs.defs {
            if let Some(reg) = d.as_real_reg() {
                if reg.get_index() >= shim.env.rru.allocable {
                    continue;
                }
                // Tolerate multiple defs of the same RReg. We see
                // this e.g. on call instructions from Cranelift (a
                // clobber and a retval).
                let idx = shim.ra2_env().pregs_by_rreg_index[reg.get_index()].index();
                assert!(idx < 64);
                if def_rregs & (1 << idx) != 0 {
                    continue;
                }
                def_rregs |= 1 << idx;
            }
            let vreg = shim.translate_reg_to_vreg(d);
            let constraint = shim.translate_reg_to_constraint(d);
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                constraint,
                regalloc2::OperandKind::Def,
                regalloc2::OperandPos::Late,
            ));
        }
        for &m in &reg_vecs.mods {
            if let Some(reg) = m.as_real_reg() {
                if reg.get_index() >= shim.env.rru.allocable {
                    continue;
                }
            }
            let vreg = shim.translate_reg_to_vreg(m);
            let constraint = shim.translate_reg_to_constraint(m);
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                constraint,
                regalloc2::OperandKind::Mod,
                regalloc2::OperandPos::Early,
            ));
        }
        // If this is a return, use all liveouts.
        if shim.func.is_ret(InstIx::new(i as u32)) {
            for &liveout in shim.func.func_liveouts().iter() {
                shim.operands.push(regalloc2::Operand::reg_fixed_use(
                    shim.translate_realreg_to_vreg(liveout),
                    shim.ra2_env().pregs_by_rreg_index[liveout.get_index()],
                ));
            }
        }
        let end = shim.operands.len();
        log::debug!(
            "operands for inst {}: {:?}",
            shim.operand_ranges.len(),
            &shim.operands[start..end]
        );
        shim.operand_ranges.push((start as u32, end as u32));
    }

    log::info!(
        "regalloc2-to-regalloc shim: insns = {} moves = {}",
        shim.func.insns().len(),
        moves
    );

    // Compute safepoint map and reftyped-vregs list.
    if let Some(sri) = sri {
        for insn in &sri.safepoint_insns {
            let ra2_insn = insn.get() as usize + 1;
            shim.safepoints.set(ra2_insn, true);
        }
        for vreg in &sri.reftyped_vregs {
            let vreg = shim.translate_virtualreg_to_vreg(*vreg);
            shim.reftype_vregs.push(vreg);
        }
    }

    Ok(shim)
}

fn edit_insts<'a, F: Function>(
    shim: &Shim<'a, F>,
    from: regalloc2::Allocation,
    to: regalloc2::Allocation,
    to_vreg: Option<regalloc2::VReg>,
    clobbers: Option<&mut Set<RealReg>>,
) -> SmallVec<[InstToInsert; 2]> {
    let mut ret = smallvec![];
    if from.is_reg() && to.is_reg() {
        assert_eq!(to.as_reg().unwrap().class(), from.as_reg().unwrap().class());
        let to = shim.ra2_env().rregs_by_preg_index[to.as_reg().unwrap().index()];
        let from = shim.ra2_env().rregs_by_preg_index[from.as_reg().unwrap().index()];
        if to != from {
            if let Some(clobbers) = clobbers {
                clobbers.insert(to);
            }
            assert_eq!(to.get_class(), from.get_class());
            ret.push(InstToInsert::Move {
                to_reg: Writable::from_reg(to),
                from_reg: from,
                for_vreg: None,
            });
        }
        if let Some(to_vreg) = to_vreg {
            let for_reg = shim.translate_vreg_to_reg(to_vreg);
            ret.push(InstToInsert::DefReg {
                to_reg: Writable::from_reg(to),
                for_reg,
            });
        }
    } else if from.is_reg() && to.is_stack() {
        let from = shim.ra2_env().rregs_by_preg_index[from.as_reg().unwrap().index()];
        let to = SpillSlot::new(to.as_stack().unwrap().index() as u32);
        ret.push(InstToInsert::Spill {
            to_slot: to,
            from_reg: from,
            for_vreg: None,
        });
        if let Some(to_vreg) = to_vreg {
            let for_reg = shim.translate_vreg_to_reg(to_vreg);
            ret.push(InstToInsert::DefSlot {
                to_slot: to,
                for_reg,
            });
        }
    } else if from.is_stack() && to.is_reg() {
        let to = shim.ra2_env().rregs_by_preg_index[to.as_reg().unwrap().index()];
        let from = SpillSlot::new(from.as_stack().unwrap().index() as u32);
        if let Some(clobbers) = clobbers {
            clobbers.insert(to);
        }
        ret.push(InstToInsert::Reload {
            to_reg: Writable::from_reg(to),
            from_slot: from,
            for_vreg: None,
        });
        if let Some(to_vreg) = to_vreg {
            let for_reg = shim.translate_vreg_to_reg(to_vreg);
            ret.push(InstToInsert::DefReg {
                to_reg: Writable::from_reg(to),
                for_reg,
            });
        }
    } else {
        panic!("Slot-to-slot move impossible!");
    }
    ret
}

struct Mapper<'a, 'b, F: Function> {
    shim: &'b Shim<'a, F>,
    operands: &'b [regalloc2::Operand],
    allocs: &'b [regalloc2::Allocation],
}

impl<'a, 'b, F: Function> std::fmt::Debug for Mapper<'a, 'b, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "mapper({:?}, {:?})", self.operands, self.allocs)
    }
}

impl<'a, 'b, F: Function> Mapper<'a, 'b, F> {
    fn get_vreg_at_point(&self, vreg: VirtualReg, pos: regalloc2::OperandPos) -> Option<RealReg> {
        let vreg = self.shim.translate_virtualreg_to_vreg(vreg);
        for (i, op) in self.operands.iter().enumerate() {
            if op.vreg() == vreg && (op.pos() == pos || op.kind() == regalloc2::OperandKind::Mod) {
                if self.allocs[i].is_reg() {
                    return Some(
                        self.shim.ra2_env().rregs_by_preg_index
                            [self.allocs[i].as_reg().unwrap().index()],
                    );
                } else {
                    return None;
                }
            }
        }
        None
    }
}

impl<'a, 'b, F: Function> RegUsageMapper for Mapper<'a, 'b, F> {
    fn get_use(&self, vreg: VirtualReg) -> Option<RealReg> {
        self.get_vreg_at_point(vreg, regalloc2::OperandPos::Early)
    }

    fn get_def(&self, vreg: VirtualReg) -> Option<RealReg> {
        self.get_vreg_at_point(vreg, regalloc2::OperandPos::Late)
    }

    fn get_mod(&self, vreg: VirtualReg) -> Option<RealReg> {
        self.get_vreg_at_point(vreg, regalloc2::OperandPos::Early)
    }
}

fn edit_insn_registers<'a, F: Function>(
    bix: BlockIx,
    iix: InstIx,
    insn: &mut F::Inst,
    shim: &Shim<'a, F>,
    out: &regalloc2::Output,
    clobbers: &mut Set<RealReg>,
    checker: &mut Option<CheckerContext>,
) -> Result<(), CheckerErrors> {
    let (op_start, op_end) = shim.operand_ranges[(iix.get() + 1) as usize];
    let operands = &shim.operands[op_start as usize..op_end as usize];
    let allocs = &out.allocs[op_start as usize..op_end as usize];
    let mapper = Mapper {
        shim,
        operands,
        allocs,
    };
    log::debug!("iix {:?}: mapper {:?}", iix, mapper);

    if let Some(checker) = checker.as_mut() {
        checker.handle_insn::<F, _>(&shim.env.rru, bix, iix, insn, &mapper)?;
    }

    F::map_regs(insn, &mapper);

    if shim.func.is_included_in_clobbers(insn) {
        for (op, alloc) in operands.iter().zip(allocs.iter()) {
            if op.kind() != regalloc2::OperandKind::Use && alloc.is_reg() {
                let rreg = shim.ra2_env().rregs_by_preg_index[alloc.as_reg().unwrap().index()];
                assert!(rreg.is_valid());
                clobbers.insert(rreg);
            }
        }
    }

    Ok(())
}

fn handle_nop<'a, F: Function>(
    shim: &Shim<'a, F>,
    bix: BlockIx,
    iix: InstIx,
    checker: &mut Option<CheckerContext>,
) -> Result<(), CheckerErrors> {
    if let Some(checker) = checker.as_mut() {
        let mapper = Mapper {
            shim,
            operands: &[],
            allocs: &[],
        };
        let nop = shim.func.gen_zero_len_nop();
        checker.handle_insn::<F, _>(&shim.env.rru, bix, iix, &nop, &mapper)?;
    }
    Ok(())
}

fn compute_insts_to_add<'a, F: Function>(
    shim: &Shim<'a, F>,
    out: &regalloc2::Output,
) -> Vec<InstToInsertAndExtPoint> {
    let mut ret = vec![];
    for (pos, edit) in &out.edits {
        let pos = shim.translate_pos(*pos);
        match edit {
            &regalloc2::Edit::Move { from, to, to_vreg } => {
                for edit in edit_insts(shim, from, to, to_vreg, None) {
                    let inst_iep = InstToInsertAndExtPoint::new(edit, pos.clone());
                    log::debug!("inst_to_add: {:?}", inst_iep);
                    ret.push(inst_iep);
                }
            }
            &regalloc2::Edit::DefAlloc { alloc, vreg } => {
                if let Some(preg) = alloc.as_reg() {
                    let to_reg =
                        Writable::from_reg(shim.ra2_env().rregs_by_preg_index[preg.index()]);
                    let for_reg = shim.translate_vreg_to_reg(vreg);
                    let edit = InstToInsert::DefReg { to_reg, for_reg };
                    let inst_iep = InstToInsertAndExtPoint::new(edit, pos.clone());
                    ret.push(inst_iep);
                } else if let Some(slot) = alloc.as_stack() {
                    let to_slot = SpillSlot::new(slot.index() as u32);
                    let for_reg = shim.translate_vreg_to_reg(vreg);
                    let edit = InstToInsert::DefSlot { to_slot, for_reg };
                    let inst_iep = InstToInsertAndExtPoint::new(edit, pos.clone());
                    ret.push(inst_iep);
                }
            }
        }
    }
    ret
}

pub(crate) fn finalize<'a, F: Function>(
    shim: Shim<'a, F>,
    out: regalloc2::Output,
    run_checker: bool,
) -> Result<RegAllocResult<F>, RegAllocError> {
    let mut checker = if run_checker {
        Some(CheckerContext::new(
            shim.func,
            &shim.env.rru,
            &compute_insts_to_add(&shim, &out),
            /* TODO stackmap_info */ None,
        ))
    } else {
        None
    };

    if log::log_enabled!(log::Level::Debug) {
        log::debug!("regalloc2 shim: edits:");
        for edit in &out.edits {
            log::debug!(" edit: {:?}", edit);
        }
    }

    let mut new_insns = vec![];
    let nop = shim.func.gen_zero_len_nop();
    let mut edit_idx = 0;
    let mut safepoint_list_idx = 0;
    let mut target_map: TypedIxVec<BlockIx, InstIx> = TypedIxVec::new();
    let mut orig_insn_map: TypedIxVec<InstIx, InstIx> = TypedIxVec::new();
    let mut new_safepoint_insns: Vec<InstIx> = vec![];
    let mut stackmaps: Vec<Vec<SpillSlot>> = vec![];
    let mut clobbers = Set::empty();

    for block in shim.func.blocks() {
        target_map.push(InstIx::new(new_insns.len() as u32));
        for iix in shim.func.block_insns(block) {
            let i = iix.get() as usize;
            // i + 1 because of entry inst.
            let ra2_inst = regalloc2::Inst::new(i + 1);
            let mut insn = std::mem::replace(&mut shim.func.insns_mut()[i], nop.clone());

            let pos = regalloc2::ProgPoint::before(ra2_inst);
            while edit_idx < out.edits.len() && out.edits[edit_idx].0 <= pos {
                match &out.edits[edit_idx].1 {
                    &regalloc2::Edit::Move { from, to, .. } => {
                        for inst in edit_insts(&shim, from, to, None, Some(&mut clobbers)) {
                            if let Some(insn) = inst.construct(shim.func) {
                                new_insns.push(insn);
                                orig_insn_map.push(InstIx::invalid_value());
                            }
                        }
                    }
                    _ => {}
                }
                edit_idx += 1;
            }

            // regalloc2 handles moves on its own -- we do not need to
            // edit them here (and in fact it will fail, as there will
            // be no corresponding operands).
            if shim.func.is_move(&insn).is_none() {
                edit_insn_registers(
                    block,
                    iix,
                    &mut insn,
                    &shim,
                    &out,
                    &mut clobbers,
                    &mut checker,
                )
                .map_err(|err| RegAllocError::RegChecker(err))?;
                orig_insn_map.push(iix);
                new_insns.push(insn);
            } else {
                handle_nop(&shim, block, iix, &mut checker)
                    .map_err(|err| RegAllocError::RegChecker(err))?;
            }

            if shim.safepoints.get(ra2_inst.index()) {
                new_safepoint_insns.push(InstIx::new((new_insns.len() - 1) as u32));
                let pt = regalloc2::ProgPoint::before(ra2_inst);
                log::debug!(
                    " -> inst {:?} is safepoint; looking for slots at pt {:?}",
                    ra2_inst,
                    pt
                );
                let mut slots = vec![];
                if safepoint_list_idx < out.safepoint_slots.len() {
                    assert!(out.safepoint_slots[safepoint_list_idx].0 >= pt);
                }
                while safepoint_list_idx < out.safepoint_slots.len()
                    && out.safepoint_slots[safepoint_list_idx].0 == pt
                {
                    slots.push(SpillSlot::new(
                        out.safepoint_slots[safepoint_list_idx].1.index() as u32,
                    ));
                    log::debug!(" -> slot: {:?}", slots.last().unwrap());
                    safepoint_list_idx += 1;
                }
                stackmaps.push(slots);
            }

            let pos = regalloc2::ProgPoint::after(regalloc2::Inst::new(i + 1));
            while edit_idx < out.edits.len() && out.edits[edit_idx].0 <= pos {
                assert_eq!(out.edits[edit_idx].0, pos);
                match &out.edits[edit_idx].1 {
                    &regalloc2::Edit::Move { from, to, .. } => {
                        for inst in edit_insts(&shim, from, to, None, Some(&mut clobbers)) {
                            if let Some(insn) = inst.construct(shim.func) {
                                new_insns.push(insn);
                                orig_insn_map.push(InstIx::invalid_value());
                            }
                        }
                    }
                    _ => {}
                }
                edit_idx += 1;
            }
        }
    }

    if let Some(checker) = checker.take() {
        log::debug!("running checker");
        checker
            .run()
            .map_err(|err| RegAllocError::RegChecker(err))?;
    }

    Ok(RegAllocResult {
        insns: new_insns,
        target_map,
        orig_insn_map,
        clobbered_registers: clobbers,
        num_spill_slots: out.num_spillslots as u32,
        block_annotations: None,
        stackmaps,
        new_safepoint_insns,
    })
}

impl Regalloc2Env {
    fn translate_rc(&self, rc: RegClass) -> regalloc2::RegClass {
        match rc {
            RegClass::I64 => regalloc2::RegClass::Int,
            x if x == self.float_regclass => regalloc2::RegClass::Float,
            _ => unimplemented!("Only I64 and V128 regclasses are used"),
        }
    }

    fn translate_to_rc(&self, rc: regalloc2::RegClass) -> RegClass {
        match rc {
            regalloc2::RegClass::Int => RegClass::I64,
            regalloc2::RegClass::Float => self.float_regclass,
        }
    }
}

impl<'a, F: Function> Shim<'a, F> {
    fn ra2_env(&self) -> &Regalloc2Env {
        self.env.regalloc2.as_ref().unwrap()
    }

    fn translate_realreg_to_preg(&self, reg: RealReg) -> regalloc2::PReg {
        self.ra2_env().pregs_by_rreg_index[reg.get_index()]
    }

    fn translate_realreg_to_vreg(&self, reg: RealReg) -> regalloc2::VReg {
        let preg = self.translate_realreg_to_preg(reg);
        regalloc2::VReg::new(preg.index(), preg.class())
    }

    fn translate_virtualreg_to_vreg(&self, reg: VirtualReg) -> regalloc2::VReg {
        let rc = reg.get_class();
        let trc = self.ra2_env().translate_rc(rc);
        regalloc2::VReg::new(reg.get_index() + self.ra2_env().vreg_offset, trc)
    }

    fn translate_reg_to_vreg(&self, reg: Reg) -> regalloc2::VReg {
        if reg.is_real() {
            self.translate_realreg_to_vreg(reg.to_real_reg())
        } else {
            self.translate_virtualreg_to_vreg(reg.to_virtual_reg())
        }
    }

    fn translate_vreg_to_reg(&self, vreg: regalloc2::VReg) -> Reg {
        if vreg.vreg() >= self.ra2_env().vreg_offset {
            let idx = vreg.vreg() - self.ra2_env().vreg_offset;
            Reg::new_virtual(self.ra2_env().translate_to_rc(vreg.class()), idx as u32)
        } else {
            let idx = vreg.vreg();
            self.ra2_env().rregs_by_preg_index[idx].to_reg()
        }
    }

    fn translate_reg_to_constraint(&self, reg: Reg) -> regalloc2::OperandConstraint {
        if reg.is_real() {
            let preg = self.translate_realreg_to_preg(reg.to_real_reg());
            regalloc2::OperandConstraint::FixedReg(preg)
        } else {
            regalloc2::OperandConstraint::Reg
        }
    }

    fn translate_pos(&self, pos: regalloc2::ProgPoint) -> InstExtPoint {
        if pos.inst().index() == 0 {
            // We insert a virtual livein-producing instruction at
            // inst 0, so inst 0 per regalloc2 is pre-inst 0 for the
            // regalloc.rs client.
            return InstExtPoint::new(InstIx::new(0), ExtPoint::Reload);
        }
        let inst = InstIx::new((pos.inst().index() - 1) as u32);

        InstExtPoint::new(
            inst,
            match pos.pos() {
                regalloc2::InstPosition::Before => ExtPoint::Reload,
                regalloc2::InstPosition::After => ExtPoint::Spill,
            },
        )
    }
}

impl<'a, F: Function> regalloc2::Function for Shim<'a, F> {
    fn num_insts(&self) -> usize {
        // Add 1 for the virtual entry instruction.
        self.func.insns().len() + 1
    }

    fn num_blocks(&self) -> usize {
        self.func.blocks().len()
    }

    fn entry_block(&self) -> regalloc2::Block {
        // Only 0 is supported, to keep the virtual entry instruction
        // handling simple.
        assert_eq!(self.func.entry_block().get(), 0);
        regalloc2::Block::new(0)
    }

    fn block_insns(&self, block: regalloc2::Block) -> regalloc2::InstRange {
        let range = self.func.block_insns(BlockIx::new(block.index() as u32));
        let mut start = regalloc2::Inst::new(range.first().get() as usize);
        let mut end = regalloc2::Inst::new(range.first().get() as usize + range.len());
        // Virtual entry instruction offsets by 1.
        if block.index() > 0 {
            start = start.next();
        }
        end = end.next();
        regalloc2::InstRange::forward(start, end)
    }

    fn block_succs(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        let (start, end) = self.succ_ranges[block.index()];
        &self.succs[start as usize..end as usize]
    }

    fn block_preds(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        let (start, end) = self.pred_ranges[block.index()];
        &self.preds[start as usize..end as usize]
    }

    fn block_params(&self, _block: regalloc2::Block) -> &[regalloc2::VReg] {
        // We don't use blockparams.
        &[]
    }

    fn is_ret(&self, insn: regalloc2::Inst) -> bool {
        if insn.index() == 0 {
            false
        } else {
            self.func.is_ret(InstIx::new((insn.index() as u32) - 1))
        }
    }

    fn is_branch(&self, _insn: regalloc2::Inst) -> bool {
        // Only needed if we use blockparams.
        false
    }

    fn branch_blockparam_arg_offset(
        &self,
        _block: regalloc2::Block,
        insn: regalloc2::Inst,
    ) -> usize {
        // We don't use blockparams, so blockparams start at the very
        // end of the operands.
        self.inst_operands(insn).len()
    }

    fn requires_refs_on_stack(&self, insn: regalloc2::Inst) -> bool {
        self.safepoints.get(insn.index())
    }

    fn is_move(&self, insn: regalloc2::Inst) -> Option<(regalloc2::Operand, regalloc2::Operand)> {
        if insn.index() == 0 {
            return None;
        }
        let insn = insn.index() - 1;
        let inst = &self.func.insns()[insn];
        self.func
            .is_move(inst)
            .map(|(dst, src)| {
                let src_constraint = self.translate_reg_to_constraint(src);
                let dst_constraint = self.translate_reg_to_constraint(dst.to_reg());
                let src_vreg = self.translate_reg_to_vreg(src);
                let dst_vreg = self.translate_reg_to_vreg(dst.to_reg());
                (
                    regalloc2::Operand::new(
                        src_vreg,
                        src_constraint,
                        regalloc2::OperandKind::Use,
                        regalloc2::OperandPos::Early,
                    ),
                    regalloc2::Operand::new(
                        dst_vreg,
                        dst_constraint,
                        regalloc2::OperandKind::Def,
                        regalloc2::OperandPos::Late,
                    ),
                )
            })
            .filter(|(dst, src)| dst.class() == src.class())
    }

    // --------------------------
    // Instruction register slots
    // --------------------------

    fn inst_operands(&self, insn: regalloc2::Inst) -> &[regalloc2::Operand] {
        let (start, end) = self.operand_ranges[insn.index()];
        &self.operands[start as usize..end as usize]
    }

    fn inst_clobbers(&self, _insn: regalloc2::Inst) -> &[regalloc2::PReg] {
        // We don't use clobbers; we translate the regalloc1 func's
        // never-used defs.
        &[]
    }

    fn num_vregs(&self) -> usize {
        self.ra2_env().vreg_offset + self.func.get_num_vregs()
    }

    fn reftype_vregs(&self) -> &[regalloc2::VReg] {
        &self.reftype_vregs[..]
    }

    fn is_pinned_vreg(&self, vreg: regalloc2::VReg) -> Option<regalloc2::PReg> {
        if vreg.vreg() < self.ra2_env().vreg_offset {
            Some(regalloc2::PReg::new(vreg.vreg(), vreg.class()))
        } else {
            None
        }
    }

    fn pinned_vregs(&self) -> &[regalloc2::VReg] {
        &self.ra2_env().pinned_vregs[..]
    }

    fn spillslot_size(&self, regclass: regalloc2::RegClass) -> usize {
        let regclass = match regclass {
            regalloc2::RegClass::Int => RegClass::I64,
            regalloc2::RegClass::Float => RegClass::V128,
        };
        self.func.get_spillslot_size(regclass, None) as usize
    }

    fn multi_spillslot_named_by_last_slot(&self) -> bool {
        false
    }
}

#[derive(Clone, Debug)]
pub struct Regalloc2Options {
    /// The first `num_int_preferred` int-class regs are preferred
    /// (e.g., perhaps caller-saved so cheaper to use).
    pub num_int_preferred: usize,
    /// The first `num_float_preferred` float-class regs are preferred
    /// (e.g., perhaps caller-saved so cheaper to use).
    pub num_float_preferred: usize,
    /// Ignore uses of scratch registers rather than flagging an
    /// error; the client "knows what it's doing" (e.g. only mentions
    /// them as clobbers).
    pub ignore_scratch_reg_mentions: bool,
    /// Add verbose logging.
    pub verbose_log: bool,
}

impl std::default::Default for Regalloc2Options {
    fn default() -> Self {
        Self {
            num_int_preferred: 8,
            num_float_preferred: 8,
            ignore_scratch_reg_mentions: true,
            verbose_log: false,
        }
    }
}

pub(crate) fn run<'a, F: Function>(
    func: &mut F,
    env: &RegEnv,
    stackmap_info: Option<&StackmapRequestInfo>,
    run_checker: bool,
    opts: &Regalloc2Options,
) -> Result<RegAllocResult<F>, RegAllocError> {
    let ra2_func = create_shim(func, env, stackmap_info, opts)?;
    let ra2_opts = regalloc2::RegallocOptions {
        verbose_log: opts.verbose_log,
    };
    let result = regalloc2::run(&ra2_func, &env.regalloc2.as_ref().unwrap().env, &ra2_opts)
        .map_err(|err| match err {
            regalloc2::RegAllocError::CritEdge(from, to) => {
                RegAllocError::Analysis(AnalysisError::CriticalEdge {
                    from: BlockIx::new(from.index() as u32),
                    to: BlockIx::new(to.index() as u32),
                })
            }
            regalloc2::RegAllocError::EntryLivein => {
                RegAllocError::Analysis(AnalysisError::EntryLiveinValues(vec![]))
            }
            _ => RegAllocError::Other(format!("{:?}", err)),
        })?;
    log::info!("regalloc2 stats: {:?}", result.stats);
    finalize(ra2_func, result, run_checker)
}
