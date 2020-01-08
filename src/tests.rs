/// Test cases.  The list of them is right at the bottom, function |find_Func|.
/// Add new ones there.

use crate::data_structures::{Insn, Func, Reg, AM, RI, Vec_Insn, mkVReg, mkInsnIx, Label, is_goto_insn, Slot, RReg, BinOp, mk_Vec_Insn, RI_I, mkRReg, Reg_R, AM_R, AM_RI, AM_RR, RI_R};

// Random helpers.

fn mkTextLabel(n: usize) -> String {
    "L".to_string() + &n.to_string()
}

fn mkUnresolved(name: String) -> Label { Label::Unresolved { name }}

fn remapControlFlowTarget(insn: &mut Insn, from: &String, to: &String)
{
    match insn {
        Insn::Goto { ref mut target } => {
            target.remapControlFlow(from, to);
        },
        Insn::GotoCTF { cond:_, ref mut targetT, ref mut targetF } => {
            targetT.remapControlFlow(from, to);
            targetF.remapControlFlow(from, to);
        },
        _ => ()
    }
}

enum Stmt {
    Vanilla     { insn: Insn },
    IfThen      { cond: Reg, stmts_t: Vec::<Stmt> },
    IfThenElse  { cond: Reg,
                  stmts_t: Vec::<Stmt>, stmts_e: Vec::<Stmt> },
    RepeatUntil { stmts: Vec::<Stmt>, cond: Reg },
    WhileDo     { cond: Reg, stmts: Vec::<Stmt> }
}

// Various handy wrappers, mostly wrappings of i_* functions
fn s_if_then_else(cond: Reg,
                  stmts_t: Vec::<Stmt>, stmts_e: Vec::<Stmt>) -> Stmt {
    Stmt::IfThenElse { cond, stmts_t, stmts_e }
}
fn s_if_then(cond: Reg, stmts_t: Vec::<Stmt>) -> Stmt {
    Stmt::IfThenElse { cond, stmts_t, stmts_e: vec![] }
}
fn s_repeat_until(stmts: Vec::<Stmt>, cond: Reg) -> Stmt {
    Stmt::RepeatUntil { stmts, cond }
}
fn s_while_do(cond: Reg, stmts: Vec::<Stmt>) -> Stmt {
    Stmt::WhileDo { cond, stmts }
}

fn s_vanilla(insn: Insn) -> Stmt {
    Stmt::Vanilla { insn }
}

fn s_imm(dst: Reg, imm: u32) -> Stmt {
    s_vanilla( i_imm(dst, imm) )
}
fn s_copy(dst: Reg, src: Reg) -> Stmt {
    s_vanilla( i_copy(dst, src) )
}
fn s_load(dst: Reg, addr: AM) -> Stmt {
    s_vanilla( i_load(dst, addr) )
}
fn s_store(addr: AM, src: Reg) -> Stmt {
    s_vanilla( i_store(addr, src) )
}
fn s_print_s<'a>(str: &'a str) -> Stmt {
    s_vanilla( i_print_s(str) )
}
fn s_print_i(reg: Reg) -> Stmt {
    s_vanilla( i_print_i(reg) )
}

fn s_add(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_add(dst, srcL, srcR) )
}
fn s_sub(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_sub(dst, srcL, srcR) )
}
fn s_mul(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_mul(dst, srcL, srcR) )
}
fn s_mod(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_mod(dst, srcL, srcR) )
}
fn s_shr(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_shr(dst, srcL, srcR) )
}
fn s_and(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_and(dst, srcL, srcR) )
}
fn s_cmp_eq(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_cmp_eq(dst, srcL, srcR) )
}
fn s_cmp_lt(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_cmp_lt(dst, srcL, srcR) )
}
fn s_cmp_le(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_cmp_le(dst, srcL, srcR) )
}
fn s_cmp_ge(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_cmp_ge(dst, srcL, srcR) )
}
fn s_cmp_gt(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_cmp_gt(dst, srcL, srcR) )
}

fn s_addm(dst: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_addm(dst, srcR) )
}
fn s_subm(dst: Reg, srcR: RI) -> Stmt {
    s_vanilla( i_subm(dst, srcR) )
}

//=============================================================================
// The "blockifier".  This is just to make it easier to write test cases, by
// allowing direct use of if-then-else, do-while and repeat-until.  It is
// otherwise entirely unrelated to the register allocator proper.

struct Blockifier {
    name:    String,
    blocks:  Vec::<Vec_Insn>,
    currBNo: usize,  // index into |blocks|
    nVRegs:  u32
}

impl Blockifier {
    fn new<'a>(name: &'a str) -> Self {
        Self {
            name: name.to_string(),
            blocks: vec![],
            currBNo: 0,
            nVRegs: 0
        }
    }

    // Get a new VReg name
    fn vreg(&mut self) -> Reg {
        let v = Reg::VReg(mkVReg(self.nVRegs));
        self.nVRegs += 1;
        v
    }

    // Recursive worker function, which flattens out the control flow,
    // producing a set of blocks
    fn blockify(&mut self, stmts: Vec::<Stmt>) -> (usize, usize) {
        let entryBNo = self.blocks.len();
        let mut currBNo = entryBNo;
        self.blocks.push(Vec_Insn::new());
        for s in stmts {
            match s {
                Stmt::Vanilla { insn } => {
                    self.blocks[currBNo].push(insn);
                },
                Stmt::IfThenElse { cond, stmts_t, stmts_e } => {
                    let (t_ent, t_exit) = self.blockify(stmts_t);
                    let (e_ent, e_exit) = self.blockify(stmts_e);
                    let cont = self.blocks.len();
                    self.blocks.push(Vec_Insn::new());
                    self.blocks[t_exit].push(i_goto(&mkTextLabel(cont)));
                    self.blocks[e_exit].push(i_goto(&mkTextLabel(cont)));
                    self.blocks[currBNo].push(i_goto_ctf(cond,
                                                         &mkTextLabel(t_ent),
                                                         &mkTextLabel(e_ent)));
                    currBNo = cont;
                },
                Stmt::RepeatUntil { stmts, cond } => {
                    let (s_ent, s_exit) = self.blockify(stmts);
                    self.blocks[currBNo].push(i_goto(&mkTextLabel(s_ent)));
                    let cont = self.blocks.len();
                    self.blocks.push(Vec_Insn::new());
                    self.blocks[s_exit].push(i_goto_ctf(cond,
                                                        &mkTextLabel(cont),
                                                        &mkTextLabel(s_ent)));
                    currBNo = cont;
                },
                Stmt::WhileDo { cond, stmts } => {
                    let condblock = self.blocks.len();
                    self.blocks.push(Vec_Insn::new());
                    self.blocks[currBNo].push(i_goto(&mkTextLabel(condblock)));
                    let (s_ent, s_exit) = self.blockify(stmts);
                    self.blocks[s_exit].push(i_goto(&mkTextLabel(condblock)));
                    let cont = self.blocks.len();
                    self.blocks.push(Vec_Insn::new());
                    self.blocks[condblock].push(i_goto_ctf(cond,
                                                           &mkTextLabel(s_ent),
                                                           &mkTextLabel(cont)));
                    currBNo = cont;
                },
                _ => panic!("blockify: unhandled case")
            }
        }
        (entryBNo, currBNo)
    }

    // The main external function.  Convert the given statements, into a Func.
    fn finish(&mut self, stmts: Vec::<Stmt>) -> Func {

        let (ent_bno, exit_bno) = self.blockify(stmts);
        self.blocks[exit_bno].push(i_finish());

        let mut blockz = Vec::<Vec_Insn>::new();
        std::mem::swap(&mut self.blocks, &mut blockz);

        // BEGIN optionally, short out blocks that merely jump somewhere else
        let mut cleanedUp = Vec::<Option<Vec_Insn>>::new();
        for ivec in blockz {
            cleanedUp.push(Some(ivec));
        }

        //println!("Before:");
        //let mut n = 0;
        //for b in &cleanedUp {
        //    println!("   {}  {}", n, b.show());
        //    n += 1;
        //}
        loop {
            // Repeatedly, look for a block that simply jumps to another one
            let mut n = 0;
            let mut redir: Option<(usize, String)> = None;
            for maybe_b in &cleanedUp {
                n += 1;
                let b = match maybe_b {
                    None => continue,
                    Some(b) => b
                };

                debug_assert!(b.len() > 0);
                if b.len() == 1 {
                    if let Some(targetLabel) = is_goto_insn(&b[mkInsnIx(0)]) {
                        if let Label::Unresolved { name } = targetLabel {
                            redir = Some((n - 1, name));
                            break;
                        }
                    }
                }
            }

            match redir {
                // We didn't find any
                None => break,
                // Forget about the block, and apply the redirection to all
                // the rest
                Some((from, to)) => {
                    cleanedUp[from] = None;
                    let nnn = cleanedUp.len();
                    for i in 0 .. nnn {
                        match cleanedUp[i] {
                            None => { },
                            Some(ref mut insns) => {
                                let mmm = insns.len();
                                for j in mkInsnIx(0) .dotdot( mkInsnIx(mmm) ) {
                                    remapControlFlowTarget(&mut insns[j],
                                                           &mkTextLabel(from),
                                                           &to);
                                }
                            }
                        }
                    }
                }
            }
        } // loop {

        //println!("Blocks:");
        //let mut n = 0;
        //for b in &cleanedUp {
        //    println!("   {}  {}", n, b.show());
        //    n += 1;
        //}
        // END optionally, short out blocks that merely jump somewhere else

        // Convert (ent_bno, exit_bno, cleanedUp) into a Func
        let mut func = Func::new(&self.name, &mkTextLabel(ent_bno));
        func.nVRegs = 3; // or whatever
        let mut n = 0;
        for mb_ivec in cleanedUp {
            if let Some(ivec) = mb_ivec {
                func.block(&mkTextLabel(n), ivec);
            }
            n += 1;
        }

        func.finish();

        func
    }
}

fn i_imm(dst: Reg, imm: u32) -> Insn {
    Insn::Imm { dst, imm }
}
fn i_copy(dst: Reg, src: Reg) -> Insn {
    Insn::Copy { dst, src }
}
// For BinOp variants see below

fn i_load(dst: Reg, addr: AM) -> Insn {
    Insn::Load { dst, addr }
}
fn i_store(addr: AM, src: Reg) -> Insn {
    Insn::Store { addr, src }
}
fn i_goto<'a>(target: &'a str) -> Insn {
    Insn::Goto { target: mkUnresolved(target.to_string()) }
}
fn i_goto_ctf<'a>(cond: Reg, targetT: &'a str, targetF: &'a str) -> Insn {
    Insn::GotoCTF { cond: cond,
                    targetT: mkUnresolved(targetT.to_string()),
                    targetF: mkUnresolved(targetF.to_string()) }
}
fn i_print_s<'a>(str: &'a str) -> Insn { Insn::PrintS { str: str.to_string() } }
fn i_print_i(reg: Reg) -> Insn { Insn::PrintI { reg } }
fn i_finish() -> Insn { Insn::Finish { } }

fn i_add(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::Add, dst, srcL, srcR }
}
fn i_sub(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::Sub, dst, srcL, srcR }
}
fn i_mul(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::Mul, dst, srcL, srcR }
}
fn i_mod(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::Mod, dst, srcL, srcR }
}
fn i_shr(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::Shr, dst, srcL, srcR }
}
fn i_and(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::And, dst, srcL, srcR }
}
fn i_cmp_eq(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::CmpEQ, dst, srcL, srcR }
}
fn i_cmp_lt(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::CmpLT, dst, srcL, srcR }
}
fn i_cmp_le(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::CmpLE, dst, srcL, srcR }
}
fn i_cmp_ge(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::CmpGE, dst, srcL, srcR }
}
fn i_cmp_gt(dst: Reg, srcL: Reg, srcR: RI) -> Insn {
    Insn::BinOp { op: BinOp::CmpGT, dst, srcL, srcR }
}

// 2-operand versions of i_add and i_sub, for experimentation
fn i_addm(dst: Reg, srcR: RI) -> Insn {
    Insn::BinOpM { op: BinOp::Add, dst, srcR }
}
fn i_subm(dst: Reg, srcR: RI) -> Insn {
    Insn::BinOpM { op: BinOp::Sub, dst, srcR }
}

// Whatever the current badness is
fn test__badness() -> Func {
    let mut func = Func::new("badness", "start");

    func.block("start", mk_Vec_Insn(vec![
        i_print_s("!!Badness!!\n"),
        i_finish()
    ]));

    func.finish();
    func
}

fn test__straight_line() -> Func {
    let mut func = Func::new("straight_line", "b0");

    // Regs, virtual and real, that we want to use.
    let vA = func.vreg();

    func.block("b0", mk_Vec_Insn(vec![
        i_print_s("Start\n"),
        i_imm(vA, 10),
        i_add(vA, vA, RI_I(7)),
        i_goto("b1"),
    ]));
    func.block("b1", mk_Vec_Insn(vec![
        i_print_s("Result = "),
        i_print_i(vA),
        i_print_s("\n"),
        i_finish()
    ]));

    func.finish();
    func
}

fn test__fill_then_sum() -> Func {
    let mut func = Func::new("fill_then_sum", "set-loop-pre");

    // Regs, virtual and real, that we want to use.
    let vNENT = func.vreg();
    let vI    = func.vreg();
    let vSUM  = func.vreg();
    let rTMP  = Reg_R(mkRReg(2)); // "2" is arbitrary.
    let vTMP2 = func.vreg();

    // Loop pre-header for filling array with numbers.
    // This is also the entry point.
    func.block("set-loop-pre", mk_Vec_Insn(vec![
        i_imm (vNENT, 10),
        i_imm (vI,    0),
        i_goto("set-loop")
    ]));

    // Filling loop
    func.block("set-loop", mk_Vec_Insn(vec![
        i_store   (AM_R(vI), vI),
        i_add     (vI,   vI, RI_I(1)),
        i_cmp_lt  (rTMP, vI, RI_R(vNENT)),
        i_goto_ctf(rTMP, "set-loop", "sum-loop-pre")
    ]));

    // Loop pre-header for summing them
    func.block("sum-loop-pre", mk_Vec_Insn(vec![
        i_imm(vSUM, 0),
        i_imm(vI,   0),
        i_goto("sum-loop")
    ]));

    // Summing loop
    func.block("sum-loop", mk_Vec_Insn(vec![
        i_load  (rTMP,  AM_R(vI)),
        i_add   (vSUM,  vSUM, RI_R(rTMP)),
        i_add   (vI,    vI,   RI_I(1)),
        i_cmp_lt(vTMP2, vI,   RI_R(vNENT)),
        i_goto_ctf(vTMP2, "sum-loop", "print-result")
    ]));

    // After loop.  Print result and stop.
    func.block("print-result", mk_Vec_Insn(vec![
        i_print_s("Sum = "),
        i_print_i(vSUM),
        i_print_s("\n"),
        i_finish()
    ]));

    func.finish();
    func
}

fn test__ssort() -> Func {
    let mut func = Func::new("ssort", "Lstart");

    // This is a simple "shellsort" test.  An array of numbers to sort is
    // placed in mem[5..24] and an increment table is placed in mem[0..4].
    // mem[5..24] is then sorted and the result is printed.
    //
    // This test features 15 basic blocks, 10 virtual registers, at least one
    // of which has multiple independent live ranges, a 3-deep loop nest, and
    // some live ranges which span parts of the loop nest.  So it's an
    // interesting test case.

    let lo = func.vreg();
    let hi = func.vreg();
    let i = func.vreg();
    let j = func.vreg();
    let h = func.vreg();
    let bigN = func.vreg();
    let v = func.vreg();
    let hp = func.vreg();
    let t0 = func.vreg();
    let zero = func.vreg();

    func.block("Lstart", mk_Vec_Insn(vec![
        i_imm(zero, 0),
        // Store the increment table
        i_imm(t0,   1),        i_store(AM_RI(zero,0),  t0),
        i_imm(t0,   4),        i_store(AM_RI(zero,1),  t0),
        i_imm(t0,  13),        i_store(AM_RI(zero,2),  t0),
        i_imm(t0,  40),        i_store(AM_RI(zero,3),  t0),
        i_imm(t0, 121),        i_store(AM_RI(zero,4),  t0),
        // Store the numbers to be sorted
        i_imm(t0,  30),        i_store(AM_RI(zero,5),  t0),
        i_imm(t0,  29),        i_store(AM_RI(zero,6),  t0),
        i_imm(t0,  31),        i_store(AM_RI(zero,7),  t0),
        i_imm(t0,  29),        i_store(AM_RI(zero,8),  t0),
        i_imm(t0,  32),        i_store(AM_RI(zero,9),  t0),
        i_imm(t0,  66),        i_store(AM_RI(zero,10), t0),
        i_imm(t0,  77),        i_store(AM_RI(zero,11), t0),
        i_imm(t0,  44),        i_store(AM_RI(zero,12), t0),
        i_imm(t0,  22),        i_store(AM_RI(zero,13), t0),
        i_imm(t0,  11),        i_store(AM_RI(zero,14), t0),
        i_imm(t0,  99),        i_store(AM_RI(zero,15), t0),
        i_imm(t0,  11),        i_store(AM_RI(zero,16), t0),
        i_imm(t0,  12),        i_store(AM_RI(zero,17), t0),
        i_imm(t0,   7),        i_store(AM_RI(zero,18), t0),
        i_imm(t0,   9),        i_store(AM_RI(zero,19), t0),
        i_imm(t0,   2),        i_store(AM_RI(zero,20), t0),
        i_imm(t0,  32),        i_store(AM_RI(zero,21), t0),
        i_imm(t0,  23),        i_store(AM_RI(zero,22), t0),
        i_imm(t0,  41),        i_store(AM_RI(zero,23), t0),
        i_imm(t0,  14),        i_store(AM_RI(zero,24), t0),
        // The real computation begins here
        i_imm(lo, 5),  // Lowest address of the range to sort
        i_imm(hi, 24), // Highest address of the range to sort
        i_sub(t0, hi, RI_R(lo)),
        i_add(bigN, t0, RI_I(1)),
        i_imm(hp, 0),
        i_goto("L11")
    ]));

    func.block("L11", mk_Vec_Insn(vec![
        i_load(t0, AM_R(hp)),
        i_cmp_gt(t0, t0, RI_R(bigN)),
        i_goto_ctf(t0, "L20", "L11a")
    ]));

    func.block("L11a", mk_Vec_Insn(vec![
        i_add(hp, hp, RI_I(1)),
        i_goto("L11")
    ]));

    func.block("L20", mk_Vec_Insn(vec![
        i_cmp_lt(t0, hp, RI_I(1)),
        i_goto_ctf(t0, "L60", "L21a"),
    ]));

    func.block("L21a", mk_Vec_Insn(vec![
        i_sub(t0, hp, RI_I(1)),
        i_load(h, AM_R(t0)),
        //printf("h = %u\n", h),
        i_add(i, lo, RI_R(h)),
        i_goto("L30"),
    ]));

    func.block("L30", mk_Vec_Insn(vec![
        i_cmp_gt(t0, i, RI_R(hi)),
        i_goto_ctf(t0, "L50", "L30a"),
    ]));

    func.block("L30a", mk_Vec_Insn(vec![
        i_load(v, AM_R(i)),
        i_add(j, i, RI_I(0)),  // FIXME: is this a coalescable copy?
        i_goto("L40"),
    ]));

    func.block("L40", mk_Vec_Insn(vec![
        i_sub(t0, j, RI_R(h)),
        i_load(t0, AM_R(t0)),
        i_cmp_le(t0, t0, RI_R(v)),
        i_goto_ctf(t0, "L45", "L40a"),
    ]));

    func.block("L40a", mk_Vec_Insn(vec![
        i_sub(t0, j, RI_R(h)),
        i_load(t0, AM_R(t0)),
        i_store(AM_R(j), t0),
        i_sub(j, j, RI_R(h)),
        i_add(t0, lo, RI_R(h)),
        i_sub(t0, t0, RI_I(1)),
        i_cmp_le(t0, j, RI_R(t0)),
        i_goto_ctf(t0, "L45", "L40"),
    ]));

    func.block("L45", mk_Vec_Insn(vec![
        i_store(AM_R(j), v),
        i_add(i, i, RI_I(1)),
        i_goto("L30"),
    ]));

    func.block("L50", mk_Vec_Insn(vec![
        i_sub(hp, hp, RI_I(1)),
        i_goto("L20"),
    ]));

    func.block("L60", mk_Vec_Insn(vec![
        i_add(i, lo, RI_I(0)), // FIXME: ditto
        i_goto("L61")
    ]));

    func.block("L61", mk_Vec_Insn(vec![
        i_cmp_gt(t0, i, RI_R(hi)),
        i_goto_ctf(t0, "L62", "L61a"),
    ]));

    func.block("L61a", mk_Vec_Insn(vec![
        i_load(t0, AM_R(i)),
        i_print_i(t0),
        i_print_s(" "),
        i_add(i, i, RI_I(1)),
        i_goto("L61"),
    ]));

    func.block("L62", mk_Vec_Insn(vec![
        i_print_s("\n"),
        i_finish()
    ]));

    func.finish();
    func
}

fn test__3_loops() -> Func {
    let mut func = Func::new("3_loops", "start");

    let v00  = func.vreg();
    let v01  = func.vreg();
    let v02  = func.vreg();
    let v03  = func.vreg();
    let v04  = func.vreg();
    let v05  = func.vreg();
    let v06  = func.vreg();
    let v07  = func.vreg();
    let v08  = func.vreg();
    let v09  = func.vreg();
    let v10  = func.vreg();
    let v11  = func.vreg();
    let vI   = func.vreg();
    let vJ   = func.vreg();
    let vSUM = func.vreg();
    let vTMP = func.vreg();

    // Loop pre-header for filling array with numbers.
    // This is also the entry point.
    func.block("start", mk_Vec_Insn(vec![
        i_imm(v00, 0),
        i_imm(v01, 0),
        i_imm(v02, 0),
        i_imm(v03, 0),
        i_imm(v04, 0),
        i_imm(v05, 0),
        i_imm(v06, 0),
        i_imm(v07, 0),
        i_imm(v08, 0),
        i_imm(v09, 0),
        i_imm(v10, 0),
        i_imm(v11, 0),
        i_imm(vI, 0),
        i_goto("outer-loop-cond")
    ]));

    // Outer loop
    func.block("outer-loop-cond", mk_Vec_Insn(vec![
        i_add     (vI,   vI, RI_I(1)),
        i_cmp_le  (vTMP, vI, RI_I(20)),
        i_goto_ctf(vTMP, "outer-loop-1", "after-outer-loop")
    ]));

    func.block("outer-loop-1", mk_Vec_Insn(vec![
        i_add(v00, v00, RI_I(1)),
        i_add(v01, v01, RI_I(1)),
        i_add(v02, v02, RI_I(1)),
        i_add(v03, v03, RI_I(1)),
        i_goto("outer-loop-cond")
    ]));

    // After loop.  Print result and stop.
    func.block("after-outer-loop", mk_Vec_Insn(vec![
        i_imm(vSUM, 0),
        i_add(vSUM, vSUM, RI_R(v00)),
        i_add(vSUM, vSUM, RI_R(v01)),
        i_add(vSUM, vSUM, RI_R(v02)),
        i_add(vSUM, vSUM, RI_R(v03)),
        i_add(vSUM, vSUM, RI_R(v04)),
        i_add(vSUM, vSUM, RI_R(v05)),
        i_add(vSUM, vSUM, RI_R(v06)),
        i_add(vSUM, vSUM, RI_R(v07)),
        i_add(vSUM, vSUM, RI_R(v08)),
        i_add(vSUM, vSUM, RI_R(v09)),
        i_add(vSUM, vSUM, RI_R(v10)),
        i_add(vSUM, vSUM, RI_R(v11)),
        i_print_s("Sum = "),
        i_print_i(vSUM),
        i_print_s("\n"),
        i_finish()
    ]));

    func.finish();
    func
}

fn test__stmts() -> Func {
    let mut bif = Blockifier::new("stmts");
    let vI = bif.vreg();
    let vJ = bif.vreg();
    let vSUM = bif.vreg();
    let vTMP = bif.vreg();
    let stmts = vec![
        s_imm(vSUM, 0),
        s_imm(vI, 0),
        s_repeat_until(vec![
            s_imm(vJ, 0),
            s_repeat_until(vec![
                s_mul   (vTMP, vI,   RI_R(vJ)),
                s_add   (vSUM, vSUM, RI_R(vTMP)),
                s_add   (vJ,   vJ,   RI_I(1)),
                s_cmp_gt(vTMP, vJ,   RI_I(10))
                ],
                vTMP
            ),
            s_add   (vSUM, vSUM, RI_R(vI)),
            s_add   (vI,   vI,   RI_I(1)),
            s_cmp_gt(vTMP, vI,   RI_I(10))
            ],
            vTMP
        ),
        s_print_s("Result is "),
        s_print_i(vSUM),
        s_print_s("\n")
    ];
    /*
    let stmts = vec![
        s_imm(v0, 0),
        s_imm(v1, 0),
        s_imm(v2, 0),
        s_add(v0, v1, RI_R(v2)),
        s_add(v2, v1, RI_R(v0)),
        s_ite(v0, vec![
                  s_add(v2, v2, RI_I(0)),
                  s_ite(v2, vec![
                            s_add(v2, v2, RI_I(1))
                        ], vec![
                            s_add(v2, v2, RI_I(2))
                        ],
                  ),
              ], vec![
                  s_add(v1, v1, RI_I(3))
              ]
        ),
        s_add(v0, v0, RI_I(4)),
        s_repeat_until(
            vec![
                  s_add(v1, v1, RI_I(5)),
                  s_add(v1, v1, RI_I(6)),
                  s_add(v1, v1, RI_I(7))
            ],
            v0
        ),
        s_add(v0, v0, RI_I(10)),
        s_add(v0, v0, RI_I(11)),
        s_while_do(
            v2,
            vec![
                s_add(v2, v2, RI_I(12))
            ]
        )
    ];
     */
    bif.finish(stmts)
}

// Test cases where live range splitting might obviously help

fn test__needs_splitting() -> Func {
    let mut bif = Blockifier::new("needs_splitting");
    let v10 = bif.vreg();
    let v11 = bif.vreg();
    let v12 = bif.vreg();

    let v20 = bif.vreg();
    let v21 = bif.vreg();
    let v22 = bif.vreg();

    let vI   = bif.vreg();
    let vSUM = bif.vreg();
    let vTMP = bif.vreg();

    let stmts = vec![
        // Both the v1x and the v2x set become live at this point
        s_imm(v10, 1),
        s_imm(v11, 2),
        s_imm(v12, 3),
        s_imm(v20, 4),
        s_imm(v21, 5),
        s_imm(v22, 6),

        // In this loop, v1x are hot, but v2x are unused.  In an ideal world,
        // the v2x set would be spilled across the loop and reloaded after
        // that.
        s_imm(vI, 0),
        s_repeat_until(vec![
            s_add(v10, v10, RI_I(1)),
            s_add(v11, v11, RI_I(2)),
            s_add(v12, v12, RI_I(3)),
            s_add(vI,   vI, RI_I(1)),
            s_cmp_ge(vTMP, vI, RI_I(100))
            ],
            vTMP
        ),

        // Conversely, v2x in this loop are hot, and v1x are unused, but still
        // need to stay alive across it.
        s_imm(vI, 0),
        s_repeat_until(vec![
            s_add(v20, v20, RI_I(1)),
            s_add(v21, v21, RI_I(2)),
            s_add(v22, v22, RI_I(3)),
            s_add(vI,   vI, RI_I(1)),
            s_cmp_ge(vTMP, vI, RI_I(100))
            ],
            vTMP
        ),

        // All in all, the v1x and v2x set are both still live down to here.
        s_imm(vSUM, 0),
        s_add(vSUM, vSUM, RI_R(v10)),
        s_add(vSUM, vSUM, RI_R(v11)),
        s_add(vSUM, vSUM, RI_R(v12)),
        s_add(vSUM, vSUM, RI_R(v20)),
        s_add(vSUM, vSUM, RI_R(v21)),
        s_add(vSUM, vSUM, RI_R(v22)),

        s_print_s("Result is "),
        s_print_i(vSUM),
        s_print_s("\n")
    ];
    bif.finish(stmts)
}

// This is the same as needs_splitting, but with the live ranges split "manually"
fn test__needs_splitting2() -> Func {
    let mut bif = Blockifier::new("needs_splitting2");
    let v10 = bif.vreg();
    let v11 = bif.vreg();
    let v12 = bif.vreg();

    let v20 = bif.vreg();
    let v21 = bif.vreg();
    let v22 = bif.vreg();

    // Post-split versions of v10 .. v22
    let s1v10 = bif.vreg();
    let s1v11 = bif.vreg();
    let s1v12 = bif.vreg();

    let s1v20 = bif.vreg();
    let s1v21 = bif.vreg();
    let s1v22 = bif.vreg();

    let s2v20 = bif.vreg();
    let s2v21 = bif.vreg();
    let s2v22 = bif.vreg();

    let vI   = bif.vreg();
    let vSUM = bif.vreg();
    let vTMP = bif.vreg();

    let stmts = vec![
        // Both the v1x and the v2x set become live at this point
        s_imm(v10, 0),
        s_imm(v11, 0),
        s_imm(v12, 0),
        s_imm(v20, 0),
        s_imm(v21, 0),
        s_imm(v22, 0),

        s_copy(s1v20, v20),
        s_copy(s1v21, v21),
        s_copy(s1v22, v22),

        // In this loop, v1x are hot, but v2x are unused.  In an ideal world,
        // the v2x set would be spilled across the loop and reloaded after
        // that.
        s_imm(vI, 0),
        s_repeat_until(vec![
            s_add(v10, v10, RI_I(1)),
            s_add(v11, v11, RI_I(2)),
            s_add(v12, v12, RI_I(3)),
            s_add(vI,   vI, RI_I(1)),
            s_cmp_ge(vTMP, vI, RI_I(100))
            ],
            vTMP
        ),

        s_copy(s1v10, v10),
        s_copy(s1v11, v11),
        s_copy(s1v12, v12),

        s_copy(s2v20, s1v20),
        s_copy(s2v21, s1v21),
        s_copy(s2v22, s1v22),

        // Conversely, v2x in this loop are hot, and v1x are unused, but still
        // need to stay alive across it.
        s_imm(vI, 0),
        s_repeat_until(vec![
            s_add(s2v20, s2v20, RI_I(1)),
            s_add(s2v21, s2v21, RI_I(2)),
            s_add(s2v22, s2v22, RI_I(3)),
            s_add(vI,   vI, RI_I(1)),
            s_cmp_ge(vTMP, vI, RI_I(100))
            ],
            vTMP
        ),

        // All in all, the v1x and v2x set are both still live down to here.
        s_imm(vSUM, 0),
        s_add(vSUM, vSUM, RI_R(s1v10)),
        s_add(vSUM, vSUM, RI_R(s1v11)),
        s_add(vSUM, vSUM, RI_R(s1v12)),
        s_add(vSUM, vSUM, RI_R(s2v20)),
        s_add(vSUM, vSUM, RI_R(s2v21)),
        s_add(vSUM, vSUM, RI_R(s2v22)),

        s_print_s("Result is "),
        s_print_i(vSUM),
        s_print_s("\n")
    ];
    bif.finish(stmts)
}

// A big test.  This is derived from function fallbackQSort3 in the bzip2
// sources.  Just be glad it was me and not you that had to translate it by
// hand into machine code.  It generates 900 pseudo-random numbers, and then
// sorts them using a Bentley-Sedgewick style 3-way-partitioning quicksort.
// The result is checked for in-orderness and checksummed.  This is not
// recursive (it can't be) so it maintains an explicit stack of
// yet-to-be-processed subranges.  (Two stacks, really).
//
// This test has: 56 basic blocks, 215 insns, 36 virtual registers, 17
// simultaneously live values, 735 live range fragments, 100 vreg live ranges.
/*
   Dynamic results by number of regs available, 2019Dec19:
   17  224440 insns, 0 spills, 0 reloads
   16  226241 insns, 1 spills, 1800 reloads
   15  228045 insns, 2 spills, 3603 reloads
   14  229804 insns, 589 spills, 4775 reloads
   13  232127 insns, 590 spills, 7097 reloads
   12  234450 insns, 591 spills, 9419 reloads
   11  241229 insns, 1752 spills, 15037 reloads
   10  248034 insns, 2913 spills, 20681 reloads
   9   257322 insns, 4655 spills, 28227 reloads
   8   265026 insns, 7508 spills, 33078 reloads
   7   269598 insns, 8509 spills, 36649 reloads
   6   276782 insns, 10453 spills, 41889 reloads
   5   305031 insns, 14401 spills, 66190 reloads
   4   384631 insns, 25980 spills, 134211 reloads
   3   410510 insns, 36512 spills, 149558 reloads
   2  out of regs in spill/reload (load and store insns can reference 3 regs)
*/
fn test__qsort() -> Func {
    let mut bif = Blockifier::new("qsort");

    // All your virtual register are belong to me.  Bwahaha.  Ha.  Ha.
    let offs_stackLo = bif.vreg();
    let offs_stackHi = bif.vreg();
    let offs_numbers = bif.vreg();
    let nNumbers = bif.vreg();
    let rand = bif.vreg();
    let loSt = bif.vreg();
    let hiSt = bif.vreg();
    let keepGoingI = bif.vreg();
    let keepGoingO = bif.vreg();
    let unLo = bif.vreg();
    let unHi = bif.vreg();
    let ltLo = bif.vreg();
    let gtHi = bif.vreg();
    let n = bif.vreg();
    let m = bif.vreg();
    let sp = bif.vreg();
    let lo = bif.vreg();
    let hi = bif.vreg();
    let med = bif.vreg();
    let r3 = bif.vreg();
    let yyp1 = bif.vreg();
    let yyp2 = bif.vreg();
    let yyn = bif.vreg();
    let t0 = bif.vreg();
    let t1 = bif.vreg();
    let t2 = bif.vreg();
    let zztmp1 = bif.vreg();
    let zztmp2 = bif.vreg();
    let taa = bif.vreg();
    let tbb = bif.vreg();
    let i = bif.vreg();
    let inOrder = bif.vreg();
    let sum = bif.vreg();
    let pass = bif.vreg();
    let sp_gt_zero = bif.vreg();
    let guard = bif.vreg();

    let stmts = vec![
    // mem[] layout and base offsets
    //
    // stackLo is [0..49]   (actually only needs 10 entries)
    // stackHi is [50..99]  (ditto)
    // array to sort is [100..999]
    s_imm(offs_stackLo, 0),
    s_imm(offs_stackHi, 50),
    s_imm(offs_numbers, 100),
    s_imm(nNumbers, 900),

    // Fill mem[100..999] with "random" numbers
    s_imm(rand, 0),
    s_imm(i, 0),
    s_repeat_until(vec![
        s_mul(t0, rand, RI_I(7621)),
        s_add(t0, t0, RI_I(1)),
        s_mod(rand, t0, RI_I(32768)),
        s_mod(t0, rand, RI_I(10000)),
        s_store(AM_RR(offs_numbers, i), t0),
        s_add(i, i, RI_I(1)),
        s_cmp_ge(guard, i, RI_R(nNumbers))
        ],
        guard
    ),

    s_imm(rand, 0),
    s_imm(sp, 0),
    s_copy(loSt, offs_numbers),
    s_sub(t0, offs_numbers, RI_I(1)),
    s_add(hiSt, t0, RI_R(nNumbers)),

    // Push initial stack entry
    s_store(AM_RR(offs_stackLo, sp), loSt),
    s_store(AM_RR(offs_stackHi, sp), hiSt),
    s_add(sp, sp, RI_I(1)),

    s_cmp_gt(sp_gt_zero, sp, RI_I(0)),
    s_while_do(
        sp_gt_zero,
        vec![
        s_cmp_lt(t0, sp, RI_I(10)),
        //////assert(t0),

        s_sub(sp, sp, RI_I(1)),
        s_load(lo, AM_RR(offs_stackLo, sp)),
        s_load(hi, AM_RR(offs_stackHi, sp)),

        s_cmp_lt(t0, lo, RI_R(hi)),
        s_if_then(t0, vec![

            s_mul(t0, rand, RI_I(7621)),
            s_add(t0, t0, RI_I(1)),
            s_mod(rand, t0, RI_I(32768)),

            s_mod(r3, rand, RI_I(3)),
            s_cmp_eq(t0, r3, RI_I(0)),
            s_if_then_else(t0, vec![
                s_load(med, AM_R(lo))
            ], vec![
                s_cmp_eq(t0, r3, RI_I(1)),
                s_if_then_else(t0, vec![
                    s_add(t0, lo, RI_R(hi)),
                    s_shr(t0, t0, RI_I(1)),
                    s_load(med, AM_R(t0))
                ], vec![
                    s_load(med, AM_R(hi))
                ]),
            ]),

            s_copy(unLo, lo),
            s_copy(ltLo, lo),
            s_copy(unHi, hi),
            s_copy(gtHi, hi),

            s_imm(keepGoingO, 1),
            s_while_do(
                keepGoingO,
                vec![
                s_imm(keepGoingI, 1),
                s_cmp_le(guard, unLo, RI_R(unHi)),
                s_while_do(
                    guard,
                    vec![
                    s_load(t1, AM_R(unLo)),
                    s_cmp_eq(t0, t1, RI_R(med)),
                    s_if_then_else(t0, vec![
                        s_load(zztmp1, AM_R(unLo)),
                        s_load(zztmp2, AM_R(ltLo)),
                        s_store(AM_R(unLo), zztmp2),
                        s_store(AM_R(ltLo), zztmp1),
                        s_add(ltLo, ltLo, RI_I(1)),
                        s_add(unLo, unLo, RI_I(1))
                    ], vec![
                        s_cmp_gt(t0, t1, RI_R(med)),
                        s_if_then_else(t0, vec![
                           s_imm(keepGoingI, 0)
                        ], vec![
                           s_add(unLo, unLo, RI_I(1))
                        ])
                    ]),
                    s_cmp_le(guard, unLo, RI_R(unHi)),
                    s_and(guard, guard, RI_R(keepGoingI)),
                ]),
                s_imm(keepGoingI, 1),
                s_cmp_le(guard, unLo, RI_R(unHi)),
                s_while_do(
                    guard,
                    vec![
                    s_load(t1, AM_R(unHi)),
                    s_cmp_eq(t0, t1, RI_R(med)),
                    s_if_then_else(t0, vec![
                        s_load(zztmp1, AM_R(unHi)),
                        s_load(zztmp2, AM_R(gtHi)),
                        s_store(AM_R(unHi), zztmp2),
                        s_store(AM_R(gtHi), zztmp1),
                        s_sub(gtHi, gtHi, RI_I(1)),
                        s_sub(unHi, unHi, RI_I(1))
                    ], vec![
                        s_cmp_lt(t0, t1, RI_R(med)),
                        s_if_then_else(t0, vec![
                           s_imm(keepGoingI, 0)
                        ], vec![
                           s_sub(unHi, unHi, RI_I(1))
                        ]),
                    ]),
                    s_cmp_le(guard, unLo, RI_R(unHi)),
                    s_and(guard, guard, RI_R(keepGoingI)),
                ]),
                s_cmp_gt(t0, unLo, RI_R(unHi)),
                s_if_then_else(t0, vec![
                    s_imm(keepGoingO, 0)
                ], vec![
                    s_load(zztmp1, AM_R(unLo)),
                    s_load(zztmp2, AM_R(unHi)),
                    s_store(AM_R(unLo), zztmp2),
                    s_store(AM_R(unHi), zztmp1),
                    s_add(unLo, unLo, RI_I(1)),
                    s_sub(unHi, unHi, RI_I(1)),
                ]),
            ]),
            s_sub(t0, unLo, RI_I(1)),
            s_cmp_eq(t0, unHi, RI_R(t0)),
            //////assert( t0 ),

            s_cmp_ge(t0, gtHi, RI_R(ltLo)),
            s_if_then(t0, vec![
                s_sub(taa, ltLo, RI_R(lo)),
                s_sub(tbb, unLo, RI_R(ltLo)),
                s_cmp_lt(t0, taa, RI_R(tbb)),
                s_if_then_else(t0, vec![
                   s_copy(n, taa)
                ], vec![
                   s_copy(n, tbb)
                ]),

                s_copy(yyp1, lo),
                s_sub(yyp2, unLo, RI_R(n)),
                s_copy(yyn, n),
                s_cmp_gt(guard, yyn, RI_I(0)),
                s_while_do(
                   guard,
                   vec![
                   s_load(zztmp1, AM_R(yyp1)),
                   s_load(zztmp2, AM_R(yyp2)),
                   s_store(AM_R(yyp1), zztmp2),
                   s_store(AM_R(yyp2), zztmp1),
                   s_add(yyp1, yyp1, RI_I(1)),
                   s_add(yyp2, yyp2, RI_I(1)),
                   s_sub(yyn, yyn, RI_I(1)),
                   s_cmp_gt(guard, yyn, RI_I(0)),
                ]),

                s_sub(taa, hi, RI_R(gtHi)),
                s_sub(tbb, gtHi, RI_R(unHi)),
                s_cmp_lt(t0, taa, RI_R(tbb)),
                s_if_then_else(t0, vec![
                   s_copy(m, taa)
                ], vec![
                   s_copy(m, tbb)
                ]),

                s_copy(yyp1, unLo),
                s_sub(yyp2, hi, RI_R(m)),
                s_add(yyp2, yyp2, RI_I(1)),
                s_copy(yyn, m),
                s_cmp_gt(guard, yyn, RI_I(0)),
                s_while_do(
                   guard,
                   vec![
                   s_load(zztmp1, AM_R(yyp1)),
                   s_load(zztmp2, AM_R(yyp2)),
                   s_store(AM_R(yyp1), zztmp2),
                   s_store(AM_R(yyp2), zztmp1),
                   s_add(yyp1, yyp1, RI_I(1)),
                   s_add(yyp2, yyp2, RI_I(1)),
                   s_sub(yyn, yyn, RI_I(1)),
                   s_cmp_gt(guard, yyn, RI_I(0)),
                ]),

                s_add(n, lo, RI_R(unLo)),
                s_sub(n, n, RI_R(ltLo)),
                s_sub(n, n, RI_I(1)),
                s_sub(m, gtHi, RI_R(unHi)),
                s_sub(m, hi, RI_R(m)),
                s_add(m, m, RI_I(1)),

                s_sub(t1, n, RI_R(lo)),
                s_sub(t2, hi, RI_R(m)),
                s_cmp_gt(t0, t1, RI_R(t2)),
                s_if_then_else(t0, vec![
                   s_store(AM_RR(offs_stackLo, sp), lo),
                   s_store(AM_RR(offs_stackHi, sp), n),
                   s_add(sp, sp, RI_I(1)),
                   s_store(AM_RR(offs_stackLo, sp), m),
                   s_store(AM_RR(offs_stackHi, sp), hi),
                   s_add(sp, sp, RI_I(1)),
                ], vec![
                   s_store(AM_RR(offs_stackLo, sp), m),
                   s_store(AM_RR(offs_stackHi, sp), hi),
                   s_add(sp, sp, RI_I(1)),
                   s_store(AM_RR(offs_stackLo, sp), lo),
                   s_store(AM_RR(offs_stackHi, sp), n),
                   s_add(sp, sp, RI_I(1)),
                ]),
            ]),
        ]), // end "if this work unit has more than one item"
        s_cmp_gt(sp_gt_zero, sp, RI_I(0))
    ]), // end outer loop

    // Check the results, as much as we reasonably can.
    s_imm(sum, 0),
    s_imm(inOrder, 1),
    s_load(sum, AM_R(offs_numbers)),
    s_add(i, offs_numbers, RI_I(1)),
    s_repeat_until(vec![
        s_load(t0, AM_R(i)),
        s_add(sum, sum, RI_R(t0)),
        s_sub(t2, i, RI_I(1)),
        s_load(t1, AM_R(t2)),
        s_cmp_gt(t2, t1, RI_R(t0)),
        s_if_then(t2, vec![
           s_imm(inOrder, 0)
        ]),
        s_add(i, i, RI_I(1)),
        s_add(guard, offs_numbers, RI_R(nNumbers)),
        s_cmp_ge(guard, i, RI_R(guard))
        ],
        guard
    ),

    s_cmp_eq(pass, sum, RI_I(4272946)),
    s_and(pass, inOrder, RI_R(pass)),
    s_if_then_else(pass, vec![
        s_print_s("PASS (in order, and correct checksum)")
    ], vec![
        s_print_s("FAIL (not in order, or incorrect checksum)")
    ]),
    s_print_s("\n")

    ];

    bif.finish(stmts)
}

// This is a version of fill_then_sum that uses some 2-operand insns.
fn test__fill_then_sum_2a() -> Func {
    let mut func = Func::new("fill_then_sum_2a", "set-loop-pre");

    // Regs, virtual and real, that we want to use.
    let vNENT = func.vreg();
    let vI    = func.vreg();
    let vSUM  = func.vreg();
    let rTMP  = Reg_R(mkRReg(2)); // "2" is arbitrary.
    let vTMP2 = func.vreg();

    // Loop pre-header for filling array with numbers.
    // This is also the entry point.
    func.block("set-loop-pre", mk_Vec_Insn(vec![
        i_imm (vNENT, 10),
        i_imm (vI,    0),
        i_goto("set-loop")
    ]));

    // Filling loop
    func.block("set-loop", mk_Vec_Insn(vec![
        i_store   (AM_R(vI), vI),
        i_addm    (vI,   RI_I(1)),
        i_cmp_lt  (rTMP, vI, RI_R(vNENT)),
        i_goto_ctf(rTMP, "set-loop", "sum-loop-pre")
    ]));

    // Loop pre-header for summing them
    func.block("sum-loop-pre", mk_Vec_Insn(vec![
        i_imm(vSUM, 0),
        i_imm(vI,   0),
        i_goto("sum-loop")
    ]));

    // Summing loop
    func.block("sum-loop", mk_Vec_Insn(vec![
        i_load  (rTMP,  AM_R(vI)),
        i_addm  (vSUM,  RI_R(rTMP)),
        i_addm  (vI,    RI_I(1)),
        i_cmp_lt(vTMP2, vI,   RI_R(vNENT)),
        i_goto_ctf(vTMP2, "sum-loop", "print-result")
    ]));

    // After loop.  Print result and stop.
    func.block("print-result", mk_Vec_Insn(vec![
        i_print_s("Sum = "),
        i_print_i(vSUM),
        i_print_s("\n"),
        i_finish()
    ]));

    func.finish();
    func
}

// This is a version of ssort that uses some 2-operand insns.
fn test__ssort_2a() -> Func {
    let mut func = Func::new("ssort_2a", "Lstart");

    // This is a simple "shellsort" test.  An array of numbers to sort is
    // placed in mem[5..24] and an increment table is placed in mem[0..4].
    // mem[5..24] is then sorted and the result is printed.
    //
    // This test features 15 basic blocks, 10 virtual registers, at least one
    // of which has multiple independent live ranges, a 3-deep loop nest, and
    // some live ranges which span parts of the loop nest.  So it's an
    // interesting test case.

    let lo = func.vreg();
    let hi = func.vreg();
    let i = func.vreg();
    let j = func.vreg();
    let h = func.vreg();
    let bigN = func.vreg();
    let v = func.vreg();
    let hp = func.vreg();
    let t0 = func.vreg();
    let zero = func.vreg();

    func.block("Lstart", mk_Vec_Insn(vec![
        i_imm(zero, 0),
        // Store the increment table
        i_imm(t0,   1),        i_store(AM_RI(zero,0),  t0),
        i_imm(t0,   4),        i_store(AM_RI(zero,1),  t0),
        i_imm(t0,  13),        i_store(AM_RI(zero,2),  t0),
        i_imm(t0,  40),        i_store(AM_RI(zero,3),  t0),
        i_imm(t0, 121),        i_store(AM_RI(zero,4),  t0),
        // Store the numbers to be sorted
        i_imm(t0,  30),        i_store(AM_RI(zero,5),  t0),
        i_imm(t0,  29),        i_store(AM_RI(zero,6),  t0),
        i_imm(t0,  31),        i_store(AM_RI(zero,7),  t0),
        i_imm(t0,  29),        i_store(AM_RI(zero,8),  t0),
        i_imm(t0,  32),        i_store(AM_RI(zero,9),  t0),
        i_imm(t0,  66),        i_store(AM_RI(zero,10), t0),
        i_imm(t0,  77),        i_store(AM_RI(zero,11), t0),
        i_imm(t0,  44),        i_store(AM_RI(zero,12), t0),
        i_imm(t0,  22),        i_store(AM_RI(zero,13), t0),
        i_imm(t0,  11),        i_store(AM_RI(zero,14), t0),
        i_imm(t0,  99),        i_store(AM_RI(zero,15), t0),
        i_imm(t0,  11),        i_store(AM_RI(zero,16), t0),
        i_imm(t0,  12),        i_store(AM_RI(zero,17), t0),
        i_imm(t0,   7),        i_store(AM_RI(zero,18), t0),
        i_imm(t0,   9),        i_store(AM_RI(zero,19), t0),
        i_imm(t0,   2),        i_store(AM_RI(zero,20), t0),
        i_imm(t0,  32),        i_store(AM_RI(zero,21), t0),
        i_imm(t0,  23),        i_store(AM_RI(zero,22), t0),
        i_imm(t0,  41),        i_store(AM_RI(zero,23), t0),
        i_imm(t0,  14),        i_store(AM_RI(zero,24), t0),
        // The real computation begins here
        i_imm(lo, 5),  // Lowest address of the range to sort
        i_imm(hi, 24), // Highest address of the range to sort
        i_copy(t0, hi),
        i_subm(t0, RI_R(lo)),
        i_add(bigN, t0, RI_I(1)),
        i_imm(hp, 0),
        i_goto("L11")
    ]));

    func.block("L11", mk_Vec_Insn(vec![
        i_load(t0, AM_R(hp)),
        i_cmp_gt(t0, t0, RI_R(bigN)),
        i_goto_ctf(t0, "L20", "L11a")
    ]));

    func.block("L11a", mk_Vec_Insn(vec![
        i_addm(hp, RI_I(1)),
        i_goto("L11")
    ]));

    func.block("L20", mk_Vec_Insn(vec![
        i_cmp_lt(t0, hp, RI_I(1)),
        i_goto_ctf(t0, "L60", "L21a"),
    ]));

    func.block("L21a", mk_Vec_Insn(vec![
        i_copy(t0, hp),
        i_subm(t0, RI_I(1)),
        i_load(h, AM_R(t0)),
        //printf("h = %u\n", h),
        i_copy(i, lo),
        i_addm(i, RI_R(h)),
        i_goto("L30"),
    ]));

    func.block("L30", mk_Vec_Insn(vec![
        i_cmp_gt(t0, i, RI_R(hi)),
        i_goto_ctf(t0, "L50", "L30a"),
    ]));

    func.block("L30a", mk_Vec_Insn(vec![
        i_load(v, AM_R(i)),
        i_copy(j, i),  // FIXME: is this a coalescable copy?
        i_goto("L40"),
    ]));

    func.block("L40", mk_Vec_Insn(vec![
        i_copy(t0, j),
        i_subm(t0, RI_R(h)),
        i_load(t0, AM_R(t0)),
        i_cmp_le(t0, t0, RI_R(v)),
        i_goto_ctf(t0, "L45", "L40a"),
    ]));

    func.block("L40a", mk_Vec_Insn(vec![
        i_copy(t0, j),
        i_subm(t0, RI_R(h)),
        i_load(t0, AM_R(t0)),
        i_store(AM_R(j), t0),
        i_subm(j, RI_R(h)),
        i_copy(t0, lo),
        i_addm(t0, RI_R(h)),
        i_subm(t0, RI_I(1)),
        i_cmp_le(t0, j, RI_R(t0)),
        i_goto_ctf(t0, "L45", "L40"),
    ]));

    func.block("L45", mk_Vec_Insn(vec![
        i_store(AM_R(j), v),
        i_addm(i, RI_I(1)),
        i_goto("L30"),
    ]));

    func.block("L50", mk_Vec_Insn(vec![
        i_subm(hp, RI_I(1)),
        i_goto("L20"),
    ]));

    func.block("L60", mk_Vec_Insn(vec![
        i_copy(i, lo), // FIXME: ditto
        i_goto("L61")
    ]));

    func.block("L61", mk_Vec_Insn(vec![
        i_cmp_gt(t0, i, RI_R(hi)),
        i_goto_ctf(t0, "L62", "L61a"),
    ]));

    func.block("L61a", mk_Vec_Insn(vec![
        i_load(t0, AM_R(i)),
        i_print_i(t0),
        i_print_s(" "),
        i_addm(i, RI_I(1)),
        i_goto("L61"),
    ]));

    func.block("L62", mk_Vec_Insn(vec![
        i_print_s("\n"),
        i_finish()
    ]));

    func.finish();
    func
}

// This is the list of available tests.  This function returns either the
// requested Func, or if not found, a list of the available ones.
pub fn find_Func(name: &String) -> Result::<Func, Vec::<String>> {
    // This is really stupid.  Fortunately it's not performance critical :)
    let all_Funcs = vec![
        test__badness(),           // Whatever the current badness is
        test__straight_line(),     // straight_line
        test__fill_then_sum(),     // fill_then_sum
        test__ssort(),             // shellsort
        test__3_loops(),           // three loops
        test__stmts(),             // a small Stmty test
        test__needs_splitting(),   // LR splitting might help here ..
        test__needs_splitting2(),  // .. same, but with LRs split by hand
        test__qsort(),             // big qsort test, 3-operand only
        test__fill_then_sum_2a(),  // 2-operand version of fill_then_sum
        test__ssort_2a()           // 2-operand version of shellsort
    ];

    let mut all_names = Vec::new();
    for cand in &all_Funcs {
        all_names.push(cand.name.clone());
    }

    for cand in all_Funcs {
        if cand.name == *name {
            return Ok(cand);
        }
    }

    Err(all_names)
}
