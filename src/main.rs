
#![allow(non_snake_case)]
#![allow(unused_imports)]
#![allow(non_camel_case_types)]

/* TODOs, 11 Dec 2019

MVP (without these, the implementation is useless in practice):

- add a spill-slot allocation mechanism, even if it is pretty crude

- support multiple register classes

- add a random-Func generator and maybe some way to run it in a loop
  (a.k.a a differential fuzzer)

Post-MVP:

- Move Coalescing

- Live Range Splitting

Tidyings:

- (should do) fn CFGInfo::create::dfs: use an explicit stack instead of
  recursion.

- (minor) add an LR classifier (Spill/Reload/Normal) and use that instead
  of current in-line tests

- Is it really necessary to have both SpillAndOrReloadInfo and EditListItem?
  Can we get away with just one?

- Use IndexedVec instead of Vec?

Performance:

- Collect typical use data for each Set<T> instance and replace with a
  suitable optimised replacement.

- Ditto FxHashMap (if we have to have it at all)

- Replace SortedFragIxs with something more efficient

- Currently we call getRegUsage three times for each insn.  Just do this
  once and cache the results.

- Insn rewrite loop: don't clone mapD; just use it as soon as it's available.

- Insn rewrite loop: move cursors forwards at Point granularity so we don't
  have to repeatedly re-scan the groups looking for particular LR kinds?
*/


use std::{fs, io};
use std::io::BufRead;
use std::env;
use std::collections::hash_set::Iter;
use std::collections::VecDeque;
use std::hash::Hash;
use std::convert::TryInto;
use std::cmp::Ordering;
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;


//=============================================================================
// A simple trait for printing things, a.k.a. "Let's play 'Spot the ex-Haskell
// programmer'".

trait Show {
    fn show(&self) -> String;
}
impl Show for bool {
    fn show(&self) -> String {
        (if *self { "True" } else { "False" }).to_string()
    }
}
impl Show for u16 {
    fn show(&self) -> String {
        self.to_string()
    }
}
impl Show for u32 {
    fn show(&self) -> String {
        self.to_string()
    }
}
impl<T: Show> Show for &T {
    fn show(&self) -> String {
        (*self).show()
    }
}
impl<T: Show> Show for Vec<T> {
    fn show(&self) -> String {
        let mut first = true;
        let mut res = "[".to_string();
        for item in self.iter() {
            if !first {
                res += &", ".to_string();
            }
            first = false;
            res += &item.show();
        }
        res + &"]".to_string()
    }
}
impl<T: Show> Show for Option<T> {
    fn show(&self) -> String {
        match self {
            None => "None".to_string(),
            Some(x) => "Some(".to_string() + &x.show() + &")".to_string()
        }
    }
}
impl<A: Show, B: Show> Show for (A, B) {
    fn show(&self) -> String {
        "(".to_string() + &self.0.show() + &",".to_string() + &self.1.show()
            + &")".to_string()
    }
}
impl<A: Show, B: Show, C: Show> Show for (A, B, C) {
    fn show(&self) -> String {
        "(".to_string() + &self.0.show() + &",".to_string() + &self.1.show()
            + &",".to_string() + &self.2.show() + &")".to_string()
    }
}


//=============================================================================
// Definitions of things which are wrappers around integers,
// and printing thereof

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum RReg {
    RReg(u32)
}
fn mkRReg(n: u32) -> RReg { RReg::RReg(n) }
impl RReg {
    fn get(self) -> u32 { match self { RReg::RReg(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for RReg {
    fn show(&self) -> String {
        "R".to_string() + &self.get().to_string()
    }
}


#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum VReg {
    VReg(u32)
}
fn mkVReg(n: u32) -> VReg { VReg::VReg(n) }
impl VReg {
    fn get(self) -> u32 { match self { VReg::VReg(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for VReg {
    fn show(&self) -> String {
        "v".to_string() + &self.get().to_string()
    }
}


#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum Reg {
    RReg(RReg),
    VReg(VReg)
}
fn Reg_R(rreg: RReg) -> Reg { Reg::RReg(rreg) }
fn Reg_V(vreg: VReg) -> Reg { Reg::VReg(vreg) }
impl Show for Reg {
    fn show(&self) -> String {
        match self {
            Reg::RReg(rreg) => rreg.show(),
            Reg::VReg(vreg) => vreg.show()
        }
    }
}
impl Reg {
    fn getRReg(&self) -> RReg {
        match self {
            Reg::RReg(rreg) => *rreg,
            Reg::VReg(_)    => panic!("Reg::getRReg: is not a RReg!")
        }
    }
    fn getVReg(&self) -> VReg {
        match self {
            Reg::RReg(_)     => panic!("Reg::getRReg: is not a VReg!"),
            Reg::VReg(vreg)  => *vreg
        }
    }
    // Apply a vreg-rreg mapping to a Reg.  This used for registers used in
    // either a read- or a write-role.
    fn apply_D_or_U(&mut self, map: &Map::<VReg, RReg>) {
        match self {
            Reg::RReg(_) => {},
            Reg::VReg(vreg) => {
                if let Some(rreg) = map.get(vreg) {
                    *self = Reg::RReg(*rreg);
                } else {
                    panic!("Reg::apply_D_or_U: no mapping for {}", vreg.show());
                }
            }
        }
    }
    // Apply a pair of vreg-rreg mappings to a Reg.  The mappings *must*
    // agree!  This seems a bit strange at first.  It is used for registers
    // used in a modify-role.
    fn apply_M(&mut self, mapD: &Map::<VReg, RReg>, mapU: &Map::<VReg, RReg>) {
        match self {
            Reg::RReg(_) => {},
            Reg::VReg(vreg) => {
                let mb_result_D = mapD.get(vreg);
                let mb_result_U = mapU.get(vreg);
                // Failure of this is serious and should be investigated.
                if mb_result_D != mb_result_U {
                    panic!(
                        "Reg::apply_M: inconsistent mappings for {}: D={}, U={}",
                        vreg.show(), mb_result_D.show(), mb_result_U.show());
                }
                if let Some(rreg) = mb_result_D {
                    *self = Reg::RReg(*rreg);
                } else {
                    panic!("Reg::apply: no mapping for {}", vreg.show());
                }
            }
        }
    }
}


#[derive(Copy, Clone)]
enum Slot {
    Slot(u32)
}
fn mkSlot(n: u32) -> Slot { Slot::Slot(n) }
impl Slot {
    fn get(self) -> u32 { match self { Slot::Slot(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for Slot {
    fn show(&self) -> String {
        "S".to_string() + &self.get().to_string()
    }
}


// The absolute index of a Block (in Func::blocks[]).
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum BlockIx {
    BlockIx(u32)
}
fn mkBlockIx(n: u32) -> BlockIx { BlockIx::BlockIx(n) }
impl BlockIx {
    fn get(self) -> u32 { match self { BlockIx::BlockIx(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for BlockIx {
    fn show(&self) -> String { "b".to_string() + &self.get().to_string() }
}


// The absolute index of an Insn (in Func::insns[]).
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum InsnIx {
    InsnIx(u32)
}
fn mkInsnIx(n: u32) -> InsnIx { InsnIx::InsnIx(n) }
impl InsnIx {
    fn get(self) -> u32 { match self { InsnIx::InsnIx(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
    fn plus(self, delta: u32) -> Self { InsnIx::InsnIx(self.get() + delta) }
}
impl Show for InsnIx {
    fn show(&self) -> String { "i".to_string() + &self.get().to_string() }
}


//=============================================================================
// Definition of instructions, and printing thereof.  Destinations are on the
// left.

#[derive(Clone)]
enum Label {
    Unresolved { name: String },
    Resolved { name: String, bix: BlockIx }
}

fn mkUnresolved(name: String) -> Label { Label::Unresolved { name }}

impl Show for Label {
    fn show(&self) -> String {
        match self {
            Label::Unresolved { name } =>
                "??:".to_string() + &name.to_string(),
            Label::Resolved { name, bix } =>
                bix.show() + &":".to_string() + &name.to_string()
        }
    }
}
impl Label {
    fn getBlockIx(&self) -> BlockIx {
        match self {
            Label::Resolved { name:_, bix } => *bix,
            Label::Unresolved { .. } =>
                panic!("Label::getBlockIx: unresolved label!")
        }
    }

    fn remapControlFlow(&mut self, from: &String, to: &String) {
        match self {
            Label::Resolved { .. } => {
                panic!("Label::remapControlFlow on resolved label");
            },
            Label::Unresolved { name } => {
                if name == from {
                    *name = to.clone();
                }
            }
        }
    }
}

fn resolveLabel<F>(label: &mut Label, lookup: F)
    where F: Fn(String) -> BlockIx
{
    let resolved = 
        match label {
            Label::Unresolved { name } =>
                Label::Resolved { name: name.clone(),
                                  bix: lookup(name.clone()) },
            Label::Resolved { .. } =>
                panic!("resolveLabel: is already resolved!")
        };
    *label = resolved;
}


#[derive(Copy, Clone)]
enum RI {
    Reg { reg: Reg },
    Imm { imm: u32 }
}
fn RI_R(reg: Reg) -> RI { RI::Reg { reg } }
fn RI_I(imm: u32) -> RI { RI::Imm { imm } }
impl Show for RI {
    fn show(&self) -> String {
        match self {
            RI::Reg { reg } => reg.show(),
            RI::Imm { imm } => imm.to_string()
        }
    }
}
impl RI {
    fn addRegReadsTo(&self, uce: &mut Set::<Reg>) {
        match self {
            RI::Reg { reg } => uce.insert(*reg),
            RI::Imm { ..  } => { }
        }
    }
    fn apply_D_or_U(&mut self, map: &Map::<VReg, RReg>) {
        match self {
            RI::Reg { ref mut reg } => { reg.apply_D_or_U(map); },
            RI::Imm { .. }          => {}
        }
    }
}


#[derive(Copy, Clone)]
enum AM {
   RI { base: Reg, offset: u32 },
   RR { base: Reg, offset: Reg }
}
fn AM_R(base: Reg)               -> AM { AM::RI { base, offset: 0 } }
fn AM_RI(base: Reg, offset: u32) -> AM { AM::RI { base, offset } }
fn AM_RR(base: Reg, offset: Reg) -> AM { AM::RR { base, offset } }
impl Show for AM {
    fn show(&self) -> String {
        match self {
            AM::RI { base, offset } =>
                "[".to_string() + &base.show() + &" + ".to_string()
                + &offset.show() + &"]".to_string(),
            AM::RR { base, offset } =>
                "[".to_string() + &base.show() + &" + ".to_string()
                + &offset.show() + &"]".to_string()
        }
    }
}
impl AM {
    fn addRegReadsTo(&self, uce: &mut Set::<Reg>) {
        match self {
            AM::RI { base, .. } =>
                uce.insert(*base),
            AM::RR { base, offset } =>
                { uce.insert(*base); uce.insert(*offset); },
        }
    }
    fn apply_D_or_U(&mut self, map: &Map::<VReg, RReg>) {
        match self {
            AM::RI { ref mut base, .. } =>
                { base.apply_D_or_U(map); },
            AM::RR { ref mut base, ref mut offset } =>
                { base.apply_D_or_U(map); offset.apply_D_or_U(map); }
        }
    }
}


#[derive(Copy, Clone)]
enum BinOp {
    Add, Sub, Mul, Mod, Shr, And, CmpEQ, CmpLT, CmpLE, CmpGE, CmpGT
}
impl Show for BinOp {
    fn show(&self) -> String {
        match self {
            BinOp::Add   => "add".to_string(),
            BinOp::Sub   => "sub".to_string(),
            BinOp::Mul   => "mul".to_string(),
            BinOp::Mod   => "mod".to_string(),
            BinOp::Shr   => "shr".to_string(),
            BinOp::And   => "and".to_string(),
            BinOp::CmpEQ => "cmpeq".to_string(),
            BinOp::CmpLT => "cmplt".to_string(),
            BinOp::CmpLE => "cmple".to_string(),
            BinOp::CmpGE => "cmpge".to_string(),
            BinOp::CmpGT => "cmpgt".to_string()
        }
    }
}
impl BinOp {
    fn calc(self, argL: u32, argR: u32) -> u32 {
        match self {
            BinOp::Add   => u32::wrapping_add(argL, argR),
            BinOp::Sub   => u32::wrapping_sub(argL, argR),
            BinOp::Mul   => u32::wrapping_mul(argL, argR),
            BinOp::Mod   => argL % argR,
            BinOp::Shr   => argL >> (argR & 31),
            BinOp::And   => argL & argR,
            BinOp::CmpEQ => if argL == argR { 1 } else { 0 },
            BinOp::CmpLT => if argL <  argR { 1 } else { 0 },
            BinOp::CmpLE => if argL <= argR { 1 } else { 0 },
            BinOp::CmpGE => if argL >= argR { 1 } else { 0 }
            BinOp::CmpGT => if argL >  argR { 1 } else { 0 }
        }
    }
}


#[derive(Clone)]
enum Insn {
    Imm     { dst: Reg, imm: u32 },
    Copy    { dst: Reg, src: Reg },
    BinOp   { op: BinOp, dst: Reg, srcL: Reg, srcR: RI },
    BinOpM  { op: BinOp, dst: Reg, srcR: RI }, // "mod" semantics for |dst|
    Load    { dst: Reg, addr: AM },
    Store   { addr: AM, src: Reg },
    Spill   { dst: Slot, src: RReg },
    Reload  { dst: RReg, src: Slot },
    Goto    { target: Label },
    GotoCTF { cond: Reg, targetT: Label, targetF: Label },
    PrintS  { str: String },
    PrintI  { reg: Reg },
    Finish  { }
}

impl Show for Insn {
    fn show(&self) -> String {
        fn ljustify(s: String, w: usize) -> String {
            if s.len() >= w {
                s
            } else {
                // BEGIN hack
                let mut need = w - s.len();
                if need > 4 { need = 4; }
                let extra = [" ", "  ", "   ", "    "][need - 1];
                // END hack
                s + &extra.to_string()
            }
        }

        match self {
            Insn::Imm { dst, imm } =>
                "imm    ".to_string()
                + &dst.show() + &", ".to_string() + &imm.to_string(),
            Insn::Copy { dst, src } =>
                "copy   ".to_string()
                + &dst.show() + &", ".to_string() + &src.show(),
            Insn::BinOp { op, dst, srcL, srcR } =>
                ljustify(op.show(), 6)
                + &" ".to_string() + &dst.show()
                + &", ".to_string() + &srcL.show() + &", ".to_string()
                + &srcR.show(),
            Insn::BinOpM { op, dst, srcR } =>
                ljustify(op.show() + &"m".to_string(), 6)
                + &" ".to_string() + &dst.show()
                + &", ".to_string() + &srcR.show(),
            Insn::Load { dst, addr } =>
                "load   ".to_string() + &dst.show() + &", ".to_string()
                + &addr.show(),
            Insn::Store { addr, src } =>
                "store  ".to_string() + &addr.show()
                + &", ".to_string()
                + &src.show(),
            Insn::Spill { dst, src } => {
                "SPILL  ".to_string() + &dst.show() + &", ".to_string()
                + &src.show()
            },
            Insn::Reload { dst, src } => {
                "RELOAD ".to_string() + &dst.show() + &", ".to_string()
                + &src.show()
            },
            Insn::Goto { target } =>
                "goto   ".to_string()
                + &target.show(),
            Insn::GotoCTF { cond, targetT, targetF } =>
                "goto   if ".to_string()
                + &cond.show() + &" then ".to_string() + &targetT.show()
                + &" else ".to_string() + &targetF.show(),
            Insn::PrintS { str } => {
                let mut res = "prints '".to_string();
                for c in str.chars() {
                    res += &(if c == '\n' { "\\n".to_string() }
                                     else { c.to_string() });
                }
                res + &"'".to_string()
            }
            Insn::PrintI { reg } =>
                "printi ".to_string()
                + &reg.show(),
            Insn::Finish { } =>
                "finish ".to_string(),
            _ => "other".to_string()
        }
    }
}

impl Insn {
    // Returns a vector of BlockIxs, being those that this insn might jump to.
    // This might contain duplicates (although it would be pretty strange if
    // it did). This function should not be applied to non-control-flow
    // instructions.  The labels are assumed all to be "resolved".
    fn getTargets(&self) -> Vec::<BlockIx> {
        match self {
            Insn::Goto { target } =>
                vec![target.getBlockIx()],
            Insn::GotoCTF { cond:_, targetT, targetF } =>
                vec![targetT.getBlockIx(), targetF.getBlockIx()],
            Insn::Finish { } =>
                vec![],
            _other =>
                panic!("Insn::getTargets: incorrectly applied to: {}",
                        self.show())
        }
    }

    // Returns three sets of regs, (def, mod, use), being those def'd
    // (written), those mod'd (modified) and those use'd (read) by the
    // instruction, respectively.  Note "use" is sometimes written as "uce"
    // below since "use" is a Rust reserved word, and similarly "mod" is
    // written "m0d" (that's a zero, not capital-o).
    //
    // Be careful here.  If an instruction really modifies a register -- as is
    // typical for x86 -- that register needs to be in the |mod| set, and not
    // in the |def| and |use| sets.  *Any* mistake in describing register uses
    // here will almost certainly lead to incorrect register allocations.
    //
    // Also the following must hold: the union of |def| and |use| must be
    // disjoint from |mod|.
    fn getRegUsage(&self) -> (Set::<Reg>, Set::<Reg>, Set::<Reg>) {
        let mut def = Set::<Reg>::empty();
        let mut m0d = Set::<Reg>::empty();
        let mut uce = Set::<Reg>::empty();
        match self {
            Insn::Imm { dst, imm:_ } => {
                def.insert(*dst);
            },
            Insn::Copy { dst, src } => {
                def.insert(*dst);
                uce.insert(*src);
            },
            Insn::BinOp { op:_, dst, srcL, srcR } => {
                def.insert(*dst);
                uce.insert(*srcL);
                srcR.addRegReadsTo(&mut uce);
            },
            Insn::BinOpM { op:_, dst, srcR } => {
                m0d.insert(*dst);
                srcR.addRegReadsTo(&mut uce);
            },
            Insn::Store { addr, src } => {
                addr.addRegReadsTo(&mut uce);
                uce.insert(*src);
            },
            Insn::Load { dst, addr } => {
                def.insert(*dst);
                addr.addRegReadsTo(&mut uce);
            },
            Insn::Goto { .. } => { },
            Insn::GotoCTF { cond, targetT:_, targetF:_ } => {
                uce.insert(*cond);
            },
            Insn::PrintS { .. } => { },
            Insn::PrintI { reg } => {
                uce.insert(*reg);
            },
            Insn::Finish { } => { },
            _other => panic!("Insn::getRegUsage: unhandled: {}", self.show())
        }
        // Failure of either of these is serious and should be investigated.
        debug_assert!(!def.intersects(&m0d));
        debug_assert!(!uce.intersects(&m0d));
        (def, m0d, uce)
    }

    // Apply the specified VReg->RReg mappings to the instruction, thusly:
    // * For registers mentioned in a read role, apply mapU.
    // * For registers mentioned in a write role, apply mapD.
    // * For registers mentioned in a modify role, mapU and mapD *must* agree
    //   (if not, our caller is buggy).  So apply either map to that register.
    fn mapRegs_D_U(&mut self, mapD: &Map::<VReg, RReg>,
                              mapU: &Map::<VReg, RReg>) {
        let mut ok = true;
        match self {
            Insn::Imm { dst, imm:_ } => {
                dst.apply_D_or_U(mapD);
            },
            Insn::Copy { dst, src } => {
                dst.apply_D_or_U(mapD);
                src.apply_D_or_U(mapU);
            },
            Insn::BinOp { op:_, dst, srcL, srcR } => {
                dst.apply_D_or_U(mapD);
                srcL.apply_D_or_U(mapU);
                srcR.apply_D_or_U(mapU);
            },
            Insn::BinOpM { op:_, dst, srcR } => {
                dst.apply_M(mapD, mapU);
                srcR.apply_D_or_U(mapU);
            },
            Insn::Store { addr, src } => {
                addr.apply_D_or_U(mapU);
                src.apply_D_or_U(mapU);
            },
            Insn::Load { dst, addr } => {
                dst.apply_D_or_U(mapD);
                addr.apply_D_or_U(mapU);
            },
            Insn::Goto { .. } => { },
            Insn::GotoCTF { cond, targetT:_, targetF:_ } => {
                cond.apply_D_or_U(mapU);
            },
            Insn::PrintS { .. } => { },
            Insn::PrintI { reg } => {
                reg.apply_D_or_U(mapU);
            },
            Insn::Finish { } => { },
            _ => {
                ok = false;
            }
        }
        if !ok {
            panic!("Insn::mapRegs_D_U: unhandled: {}", self.show());
        }
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
fn i_spill(dst: Slot, src: RReg) -> Insn {
    Insn::Spill { dst, src }
}
fn i_reload(dst: RReg, src: Slot) -> Insn {
    Insn::Reload { dst, src }
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


fn is_control_flow_insn(insn: &Insn) -> bool {
    match insn {
        Insn::Goto { .. } | Insn::GotoCTF { .. } | Insn::Finish{} => true,
        _ => false
    }
}

fn is_goto_insn(insn: &Insn) -> Option<Label> {
    match insn {
        Insn::Goto { target } => Some(target.clone()),
        _ => None
    }
}

fn resolveInsn<F>(insn: &mut Insn, lookup: F)
    where F: Copy + Fn(String) -> BlockIx
{
    match insn {
        Insn::Goto { ref mut target } => resolveLabel(target, lookup),
        Insn::GotoCTF { cond:_, ref mut targetT, ref mut targetF } => {
            resolveLabel(targetT, lookup);
            resolveLabel(targetF, lookup);
        },
        _ => ()
    }
}

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


//=============================================================================
// Metrics.  Meaning, estimated hotness, etc, numbers, which don't have any
// effect on the correctness of the resulting allocation, but which are
// important for getting a good allocation, basically by giving preference for
// the hottest values getting a register.

/* Required metrics:
   Block (a basic block):
   - Estimated relative execution frequency ("EEF")
     Calculated from loop nesting depth, depth inside an if-tree, etc
     Suggested: u16

   Frag (Live Range Fragment):
   - Length (in instructions).  Can be calculated, = end - start + 1.
   - Number of uses (of the associated Reg)
     Suggested: u16

   LR (Live Range, = a set of Live Range Fragments):
   - spill cost (can be calculated)
     = sum, for each frag:
            frag.#uses / frag.len * frag.block.eef
       with the proviso that spill/reload LRs must have spill cost of infinity
     Do this with a f32 so we don't have to worry about scaling/overflow.
*/


//=============================================================================
// Definition of Block and Func, and printing thereof.

struct Block {
    name:  String,
    start: InsnIx,
    len:   u32,
    eef:   u16
}
fn mkBlock(name: String, start: InsnIx, len: u32) -> Block {
    Block { name: name, start: start, len: len, eef: 1 }
}
impl Clone for Block {
    // This is only needed for debug printing.
    fn clone(&self) -> Self {
        Block { name:  self.name.clone(),
                start: self.start,
                len:   self.len,
                eef:   self.eef }
    }
}
impl Block {
    fn containsInsnIx(&self, iix: InsnIx) -> bool {
        iix.get() >= self.start.get()
            && iix.get() < self.start.get() + self.len
    }
}


struct Func {
    name:   String,
    entry:  Label,
    nVRegs: u32,
    insns:  Vec::</*InsnIx, */Insn>,    // indexed by InsnIx
    blocks: Vec::</*BlockIx, */Block>   // indexed by BlockIx
    // Note that |blocks| must be in order of increasing |Block::start|
    // fields.  Code that wants to traverse the blocks in some other order
    // must represent the ordering some other way; rearranging Func::blocks is
    // not allowed.
}
impl Clone for Func {
    // This is only needed for debug printing.
    fn clone(&self) -> Self {
        Func { name:   self.name.clone(),
               entry:  self.entry.clone(),
               nVRegs: self.nVRegs,
               insns:  self.insns.clone(),
               blocks: self.blocks.clone() }
    }
}

// Find a block Ix for a block name
fn lookup(blocks: &Vec::<Block>, name: String) -> BlockIx {
    let mut bix = 0;
    for b in blocks.iter() {
        if b.name == name {
            return mkBlockIx(bix);
        }
        bix += 1;
    }
    panic!("Func::lookup: can't resolve label name '{}'", name);
}

impl Func {
    fn new<'a>(name: &'a str, entry: &'a str) -> Self {
        Func {
            name: name.to_string(),
            entry: Label::Unresolved { name: entry.to_string() },
            nVRegs: 0,
            insns: Vec::<Insn>::new(),
            blocks: Vec::<Block>::new()
        }
    }

    fn print(&self, who: &str) {
        println!("");
        println!("Func {}: name='{}' entry='{}' {{",
                 who, self.name, self.entry.show());
        let mut ix = 0;
        for b in self.blocks.iter() {
            if ix > 0 {
                println!("");
            }
            println!("  {}:{}", mkBlockIx(ix).show(), b.name);
            for i in b.start.get() .. b.start.get() + b.len {
                println!("      {:<3}   {}"
                         , mkInsnIx(i).show(), self.insns[i as usize].show());
            }
            ix += 1;
        }
        println!("}}");
    }

    // Get a new VReg name
    fn vreg(&mut self) -> Reg {
        let v = Reg::VReg(mkVReg(self.nVRegs));
        self.nVRegs += 1;
        v
    }

    // Add a block to the Func
    fn block<'a>(&mut self, name: &'a str, mut insns: Vec::<Insn>) {
        let start = self.insns.len() as u32;
        let len = insns.len() as u32;
        self.insns.append(&mut insns);
        let b = mkBlock(name.to_string(), mkInsnIx(start), len);
        self.blocks.push(b);
    }

    // All blocks have been added.  Resolve labels and we're good to go.
    /* .finish(): check
          - all blocks nonempty
          - all blocks end in i_finish, i_goto or i_goto_ctf
          - no blocks have those insns before the end
          - blocks are in increasing order of ::start fields
          - all referenced blocks actually exist
          - convert references to block numbers
    */
    fn finish(&mut self) {
        for bixNo in 0 .. self.blocks.len() {
            let b = &self.blocks[bixNo];
            if b.len == 0 {
                panic!("Func::done: a block is empty");
            }
            if bixNo > 0
                && self.blocks[bixNo - 1].start >= self.blocks[bixNo].start {
                panic!("Func: blocks are not in increasing order of InsnIx");
            }
            for i in 0 .. b.len {
                let iix = mkInsnIx(b.start.get() + i);
                if i == b.len - 1 &&
                    !is_control_flow_insn(&self.insns[iix.get_usize()]) {
                    panic!("Func: block must end in control flow insn");
                }
                if i != b.len -1 &&
                    is_control_flow_insn(&self.insns[iix.get_usize()]) {
                    panic!("Func: block contains control flow insn not at end");
                }
            }
        }

        // Resolve all labels
        let blocks = &self.blocks;
        for i in self.insns.iter_mut() {
            resolveInsn(i, |name| lookup(blocks, name));
        }
        resolveLabel(&mut self.entry, |name| lookup(blocks, name));
    }
}


//=============================================================================
// The interpreter

struct IState<'a> {
    func:      &'a Func,
    nia:       InsnIx, // Program counter ("next instruction address")
    vregs:     Vec::<Option::<u32>>, // unlimited
    rregs:     Vec::<Option::<u32>>, // [0 .. maxRRegs)
    mem:       Vec::<Option::<u32>>, // [0 .. maxMem)
    slots:     Vec::<Option::<u32>>, // [0..] Spill slots, no upper limit
    n_insns:   usize,  // Stats: number of insns executed
    n_spills:  usize,  // Stats: .. of which are spills
    n_reloads: usize   // Stats: .. of which are reloads
}

impl<'a> IState<'a> {
    fn new(func: &'a Func, maxRRegs: usize, maxMem: usize) -> Self {
        let mut state =
            IState {
                func:      func,
                nia:       func.blocks[func.entry.getBlockIx().get_usize()]
                               .start,
                vregs:     Vec::new(),
                rregs:     Vec::new(),
                mem:       Vec::new(),
                slots:     Vec::new(),
                n_insns:   0,
                n_spills:  0,
                n_reloads: 0
            };
        state.rregs.resize(maxRRegs, None);
        state.mem.resize(maxMem, None);
        state
    }

    fn getRReg(&self, rreg: RReg) -> u32 {
        // No automatic resizing.  If the rreg doesn't exist, just fail.
        match self.rregs.get(rreg.get_usize()) {
            None =>
                panic!("IState::getRReg: invalid rreg# {}", rreg.get()),
            Some(None) =>
                panic!("IState::getRReg: read of uninit rreg# {}", rreg.get()),
            Some(Some(val))
                => *val
        }
    }

    fn setRReg(&mut self, rreg: RReg, val: u32) {
        // No automatic resizing.  If the rreg doesn't exist, just fail.
        match self.rregs.get_mut(rreg.get_usize()) {
            None =>
                panic!("IState::setRReg: invalid rreg# {}", rreg.get()),
            Some(valP)
                => *valP = Some(val)
        }
    }

    fn getVReg(&self, vreg: VReg) -> u32 {
        // The vector might be too small.  But in that case we'd be
        // reading the vreg uninitialised anyway, so just complain.
        match self.vregs.get(vreg.get_usize()) {
            None |          // indexing error
            Some(None) =>   // entry present, but has never been written
                panic!("IState::getVReg: read of uninit vreg # {}", vreg.get()),
            Some(Some(val))
                => *val
        }
    }

    fn setVReg(&mut self, vreg: VReg, val: u32) {
        // Auto-resize the vector if necessary
        let ix = vreg.get_usize();
        if ix >= self.vregs.len() {
            self.vregs.resize(ix + 1, None);
        }
        debug_assert!(ix < self.vregs.len());
        self.vregs[ix] = Some(val);
    }

    fn getSlot(&self, slot: Slot) -> u32 {
        // The vector might be too small.  But in that case we'd be
        // reading the slot uninitialised anyway, so just complain.
        match self.slots.get(slot.get_usize()) {
            None |          // indexing error
            Some(None) =>   // entry present, but has never been written
                panic!("IState::getSlot: read of uninit slot # {}", slot.get()),
            Some(Some(val))
                => *val
        }
    }

    fn setSlot(&mut self, slot: Slot, val: u32) {
        // Auto-resize the vector if necessary
        let ix = slot.get_usize();
        if ix >= self.slots.len() {
            self.slots.resize(ix + 1, None);
        }
        debug_assert!(ix < self.slots.len());
        self.slots[ix] = Some(val);
    }

    fn getReg(&self, reg: Reg) -> u32 {
        match reg {
            Reg::RReg(rreg) => self.getRReg(rreg),
            Reg::VReg(vreg) => self.getVReg(vreg)
        }
    }

    fn setReg(&mut self, reg: Reg, val: u32) {
        match reg {
            Reg::RReg(rreg) => self.setRReg(rreg, val),
            Reg::VReg(vreg) => self.setVReg(vreg, val)
        }
    }

    fn getMem(&self, addr: u32) -> u32 {
        // No auto resizing of the memory
        match self.mem.get(addr as usize) {
            None =>
                panic!("IState::getMem: invalid addr {}", addr),
            Some(None) =>
                panic!("IState::getMem: read of uninit mem at addr {}", addr),
            Some(Some(val))
                => *val
        }
    }

    fn setMem(&mut self, addr: u32, val: u32) {
        // No auto resizing of the memory
        match self.mem.get_mut(addr as usize) {
            None =>
                panic!("IState::setMem: invalid addr {}", addr),
            Some(valP)
                => *valP = Some(val)
        }
    }

    fn getRI(&self, ri: &RI) -> u32 {
        match ri {
            RI::Reg { reg } => self.getReg(*reg),
            RI::Imm { imm } => *imm
        }
    }

    fn getAM(&self, am: &AM) -> u32 {
        match am {
            AM::RI { base, offset } => self.getReg(*base) + offset,
            AM::RR { base, offset } => self.getReg(*base) + self.getReg(*offset)
        }
    }

    // Move the interpreter one step forward
    fn step(&mut self) -> bool {
        let mut done = false;

        let iix = self.nia.get();
        self.nia = mkInsnIx(iix + 1);
        self.n_insns += 1;

        let insn = &self.func.insns[iix as usize];
        match insn {
            Insn::Imm { dst, imm } =>
                self.setReg(*dst, *imm),
            Insn::Copy { dst, src } =>
                self.setReg(*dst, self.getReg(*src)),
            Insn::BinOp { op, dst, srcL, srcR } => {
                let srcL_v = self.getReg(*srcL);
                let srcR_v = self.getRI(srcR);
                let dst_v = op.calc(srcL_v, srcR_v);
                self.setReg(*dst, dst_v);
            },
            Insn::BinOpM { op, dst, srcR } => {
                let mut dst_v = self.getReg(*dst);
                let srcR_v = self.getRI(srcR);
                dst_v = op.calc(dst_v, srcR_v);
                self.setReg(*dst, dst_v);
            },
            Insn::Load { dst, addr } => {
                let addr_v = self.getAM(addr);
                let dst_v = self.getMem(addr_v);
                self.setReg(*dst, dst_v);
            },
            Insn::Store { addr, src } => {
                let addr_v = self.getAM(addr);
                let src_v  = self.getReg(*src);
                self.setMem(addr_v, src_v);
            },
            Insn::Spill { dst, src } => {
                let src_v = self.getRReg(*src);
                self.setSlot(*dst, src_v);
                self.n_spills += 1;
            },
            Insn::Reload { dst, src } => {
                let src_v = self.getSlot(*src);
                self.setRReg(*dst, src_v);
                self.n_reloads += 1;
            },
            Insn::Goto { target } =>
                self.nia = self.func.blocks[target.getBlockIx().get_usize()]
                               .start,
            Insn::GotoCTF { cond, targetT, targetF } => {
                let target =
                       if self.getReg(*cond) != 0 { targetT } else { targetF };
                self.nia = self.func.blocks[target.getBlockIx().get_usize()]
                               .start;
            },
            Insn::PrintS { str } =>
                print!("{}", str),
            Insn::PrintI { reg } =>
                print!("{}", self.getReg(*reg)),
            Insn::Finish { } =>
                done = true,
            _ => {
                println!("Interp: unhandled: {}", insn.show());
                panic!("IState::step: unhandled insn");
            }
        }
        done
    }
}

impl Func {
    fn run(&self, who: &str, nRRegs: usize) {
        println!("");
        println!("Running stage '{}': Func: name='{}' entry='{}'",
                 who, self.name, self.entry.show());

        let mut istate = IState::new(&self, nRRegs, /*maxMem=*/1000);
        let mut done = false;
        while !done {
            done = istate.step();
        }

        println!("Running stage '{}': done.  {} insns, {} spills, {} reloads",
                 who, istate.n_insns, istate.n_spills, istate.n_reloads);
    }
}


//=============================================================================
// Sets of things

struct Set<T> {
    set: FxHashSet<T>
}

impl<T: Eq + Ord + Hash + Copy + Show> Set<T> {
    fn empty() -> Self {
        Self {
            set: FxHashSet::<T>::default()
        }
    }

    fn unit(item: T) -> Self {
        let mut s = Self::empty();
        s.insert(item);
        s
    }

    fn two(item1: T, item2: T) -> Self {
        let mut s = Self::empty();
        s.insert(item1);
        s.insert(item2);
        s
    }

    fn card(&self) -> usize {
        self.set.len()
    }

    fn insert(&mut self, item: T) {
        self.set.insert(item);
    }

    fn is_empty(&self) -> bool {
        self.set.is_empty()
    }

    fn contains(&self, item: T) -> bool {
        self.set.contains(&item)
    }

    fn intersect(&mut self, other: &Self) {
        let mut res = FxHashSet::<T>::default();
        for item in self.set.iter() {
            if other.set.contains(item) {
                res.insert(*item);
            }
        }
        self.set = res;
    }

    fn union(&mut self, other: &Self) {
        for item in other.set.iter() {
            self.set.insert(*item);
        }
    }

    fn remove(&mut self, other: &Self) {
        for item in other.set.iter() {
            self.set.remove(item);
        }
    }

    fn intersects(&self, other: &Self) -> bool {
        !self.set.is_disjoint(&other.set)
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        self.set.is_subset(&other.set)
    }

    fn to_vec(&self) -> Vec::<T> {
        let mut res = Vec::<T>::new();
        for item in self.set.iter() {
            res.push(*item)
        }
        res.sort_unstable();
        res
    }

    fn from_vec(vec: Vec::<T>) -> Self {
        let mut res = Set::<T>::empty();
        for x in vec {
            res.insert(x);
        }
        res
    }

    fn equals(&self, other: &Self) -> bool {
        self.set == other.set
    }
}

impl<T:  Eq + Ord + Hash + Copy + Show> Show for Set<T> {
    fn show(&self) -> String {
        let mut str = "{".to_string();
        let mut first = true;
        for item in self.to_vec().iter() {
            if !first {
                str += &", ".to_string();
            }
            first = false;
            str += &item.show();
        }
        str + &"}".to_string()
    }
}

impl<T: Eq + Ord + Hash + Copy + Show + Clone> Clone for Set<T> {
    fn clone(&self) -> Self {
        let mut res = Set::<T>::empty();
        for item in self.set.iter() {
            res.set.insert(item.clone());
        }
        res
    }
}


struct SetIter<'a, T> {
    set_iter: Iter<'a, T>
}
impl<T> Set<T> {
    fn iter(&self) -> SetIter<T> {
        SetIter { set_iter: self.set.iter() }
    }
}
impl<'a, T> Iterator for SetIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next()
    }
}


//=============================================================================
// Queues

type Queue<T> = VecDeque<T>;


//=============================================================================
// Maps

type Map<K, V> = FxHashMap<K, V>;


//=============================================================================
// Control-flow analysis results for a Func: predecessors, successors,
// dominators and loop depths.

// CFGInfo contains CFG-related info computed from a Func.
struct CFGInfo {
    // All these vectors contain one element per Block in the Func.

    // Predecessor and successor maps.
    pred_map: Vec::</*BlockIx, */Set<BlockIx>>,
    succ_map: Vec::</*BlockIx, */Set<BlockIx>>,

    // This maps from a Block to the set of Blocks it is dominated by
    dom_map:  Vec::</*BlockIx, */Set<BlockIx>>,

    // This maps from a Block to the loop depth that it is at
    depth_map: Vec::</*BlockIx, */u32>,

    // Pre- and post-order sequences.  Iterating forwards through these
    // vectors enumerates the blocks in preorder and postorder respectively.
    pre_ord:  Vec::<BlockIx>,
    post_ord: Vec::<BlockIx>
}

impl CFGInfo {
    #[inline(never)]
    fn create(func: &Func) -> Self {
        let nBlocks = func.blocks.len();

        // First calculate the succ map, since we can do that directly from
        // the Func.

        // Func::finish() ensures that all blocks are non-empty, and that only
        // the last instruction is a control flow transfer.  Hence the
        // following won't miss any edges.
        let mut succ_map = Vec::<Set<BlockIx>>::new();
        for b in func.blocks.iter() {
            let last_insn = &func.insns[ b.start.get_usize()
                                         + b.len as usize - 1 ];
            let succs = last_insn.getTargets();
            let mut bixSet = Set::<BlockIx>::empty();
            for bix in succs.iter() {
                bixSet.insert(*bix);
            }
            succ_map.push(bixSet);
        }

        // Now invert the mapping
        let mut pred_map = Vec::<Set<BlockIx>>::new();
        pred_map.resize(nBlocks, Set::empty());
        for (src, dst_set) in (0..).zip(&succ_map) {
            for dst in dst_set.iter() {
                pred_map[dst.get_usize()].insert(mkBlockIx(src));
            }
        }

        // Calculate dominators..
        let dom_map = calc_dominators(&pred_map, func.entry.getBlockIx());

        // Stay sane ..
        debug_assert!(pred_map.len() == nBlocks);
        debug_assert!(succ_map.len() == nBlocks);
        debug_assert!(dom_map.len()  == nBlocks);

        // BEGIN compute loop depth of all Blocks
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
        let mut back_edges = Set::<(BlockIx, BlockIx)>::empty(); // (m->n)
        // Iterate over all edges
        for ixnoM in 0 .. nBlocks as u32 {
            let bixM = mkBlockIx(ixnoM);
            for bixN in succ_map[bixM.get_usize()].iter() {
                if dom_map[bixM.get_usize()].contains(*bixN) {
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
            let mut Loop: Set::<BlockIx>;
            let mut Stack: Vec::<BlockIx>;
            let mut bixP: BlockIx;
            let mut bixQ: BlockIx;
            Stack = Vec::<BlockIx>::new();
            Loop = Set::<BlockIx>::two(*bixM, *bixN);
            if bixM != bixN {
                // The next line is missing in the Muchnick description.
                // Without it the algorithm doesn't make any sense, though.
                Stack.push(*bixM);
                while let Some(bixP) = Stack.pop() {
                    for bixQ in pred_map[bixP.get_usize()].iter() {
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

        natural_loops.sort_by(
            |blockSet1, blockSet2|
            blockSet1.card().partial_cmp(&blockSet2.card()).unwrap());

        let nLoops = natural_loops.len();
        let mut loop_depths = Vec::<u32>::new();
        loop_depths.resize(nLoops, 0);

        for i in 0 .. nLoops {
            let mut curr  = i;
            let mut depth = 1;
            for j in i+1 .. nLoops {
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
        let mut depth_map = Vec::<u32>::new();
        depth_map.resize(nBlocks, 0);
        for (loopBixs, depth) in natural_loops.iter().zip(loop_depths) {
            //println!("QQQQ4 {} {}", depth.show(), loopBixs.show());
            for loopBix in loopBixs.iter() {
                if depth_map[loopBix.get_usize()] < depth {
                    depth_map[loopBix.get_usize()] = depth;
                }
            }
        }

        debug_assert!(depth_map.len() == nBlocks);

        //
        // END compute loop depth of all Blocks

        // BEGIN compute preord/postord
        //
        // This is per Fig 7.12 of Muchnick 1997
        //
        let mut pre_ord  = Vec::<BlockIx>::new();
        let mut post_ord = Vec::<BlockIx>::new();

        let mut visited = Vec::<bool>::new();
        visited.resize(nBlocks, false);

        // FIXME: change this to use an explicit stack.
        fn dfs(pre_ord: &mut Vec::<BlockIx>, post_ord: &mut Vec::<BlockIx>,
               visited: &mut Vec::<bool>,
               succ_map: &Vec::</*BlockIx, */Set<BlockIx>>,
               bix: BlockIx) {
            let ix = bix.get_usize();
            debug_assert!(!visited[ix]);
            visited[ix] = true;
            pre_ord.push(bix);
            for succ in succ_map[ix].iter() {
                if !visited[succ.get_usize()] {
                    dfs(pre_ord, post_ord, visited, succ_map, *succ);
                }
            }
            post_ord.push(bix);
        }

        dfs(&mut pre_ord, &mut post_ord, &mut visited,
            &succ_map, func.entry.getBlockIx());

        debug_assert!(pre_ord.len() == post_ord.len());
        debug_assert!(pre_ord.len() <= nBlocks);
        if pre_ord.len() < nBlocks {
            // This can happen if the graph contains nodes unreachable from
            // the entry point.  In which case, deal with any leftovers.
            for i in 0 .. nBlocks {
                if !visited[i] {
                    dfs(&mut pre_ord, &mut post_ord, &mut visited,
                        &succ_map, mkBlockIx(i as u32));
                }
            }
        }
        debug_assert!(pre_ord.len() == nBlocks);
        debug_assert!(post_ord.len() == nBlocks);
        //
        // END compute preord/postord

        //println!("QQQQ pre_ord  {}", pre_ord.show());
        //println!("QQQQ post_ord {}", post_ord.show());
        CFGInfo { pred_map, succ_map, dom_map, depth_map, pre_ord, post_ord }
    }
}


// Calculate the dominance relationship, given |pred_map| and a start node
// |start|.  The resulting vector maps each block to the set of blocks that
// dominate it. This algorithm is from Fig 7.14 of Muchnick 1997. The
// algorithm is described as simple but not as performant as some others.
#[inline(never)]
fn calc_dominators(pred_map: &Vec::</*BlockIx, */Set<BlockIx>>,
                   start: BlockIx)
                   -> Vec::</*BlockIx, */Set<BlockIx>> {
    // FIXME: nice up the variable names (D, T, etc) a bit.
    let nBlocks = pred_map.len();
    let mut dom_map = Vec::<Set<BlockIx>>::new();
    {
        let r: BlockIx = start;
        let N: Set<BlockIx> =
            Set::from_vec((0 .. nBlocks as u32)
                          .map(|bixNo| mkBlockIx(bixNo)).collect());
        let mut D: Set<BlockIx>;
        let mut T: Set<BlockIx>;
        let mut n: BlockIx;
        let mut p: BlockIx;
        let mut change = true;
        dom_map.resize(nBlocks, Set::<BlockIx>::empty());
        dom_map[r.get_usize()] = Set::unit(r);
        for ixnoN in 0 .. nBlocks as u32 {
            let bixN = mkBlockIx(ixnoN);
            if bixN != r {
                dom_map[bixN.get_usize()] = N.clone();
            }
        }
        loop {
            change = false;
            for ixnoN in 0 .. nBlocks as u32 {
                let bixN = mkBlockIx(ixnoN);
                if bixN == r {
                    continue;
                }
                T = N.clone();
                for bixP in pred_map[bixN.get_usize()].iter() {
                    T.intersect(&dom_map[bixP.get_usize()]);
                }
                D = T.clone();
                D.insert(bixN);
                if !D.equals(&dom_map[bixN.get_usize()]) {
                    change = true;
                    dom_map[bixN.get_usize()] = D;
                }
            }
            if !change {
                break;
            }
        }
    }
    dom_map
}


//=============================================================================
// Computation of live-in and live-out sets

impl Func {
    // Returned vectors contain one element per block
    #[inline(never)]
    fn calc_def_and_use(&self) -> (Vec::<Set<Reg>>, Vec::<Set<Reg>>) {
        let mut def_sets = Vec::new();
        let mut use_sets = Vec::new();
        for b in self.blocks.iter() {
            let mut def = Set::empty();
            let mut uce = Set::empty();
            for iix in b.start.get_usize() .. b.start.get_usize()
                                              + b.len as usize {
                let insn = &self.insns[iix];
                let (regs_d, regs_m, regs_u) = insn.getRegUsage();
                // Add to |uce|, any registers for which the first event
                // in this block is a read.  Dealing with the "first event"
                // constraint is a bit tricky.
                for u in regs_u.iter().chain(regs_m.iter()) {
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
                for d in regs_d.iter().chain(regs_m.iter()) {
                    def.insert(*d);
                }
            }
            def_sets.push(def);
            use_sets.push(uce);
        }
        (def_sets, use_sets)
    }

    // Returned vectors contain one element per block
    #[inline(never)]
    fn calc_livein_and_liveout(&self,
                               def_sets_per_block: &Vec::<Set<Reg>>,
                               use_sets_per_block: &Vec::<Set<Reg>>,
                               cfg_info: &CFGInfo
                              ) -> (Vec::<Set<Reg>>, Vec::<Set<Reg>>) {
        let nBlocks = self.blocks.len();
        let empty = Set::<Reg>::empty();

        let mut nEvals = 0;
        let mut liveouts = Vec::<Set::<Reg>>::new();
        liveouts.resize(nBlocks, empty.clone());

        // Initialise the work queue so as to do a reverse preorder traversal
        // through the graph, after which blocks are re-evaluated on demand.
        let mut workQ = Queue::<BlockIx>::new();
        for i in 0 .. nBlocks {
            // bixI travels in "reverse preorder"
            let bixI = cfg_info.pre_ord[nBlocks - 1 - i];
            workQ.push_back(bixI);
        }

        while let Some(bixI) = workQ.pop_front() {
            // Compute a new value for liveouts[bixI]
            let ixI = bixI.get_usize();
            let mut set = Set::<Reg>::empty();
            for bixJ in cfg_info.succ_map[ixI].iter() {
                let ixJ = bixJ.get_usize();
                let mut liveinJ = liveouts[ixJ].clone();
                liveinJ.remove(&def_sets_per_block[ixJ]);
                liveinJ.union(&use_sets_per_block[ixJ]);
                set.union(&liveinJ);
            }
            nEvals += 1;

            if !set.equals(&liveouts[ixI]) {
                liveouts[ixI] = set;
                // Add |bixI|'s predecessors to the work queue, since their
                // liveout values might be affected.
                for bixJ in cfg_info.pred_map[ixI].iter() {
                    workQ.push_back(*bixJ);
                }
            }
        }

        // The liveout values are done, but we need to compute the liveins
        // too.
        let mut liveins = Vec::<Set::<Reg>>::new();
        liveins.resize(nBlocks, empty.clone());
        for ixI in 0 .. nBlocks {
            let mut liveinI = liveouts[ixI].clone();
            liveinI.remove(&def_sets_per_block[ixI]);
            liveinI.union(&use_sets_per_block[ixI]);
            liveins[ixI] = liveinI;
        }

        if false {
            let mut sum_card_LI = 0;
            let mut sum_card_LO = 0;
            for i in 0 .. nBlocks {
                sum_card_LI += liveins[i].card();
                sum_card_LO += liveouts[i].card();
            }
            println!("QQQQ calc_LI/LO: nEvals {}, tot LI {}, tot LO {}",
                     nEvals, sum_card_LI, sum_card_LO);
        }

        (liveins, liveouts)
    }
}


//=============================================================================
// Representing and printing of live range fragments.

#[derive(Copy, Clone, Hash, PartialEq, Eq, Ord)]
// There are four "points" within an instruction that are of interest, and
// these have a total ordering: R < U < D < S.  They are:
//
// * R(eload): this is where any reload insns for the insn itself are
//   considered to live.
//
// * U(se): this is where the insn is considered to use values from those of
//   its register operands that appear in a Read or Modify role.
//
// * D(ef): this is where the insn is considered to define new values for
//   those of its register operands that appear in a Write or Modify role.
//
// * S(pill): this is where any spill insns for the insn itself are considered
//   to live.
//
// Instructions in the incoming Func may only exist at the U and D points,
// and so their associated live range fragments will only mention the U and D
// points.  However, when adding spill code, we need a way to represent live
// ranges involving the added spill and reload insns, in which case R and S
// come into play:
//
// * A reload for instruction i is considered to be live from i.R to i.U.
//
// * A spill for instruction i is considered to be live from i.D to i.S.
enum Point { R, U, D, S }
impl Point {
    fn isR(self) -> bool { match self { Point::R => true, _ => false } }
    fn isU(self) -> bool { match self { Point::U => true, _ => false } }
    fn isD(self) -> bool { match self { Point::D => true, _ => false } }
    fn isS(self) -> bool { match self { Point::S => true, _ => false } }
    fn isUorD(self) -> bool { self.isU() || self.isD() }
}
impl PartialOrd for Point {
    // In short .. R < U < D < S.  This is probably what would be #derive'd
    // anyway, but we need to be sure.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // This is a bit idiotic, but hey .. hopefully LLVM can turn it into a
        // no-op.
        fn convert(pt: &Point) -> u32 {
            match pt {
                Point::R => 0,
                Point::U => 1,
                Point::D => 2,
                Point::S => 3,
            }
        }
        convert(self).partial_cmp(&convert(other))
    }
}


// See comments below on |Frag| for the meaning of |InsnPoint|.
#[derive(Copy, Clone, Hash, PartialEq, Eq, Ord)]
struct InsnPoint {
    iix: InsnIx,
    pt: Point
}
fn mkInsnPoint(iix: InsnIx, pt: Point) -> InsnPoint {
    InsnPoint { iix, pt }
}
fn InsnPoint_R(iix: InsnIx) -> InsnPoint {
    InsnPoint { iix: iix, pt: Point::R }
}
fn InsnPoint_U(iix: InsnIx) -> InsnPoint {
    InsnPoint { iix: iix, pt: Point::U }
}
fn InsnPoint_D(iix: InsnIx) -> InsnPoint {
    InsnPoint { iix: iix, pt: Point::D }
}
fn InsnPoint_S(iix: InsnIx) -> InsnPoint {
    InsnPoint { iix: iix, pt: Point::S }
}
impl PartialOrd for InsnPoint {
    // Again .. don't assume anything about the #derive'd version.  These have
    // to be ordered using |iix| as the primary key and |pt| as the
    // secondary.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.iix.partial_cmp(&other.iix) {
            Some(Ordering::Less)    => Some(Ordering::Less),
            Some(Ordering::Greater) => Some(Ordering::Greater),
            Some(Ordering::Equal)   => self.pt.partial_cmp(&other.pt),
            None => panic!("InsnPoint::partial_cmp: fail #1"),
        }
    }
}
impl Show for InsnPoint {
    fn show(&self) -> String {
        match self.pt {
            Point::R => self.iix.get().show() + &".r".to_string(),
            Point::U => self.iix.get().show() + &".u".to_string(),
            Point::D => self.iix.get().show() + &".d".to_string(),
            Point::S => self.iix.get().show() + &".s".to_string()
        }
    }
}


// A handy summary hint for a Frag.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum FragKind {
    Local,   // Fragment exists entirely inside one block
    LiveIn,  // Fragment is live in to a block, but ends inside it
    LiveOut, // Fragment is live out of a block, but starts inside it
    Thru     // Fragment is live through the block (starts and ends outside it)
}
impl Show for FragKind {
    fn show(&self) -> String {
        match self {
            FragKind::Local   => "Loc".to_string(),
            FragKind::LiveIn  => "LIN".to_string(),
            FragKind::LiveOut => "LOU".to_string(),
            FragKind::Thru    => "THR".to_string()
        }
    }
}


// Indices into vectors of Frags (see below).
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum FragIx {
    FragIx(u32)
}
fn mkFragIx(n: u32) -> FragIx { FragIx::FragIx(n) }
impl FragIx {
    fn get(self) -> u32 { match self { FragIx::FragIx(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for FragIx {
    fn show(&self) -> String {
        "f".to_string() + &self.get().to_string()
    }
}


// A Live Range Fragment (Frag) describes a consecutive sequence of one or
// more instructions, in which a Reg is "live".  The sequence must exist
// entirely inside only one basic block.
//
// However, merely indicating the start and end instruction numbers isn't
// enough: we must also include a "Use or Def" indication.  These indicate two
// different "points" within each instruction: the Use position, where
// incoming registers are read, and the Def position, where outgoing registers
// are written.  The Use position is considered to come before the Def
// position, as described for |Point| above.
//
// When we come to generate spill/restore live ranges, Point::S and Point::R
// also come into play.  Live ranges (and hence, Frags) that do not perform
// spills or restores should not use either of Point::S or Point::R.
//
// The set of positions denoted by
//
//    {0 .. #insns-1} x {Reload point, Use point, Def point, Spill point}
//
// is exactly the set of positions that we need to keep track of when mapping
// live ranges to registers.  This the reason for the type InsnPoint.  Note
// that InsnPoint values have a total ordering, at least within a single basic
// block: the insn number is used as the primary key, and the Point part is
// the secondary key, with Reload < Use < Def < Spill.
//
// Finally, a Frag has a |count| field, which is a u16 indicating how often
// the associated storage unit (Reg) is mentioned inside the Frag.  It is
// assumed that the Frag is associated with some Reg.  If not, the |count|
// field is meaningless.
//
// The |bix| field is actually redundant, since the containing |Block| can be
// inferred, laboriously, from |first| and |last|, providing you have a
// |Block| table to hand.  It is included here for convenience.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct Frag {
    bix:   BlockIx,
    kind:  FragKind,
    first: InsnPoint,
    last:  InsnPoint,
    count: u16
}
impl Show for Frag {
    fn show(&self) -> String {
        self.bix.show() + &"-".to_string()
            + &self.count.to_string() + &"x-".to_string()
            + &self.kind.show() + &"-".to_string()
            + &self.first.show() + &"-" + &self.last.show()
    }
}
fn mk_Frag_General(blocks: &Vec::<Block>, bix: BlockIx,
                   first: InsnPoint, last: InsnPoint, count: u16) -> Frag {
    let block = &blocks[bix.get_usize()];
    debug_assert!(block.len >= 1);
    debug_assert!(block.containsInsnIx(first.iix));
    debug_assert!(block.containsInsnIx(last.iix));
    debug_assert!(first <= last);
    if first == last {
        debug_assert!(count == 1);
    }
    let first_iix_in_block = block.start.get();
    let last_iix_in_block  = first_iix_in_block + block.len - 1;
    let first_pt_in_block  = InsnPoint_U(mkInsnIx(first_iix_in_block));
    let last_pt_in_block   = InsnPoint_D(mkInsnIx(last_iix_in_block));
    let kind =
        match (first == first_pt_in_block, last == last_pt_in_block) {
            (false, false) => FragKind::Local,
            (false, true)  => FragKind::LiveOut,
            (true,  false) => FragKind::LiveIn,
            (true,  true)  => FragKind::Thru
        };
    Frag { bix, kind, first, last, count }
}
fn mk_Frag_Local(blocks: &Vec::<Block>, bix: BlockIx,
                 live_after: InsnIx, dead_after: InsnIx, count: u16) -> Frag {
    let block = &blocks[bix.get_usize()];
    debug_assert!(block.containsInsnIx(live_after));
    debug_assert!(block.containsInsnIx(dead_after));
    debug_assert!(live_after <= dead_after);
    if live_after == dead_after {
        // A dead write, but we must represent it correctly.
        debug_assert!(count == 1);
        Frag { bix:   bix,
               kind:  FragKind::Local,
               first: InsnPoint_D(live_after),
               last:  InsnPoint_D(live_after),
               count: count }
    } else {
        debug_assert!(count >= 2);
        Frag { bix:   bix,
               kind:  FragKind::Local,
               first: InsnPoint_D(live_after),
               last:  InsnPoint_U(dead_after),
               count: count }
    }
}
fn mk_Frag_LiveIn(blocks: &Vec::<Block>,
                  bix: BlockIx, dead_after: InsnIx, count: u16) -> Frag {
    debug_assert!(count >= 1);
    let block = &blocks[bix.get_usize()];
    debug_assert!(block.containsInsnIx(dead_after));
    Frag { bix:   bix,
           kind:  FragKind::LiveIn,
           first: InsnPoint_U(block.start),
           last:  InsnPoint_U(dead_after),
           count: count }
}
fn mk_Frag_LiveOut(blocks: &Vec::<Block>,
                  bix: BlockIx, live_after: InsnIx, count: u16) -> Frag {
    debug_assert!(count >= 1);
    let block = &blocks[bix.get_usize()];
    debug_assert!(block.containsInsnIx(live_after));
    Frag { bix:   bix,
           kind:  FragKind::LiveOut,
           first: InsnPoint_D(live_after),
           last:  InsnPoint_D(block.start.plus(block.len - 1)),
           count: count }
}
fn mk_Frag_Thru(blocks: &Vec::<Block>, bix: BlockIx, count: u16) -> Frag {
    // Count can be any value, zero or more.
    let block = &blocks[bix.get_usize()];
    Frag { bix:   bix,
           kind:  FragKind::Thru,
           first: InsnPoint_U(block.start),
           last:  InsnPoint_D(block.start.plus(block.len - 1)),
           count: count }
}


// Comparison of Frags.  They form a partial order.
#[derive(PartialEq)]
enum FCR { LT, GT, EQ, UN }

fn cmpFrags(f1: &Frag, f2: &Frag) -> FCR {
    if f1.last < f2.first { return FCR::LT; }
    if f1.first > f2.last { return FCR::GT; }
    if f1.first == f2.first && f1.last == f2.last { return FCR::EQ; }
    FCR::UN
}
impl Frag {
    fn contains(&self, ipt: &InsnPoint) -> bool {
        self.first <= *ipt && *ipt <= self.last
    }
}


//=============================================================================
// Computation of Frags (Live Range Fragments)

// This is surprisingly complex, in part because of the need to correctly
// handle (1) live-in and live-out Regs, (2) dead writes, and (3) instructions
// that modify registers rather than merely reading or writing them.

impl Func {
    // Calculate all the Frags for |bix|.  Add them to |outFEnv| and add to
    // |outMap|, the associated FragIxs, segregated by Reg.  |bix|, |livein|
    // and |liveout| are expected to be valid in the context of the Func |self|
    // (duh!)
    fn get_Frags_for_block(&self, bix: BlockIx,
                           livein: &Set::<Reg>, liveout: &Set::<Reg>,
                           outMap: &mut Map::<Reg, Vec::<FragIx>>,
                           outFEnv: &mut Vec::<Frag>)
    {
        //println!("QQQQ --- block {}", bix.show());
        // BEGIN ProtoFrag
        // A ProtoFrag carries information about a write .. read range, within
        // a Block, which we will later turn into a fully-fledged Frag.  It
        // basically records the first and last-known InsnPoints for
        // appearances of a Reg.
        //
        // ProtoFrag also keeps count of the number of appearances of the Reg
        // to which it pertains, using |uses|.  The counts get rolled into the
        // resulting Frags, and later are used to calculate spill costs.
        //
        // The running state of this function is a map from Reg to ProtoFrag.
        // Only Regs that actually appear in the Block (or are live-in to it)
        // are mapped.  This has the advantage of economy, since most Regs
        // will not appear in (or be live-in to) most Blocks.
        //
        struct ProtoFrag {
            // The InsnPoint in this Block at which the associated Reg most
            // recently became live (when moving forwards though the Block).
            // If this value is the first InsnPoint for the Block (the U point
            // for the Block's lowest InsnIx), that indicates the associated
            // Reg is live-in to the Block.
            first: InsnPoint,

            // And this is the InsnPoint which is the end point (most recently
            // observed read, in general) for the current Frag under
            // construction.  In general we will move |last| forwards as we
            // discover reads of the associated Reg.  If this is the last
            // InsnPoint for the Block (the D point for the Block's highest
            // InsnInx), that indicates that the associated reg is live-out
            // from the Block.
            last: InsnPoint,

            // Number of mentions of the associated Reg in this ProtoFrag.
            uses: u16
        }
        impl Show for ProtoFrag {
            fn show(&self) -> String {
                self.uses.show() + &"x ".to_string() + &self.first.show()
                    + &"-".to_string() + &self.last.show()
            }
        }
        // END ProtoFrag

        fn plus1(n: u16) -> u16 { if n == 0xFFFFu16 { n } else { n+1 } }

        // Some handy constants.
        let blocks = &self.blocks;
        let block  = &blocks[bix.get_usize()];
        debug_assert!(block.len >= 1);
        let first_iix_in_block = block.start.get();
        let last_iix_in_block  = first_iix_in_block + block.len - 1;
        let first_pt_in_block  = InsnPoint_U(mkInsnIx(first_iix_in_block));
        let last_pt_in_block   = InsnPoint_D(mkInsnIx(last_iix_in_block));

        // The running state.
        let mut state = Map::<Reg, ProtoFrag>::default();

        // The generated Frags are initially are dumped in here.  We group
        // them by Reg at the end of this function.
        let mut tmpResultVec = Vec::<(Reg, Frag)>::new();

        // First, set up |state| as if all of |livein| had been written just
        // prior to the block.
        for r in livein.iter() {
            state.insert(*r, ProtoFrag { uses: 0,
                                         first: first_pt_in_block,
                                         last:  first_pt_in_block });
        }

        // Now visit each instruction in turn, examining first the registers
        // it reads, then those it modifies, and finally those it writes.
        for ix in block.start.get() .. block.start.get() + block.len {
            let iix = mkInsnIx(ix);
            let insn = &self.insns[ix as usize];

            //fn id<'a>(x: Vec::<(&'a Reg, &'a ProtoFrag)>)
            //          -> Vec::<(&'a Reg, &'a ProtoFrag)> { x }
            //println!("");
            //println!("QQQQ state before {}",
            //         id(state.iter().collect()).show());
            //println!("QQQQ insn {} {}", iix.show(), insn.show());

            let (regs_d, regs_m, regs_u) = insn.getRegUsage();

            // Examine reads.  This is pretty simple.  They simply extend an
            // existing ProtoFrag to the U point of the reading insn.
            for r in regs_u.iter() {
                let new_pf: ProtoFrag;
                match state.get(r) {
                    // First event for |r| is a read, but it's not listed in
                    // |livein|, since otherwise |state| would have an entry
                    // for it.
                    None => {
                        panic!("get_Frags_for_block: fail #1");
                    },
                    // This the first or subsequent read after a write.  Note
                    // that the "write" can be either a real write, or due to
                    // the fact that |r| is listed in |livein|.  We don't care
                    // here.
                    Some(ProtoFrag { uses, first, last }) => {
                        let new_last = InsnPoint_U(iix);
                        debug_assert!(last <= &new_last);
                        new_pf = ProtoFrag { uses: plus1(*uses),
                                             first: *first, last: new_last };
                    },
                }
                state.insert(*r, new_pf);
            }

            // Examine modifies.  These are handled almost identically to
            // reads, except that they extend an existing ProtoFrag down to
            // the D point of the modifying insn.
            for r in regs_m.iter() {
                let new_pf: ProtoFrag;
                match state.get(r) {
                    // First event for |r| is a read (really, since this insn
                    // modifies |r|), but it's not listed in |livein|, since
                    // otherwise |state| would have an entry for it.
                    None => {
                        panic!("get_Frags_for_block: fail #2");
                    },
                    // This the first or subsequent modify after a write.
                    Some(ProtoFrag { uses, first, last }) => {
                        let new_last = InsnPoint_D(iix);
                        debug_assert!(last <= &new_last);
                        new_pf = ProtoFrag { uses: plus1(*uses),
                                             first: *first, last: new_last };
                    },
                }
                state.insert(*r, new_pf);
            }

            // Examine writes (but not writes implied by modifies).  The
            // general idea is that a write causes us to terminate the
            // existing ProtoFrag, if any, add it to |tmpResultVec|, and start
            // a new frag.
            for r in regs_d.iter() {
                let new_pf: ProtoFrag;
                match state.get(r) {
                    // First mention of a Reg we've never heard of before.
                    // Start a new ProtoFrag for it and keep going.
                    None => {
                        let new_pt = InsnPoint_D(iix);
                        new_pf = ProtoFrag { uses: 1,
                                             first: new_pt, last: new_pt };
                    },
                    // There's already a ProtoFrag for |r|.  This write will
                    // start a new one, so flush the existing one and note
                    // this write.
                    Some(ProtoFrag { uses, first, last }) => {
                        if first == last {
                            debug_assert!(*uses == 1);
                        }
                        let frag = mk_Frag_General(blocks, bix,
                                                   *first, *last, *uses);
                        tmpResultVec.push((*r, frag));
                        let new_pt = InsnPoint_D(iix);
                        new_pf = ProtoFrag { uses: 1,
                                             first: new_pt, last: new_pt };
                    }
                }
                state.insert(*r, new_pf);
            }
            //println!("QQQQ state after  {}",
            //         id(state.iter().collect()).show());
        }

        // We are at the end of the block.  We still have to deal with
        // live-out Regs.  We must also deal with ProtoFrags in |state| that
        // are for registers not listed as live-out.

        // Deal with live-out Regs.  Treat each one as if it is read just
        // after the block.
        for r in liveout.iter() {
            //println!("QQQQ post: liveout:  {}", r.show());
            match state.get(r) {
                // This can't happen.  |r| is in |liveout|, but this implies
                // that it is neither defined in the block nor present in
                // |livein|.
                None => {
                    panic!("get_Frags_for_block: fail #3");
                },
                // |r| is written (or modified), either literally or by virtue
                // of being present in |livein|, and may or may not
                // subsequently be read -- we don't care, because it must be
                // read "after" the block.  Create a |LiveOut| or |Thru| frag
                // accordingly.
                Some(ProtoFrag { uses, first, last:_ }) => {
                    let frag = mk_Frag_General(blocks, bix,
                                               *first, last_pt_in_block, *uses);
                    tmpResultVec.push((*r, frag));
                }
            }
            // Remove the entry from |state| so that the following loop
            // doesn't process it again.
            state.remove(r);
        }

        // Finally, round up any remaining ProtoFrags left in |state|.
        for (r, pf) in state.iter() {
            //println!("QQQQ post: leftover: {} {}", r.show(), pf.show());
            if pf.first == pf.last {
                debug_assert!(pf.uses == 1);
            }
            let frag = mk_Frag_General(blocks, bix, pf.first, pf.last, pf.uses);
            //println!("QQQQ post: leftover: {}", (r,frag).show());
            tmpResultVec.push((*r, frag));
        }

        // Copy the entries in |tmpResultVec| into |outMap| and |outVec|.
        // TODO: do this as we go along, so as to avoid the use of a temporary
        // vector.
        for (r, frag) in tmpResultVec {
            outFEnv.push(frag);
            let new_fix = mkFragIx(outFEnv.len() as u32 - 1);
            match outMap.get_mut(&r) {
                None => { outMap.insert(r, vec![new_fix]); },
                Some(fragVec) => { fragVec.push(new_fix); }
            }
        }
    }

    #[inline(never)]
    fn get_Frags(&self,
                 livein_sets_per_block:  &Vec::<Set<Reg>>,
                 liveout_sets_per_block: &Vec::<Set<Reg>>
                ) -> (Map::<Reg, Vec<FragIx>>, Vec::<Frag>)
    {
        debug_assert!(livein_sets_per_block.len()  == self.blocks.len());
        debug_assert!(liveout_sets_per_block.len() == self.blocks.len());
        let mut resMap  = Map::<Reg, Vec<FragIx>>::default();
        let mut resFEnv = Vec::<Frag>::new();
        for bix in 0 .. self.blocks.len() {
            self.get_Frags_for_block(mkBlockIx(bix.try_into().unwrap()),
                                     &livein_sets_per_block[bix],
                                     &liveout_sets_per_block[bix],
                                     &mut resMap, &mut resFEnv);
        }
        (resMap, resFEnv)
    }
}


//=============================================================================
// Vectors of FragIxs, sorted so that the associated Frags are in ascending
// order (per their InsnPoint fields).

// The "fragment environment" (sometimes called 'fenv') to which the FragIxs
// refer, is not stored here.

#[derive(Clone)]
struct SortedFragIxs {
    fragIxs: Vec::<FragIx>
}
impl SortedFragIxs {
    fn show(&self) -> String {
        self.fragIxs.show()
    }

    fn show_with_fenv(&self, fenv: &Vec::<Frag>) -> String {
        let mut frags = Vec::<Frag>::new();
        for fix in &self.fragIxs {
            frags.push(fenv[fix.get_usize()]);
        }
        "SFIxs_".to_string() + &frags.show()
    }

    fn check(&self, fenv: &Vec::<Frag>) {
        let mut ok = true;
        for i in 1 .. self.fragIxs.len() {
            let prev_frag = &fenv[self.fragIxs[i-1].get_usize()];
            let this_frag = &fenv[self.fragIxs[i-0].get_usize()];
            if cmpFrags(prev_frag, this_frag) != FCR::LT {
                ok = false;
                break;
            }
        }
        if !ok {
            panic!("SortedFragIxs::check: vector not ok");
        }
    }

    fn new(source: &Vec::<FragIx>, fenv: &Vec::<Frag>) -> Self {
        let mut res = SortedFragIxs { fragIxs: source.clone() };
        // check the source is ordered, and clone (or sort it)
        res.fragIxs.sort_unstable_by(
            |fix_a, fix_b| {
                match cmpFrags(&fenv[fix_a.get_usize()],
                               &fenv[fix_b.get_usize()]) {
                    FCR::LT => Ordering::Less,
                    FCR::GT => Ordering::Greater,
                    FCR::EQ | FCR::UN =>
                        panic!("SortedFragIxs::new: overlapping or dup Frags!")
                }
            });
        res.check(fenv);
        res
    }

    fn unit(fix: FragIx, fenv: &Vec::<Frag>) -> Self {
        let mut res = SortedFragIxs { fragIxs: Vec::<FragIx>::new() };
        res.fragIxs.push(fix);
        res.check(fenv);
        res
    }
}


//=============================================================================
// Representing and printing live ranges.  These are represented by two
// different but closely related types, RLR and VLR.

// RLRs are live ranges for real regs (RRegs).  VLRs are live ranges for
// virtual regs (VRegs).  VLRs are the fundamental unit of allocation.  Both
// RLR and VLR pair the relevant kind of Reg with a vector of FragIxs in which
// it is live.  The FragIxs are indices into some vector of Frags (a "fragment
// environment", 'fenv'), which is not specified here.  They are sorted so as
// to give ascending order to the Frags which they refer to.
//
// VLRs contain metrics.  Not all are initially filled in:
//
// * |size| is the number of instructions in total spanned by the LR.  It must
//   not be zero.
//
// * |cost| is an abstractified measure of the cost of spilling the LR.  The
//   only constraint (w.r.t. correctness) is that normal LRs have a |Some|
//   value, whilst |None| is reserved for live ranges created for spills and
//   reloads and interpreted to mean "infinity".  This is needed to guarantee
//   that allocation can always succeed in the worst case, in which all of the
//   original live ranges of the program are spilled.
//
// RLRs don't carry any metrics info since we are not trying to allocate them.
// We merely need to work around them.
//
// I find it helpful to think of a live range, both RLRs and VLRs, as a
// "renaming equivalence class".  That is, if you rename |reg| at some point
// inside |sfrags|, then you must rename *all* occurrences of |reg| inside
// |sfrags|, since otherwise the program will no longer work.
//
// Invariants for RLR/VLR Frag sets (their |sfrags| fields):
//
// * Either |sfrags| contains just one Frag, in which case it *must* be
//   FragKind::Local.
//
// * Or |sfrags| contains more than one Frag, in which case: at least one must
//   be FragKind::LiveOut, at least one must be FragKind::LiveIn, and there
//   may be zero or more FragKind::Thrus.


struct RLR {
    rreg:   RReg,
    sfrags: SortedFragIxs
}
impl Show for RLR {
    fn show(&self) -> String {
        self.rreg.show()
            + &" ".to_string() + &self.sfrags.show()
    }
}


// VLRs are live ranges for virtual regs (VRegs).  These do carry metrics info
// and also the identity of the RReg to which they eventually got allocated.

struct VLR {
    vreg:   VReg,
    rreg:   Option<RReg>,
    sfrags: SortedFragIxs,
    size:   u16,
    cost:   Option<f32>,
}
impl Show for VLR {
    fn show(&self) -> String {
        let cost_str: String;
        match self.cost {
            None => {
                cost_str = "INFIN".to_string();
            },
            Some(c) => {
                cost_str = format!("{:<5.2}", c);
            }
        }
        let mut res = self.vreg.show();
        if self.rreg.is_some() {
            res += &"->".to_string();
            res += &self.rreg.unwrap().show();
        }
        res + &" s=".to_string() + &self.size.to_string()
            + &",c=".to_string() + &cost_str
            + &" ".to_string() + &self.sfrags.show()
    }
}


// Indices into vectors of RLRs.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RLRIx {
    RLRIx(u32)
}
fn mkRLRIx(n: u32) -> RLRIx { RLRIx::RLRIx(n) }
impl RLRIx {
    fn get(self) -> u32 { match self { RLRIx::RLRIx(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for RLRIx {
    fn show(&self) -> String {
        "rlr".to_string() + &self.get().to_string()
    }
}


// Indices into vectors of VLRs.
#[derive(Clone, Copy, PartialEq, Eq)]
enum VLRIx {
    VLRIx(u32)
}
fn mkVLRIx(n: u32) -> VLRIx { VLRIx::VLRIx(n) }
impl VLRIx {
    fn get(self) -> u32 { match self { VLRIx::VLRIx(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for VLRIx {
    fn show(&self) -> String {
        "vlr".to_string() + &self.get().to_string()
    }
}


//=============================================================================
// Merging of Frags, producing the final LRs, minus metrics

#[inline(never)]
fn merge_Frags(fragIx_vecs_per_reg: &Map::<Reg, Vec<FragIx>>,
               frag_env: &Vec::</*FragIx, */Frag>,
               cfg_info: &CFGInfo)
               -> (Vec::<RLR>, Vec::<VLR>)
{
    let mut resR = Vec::<RLR>::new();
    let mut resV = Vec::<VLR>::new();
    for (reg, all_fragIxs_for_reg) in fragIx_vecs_per_reg.iter() {

        // BEGIN merge |all_fragIxs_for_reg| entries as much as possible.
        // Each |state| entry has four components:
        //    (1) An is-this-entry-still-valid flag
        //    (2) A set of FragIxs.  These should refer to disjoint Frags.
        //    (3) A set of blocks, which are those corresponding to (2)
        //        that are LiveIn or Thru (== have an inbound value)
        //    (4) A set of blocks, which are the union of the successors of
        //        blocks corresponding to the (2) which are LiveOut or Thru
        //        (== have an outbound value)
        struct MergeGroup {
            valid: bool,
            fragIxs: Set::<FragIx>,
            live_in_blocks: Set::<BlockIx>,
            succs_of_live_out_blocks: Set::<BlockIx>
        }

        let mut state = Vec::<MergeGroup>::new();

        // Create the initial state by giving each FragIx its own Vec, and
        // tagging it with its interface blocks.
        for fix in all_fragIxs_for_reg {
            let mut live_in_blocks = Set::<BlockIx>::empty();
            let mut succs_of_live_out_blocks = Set::<BlockIx>::empty();
            let frag = &frag_env[fix.get_usize()];
            let frag_bix = frag.bix;
            let frag_succ_bixes = &cfg_info.succ_map[frag_bix.get_usize()];
            match frag.kind {
                FragKind::Local => {
                },
                FragKind::LiveIn => {
                    live_in_blocks.insert(frag_bix);
                },
                FragKind::LiveOut => {
                    succs_of_live_out_blocks.union(frag_succ_bixes);
                },
                FragKind::Thru => {
                    live_in_blocks.insert(frag_bix);
                    succs_of_live_out_blocks.union(frag_succ_bixes);
                }
            }

            let valid = true;
            let fragIxs = Set::unit(*fix);
            let mg = MergeGroup { valid, fragIxs,
                                  live_in_blocks, succs_of_live_out_blocks };
            state.push(mg);
        }

        // Iterate over |state|, merging entries as much as possible.  This
        // is, unfortunately, quadratic.
        let state_len = state.len();
        loop {
            let mut changed = false;

            for i in 0 .. state_len {
                if !state[i].valid {
                    continue;
                }
                for j in i+1 .. state_len {
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
                        let mut tmp_fragIxs = state[i].fragIxs.clone();
                        state[j].fragIxs.union(&mut tmp_fragIxs);
                        let tmp_libs = state[i].live_in_blocks.clone();
                        state[j].live_in_blocks.union(&tmp_libs);
                        let tmp_solobs
                            = state[i].succs_of_live_out_blocks.clone();
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

        // Harvest the merged Frag sets from |state|, and turn them into LRs
        // of the appropriate flavour.
        for MergeGroup { valid, fragIxs, .. } in state {
            if !valid {
                continue;
            }
            let sfrags = SortedFragIxs::new(&fragIxs.to_vec(), &frag_env);
            let size = 0;
            let cost = Some(0.0);
            match *reg {
                Reg::RReg(rreg) => {
                    resR.push(RLR { rreg: rreg, sfrags });
                }
                Reg::VReg(vreg) => {
                    resV.push(VLR { vreg: vreg, rreg: None,
                                    sfrags, size, cost });
                }
            }
        }

        // END merge |all_fragIxs_for_reg| entries as much as possible
    }

    (resR, resV)
}


//=============================================================================
// Finalising of VLRs, by setting the |size| and |cost| metrics.

// |size|: this is simple.  Simply sum the size of the individual fragments.
// Note that this must produce a value > 0 for a dead write, hence the "+1".
//
// |cost|: try to estimate the number of spills and reloads that would result
// from spilling the VLR, thusly:
//    sum, for each frag
//        # mentions of the VReg in the frag
//            (that's the per-frag, per pass spill cost)
//        *
//        the estimated execution count of the containing block
//
// all the while being very careful to avoid overflow.
#[inline(never)]
fn set_VLR_metrics(vlrs: &mut Vec::<VLR>,
                   fenv: &Vec::<Frag>, blocks: &Vec::<Block>)
{
    for vlr in vlrs {
        debug_assert!(vlr.size == 0 && vlr.cost == Some(0.0));
        debug_assert!(vlr.rreg.is_none());
        let mut tot_size: u32 = 0;
        let mut tot_cost: f32 = 0.0;

        for fix in &vlr.sfrags.fragIxs {
            let frag = &fenv[fix.get_usize()];

            // Add on the size of this fragment, but make sure we can't
            // overflow a u32 no matter how many fragments there are.
            let mut frag_size: u32 = frag.last.iix.get()
                                     - frag.first.iix.get() + 1;
            if frag_size > 0xFFFF {
                frag_size = 0xFFFF;
            }
            tot_size += frag_size;
            if tot_size > 0xFFFF { tot_size = 0xFFFF; }

            // tot_cost is a float, so no such paranoia there.
            tot_cost += frag.count as f32
                        * blocks[frag.bix.get_usize()].eef as f32;
        }

        debug_assert!(tot_cost >= 0.0);
        debug_assert!(tot_size >= 1 && tot_size <= 0xFFFF);
        vlr.size = tot_size as u16;

        // Divide tot_cost by the total length, so as to increase the apparent
        // spill cost of short LRs.  This is so as to give the advantage to
        // short LRs in competition for registers.  This seems a bit of a hack
        // to me, but hey ..
        tot_cost /= tot_size as f32;
        vlr.cost = Some(tot_cost);
    }
}

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
// Further methods on SortedFragIxs.  These are needed by the core algorithm.

impl SortedFragIxs {
    // Structural equality, at least.  Not equality in the sense of
    // deferencing the contained FragIxes.
    fn equals(&self, other: &SortedFragIxs) -> bool {
        if self.fragIxs.len() != other.fragIxs.len() {
            return false;
        }
        for (mf1, mf2) in self.fragIxs.iter().zip(&other.fragIxs) {
            if mf1 != mf2 {
                return false;
            }
        }
        true
    }

    fn add(&mut self, to_add: &Self, fenv: &Vec::<Frag>) {
        self.check(fenv);
        to_add.check(fenv);
        let sfixs_x = &self;
        let sfixs_y = &to_add;
        let mut ix = 0;
        let mut iy = 0;
        let mut res = Vec::<FragIx>::new();
        while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
            let fx = fenv[ sfixs_x.fragIxs[ix].get_usize() ];
            let fy = fenv[ sfixs_y.fragIxs[iy].get_usize() ];
            match cmpFrags(&fx, &fy) {
                FCR::LT => { res.push(sfixs_x.fragIxs[ix]); ix += 1; },
                FCR::GT => { res.push(sfixs_y.fragIxs[iy]); iy += 1; },
                FCR::EQ | FCR::UN
                    => panic!("SortedFragIxs::add: vectors intersect")
            }
        }
        // At this point, one or the other or both vectors are empty.  Hence
        // it doesn't matter in which order the following two while-loops
        // appear.
        debug_assert!(ix == sfixs_x.fragIxs.len()
                      || iy == sfixs_y.fragIxs.len());
        while ix < sfixs_x.fragIxs.len() {
            res.push(sfixs_x.fragIxs[ix]);
            ix += 1;
        }
        while iy < sfixs_y.fragIxs.len() {
            res.push(sfixs_y.fragIxs[iy]);
            iy += 1;
        }
        self.fragIxs = res;
        self.check(fenv);
    }

    fn can_add(&self, to_add: &Self, fenv: &Vec::<Frag>) -> bool {
        // This is merely a partial evaluation of add() which returns |false|
        // exactly in the cases where add() would have panic'd.
        self.check(fenv);
        to_add.check(fenv);
        let sfixs_x = &self;
        let sfixs_y = &to_add;
        let mut ix = 0;
        let mut iy = 0;
        while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
            let fx = fenv[ sfixs_x.fragIxs[ix].get_usize() ];
            let fy = fenv[ sfixs_y.fragIxs[iy].get_usize() ];
            match cmpFrags(&fx, &fy) {
                FCR::LT => { ix += 1; },
                FCR::GT => { iy += 1; },
                FCR::EQ | FCR::UN => { return false; }
            }
        }
        // At this point, one or the other or both vectors are empty.  So
        // we're guaranteed to succeed.
        debug_assert!(ix == sfixs_x.fragIxs.len()
                      || iy == sfixs_y.fragIxs.len());
        true
    }

    fn del(&mut self, to_del: &Self, fenv: &Vec::<Frag>) {
        self.check(fenv);
        to_del.check(fenv);
        let sfixs_x = &self;
        let sfixs_y = &to_del;
        let mut ix = 0;
        let mut iy = 0;
        let mut res = Vec::<FragIx>::new();
        while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
            let fx = fenv[ sfixs_x.fragIxs[ix].get_usize() ];
            let fy = fenv[ sfixs_y.fragIxs[iy].get_usize() ];
            match cmpFrags(&fx, &fy) {
                FCR::LT => { res.push(sfixs_x.fragIxs[ix]); ix += 1; },
                FCR::EQ => { ix += 1; iy += 1; }
                FCR::GT => { iy += 1; },
                FCR::EQ | FCR::UN
                    => panic!("SortedFragIxs::del: partial overlap")
            }
        }
        debug_assert!(ix == sfixs_x.fragIxs.len()
                      || iy == sfixs_y.fragIxs.len());
        // Handle leftovers
        while ix < sfixs_x.fragIxs.len() {
            res.push(sfixs_x.fragIxs[ix]);
            ix += 1;
        }
        self.fragIxs = res;
        self.check(fenv);
    }

    fn can_add_if_we_first_del(&self, to_del: &Self, to_add: &Self,
                               fenv: &Vec::<Frag>) -> bool {
        // For now, just do this the stupid way.  It would be possible to do
        // it without any allocation, but that sounds complex.
        let mut after_del = self.clone();
        after_del.del(&to_del, fenv);
        return after_del.can_add(&to_add, fenv);
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
    fn new(vlr_env: &Vec::<VLR>) -> Self {
        let mut res = Self { unallocated: Vec::new() };
        for ix in 0 .. vlr_env.len() {
            assert!(vlr_env[ix].size > 0);
            res.unallocated.push(mkVLRIx(ix as u32));
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
    fn get_longest_VLR(&mut self, vlr_env: &Vec::<VLR>) -> Option<VLRIx> {
        if self.unallocated.len() == 0 {
            return None;
        }
        let mut largestIx   = self.unallocated.len(); /*INVALID*/
        let mut largestSize = 0; /*INVALID*/
        for i in 0 .. self.unallocated.len() {
            let cand_vlrix = self.unallocated[i];
            let cand_vlr = &vlr_env[cand_vlrix.get_usize()];
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
    fn show_with_envs(&self, vlr_env: &Vec::<VLR>) -> String {
        let mut res = "".to_string();
        let mut first = true;
        for vlrix in self.unallocated.iter() {
            if !first { res += &"\n".to_string(); }
            first = false;
            res += &"TODO  ".to_string();
            res += &vlr_env[vlrix.get_usize()].show();
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
    fn new(fenv: &Vec::<Frag>) -> Self {
        Self {
            frags_in_use: SortedFragIxs::new(&vec![], fenv),
            vlrixs_assigned: Vec::<VLRIx>::new()
        }
    }

    #[inline(never)]
    fn add_RLR(&mut self, to_add: &RLR, fenv: &Vec::<Frag>) {
        // Commit this register to |to_add|, irrevocably.  Don't add it to
        // |vlrixs_assigned| since we will never want to later evict the
        // assignment.
        self.frags_in_use.add(&to_add.sfrags, fenv);
    }

    #[inline(never)]
    fn can_add_VLR_without_eviction(&self, to_add: &VLR,
                                    fenv: &Vec::<Frag>) -> bool {
        self.frags_in_use.can_add(&to_add.sfrags, fenv)
    }

    #[inline(never)]
    fn add_VLR(&mut self, to_add_vlrix: VLRIx,
               vlr_env: &Vec::<VLR>, fenv: &Vec::<Frag>) {
        let vlr = &vlr_env[to_add_vlrix.get_usize()];
        self.frags_in_use.add(&vlr.sfrags, fenv);
        self.vlrixs_assigned.push(to_add_vlrix);
    }

    #[inline(never)]
    fn del_VLR(&mut self, to_del_vlrix: VLRIx,
               vlr_env: &Vec::<VLR>, fenv: &Vec::<Frag>) {
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
        let vlr = &vlr_env[to_del_vlrix.get_usize()];
        self.frags_in_use.del(&vlr.sfrags, fenv);
    }

    #[inline(never)]
    fn find_best_evict_VLR(&self, would_like_to_add: &VLR,
                           vlr_env: &Vec::<VLR>,
                           frag_env: &Vec::<Frag>)
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
            let cand_vlr = &vlr_env[cand_vlrix.get_usize()];
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
    fn show1_with_envs(&self, fenv: &Vec::<Frag>) -> String {
        "in_use:   ".to_string() + &self.frags_in_use.show_with_fenv(&fenv)
    }
    #[inline(never)]
    fn show2_with_envs(&self, fenv: &Vec::<Frag>) -> String {
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
                  vlr_env: &Vec::<VLR>, frag_env: &Vec::<Frag>)
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
                   context: &Vec::<Frag>) -> String {
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
fn alloc_main(func: &mut Func, nRRegs: usize) -> Result<(), String> {

    let (def_sets_per_block, use_sets_per_block) = func.calc_def_and_use();
    debug_assert!(def_sets_per_block.len() == func.blocks.len());
    debug_assert!(use_sets_per_block.len() == func.blocks.len());

    let mut n = 0;
    println!("");
    for (def, uce) in def_sets_per_block.iter().zip(&use_sets_per_block) {
        println!("{:<3}   def {:<16}  use {}",
                 mkBlockIx(n).show(), def.show(), uce.show());
        n += 1;
    }

    let cfg_info = CFGInfo::create(&func);

    n = 0;
    println!("");
    for (preds, succs) in cfg_info.pred_map.iter().zip(&cfg_info.succ_map) {
        println!("{:<3}   preds {:<16}  succs {}",
                 mkBlockIx(n).show(), preds.show(), succs.show());
        n += 1;
    }

    n = 0;
    println!("");
    for (depth, dom_by) in cfg_info.depth_map.iter().zip(&cfg_info.dom_map) {
        println!("{:<3}   depth {}   dom_by {:<16}",
                 mkBlockIx(n).show(), depth, dom_by.show());
        n += 1;
    }

    // Annotate each Block with its estimated execution count
    for bixNo in 0 .. func.blocks.len() {
        let mut eef = 1;
        let mut depth = cfg_info.depth_map[bixNo];
        if depth > 3 { depth = 3; }
        for i in 0 .. depth {
            eef *= 10;
        }
        func.blocks[bixNo].eef = eef;
    }

    let (livein_sets_per_block, liveout_sets_per_block) =
        func.calc_livein_and_liveout(&def_sets_per_block,
                                     &use_sets_per_block, &cfg_info);
    debug_assert!(livein_sets_per_block.len() == func.blocks.len());
    debug_assert!(liveout_sets_per_block.len() == func.blocks.len());

    n = 0;
    println!("");
    for (livein, liveout) in livein_sets_per_block.iter()
                                                  .zip(&liveout_sets_per_block) {
        println!("{:<3}   livein {:<16}  liveout {:<16}",
                 mkBlockIx(n).show(), livein.show(), liveout.show());
        n += 1;
    }

    if !livein_sets_per_block[func.entry.getBlockIx().get_usize()].is_empty() {
        return Err("entry block has live-in values".to_string());
    }

    let (fragIxs_per_reg, mut frag_env) =
        func.get_Frags(&livein_sets_per_block, &liveout_sets_per_block);

    println!("");
    n = 0;
    for frag in &frag_env {
        println!("{:<3}   {}", mkFragIx(n).show(), frag.show());
        n += 1;
    }

    println!("");
    for (reg, fragIxs) in fragIxs_per_reg.iter() {
        println!("frags for {}   {}", reg.show(), fragIxs.show());
    }

    let (rlr_env, mut vlr_env)
        = merge_Frags(&fragIxs_per_reg, &frag_env, &cfg_info);
    set_VLR_metrics(&mut vlr_env, &frag_env, &func.blocks);

    println!("");
    n = 0;
    for lr in &rlr_env {
        println!("{:<4}   {}", mkRLRIx(n).show(), lr.show());
        n += 1;
    }

    println!("");
    n = 0;
    for lr in &vlr_env {
        println!("{:<4}   {}", mkVLRIx(n).show(), lr.show());
        n += 1;
    }


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
    for rlr in &rlr_env {
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
        let curr_vlr = &vlr_env[curr_vlrix.get_usize()];

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
            vlr_env[curr_vlrix.get_usize()].rreg = Some(rreg);
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
                     &vlr_env[vlrix_to_evict.get_usize()].show());
            debug_assert!(vlrix_to_evict != curr_vlrix);
            perRReg[rregNo].del_VLR(vlrix_to_evict, &vlr_env, &frag_env);
            prioQ.add_VLR(vlrix_to_evict);
            debug_assert!(vlr_env[vlrix_to_evict.get_usize()].rreg.is_some());
            // .. and reassign.
            let rreg = mkRReg(rregNo as u32);
            println!("--   then alloc to    {}", rreg.show());
            perRReg[rregNo].add_VLR(curr_vlrix, &vlr_env, &frag_env);
            debug_assert!(curr_vlr.rreg.is_none());
            // Directly modify bits of vlr_env.  This means we have to abandon
            // the immutable borrow for curr_vlr, but that's OK -- we won't
            // need it again again (in this loop iteration).
            vlr_env[curr_vlrix.get_usize()].rreg = Some(rreg);
            vlr_env[vlrix_to_evict.get_usize()].rreg = None;
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
            let frag: &Frag = &frag_env[fix.get_usize()];
            for iixNo in frag.first.iix.get() .. frag.last.iix.get() + 1 {
                let insn: &Insn = &func.insns[iixNo as usize];
                let (regs_d, regs_m, regs_u) = insn.getRegUsage();
                // If this insn doesn't mention the vreg we're spilling for,
                // move on.
                if !regs_d.contains(curr_vlr_reg)
                   && !regs_m.contains(curr_vlr_reg)
                   && !regs_u.contains(curr_vlr_reg) {
                    continue;
                }
                let iix = mkInsnIx(iixNo);
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
            let vlr_assigned = &vlr_env[vlrix_assigned.get_usize()];
            // All the Frags in |vlr_assigned| require |vlr_assigned.reg| to
            // be mapped to the real reg |i|
            let vreg = vlr_assigned.vreg;
            // .. collect up all its constituent Frags.
            for fix in &vlr_assigned.sfrags.fragIxs {
                let frag = &frag_env[fix.get_usize()];
                fragMapsByStart.push((*fix, vreg, rreg));
                fragMapsByEnd.push((*fix, vreg, rreg));
            }
        }
    }

    fragMapsByStart.sort_unstable_by(
        |(fixNo1, _, _), (fixNo2, _, _)|
        frag_env[fixNo1.get_usize()].first.iix
            .partial_cmp(&frag_env[fixNo2.get_usize()].first.iix)
            .unwrap());

    fragMapsByEnd.sort_unstable_by(
        |(fixNo1, _, _), (fixNo2, _, _)|
        frag_env[fixNo1.get_usize()].last.iix
            .partial_cmp(&frag_env[fixNo2.get_usize()].last.iix)
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

    for insnNo in 0u32 .. func.insns.len() as u32 {
        //println!("");
        //println!("QQQQ insn {}: {}",
        //         insnNo, func.insns[insnNo as usize].show());
        //println!("QQQQ init map {}", showMap(&map));
        // advance [cursorStarts, +numStarts) to the group for insnNo
        while cursorStarts < fragMapsByStart.len()
              && frag_env[ fragMapsByStart[cursorStarts].0.get_usize() ]
                 .first.iix.get() < insnNo {
            cursorStarts += 1;
        }
        numStarts = 0;
        while cursorStarts + numStarts < fragMapsByStart.len()
              && frag_env[ fragMapsByStart[cursorStarts + numStarts]
                           .0.get_usize() ]
                 .first.iix.get() == insnNo {
            numStarts += 1;
        }

        // advance [cursorEnds, +numEnds) to the group for insnNo
        while cursorEnds < fragMapsByEnd.len()
              && frag_env[ fragMapsByEnd[cursorEnds].0.get_usize() ]
                 .last.iix.get() < insnNo {
            cursorEnds += 1;
        }
        numEnds = 0;
        while cursorEnds + numEnds < fragMapsByEnd.len()
              && frag_env[ fragMapsByEnd[cursorEnds + numEnds]
                           .0.get_usize() ]
                 .last.iix.get() == insnNo {
            numEnds += 1;
        }

        // So now, fragMapsByStart[cursorStarts, +numStarts) are the mappings
        // for fragments that begin at this instruction, in no particular
        // order.  And fragMapsByEnd[cursorEnd, +numEnd) are the FragIxs for
        // fragments that end at this instruction.

        //println!("insn no {}:", insnNo);
        //for j in cursorStarts .. cursorStarts + numStarts {
        //    println!("   s: {} {}",
        //             (fragMapsByStart[j].1, fragMapsByStart[j].2).show(),
        //             frag_env[ fragMapsByStart[j].0.get_usize() ]
        //             .show());
        //}
        //for j in cursorEnds .. cursorEnds + numEnds {
        //    println!("   e: {} {}",
        //             (fragMapsByEnd[j].1, fragMapsByEnd[j].2).show(),
        //             frag_env[ fragMapsByEnd[j].0.get_usize() ]
        //             .show());
        //}

        // Sanity check all frags.  In particular, reload and spill frags are
        // heavily constrained.  No functional effect.
        for j in cursorStarts .. cursorStarts + numStarts {
            let frag = &frag_env[ fragMapsByStart[j].0.get_usize() ];
            // "It really starts here, as claimed."
            debug_assert!(frag.first.iix.get() == insnNo);
            debug_assert!(is_sane(&frag));
        }
        for j in cursorEnds .. cursorEnds + numEnds {
            let frag = &frag_env[ fragMapsByEnd[j].0.get_usize() ];
            // "It really ends here, as claimed."
            debug_assert!(frag.last.iix.get() == insnNo);
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
            let frag = &frag_env[ fragMapsByStart[j].0.get_usize() ];
            if frag.first.pt.isR() { //////// STARTS at I.r
                map.insert(fragMapsByStart[j].1, fragMapsByStart[j].2);
            }
        }

        // Update map for I.u:
        //   add frags starting at I.u
        //   mapU := map
        //   remove frags ending at I.u
        for j in cursorStarts .. cursorStarts + numStarts {
            let frag = &frag_env[ fragMapsByStart[j].0.get_usize() ];
            if frag.first.pt.isU() { //////// STARTS at I.u
                map.insert(fragMapsByStart[j].1, fragMapsByStart[j].2);
            }
        }
        let mapU = map.clone();
        for j in cursorEnds .. cursorEnds + numEnds {
            let frag = &frag_env[ fragMapsByEnd[j].0.get_usize() ];
            if frag.last.pt.isU() { //////// ENDS at I.U
                map.remove(&fragMapsByEnd[j].1);
            }
        }

        // Update map for I.d:
        //   add frags starting at I.d
        //   mapD := map
        //   remove frags ending at I.d
        for j in cursorStarts .. cursorStarts + numStarts {
            let frag = &frag_env[ fragMapsByStart[j].0.get_usize() ];
            if frag.first.pt.isD() { //////// STARTS at I.d
                map.insert(fragMapsByStart[j].1, fragMapsByStart[j].2);
            }
        }
        let mapD = map.clone();
        for j in cursorEnds .. cursorEnds + numEnds {
            let frag = &frag_env[ fragMapsByEnd[j].0.get_usize() ];
            if frag.last.pt.isD() { //////// ENDS at I.d
                map.remove(&fragMapsByEnd[j].1);
            }
        }

        // Update map for I.s:
        //   no frags should start at I.s (it's a spill insn)
        //   remove frags ending at I.s
        for j in cursorEnds .. cursorEnds + numEnds {
            let frag = &frag_env[ fragMapsByEnd[j].0.get_usize() ];
            if frag.last.pt.isS() { //////// ENDS at I.s
                map.remove(&fragMapsByEnd[j].1);
            }
        }

        //println!("QQQQ mapU {}", showMap(&mapU));
        //println!("QQQQ mapD {}", showMap(&mapD));

        // Finally, we have mapU/mapD set correctly for this instruction.
        // Apply it.
        func.insns[insnNo as usize].mapRegs_D_U(&mapD, &mapU);

        // Update cursorStarts and cursorEnds for the next iteration
        cursorStarts += numStarts;
        cursorEnds += numEnds;

        if func.blocks.iter().any(|b| b.start.get() + b.len - 1 == insnNo) {
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
        let vlr = &vlr_env[eli.vlrix.get_usize()];
        let vlr_sfrags = &vlr.sfrags;
        debug_assert!(vlr.sfrags.fragIxs.len() == 1);
        let vlr_frag = frag_env[ vlr_sfrags.fragIxs[0].get_usize() ];
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
    let mut curB = 0; // cursor in Func::blocks

    let mut newInsns = Vec::<Insn>::new();
    let mut newBlocks = Vec::<Block>::new();

    for iixNo in 0 .. func.insns.len() {
        let iix = mkInsnIx(iixNo as u32);

        // Is |iixNo| the first instruction in a block?  Meaning, are we
        // starting a new block?
        debug_assert!(curB < func.blocks.len());
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
        newInsns.push(func.insns[iixNo as usize].clone());
        // Copy spills for this insn
        while curSnR < spillsAndReloads.len()
              && spillsAndReloads[curSnR].0 == InsnPoint_S(iix) {
            newInsns.push(spillsAndReloads[curSnR].1.clone());
            curSnR += 1;
        }

        // Is |iixNo| the last instruction in a block?
        if iixNo + 1 == func.blocks[curB].start.get_usize()
                        + func.blocks[curB].len as usize {
            debug_assert!(curB < func.blocks.len());
            debug_assert!(newBlocks.len() > 0);
            debug_assert!(curB == newBlocks.len() - 1);
            newBlocks[curB].len = newInsns.len() as u32
                                  - newBlocks[curB].start.get();
            curB += 1;
        }
    }

    debug_assert!(curSnR == spillsAndReloads.len());
    debug_assert!(curB == func.blocks.len());
    debug_assert!(curB == newBlocks.len());

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


//=============================================================================
// Top level

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        println!("usage: {} <name of Func to use> <num real regs>", args[0]);
        return;
    }

    let mut func = match find_Func(&args[1]) {
        Ok(func) => func,
        Err(available_func_names) => {
            println!("{}: can't find Func with name '{}'", args[0], args[1]);
            println!("{}: available Func names are:", args[0]);
            for name in available_func_names {
                println!("{}:     {}", args[0], name);
            }
            return;
        }
    };

    let nRRegs = match args[2].parse::<usize>() {
        Ok(n) if n >= 1 => n,
        _other => {
            println!("{}: invalid #rregs.  Must be 1 or more.", args[0]);
            return;
        }
    };

    func.print("Initial");

    func.run("Before allocation", nRRegs);

    // Just so we can run it later.  Not needed for actual allocation.
    let original_func = func.clone();

    let alloc_res = alloc_main(&mut func, nRRegs);
    match alloc_res {
        Err(s) => {
            println!("{}: allocation failed: {}", args[0], s);
            return;
        }
        Ok(_) => { }
    }

    func.print("After allocation");

    original_func.run("Before allocation", nRRegs);
    func.run("After allocation", nRRegs);

    println!("");
}


//=============================================================================
// Test cases

#[test]
fn test_SortedFragIxs() {

    // Create a Frag and FragIx from two InsnPoints.
    fn gen_fix(fenv: &mut Vec::<Frag>,
               first: InsnPoint, last: InsnPoint) -> FragIx {
        assert!(first <= last);
        let res = mkFragIx(fenv.len() as u32);
        let frag = Frag { bix: mkBlockIx(123),
                          kind: FragKind::Local, first, last, count: 0 };
        fenv.push(frag);
        res
    }

    fn getFrag(fenv: &'a Vec::<Frag>, fix: FragIx) -> &'a Frag {
        &fenv[ fix.get_usize() ]
    }

    let iix3  = mkInsnIx(3);
    let iix4  = mkInsnIx(4);
    let iix5  = mkInsnIx(5);
    let iix6  = mkInsnIx(6);
    let iix7  = mkInsnIx(7);
    let iix10 = mkInsnIx(10);
    let iix12 = mkInsnIx(12);
    let iix15 = mkInsnIx(15);

    let fp_3u = InsnPoint_U(iix3);
    let fp_3d = InsnPoint_D(iix3);

    let fp_4u = InsnPoint_U(iix4);

    let fp_5u = InsnPoint_U(iix5);
    let fp_5d = InsnPoint_D(iix5);

    let fp_6u = InsnPoint_U(iix6);
    let fp_6d = InsnPoint_D(iix6);

    let fp_7u = InsnPoint_U(iix7);
    let fp_7d = InsnPoint_D(iix7);

    let fp_10u = InsnPoint_U(iix10);
    let fp_12u = InsnPoint_U(iix12);
    let fp_15u = InsnPoint_U(iix15);

    let mut fenv = Vec::<Frag>::new();

    let fix_3u    = gen_fix(&mut fenv, fp_3u, fp_3u);
    let fix_3d    = gen_fix(&mut fenv, fp_3d, fp_3d);
    let fix_4u    = gen_fix(&mut fenv, fp_4u, fp_4u);
    let fix_3u_5u = gen_fix(&mut fenv, fp_3u, fp_5u);
    let fix_3d_5d = gen_fix(&mut fenv, fp_3d, fp_5d);
    let fix_3d_5u = gen_fix(&mut fenv, fp_3d, fp_5u);
    let fix_3u_5d = gen_fix(&mut fenv, fp_3u, fp_5d);
    let fix_6u_6d = gen_fix(&mut fenv, fp_6u, fp_6d);
    let fix_7u_7d = gen_fix(&mut fenv, fp_7u, fp_7d);
    let fix_10u   = gen_fix(&mut fenv, fp_10u, fp_10u);
    let fix_12u   = gen_fix(&mut fenv, fp_12u, fp_12u);
    let fix_15u   = gen_fix(&mut fenv, fp_15u, fp_15u);

    // Boundary checks for point ranges, 3u vs 3d
    assert!(cmpFrags(getFrag(&fenv, fix_3u), getFrag(&fenv, fix_3u))
            == FCR::EQ);
    assert!(cmpFrags(getFrag(&fenv, fix_3u), getFrag(&fenv, fix_3d))
            == FCR::LT);
    assert!(cmpFrags(getFrag(&fenv, fix_3d), getFrag(&fenv, fix_3u))
            == FCR::GT);

    // Boundary checks for point ranges, 3d vs 4u
    assert!(cmpFrags(getFrag(&fenv, fix_3d), getFrag(&fenv, fix_3d))
            == FCR::EQ);
    assert!(cmpFrags(getFrag(&fenv, fix_3d), getFrag(&fenv, fix_4u))
            == FCR::LT);
    assert!(cmpFrags(getFrag(&fenv, fix_4u), getFrag(&fenv, fix_3d))
            == FCR::GT);

    // Partially overlapping
    assert!(cmpFrags(getFrag(&fenv, fix_3d_5d), getFrag(&fenv, fix_3u_5u))
            == FCR::UN);
    assert!(cmpFrags(getFrag(&fenv, fix_3u_5u), getFrag(&fenv, fix_3d_5d))
            == FCR::UN);

    // Completely overlapping: one contained within the other
    assert!(cmpFrags(getFrag(&fenv, fix_3d_5u), getFrag(&fenv, fix_3u_5d))
            == FCR::UN);
    assert!(cmpFrags(getFrag(&fenv, fix_3u_5d), getFrag(&fenv, fix_3d_5u))
            == FCR::UN);

    // Create a SortedFragIxs from a bunch of Frag indices
    fn genSMF(fenv: &Vec::<Frag>, frags: &Vec::<FragIx>) -> SortedFragIxs {
        SortedFragIxs::new(&frags, fenv)
    }

    // Construction tests
    // These fail due to overlap
    //let _ = genSMF(&fenv, &vec![fix_3u_3u, fix_3u_3u]);
    //let _ = genSMF(&fenv, &vec![fix_3u_5u, fix_3d_5d]);

    // These fail due to not being in order
    //let _ = genSMF(&fenv, &vec![fix_4u_4u, fix_3u_3u]);

    // Simple non-overlap tests for add()

    let smf_empty  = genSMF(&fenv, &vec![]);
    let smf_6_7_10 = genSMF(&fenv, &vec![fix_6u_6d, fix_7u_7d, fix_10u]);
    let smf_3_12   = genSMF(&fenv, &vec![fix_3u, fix_12u]);
    let smf_3_6_7_10_12 = genSMF(&fenv, &vec![fix_3u, fix_6u_6d, fix_7u_7d,
                                             fix_10u, fix_12u]);
    let mut tmp;

    tmp = smf_empty. clone() ; tmp.add(&smf_empty, &fenv);
    assert!(tmp .equals( &smf_empty ));

    tmp = smf_3_12 .clone() ; tmp.add(&smf_empty, &fenv);
    assert!(tmp .equals( &smf_3_12 ));

    tmp = smf_empty .clone() ; tmp.add(&smf_3_12, &fenv);
    assert!(tmp .equals( &smf_3_12 ));

    tmp = smf_6_7_10 .clone() ; tmp.add(&smf_3_12, &fenv);
    assert!(tmp .equals( &smf_3_6_7_10_12 ));

    tmp = smf_3_12 .clone() ; tmp.add(&smf_6_7_10, &fenv);
    assert!(tmp .equals( &smf_3_6_7_10_12 ));

    // Tests for can_add()
    assert!(true  == smf_empty .can_add( &smf_empty, &fenv ));
    assert!(true  == smf_empty .can_add( &smf_3_12,  &fenv ));
    assert!(true  == smf_3_12  .can_add( &smf_empty, &fenv ));
    assert!(false == smf_3_12  .can_add( &smf_3_12,  &fenv ));

    assert!(true == smf_6_7_10 .can_add( &smf_3_12, &fenv ));

    assert!(true == smf_3_12 .can_add( &smf_6_7_10, &fenv ));

    // Tests for del()
    let smf_6_7  = genSMF(&fenv, &vec![fix_6u_6d, fix_7u_7d]);
    let smf_6_10 = genSMF(&fenv, &vec![fix_6u_6d, fix_10u]);
    let smf_7    = genSMF(&fenv, &vec![fix_7u_7d]);
    let smf_10   = genSMF(&fenv, &vec![fix_10u]);

    tmp = smf_empty. clone() ; tmp.del(&smf_empty, &fenv);
    assert!(tmp .equals( &smf_empty ));

    tmp = smf_3_12 .clone() ; tmp.del(&smf_empty, &fenv);
    assert!(tmp .equals( &smf_3_12 ));

    tmp = smf_empty .clone() ; tmp.del(&smf_3_12, &fenv);
    assert!(tmp .equals( &smf_empty ));

    tmp = smf_6_7_10 .clone() ; tmp.del(&smf_3_12, &fenv);
    assert!(tmp .equals( &smf_6_7_10 ));

    tmp = smf_3_12 .clone() ; tmp.del(&smf_6_7_10, &fenv);
    assert!(tmp .equals( &smf_3_12 ));

    tmp = smf_6_7_10 .clone() ; tmp.del(&smf_6_7, &fenv);
    assert!(tmp .equals( &smf_10 ));

    tmp = smf_6_7_10 .clone() ; tmp.del(&smf_10, &fenv);
    assert!(tmp .equals( &smf_6_7 ));

    tmp = smf_6_7_10 .clone() ; tmp.del(&smf_7, &fenv);
    assert!(tmp .equals( &smf_6_10 ));

    // Tests for can_add_if_we_first_del()
    let smf_10_12 = genSMF(&fenv, &vec![fix_10u, fix_12u]);

    assert!(true == smf_6_7_10
                    .can_add_if_we_first_del( /*d=*/&smf_10_12,
                                              /*a=*/&smf_3_12, &fenv ));

    assert!(false == smf_6_7_10
                     .can_add_if_we_first_del( /*d=*/&smf_10_12,
                                               /*a=*/&smf_7, &fenv ));
}


//=============================================================================
// The "blockifier".  This is just to make it easier to write test cases, by
// allowing direct use of if-then-else, do-while and repeat-until.  It is
// otherwise entirely unrelated to the register allocator proper.

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

struct Blockifier {
    name:    String,
    blocks:  Vec::< Vec<Insn> >,
    currBNo: usize,  // index into |blocks|
    nVRegs:  u32
}

fn mkTextLabel(n: usize) -> String {
    "L".to_string() + &n.to_string()
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
        self.blocks.push(vec![]);
        for s in stmts {
            match s {
                Stmt::Vanilla { insn } => {
                    self.blocks[currBNo].push(insn);
                },
                Stmt::IfThenElse { cond, stmts_t, stmts_e } => {
                    let (t_ent, t_exit) = self.blockify(stmts_t);
                    let (e_ent, e_exit) = self.blockify(stmts_e);
                    let cont = self.blocks.len();
                    self.blocks.push(vec![]);
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
                    self.blocks.push(vec![]);
                    self.blocks[s_exit].push(i_goto_ctf(cond,
                                                        &mkTextLabel(cont),
                                                        &mkTextLabel(s_ent)));
                    currBNo = cont;
                },
                Stmt::WhileDo { cond, stmts } => {
                    let condblock = self.blocks.len();
                    self.blocks.push(vec![]);
                    self.blocks[currBNo].push(i_goto(&mkTextLabel(condblock)));
                    let (s_ent, s_exit) = self.blockify(stmts);
                    self.blocks[s_exit].push(i_goto(&mkTextLabel(condblock)));
                    let cont = self.blocks.len();
                    self.blocks.push(vec![]);
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

        let mut blockz = Vec::<Vec<Insn>>::new();
        std::mem::swap(&mut self.blocks, &mut blockz);

        // BEGIN optionally, short out blocks that merely jump somewhere else
        let mut cleanedUp = Vec::<Option<Vec<Insn>>>::new();
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
                    if let Some(targetLabel) = is_goto_insn(&b[0]) {
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
                                for j in 0 .. mmm {
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


//=============================================================================
// Test cases.  The list of them is right at the bottom, function |find_Func|.
// Add new ones there.

// Whatever the current badness is
fn test__badness() -> Func {
    let mut func = Func::new("badness", "start");

    func.block("start", vec![
        i_print_s("!!Badness!!\n"),
        i_finish()
    ]);

    func.finish();
    func
}

fn test__straight_line() -> Func {
    let mut func = Func::new("straight_line", "b0");

    // Regs, virtual and real, that we want to use.
    let vA = func.vreg();

    func.block("b0", vec![
        i_print_s("Start\n"),
        i_imm(vA, 10),
        i_add(vA, vA, RI_I(7)),
        i_goto("b1"),
    ]);
    func.block("b1", vec![
        i_print_s("Result = "),
        i_print_i(vA),
        i_print_s("\n"),
        i_finish()
    ]);

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
    func.block("set-loop-pre", vec![
        i_imm (vNENT, 10),
        i_imm (vI,    0),
        i_goto("set-loop")
    ]);

    // Filling loop
    func.block("set-loop", vec![
        i_store   (AM_R(vI), vI),
        i_add     (vI,   vI, RI_I(1)),
        i_cmp_lt  (rTMP, vI, RI_R(vNENT)),
        i_goto_ctf(rTMP, "set-loop", "sum-loop-pre")
    ]);

    // Loop pre-header for summing them
    func.block("sum-loop-pre", vec![
        i_imm(vSUM, 0),
        i_imm(vI,   0),
        i_goto("sum-loop")
    ]);

    // Summing loop
    func.block("sum-loop", vec![
        i_load  (rTMP,  AM_R(vI)),
        i_add   (vSUM,  vSUM, RI_R(rTMP)),
        i_add   (vI,    vI,   RI_I(1)),
        i_cmp_lt(vTMP2, vI,   RI_R(vNENT)),
        i_goto_ctf(vTMP2, "sum-loop", "print-result")
    ]);

    // After loop.  Print result and stop.
    func.block("print-result", vec![
        i_print_s("Sum = "),
        i_print_i(vSUM),
        i_print_s("\n"),
        i_finish()
    ]);

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

    func.block("Lstart", vec![
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
    ]);

    func.block("L11", vec![
        i_load(t0, AM_R(hp)),
        i_cmp_gt(t0, t0, RI_R(bigN)),
        i_goto_ctf(t0, "L20", "L11a")
    ]);

    func.block("L11a", vec![
        i_add(hp, hp, RI_I(1)),
        i_goto("L11")
    ]);

    func.block("L20", vec![
        i_cmp_lt(t0, hp, RI_I(1)),
        i_goto_ctf(t0, "L60", "L21a"),
    ]);

    func.block("L21a", vec![
        i_sub(t0, hp, RI_I(1)),
        i_load(h, AM_R(t0)),
        //printf("h = %u\n", h),
        i_add(i, lo, RI_R(h)),
        i_goto("L30"),
    ]);

    func.block("L30", vec![
        i_cmp_gt(t0, i, RI_R(hi)),
        i_goto_ctf(t0, "L50", "L30a"),
    ]);

    func.block("L30a", vec![
        i_load(v, AM_R(i)),
        i_add(j, i, RI_I(0)),  // FIXME: is this a coalescable copy?
        i_goto("L40"),
    ]);

    func.block("L40", vec![
        i_sub(t0, j, RI_R(h)),
        i_load(t0, AM_R(t0)),
        i_cmp_le(t0, t0, RI_R(v)),
        i_goto_ctf(t0, "L45", "L40a"),
    ]);

    func.block("L40a", vec![
        i_sub(t0, j, RI_R(h)),
        i_load(t0, AM_R(t0)),
        i_store(AM_R(j), t0),
        i_sub(j, j, RI_R(h)),
        i_add(t0, lo, RI_R(h)),
        i_sub(t0, t0, RI_I(1)),
        i_cmp_le(t0, j, RI_R(t0)),
        i_goto_ctf(t0, "L45", "L40"),
    ]);

    func.block("L45", vec![
        i_store(AM_R(j), v),
        i_add(i, i, RI_I(1)),
        i_goto("L30"),
    ]);

    func.block("L50", vec![
        i_sub(hp, hp, RI_I(1)),
        i_goto("L20"),
    ]);

    func.block("L60", vec![
        i_add(i, lo, RI_I(0)), // FIXME: ditto
        i_goto("L61")
    ]);

    func.block("L61", vec![
        i_cmp_gt(t0, i, RI_R(hi)),
        i_goto_ctf(t0, "L62", "L61a"),
    ]);

    func.block("L61a", vec![
        i_load(t0, AM_R(i)),
        i_print_i(t0),
        i_print_s(" "),
        i_add(i, i, RI_I(1)),
        i_goto("L61"),
    ]);

    func.block("L62", vec![
        i_print_s("\n"),
        i_finish()
    ]);

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
    func.block("start", vec![
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
    ]);

    // Outer loop
    func.block("outer-loop-cond", vec![
        i_add     (vI,   vI, RI_I(1)),
        i_cmp_le  (vTMP, vI, RI_I(20)),
        i_goto_ctf(vTMP, "outer-loop-1", "after-outer-loop")
    ]);

    func.block("outer-loop-1", vec![
        i_add(v00, v00, RI_I(1)),
        i_add(v01, v01, RI_I(1)),
        i_add(v02, v02, RI_I(1)),
        i_add(v03, v03, RI_I(1)),
        i_goto("outer-loop-cond")
    ]);

    // After loop.  Print result and stop.
    func.block("after-outer-loop", vec![
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
    ]);

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
    func.block("set-loop-pre", vec![
        i_imm (vNENT, 10),
        i_imm (vI,    0),
        i_goto("set-loop")
    ]);

    // Filling loop
    func.block("set-loop", vec![
        i_store   (AM_R(vI), vI),
        i_addm    (vI,   RI_I(1)),
        i_cmp_lt  (rTMP, vI, RI_R(vNENT)),
        i_goto_ctf(rTMP, "set-loop", "sum-loop-pre")
    ]);

    // Loop pre-header for summing them
    func.block("sum-loop-pre", vec![
        i_imm(vSUM, 0),
        i_imm(vI,   0),
        i_goto("sum-loop")
    ]);

    // Summing loop
    func.block("sum-loop", vec![
        i_load  (rTMP,  AM_R(vI)),
        i_addm  (vSUM,  RI_R(rTMP)),
        i_addm  (vI,    RI_I(1)),
        i_cmp_lt(vTMP2, vI,   RI_R(vNENT)),
        i_goto_ctf(vTMP2, "sum-loop", "print-result")
    ]);

    // After loop.  Print result and stop.
    func.block("print-result", vec![
        i_print_s("Sum = "),
        i_print_i(vSUM),
        i_print_s("\n"),
        i_finish()
    ]);

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

    func.block("Lstart", vec![
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
    ]);

    func.block("L11", vec![
        i_load(t0, AM_R(hp)),
        i_cmp_gt(t0, t0, RI_R(bigN)),
        i_goto_ctf(t0, "L20", "L11a")
    ]);

    func.block("L11a", vec![
        i_addm(hp, RI_I(1)),
        i_goto("L11")
    ]);

    func.block("L20", vec![
        i_cmp_lt(t0, hp, RI_I(1)),
        i_goto_ctf(t0, "L60", "L21a"),
    ]);

    func.block("L21a", vec![
        i_copy(t0, hp),
        i_subm(t0, RI_I(1)),
        i_load(h, AM_R(t0)),
        //printf("h = %u\n", h),
        i_copy(i, lo),
        i_addm(i, RI_R(h)),
        i_goto("L30"),
    ]);

    func.block("L30", vec![
        i_cmp_gt(t0, i, RI_R(hi)),
        i_goto_ctf(t0, "L50", "L30a"),
    ]);

    func.block("L30a", vec![
        i_load(v, AM_R(i)),
        i_copy(j, i),  // FIXME: is this a coalescable copy?
        i_goto("L40"),
    ]);

    func.block("L40", vec![
        i_copy(t0, j),
        i_subm(t0, RI_R(h)),
        i_load(t0, AM_R(t0)),
        i_cmp_le(t0, t0, RI_R(v)),
        i_goto_ctf(t0, "L45", "L40a"),
    ]);

    func.block("L40a", vec![
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
    ]);

    func.block("L45", vec![
        i_store(AM_R(j), v),
        i_addm(i, RI_I(1)),
        i_goto("L30"),
    ]);

    func.block("L50", vec![
        i_subm(hp, RI_I(1)),
        i_goto("L20"),
    ]);

    func.block("L60", vec![
        i_copy(i, lo), // FIXME: ditto
        i_goto("L61")
    ]);

    func.block("L61", vec![
        i_cmp_gt(t0, i, RI_R(hi)),
        i_goto_ctf(t0, "L62", "L61a"),
    ]);

    func.block("L61a", vec![
        i_load(t0, AM_R(i)),
        i_print_i(t0),
        i_print_s(" "),
        i_addm(i, RI_I(1)),
        i_goto("L61"),
    ]);

    func.block("L62", vec![
        i_print_s("\n"),
        i_finish()
    ]);

    func.finish();
    func
}

// This is the list of available tests.  This function returns either the
// requested Func, or if not found, a list of the available ones.
fn find_Func(name: &String) -> Result::<Func, Vec::<String>> {
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
