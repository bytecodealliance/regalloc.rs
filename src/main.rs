
#![allow(non_snake_case)]
#![allow(unused_imports)]
#![allow(non_camel_case_types)]

use std::{fs, io};
use std::io::BufRead;
use std::env;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::convert::TryInto;
use std::cmp::Ordering;


//=============================================================================
// A simple trait for printing things, a.k.a. "Let's play 'Spot the ex-Haskell
// programmer'".

trait Show {
    fn show(&self) -> String;
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
impl Show for u32 {
    fn show(&self) -> String {
        self.to_string()
    }
}
impl Show for bool {
    fn show(&self) -> String {
        (if *self { "True" } else { "False" }).to_string()
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
}


#[derive(Copy, Clone)]
enum SlotIx {
    Slot(u32)
}


// The absolute index of a Block (in CFG::blocks[]).
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


// The absolute index of an Insn (in CFG::insns[]).
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
enum Label<'a> {
    Unresolved { name: &'a str },
    Resolved { name: &'a str, bix: BlockIx }
}

fn mkUnresolved<'a>(name: &'a str) -> Label<'a> { Label::Unresolved { name }}

impl<'a> Show for Label<'a> {
    fn show(&self) -> String {
        match self {
            Label::Unresolved { name } =>
                "??:".to_string() + &name.to_string(),
            Label::Resolved { name, bix } =>
                bix.show() + &":".to_string() + &name.to_string()
        }
    }
}
impl<'a> Label<'a> {
    fn getBlockIx(&self) -> BlockIx {
        match self {
            Label::Resolved { name:_, bix } => *bix,
            Label::Unresolved { .. } =>
                panic!("Label::getBlockIx: unresolved label!")
        }
    }
}

fn resolveLabel<'a, F>(label: &mut Label<'a>, lookup: F)
    where F: Fn(&'a str) -> BlockIx
{
    let resolved = 
        match label {
            Label::Unresolved { name } =>
                Label::Resolved { name: name, bix: lookup(name) },
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
    fn addRegReadsTo(&self, uce: &mut Vec::<Reg>) {
        match self {
            RI::Reg { reg } => uce.push(*reg),
            RI::Imm { ..  } => { }
        }
    }
}


#[derive(Copy, Clone)]
enum BinOp {
    Add,
    CmpLT
}
impl Show for BinOp {
    fn show(&self) -> String {
        match self {
            BinOp::Add   => "add   ".to_string(),
            BinOp::CmpLT => "cmplt ".to_string()
        }
    }
}
impl BinOp {
    fn calc(self, argL: u32, argR: u32) -> u32 {
        match self {
            BinOp::Add   => argL + argR,
            BinOp::CmpLT => if argL < argR { 1 } else { 0 }
        }
    }
}


#[derive(Clone)]
enum Insn<'a> {
    Imm { dst: Reg, imm: u32 },
    BinOp { op: BinOp, dst: Reg, srcL: Reg, srcR: RI },
    Load { dst: Reg, addr: Reg },
    Store { addr: Reg, src: Reg },
    Spill { dst: SlotIx, src: Reg },
    Reload { dst: Reg, src: SlotIx },
    Goto { target: Label<'a> },
    GotoCTF { cond: Reg, targetT: Label<'a>, targetF: Label<'a> },
    PrintS { str: &'a str },
    PrintI { reg: Reg },
    Finish { }
}

impl<'a> Show for Insn<'a> {
    fn show(&self) -> String {
        match self {
            Insn::Imm { dst, imm } =>
                "imm    ".to_string()
                + &dst.show() + &", ".to_string() + &imm.to_string(),
            Insn::BinOp { op, dst, srcL, srcR } =>
                op.show() + &" ".to_string() + &dst.show()
                + &", ".to_string() + &srcL.show() + &", ".to_string()
                + &srcR.show(),
            Insn::Load { dst, addr } =>
                "load   ".to_string() + &dst.show() + &", [".to_string()
                + &addr.show() + &"]".to_string(),
            Insn::Store { addr, src } =>
                "store  [".to_string() + &addr.show() + &"], ".to_string()
                + &src.show(),
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

impl<'a> Insn<'a> {
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

    // Returns a pair of vectors of regs, being those def'd (written) and
    // use'd (read) by the instruction, respectively.  Note that the vectors
    // may contain duplicates, particularly in the (fairly common) case where
    // an instruction reads the same register twice.
    fn getRegUsage(&self) -> (Vec::<Reg>, Vec::<Reg>) {
        let mut def = Vec::<Reg>::new();
        let mut uce = Vec::<Reg>::new();
        match self {
            Insn::Imm { dst, imm:_ } => {
                def.push(*dst);
            },
            Insn::BinOp { op:_, dst, srcL, srcR } => {
                def.push(*dst);
                uce.push(*srcL);
                srcR.addRegReadsTo(&mut uce);
            },
            Insn::Store { addr, src } => {
                uce.push(*addr);
                uce.push(*src);
            },
            Insn::Load { dst, addr } => {
                def.push(*dst);
                uce.push(*addr);
            },
            Insn::Goto { .. } => { },
            Insn::GotoCTF { cond, targetT:_, targetF:_ } => {
                uce.push(*cond);
            },
            Insn::PrintS { .. } => { },
            Insn::PrintI { reg } => {
                uce.push(*reg);
            },
            Insn::Finish { } => { },
            _other => panic!("Insn::getRegUsage: unhandled: {}", self.show())
        }
        (def, uce)
    }
}

fn i_imm<'a>(dst: Reg, imm: u32) -> Insn<'a> { Insn::Imm { dst, imm } }
// For BinOp variants see below
fn i_load<'a>(dst: Reg, addr: Reg) -> Insn<'a> { Insn::Load { dst, addr } }
fn i_store<'a>(addr: Reg, src: Reg) -> Insn<'a> { Insn::Store { addr, src } }
fn i_goto<'a>(target: &'a str) -> Insn<'a> {
    Insn::Goto { target: mkUnresolved(target) }
}
fn i_goto_ctf<'a>(cond: Reg, targetT: &'a str, targetF: &'a str) -> Insn<'a> {
    Insn::GotoCTF { cond: cond, targetT: mkUnresolved(targetT),
                    targetF: mkUnresolved(targetF) }
}
fn i_print_s<'a>(str: &'a str) -> Insn<'a> { Insn::PrintS { str } }
fn i_print_i<'a>(reg: Reg) -> Insn<'a> { Insn::PrintI { reg } }
fn i_finish<'a>() -> Insn<'a> { Insn::Finish { } }

fn i_add<'a>(dst: Reg, srcL: Reg, srcR: RI) -> Insn<'a> {
    Insn::BinOp { op: BinOp::Add, dst, srcL, srcR }
}
fn i_cmp_lt<'a>(dst: Reg, srcL: Reg, srcR: RI) -> Insn<'a> {
    Insn::BinOp { op: BinOp::CmpLT, dst, srcL, srcR }
}

fn is_control_flow_insn<'a>(insn: &Insn<'a>) -> bool {
    match insn {
        Insn::Goto { .. } | Insn::GotoCTF { .. } | Insn::Finish{} => true,
        _ => false
    }
}

fn resolveInsn<'a, F>(insn: &mut Insn<'a>, lookup: F)
    where F: Copy + Fn(&'a str) -> BlockIx
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
// Definition of Block and CFG, and printing thereof.

struct Block<'a> {
    name: &'a str,
    start: InsnIx,
    len: u32,
    eef: u16
}
fn mkBlock<'a>(name: &'a str, start: InsnIx, len: u32) -> Block<'a> {
    Block { name: name, start: start, len: len, eef: 1 }
}
impl<'a> Block<'a> {
    fn containsInsnIx(&self, iix: InsnIx) -> bool {
        iix.get() >= self.start.get()
            && iix.get() < self.start.get() + self.len
    }
}


struct CFG<'a> {
    name:   &'a str,
    entry:  Label<'a>,
    nVRegs: u32,
    insns:  Vec::</*InsnIx, */Insn<'a>>,    // indexed by InsnIx
    blocks: Vec::</*BlockIx, */Block<'a>>   // indexed by BlockIx
}

// Find a block Ix for a block name
fn lookup<'a>(blocks: &Vec::<Block<'a>>, name: &'a str) -> BlockIx {
    let mut bix = 0;
    for b in blocks.iter() {
        if b.name == name {
            return mkBlockIx(bix);
        }
        bix += 1;
    }
    panic!("CFG::lookup: can't resolve label name '{}'", name);
}

impl<'a> CFG<'a> {
    fn new(name: &'a str, entry: &'a str) -> Self {
        CFG {
            name: name,
            entry: Label::Unresolved { name: entry },
            nVRegs: 0,
            insns: Vec::<Insn<'a>>::new(),
            blocks: Vec::<Block<'a>>::new()
        }
    }

    fn print(&self, who: &str) {
        println!("");
        println!("CFG {}: name='{}' entry='{}' {{",
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

    // Add a block to the CFG
    fn block(&mut self, name: &'a str, mut insns: Vec::<Insn<'a>>) {
        let start = self.insns.len() as u32;
        let len = insns.len() as u32;
        self.insns.append(&mut insns);
        let b = mkBlock(name, mkInsnIx(start), len);
        self.blocks.push(b);
    }

    // All blocks have been added.  Resolve labels and we're good to go.
    /* .finish(): check
          - all blocks nonempty
          - all blocks end in i_finish, i_goto or i_goto_ctf
          - no blocks have those insns before the end
          - all referenced blocks actually exist
          - convert references to block numbers
    */
    fn finish(&mut self) {
        for b in self.blocks.iter() {
            if b.len == 0 {
                panic!("CFG::done: a block is empty");
            }
            for i in 0 .. b.len {
                let iix = mkInsnIx(b.start.get() + i);
                if i == b.len - 1 &&
                    !is_control_flow_insn(&self.insns[iix.get_usize()]) {
                    panic!("CFG: block must end in control flow insn");
                }
                if i != b.len -1 &&
                    is_control_flow_insn(&self.insns[iix.get_usize()]) {
                    panic!("CFG: block contains control flow insn not at end");
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
    cfg:   &'a CFG<'a>,
    nia:   InsnIx, // Program counter
    vregs: Vec::<Option::<u32>>, // unlimited
    rregs: Vec::<Option::<u32>>, // [0 .. maxRRegs)
    mem:   Vec::<Option::<u32>>  // [0 .. maxMem)
}

impl<'a> IState<'a> {
    fn new(cfg: &'a CFG<'a>, maxRRegs: usize, maxMem: usize) -> Self {
        let mut state =
            IState {
                cfg:      cfg,
                nia:      cfg.blocks[cfg.entry.getBlockIx().get_usize()].start,
                vregs:    Vec::new(),
                rregs:    Vec::new(),
                mem:      Vec::new(),
            };
        state.rregs.resize(maxRRegs, None);
        state.mem.resize(maxMem, None);
        state
    }

    fn getRReg(&self, rreg: RReg) -> u32 {
        // No automatic resizing.  If the reg doesn't exist, just fail.
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
        // No automatic resizing.  If the reg doesn't exist, just fail.
        match self.rregs.get_mut(rreg.get_usize()) {
            None =>
                panic!("IState::setRReg: invalid rreg# {}", rreg.get()),
            Some(valP)
                => *valP = Some(val)
        }
    }

    fn getVReg(&self, vreg: VReg) -> u32 {
        // The vector might be too small.  But in that case we'd be
        // reading the reg uninitialised anyway, so just complain.
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

    // Move the interpreter one step forward
    fn step(&mut self) -> bool {
        let mut done = false;

        let iix = self.nia.get();
        self.nia = mkInsnIx(iix + 1);

        let insn = &self.cfg.insns[iix as usize];
        match insn {
            Insn::Imm { dst, imm } =>
                self.setReg(*dst, *imm),
            Insn::BinOp { op, dst, srcL, srcR } => {
                let srcL_v = self.getReg(*srcL);
                let srcR_v = self.getRI(srcR);
                let dst_v = op.calc(srcL_v, srcR_v);
                self.setReg(*dst, dst_v);
            },
            Insn::Load { dst, addr } => {
                let addr_v = self.getReg(*addr);
                let dst_v = self.getMem(addr_v);
                self.setReg(*dst, dst_v);
            },
            Insn::Store { addr, src } => {
                let addr_v = self.getReg(*addr);
                let src_v  = self.getReg(*src);
                self.setMem(addr_v, src_v);
            },
            Insn::Goto { target } =>
                self.nia = self.cfg.blocks[target.getBlockIx().get_usize()]
                               .start,
            Insn::GotoCTF { cond, targetT, targetF } => {
                let target =
                       if self.getReg(*cond) != 0 { targetT } else { targetF };
                self.nia = self.cfg.blocks[target.getBlockIx().get_usize()]
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

impl<'a> CFG<'a> {
    fn run(&self, who: &str) {
        println!("");
        println!("Running stage '{}': CFG: name='{}' entry='{}'",
                 who, self.name, self.entry.show());

        let mut istate = IState::new(&self, /*maxRRegs=*/4, /*maxMem=*/64);
        let mut done = false;
        while !done {
            done = istate.step();
        }

        println!("Running stage '{}': done.", who);
    }
}


//=============================================================================
// Sets of things

struct Set<T> {
    set: HashSet<T>
}

impl<T: Eq + Ord + Hash + Copy + Show> Set<T> {
    fn empty() -> Self {
        Self {
            set: HashSet::<T>::new()
        }
    }

    fn unit(item: T) -> Self {
        let mut s = Self::empty();
        s.insert(item);
        s
    }

    fn insert(&mut self, item: T) {
        self.set.insert(item);
    }

    fn contains(&self, item: T) -> bool {
        self.set.contains(&item)
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

    fn to_vec(&self) -> Vec::<T> {
        let mut res = Vec::<T>::new();
        for item in self.set.iter() {
            res.push(*item)
        }
        res.sort_unstable();
        res
    }

    fn equals(&self, other: &Self) -> bool {
        // This is an appallingly inefficient implementation.  But it's simple.
        let v1 = self.to_vec();
        let v2 = other.to_vec();
        // Since v1 and v2 are sorted, they will be element-wise identical if
        // the sets themselves contain identical elements.
        if v1.len() != v2.len() {
            return false;
        }
        for (e1, e2) in v1.iter().zip(v2) {
            if *e1 != e2 {
                return false;
            }
        }
        true
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


//=============================================================================
// CFG successor and predecessor maps

struct CFGMap {
    pred_map: Vec::<Set<BlockIx>>, // Vec contains one element per block
    succ_map: Vec::<Set<BlockIx>>  // Ditto
}

impl CFGMap {
    fn create(cfg: &CFG) -> Self {
        // First calculate the succ map, since we can do that directly from
        // the CFG.

        // CFG::finish() ensures that all blocks are non-empty, and that only
        // the last instruction is a control flow transfer.  Hence the
        // following won't miss any edges.
        let mut succ_map = Vec::<Set<BlockIx>>::new();
        for b in cfg.blocks.iter() {
            let last_insn = &cfg.insns[ b.start.get_usize()
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
        pred_map.resize(cfg.blocks.len(), Set::empty());
        for (src, dst_set) in (0..).zip(&succ_map) {
            for dst in dst_set.to_vec().iter() {
                pred_map[dst.get_usize()].insert(mkBlockIx(src));
            }
        }

        // Stay sane ..
        debug_assert!(pred_map.len() == cfg.blocks.len());
        debug_assert!(succ_map.len() == cfg.blocks.len());

        CFGMap { pred_map, succ_map }
    }
}


//=============================================================================
// Computation of live-in and live-out sets

impl<'a> CFG<'a> {
    // Returned vectors contain one element per block
    fn calc_def_and_use(&self) -> (Vec::<Set<Reg>>, Vec::<Set<Reg>>) {
        let mut def_sets = Vec::new();
        let mut use_sets = Vec::new();
        for b in self.blocks.iter() {
            let mut def = Set::empty();
            let mut uce = Set::empty();
            for iix in b.start.get_usize() .. b.start.get_usize()
                                              + b.len as usize {
                let insn = &self.insns[iix];
                let (regs_d, regs_u) = insn.getRegUsage();
                for u in regs_u.iter() {
                    // |u| is used (read) by the instruction.  Whether or not
                    // we should consider it live-in for the block depends on
                    // whether it was been written earlier in the block.  We
                    // can determine that by checking whether it is already in
                    // the def set for the block.
                    if !def.contains(*u) {
                        uce.insert(*u);
                    }
                }
                for d in regs_d.iter() {
                    def.insert(*d);
                }
            }
            def_sets.push(def);
            use_sets.push(uce);
        }
        (def_sets, use_sets)
    }

    // Returned vectors contain one element per block
    fn calc_livein_and_liveout(&self,
                               def_sets_per_block: &Vec::<Set<Reg>>,
                               use_sets_per_block: &Vec::<Set<Reg>>,
                               cfg_map: &CFGMap
                              ) -> (Vec::<Set<Reg>>, Vec::<Set<Reg>>) {
        let empty = Set::<Reg>::empty();
        let mut liveins  = Vec::<Set::<Reg>>::new();
        let mut liveouts = Vec::<Set::<Reg>>::new();

        let nBlocks = self.blocks.len();
        liveins.resize(nBlocks, empty.clone());
        liveouts.resize(nBlocks, empty.clone());

        let mut _iterNo = 0;

        loop {
            let mut changed = false;
            let mut new_liveins  = Vec::<Set::<Reg>>::new();
            let mut new_liveouts = Vec::<Set::<Reg>>::new();

            for bix in 0 .. nBlocks {
                let def = &def_sets_per_block[bix];
                let uce = &use_sets_per_block[bix];
                let old_livein  = &liveins[bix];
                let old_liveout = &liveouts[bix];

                let mut new_livein = old_liveout.clone();
                new_livein.remove(&def);
                new_livein.union(&uce);

                let mut new_liveout = Set::<Reg>::empty();
                for succ_bix in cfg_map.succ_map[bix].to_vec().iter() {
                    new_liveout.union(&liveins[succ_bix.get_usize()]);
                }

                if !new_livein.equals(&old_livein)
                   || !new_liveout.equals(&old_liveout) {
                    changed = true;
                }

                new_liveins.push(new_livein);
                new_liveouts.push(new_liveout);
            }

            liveins = new_liveins;
            liveouts = new_liveouts;

            ////!!
            /*
            println!("");
            println!("After  iteration {}", iterNo);
            iterNo += 1;
            let mut n = 0;
            for (livein, liveout) in liveins.iter().zip(&liveouts) {
                println!("  block {}:  livein {:<16}  liveout {:<16}",
                         n, livein.show(), liveout.show());
                n += 1;
            }
            */
            ////!!

            if !changed {
                break;
            }
        }

        (liveins, liveouts)
    }
}


//=============================================================================
// Representing and printing of live range fragments.

#[derive(Copy, Clone, Hash, PartialEq, Eq, Ord)]
enum UorD { U, D }
impl PartialOrd for UorD {
    // In short .. U < D.  This is probably what would be #derive'd anyway,
    // but we need to be sure.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (UorD::U, UorD::U) => Some(Ordering::Equal),
            (UorD::U, UorD::D) => Some(Ordering::Less),
            (UorD::D, UorD::U) => Some(Ordering::Greater),
            (UorD::D, UorD::D) => Some(Ordering::Equal)
        }
    }
}


// See comments below on |Frag| for the meaning of |FragPoint|.
#[derive(Copy, Clone, Hash, PartialEq, Eq, Ord)]
struct FragPoint {
    iix:  InsnIx,
    uord: UorD
}
fn FragPoint_U(iix: InsnIx) -> FragPoint {
    FragPoint { iix: iix, uord: UorD::U }
}
fn FragPoint_D(iix: InsnIx) -> FragPoint {
    FragPoint { iix: iix, uord: UorD::D }
}
impl PartialOrd for FragPoint {
    // Again .. don't assume anything about the #derive'd version.  These have
    // to be ordered using |iix| as the primary key and |uord| as the
    // secondary.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.iix.partial_cmp(&other.iix) {
            Some(Ordering::Less)    => Some(Ordering::Less),
            Some(Ordering::Greater) => Some(Ordering::Greater),
            Some(Ordering::Equal)   => self.uord.partial_cmp(&other.uord),
            None => panic!("FragPoint::partial_cmp: fail #1"),
        }
    }
}
impl Show for FragPoint {
    fn show(&self) -> String {
        match self.uord {
            UorD::U => self.iix.get().show() + &".u".to_string(),
            UorD::D => self.iix.get().show() + &".d".to_string()
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
// different "positions" for each instruction: the Use position, where
// incoming registers are read, and the Def position, where outgoing registers
// are written.  The Use position is considered to come before the Def
// position.
//
// The set of positions indicated by {0 .. #insns-1} x {Use point, Def point}
// is exactly the set of positions that we need to keep track of when mapping
// live ranges to registers.  This the reason for the type FragPoint.  Note
// that FragPoint values have a total ordering, at least within a single basic
// block: the insn number is used as the primary key, and the Use/Def part is
// the secondary key, with Use < Def.
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
    first: FragPoint,
    last:  FragPoint,
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
               first: FragPoint_D(live_after),
               last:  FragPoint_D(live_after),
               count: count }
    } else {
        debug_assert!(count >= 2);
        Frag { bix:   bix,
               kind:  FragKind::Local,
               first: FragPoint_D(live_after),
               last:  FragPoint_U(dead_after),
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
           first: FragPoint_U(block.start),
           last:  FragPoint_U(dead_after),
           count: count }
}
fn mk_Frag_LiveOut(blocks: &Vec::<Block>,
                  bix: BlockIx, live_after: InsnIx, count: u16) -> Frag {
    debug_assert!(count >= 1);
    let block = &blocks[bix.get_usize()];
    debug_assert!(block.containsInsnIx(live_after));
    Frag { bix:   bix,
           kind:  FragKind::LiveOut,
           first: FragPoint_D(live_after),
           last:  FragPoint_D(block.start.plus(block.len - 1)),
           count: count }
}
fn mk_Frag_Thru(blocks: &Vec::<Block>, bix: BlockIx, count: u16) -> Frag {
    // Count can be any value, zero or more.
    let block = &blocks[bix.get_usize()];
    Frag { bix:   bix,
           kind:  FragKind::Thru,
           first: FragPoint_U(block.start),
           last:  FragPoint_D(block.start.plus(block.len - 1)),
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


//=============================================================================
// Computation of Frags (Live Range Fragments)

// This is surprisingly complex, in part because of the need to correctly
// handle dead writes.

// Frag_SME ("Frag State Machine Entry") defines states for a state machine
// used to track states of Regs during Frag construction.  Each state contains
// information for an Frag that is currently under construction.  There are
// really 3 states: NoInfo, Written and WrThenRd.  We don't represent NoInfo
// explicitly because most blocks don't reference most Regs, so in
// |get_Frags_for_block|, it would be wasteful to have a mapping for all Regs
// most of which were just to NoInfo.  Instead, NoInfo is implied by a Reg not
// being mapped in |state|.

impl<'a> CFG<'a> {
    // Calculate all the Frags for |bix|.  Add them to |outFEnv| and add to
    // |outMap|, the associated FragIxs, segregated by Reg.  |bix|, |livein|
    // and |liveout| are expected to be valid in the context of the CFG |self|
    // (duh!)
    fn get_Frags_for_block(&self, bix: BlockIx,
                           livein: &Set::<Reg>, liveout: &Set::<Reg>,
                           outMap: &mut HashMap::<Reg, Vec::<FragIx>>,
                           outFEnv: &mut Vec::<Frag>)
    {
        // State machine entries.  See comment above.
        enum Frag_SME {
            // So far we have seen no mention of the Reg, either in the block
            // proper or in livein.  This state is implied, per comments
            // above, and not represented.  NoInfo { .. },

            // Reg has been written.  Either prior to the block (iow, it is
            // live-in), if |wp| is None.  Or else |wp| is Some(live_after),
            // to indicate the defining insn.
            Written { uses: u16, wp: Option<InsnIx> },

            // Written, then read.  Meaning of |wp| is same as above.  |rp| is
            // the most recently observed read point, using the usual
            // dead_after indexing.
            WrThenRd { uses: u16, wp: Option<InsnIx>, rp: InsnIx }
        }
        // end State machine entries

        // Helper function: compare ordering of frag start points, taking into
        // account a possible live-in start point.
        fn precedes(point1: Option<InsnIx>, point2: InsnIx) -> bool {
            if let Some(point1_iix) = point1 {
                point1_iix.get() <= point2.get()
            } else {
                true
            }
        }
        fn plus1(n: u16) -> u16 { if n == 0xFFFFu16 { n } else { n+1 } }
        // end Helper functions

        // The running state.
        let blocks = &self.blocks;
        let block = &blocks[bix.get_usize()];
        let mut state = HashMap::<Reg, Frag_SME>::new();

        // The generated Frag components are initially are dumped in here.  We
        // group them by Reg at the end of this function.
        let mut tmpResultVec = Vec::<(Reg, Frag)>::new();

        // First, set up |state| as if all of |livein| had been written just
        // prior to the block.
        for r in livein.to_vec().iter() {
            state.insert(*r, Frag_SME::Written { uses: 0, wp: None });
        }

        // Now visit each instruction in turn, examining first its reads and
        // then its writes.
        for ix in block.start.get() .. block.start.get() + block.len {
            let iix = mkInsnIx(ix);
            let insn = &self.insns[ix as usize];
            let (regs_d, regs_u) = insn.getRegUsage();

            // Examine reads.  This is pretty simple.  They simply extend
            // existing fragments.
            for r in regs_u.iter() {
                let new_sme: Frag_SME;
                match state.get(r) {
                    // First event for |r| is a read, but it's not listed
                    // in |livein|.
                    None => {
                        panic!("get_Frags_for_block: fail #1");
                    },
                    // The first read after a write.  Note that the "write"
                    // can be either a real write, or due to the fact that |r|
                    // is listed in |livein|.  We don't care here.
                    Some(Frag_SME::Written { uses, wp }) => {
                        new_sme = Frag_SME::WrThenRd { uses: plus1(*uses),
                                                       wp: *wp, rp: iix };
                    },
                    // A subsequent read (== second or more read after a
                    // write).  Same comment as above re meaning of "write".
                    Some(Frag_SME::WrThenRd { uses, wp, rp }) => {
                        debug_assert!(precedes(*wp, *rp));
                        debug_assert!(precedes(Some(*rp), iix));
                        new_sme = Frag_SME::WrThenRd { uses: plus1(*uses),
                                                       wp: *wp, rp: iix };
                    }
                }
                state.insert(*r, new_sme);
            }

            // Examine writes.  The general idea is that a write causes us to
            // terminate the existing frag, if any, add it to |tmpResultVec|,
            // and start a new frag.  But we have to be careful to deal
            // correctly with dead writes.
            for r in regs_d.iter() {
                let new_sme: Frag_SME;
                match state.get(r) {
                    // First mention of a Reg we've never heard of before.
                    // Note it and keep going.
                    None => {
                        new_sme = Frag_SME::Written { uses: 1, wp: Some(iix) };
                    },
                    // |r| must be in |livein|, but the first event for it is
                    // a write.  That can't happen -- |livein| must be
                    // incorrect.
                    Some(Frag_SME::Written { uses:_, wp: None }) => {
                        panic!("get_Frags_for_block: fail #2");
                    },
                    // |r| has been written before in this block, but not
                    // subsequently read.  Hence the write is dead.  Emit a
                    // "point" frag, then note this new write instead.
                    Some(Frag_SME::Written { uses, wp: Some(wp_iix) }) => {
                        debug_assert!(*uses == 1);
                        let frag = mk_Frag_Local(blocks, bix,
                                                 *wp_iix, *wp_iix, *uses);
                        tmpResultVec.push((*r, frag));
                        new_sme = Frag_SME::Written { uses: 1, wp: Some(iix) };
                    },
                    // There's already a valid frag for |r|.  This write will
                    // start a new frag, so flush the existing one and note
                    // this write.
                    Some(Frag_SME::WrThenRd { uses, wp, rp }) => {
                        let frag: Frag;
                        if let Some(wr_iix) = wp {
                            frag = mk_Frag_Local(blocks, bix,
                                                 *wr_iix, *rp, *uses);
                        } else {
                            frag = mk_Frag_LiveIn(blocks, bix, *rp, *uses);
                        }
                        tmpResultVec.push((*r, frag));
                        new_sme = Frag_SME::Written { uses: 1, wp: Some(iix) };
                    }
                }
                state.insert(*r, new_sme);
            }
        }

        // We are at the end of the block.  We still have to deal with
        // live-out Regs.  We must also deal with fragments in |state| that
        // are for registers not listed as live-out.

        // Deal with live-out Regs.  Treat each one as if it is read just
        // after the block.
        for r in liveout.to_vec().iter() {
            match state.get(r) {
                // This can't happen.  It implies that |r| is in |liveout|,
                // but is neither defined in the block nor present in |livein|.
                None => {
                    panic!("get_Frags_for_block: fail #3");
                },
                // |r| is "written", either literally or by virtue of being
                // present in |livein|, and may or may not subsequently be
                // read (we don't care).  Create a |LiveOut| or |Thru| frag
                // accordingly.
                Some(Frag_SME::Written { uses, wp }) |
                Some(Frag_SME::WrThenRd { uses, wp, rp:_ }) => {
                    let frag: Frag;
                    if let Some(wr_iix) = wp {
                        frag = mk_Frag_LiveOut(blocks, bix, *wr_iix, *uses);
                    } else {
                        frag = mk_Frag_Thru(blocks, bix, *uses);
                    }
                    tmpResultVec.push((*r, frag));
                }
            }
            // Remove the entry from |state| so that the following loop
            // doesn't process it again.
            state.remove(r);
        }

        // Finally, round up any remaining valid fragments left in |state|.
        for (r, st) in state.iter() {
            match st {
                // This implies |r| is in |livein| but is neither in |liveout|
                // nor is it read in the block.  Which can't happen.
                Frag_SME::Written { uses:_, wp: None } => {
                    panic!("get_Frags_for_block: fail #4");
                },
                // This implies |r| has been written, but was never read,
                // either directly or by virtue of being in |liveout|.  So
                // just emit a "point" frag.
                Frag_SME::Written { uses, wp: Some(wp_iix) } => {
                    debug_assert!(*uses == 1);
                    let frag = mk_Frag_Local(blocks, bix,
                                             *wp_iix, *wp_iix, *uses);
                    tmpResultVec.push((*r, frag));
                },
                // This is a more normal case.  |r| is either in |livein| or
                // is first written inside the block, and later read, but is
                // not in |liveout|.
                Frag_SME::WrThenRd { uses, wp, rp } => {
                    let frag: Frag;
                    if let Some(wr_iix) = wp {
                        frag = mk_Frag_Local(blocks, bix, *wr_iix, *rp, *uses);
                    } else {
                        frag = mk_Frag_LiveIn(blocks, bix, *rp, *uses);
                    }
                    tmpResultVec.push((*r, frag));
                }
            }
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

    fn get_Frags(&self,
                 livein_sets_per_block:  &Vec::<Set<Reg>>,
                 liveout_sets_per_block: &Vec::<Set<Reg>>
                ) -> (HashMap::<Reg, Vec<FragIx>>, Vec::<Frag>)
    {
        debug_assert!(livein_sets_per_block.len()  == self.blocks.len());
        debug_assert!(liveout_sets_per_block.len() == self.blocks.len());
        let mut resMap  = HashMap::<Reg, Vec<FragIx>>::new();
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
// order (per their FragPoint fields).  

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
}


//=============================================================================
// Representing and printing live ranges.  This is parameterised over the reg
// type, since we don't care what it is.

// Finally, a live range.  This is the fundamental unit of allocation.  This
// pairs a Reg with a vector of FragIxs in which it is live.  The FragIxs are
// indices into some vector of Frags (a "fragment environment, 'fenv'), which
// is not specified here.  They are sorted so as to give ascending order to
// the Frags which they refer to.
//
// Live ranges may contain metrics.  Not all are initially filled in:
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
// I find it helpful to think of a live range as a "renaming equivalence
// class".  That is, if you rename |reg| at some point inside |sfrags|, then
// you must rename *all* occurrences of |reg| inside |sfrags|, since otherwise
// the program will no longer work.
struct LR<R> {
    reg:    R,
    sfrags: SortedFragIxs,
    size:   u16,
    cost:   Option<f32>,
}
impl<R: Show> Show for LR<R> {
    fn show(&self) -> String {
        let cost_str: String;
        match self.cost {
            None => {
                cost_str = "*INF*".to_string();
            },
            Some(c) => {
                cost_str = format!("{:<5.2}", c);
            }
        }
        self.reg.show() + &" s=".to_string() + &self.size.to_string()
            + &",c=".to_string() + &cost_str
            + &" ".to_string() + &self.sfrags.show()
    }
}


// Indices into vectors of LRs.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LRIx {
    LRIx(u32)
}
fn mkLRIx(n: u32) -> LRIx { LRIx::LRIx(n) }
impl LRIx {
    fn get(self) -> u32 { match self { LRIx::LRIx(n) => n } }
    fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for LRIx {
    fn show(&self) -> String {
        "lr".to_string() + &self.get().to_string()
    }
}


//=============================================================================
// Merging of Frags, producing the final LRs, minus metrics

fn merge_Frags(fragIx_vecs_per_reg: &HashMap::<Reg, Vec<FragIx>>,
               frag_env: &Vec::</*FragIx, */Frag>,
               cfg_map: &CFGMap)
               -> (Vec::<LR<RReg>>, Vec::<LR<VReg>>)
{
    let mut resR = Vec::<LR<RReg>>::new();
    let mut resV = Vec::<LR<VReg>>::new();
    for (reg, all_fragIxs_for_reg) in fragIx_vecs_per_reg.iter() {

        // BEGIN merge |all_fragIxs_for_reg| entries as much as possible.
        // Each |state| entry has four components:
        //    (1) An is-this-entry-still-valid flag
        //    (2) A vec of FragIxs.  These should refer to disjoint Frags.
        //    (3) A set of blocks, which are those corresponding to (2)
        //        that are LiveIn or Thru (== have an inbound value)
        //    (4) A set of blocks, which are the union of the successors of
        //        blocks corresponding to the (2) which are LiveOut or Thru
        //        (== have an outbound value)
        struct MergeGroup {
            valid: bool,
            fragIxs: Vec::<FragIx>,
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
            let frag_succ_bixes = &cfg_map.succ_map[frag_bix.get_usize()];
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
            let fragIxs = vec![*fix];
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
                        state[j].fragIxs.append(&mut tmp_fragIxs);
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
            let sfrags = SortedFragIxs::new(&fragIxs, &frag_env);
            let size = 0;
            let cost = Some(0.0);
            match *reg {
                Reg::RReg(rreg) => {
                    resR.push(LR { reg: rreg, sfrags, size, cost });
                }
                Reg::VReg(vreg) => {
                    resV.push(LR { reg: vreg, sfrags, size, cost });
                }
            }
        }

        // END merge |all_fragIxs_for_reg| entries as much as possible
    }

    (resR, resV)
}


//=============================================================================
// Finalising of LRs, by setting the |size| and |cost| metrics.

// |size|: this is simple.  Simply sum the size of the individual fragments.
// Note that this must produce a value > 0 for a dead write, hence the "+1".
//
// |cost|: try to estimate the number of spills and reloads that would result
// from spilling the LR, thusly:
//    sum, for each frag
//        # mentions of the Reg in the frag
//            (that's the per-frag, per pass spill cost)
//        *
//        the estimated execution count of the containing block
//
// all the while being very careful to avoid overflow.
fn set_LR_metrics<R>(lrs: &mut Vec::<LR<R>>,
                     fenv: &Vec::<Frag>, blocks: &Vec::<Block>)
{
    for lr in lrs {
        debug_assert!(lr.size == 0 && lr.cost == Some(0.0));
        let mut tot_size: u32 = 0;
        let mut tot_cost: f32 = 0.0;

        for fix in &lr.sfrags.fragIxs {
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
        lr.size = tot_size as u16;

        // Divide tot_cost by the total length, so as to increase the apparent
        // spill cost of short LRs.  This is so as to give the advantage to
        // short LRs in competition for registers.  This seems a bit of a hack
        // to me, but hey ..
        tot_cost /= tot_size as f32;
        tot_cost *= 10.0; // Just to make the numbers look a bit nicer
        lr.cost = Some(tot_cost);
    }
}

fn cost_is_less(cost1: Option<f32>, cost2: Option<f32>) -> bool {
    // None denotes "infinity", while Some(_) is some number less than
    // infinity.  No matter that the enclosed f32 can denote its own infinity
    // :-/
    match (cost1, cost2) {
        (None,    None) => false,
        (Some(_),  None) => true,
        (None,     Some(_)) => false,
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
    unallocated: Vec::<LRIx>
}
impl VLRPrioQ {
    fn new(vlr_env: &Vec::<LR<VReg>>) -> Self {
        let mut res = Self { unallocated: Vec::new() };
        for ix in 0 .. vlr_env.len() {
            assert!(vlr_env[ix].size > 0);
            res.unallocated.push(mkLRIx(ix as u32));
        }
        res
    }

    // Add a VLR index.
    fn add_VLR(&mut self, vlr_ix: LRIx) {
        self.unallocated.push(vlr_ix);
    }

    // Look in |unallocated| to locate the entry referencing the VLR with the
    // largest |size| value.  Remove the ref from |unallocated| and return the
    // LRIx for said entry.
    fn get_longest_VLR(&mut self, vlr_env: &Vec::<LR<VReg>>) -> Option<LRIx> {
        if self.unallocated.len() == 0 {
            return None;
        }
        let mut largestIx   = self.unallocated.len(); /*INVALID*/
        let mut largestSize = 0; /*INVALID*/
        for i in 0 .. self.unallocated.len() {
            let cand_lrix = self.unallocated[i];
            let cand_lr = &vlr_env[cand_lrix.get_usize()];
            if cand_lr.size > largestSize {
                largestSize = cand_lr.size;
                largestIx   = i;
            }
        }
        // We must have found *something* since there was at least one
        // unallocated LR still available.
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

    fn show_with_envs(&self, vlr_env: &Vec::<LR<VReg>>) -> String {
        let mut res = "".to_string();
        let mut first = true;
        for vlrix in self.unallocated.iter() {
            if !first { res += &"\n".to_string(); }
            first = false;
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
    // The union of their frags will be equal to |frags_in_use| only if no
    // RLRs have been assigned to this RReg.  If RLRs have been assigned to
    // this RReg then that union will be exactly the subset of |frags_in_use|
    // not used by the assigned RLRs.
    vlrs_assigned: Vec::<LRIx>
}
impl PerRReg {
    fn new(fenv: &Vec::<Frag>) -> Self {
        Self {
            frags_in_use: SortedFragIxs::new(&vec![], fenv),
            vlrs_assigned: Vec::<LRIx>::new()
        }
    }

    fn add_RLR(&mut self, to_add: &LR<RReg>, fenv: &Vec::<Frag>) {
        // Commit this register to |to_add|, irrevocably.  Don't add it to
        // |vlrs_assigned| since we will never want to later evict the
        // assignment.
        self.frags_in_use.add(&to_add.sfrags, fenv);
    }

    fn can_add_VLR_without_eviction(&self, to_add: &LR<VReg>,
                                    fenv: &Vec::<Frag>) -> bool {
        self.frags_in_use.can_add(&to_add.sfrags, fenv)
    }

    fn add_VLR(&mut self, to_add_vlrix: LRIx,
               vlr_env: &Vec::<LR<VReg>>, fenv: &Vec::<Frag>) {
        let vlr = &vlr_env[to_add_vlrix.get_usize()];
        self.frags_in_use.add(&vlr.sfrags, fenv);
        self.vlrs_assigned.push(to_add_vlrix);
    }

    fn del_VLR(&mut self, to_del_vlrix: LRIx,
               vlr_env: &Vec::<LR<VReg>>, fenv: &Vec::<Frag>) {
        debug_assert!(self.vlrs_assigned.len() > 0);
        // Remove it from |vlrs_assigned|
        let mut found = None;
        for i in 0 .. self.vlrs_assigned.len() {
            if self.vlrs_assigned[i] == to_del_vlrix {
                found = Some(i);
                break;
            }
        }
        if let Some(i) = found {
            self.vlrs_assigned[i]
                = self.vlrs_assigned[self.vlrs_assigned.len() - 1];
            self.vlrs_assigned.remove(self.vlrs_assigned.len() - 1);
        } else {
            panic!("PerRReg: del_VLR on VLR that isn't in vlrs_assigned");
        }
        // Remove it from |frags_in_use|
        let vlr = &vlr_env[to_del_vlrix.get_usize()];
        self.frags_in_use.del(&vlr.sfrags, fenv);
    }

    fn find_best_evict_VLR(&self, would_like_to_add: &LR<VReg>,
                           vlr_env: &Vec::<LR<VReg>>,
                           frag_env: &Vec::<Frag>)
                           -> Option<(LRIx, f32)> {
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
        let mut best_so_far: Option<(LRIx, f32)> = None;
        for cand_vlrix in &self.vlrs_assigned {
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
                // Either, this is the first possible candidate we've
                // seen, or it's better than any previous one.  In either
                // case, make note of it.
                best_so_far = Some((*cand_vlrix, cand_cost));
            }
        }
        best_so_far
    }

    fn show1_with_envs(&self, fenv: &Vec::<Frag>) -> String {
        "in_use:   ".to_string() + &self.frags_in_use.show_with_fenv(&fenv)
    }
    fn show2_with_envs(&self, fenv: &Vec::<Frag>) -> String {
        "assigned: ".to_string() + &self.vlrs_assigned.show()
    }
}


//=============================================================================
// Printing the allocator's top level state

fn print_RA_state(who: &str,
                  // State components
                  prioQ: &VLRPrioQ, perRReg: &Vec::<PerRReg>,
                  // The context (environment)
                  vlr_env: &Vec::<LR<VReg>>, frag_env: &Vec::<Frag>)
{
    println!("-------- RA state at '{}' --------", who);
    for ix in 0 .. perRReg.len() {
        println!("\n{:<3} {}\n    {}",
                 mkRReg(ix as u32).show(),
                 &perRReg[ix].show1_with_envs(&frag_env),
                 &perRReg[ix].show2_with_envs(&frag_env));
    }
    print!("\n{}\n", prioQ.show_with_envs(&vlr_env));
    println!("");
}


//=============================================================================
// Allocator top level

/* (more or less const) For each virtual live range
   - its sorted Frags
   - its total size
   - its spill cost

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

fn run_main(cfg: CFG, nRRegs: usize) {
    cfg.print("Initial");

    cfg.run("Before allocation");

    let (def_sets_per_block, use_sets_per_block) = cfg.calc_def_and_use();
    debug_assert!(def_sets_per_block.len() == cfg.blocks.len());
    debug_assert!(use_sets_per_block.len() == cfg.blocks.len());

    let mut n = 0;
    println!("");
    for (def, uce) in def_sets_per_block.iter().zip(&use_sets_per_block) {
        println!("{:<3}   def {:<16}  use {}",
                 mkBlockIx(n).show(), def.show(), uce.show());
        n += 1;
    }

    let cfg_map = CFGMap::create(&cfg);

    n = 0;
    println!("");
    for (preds, succs) in cfg_map.succ_map.iter().zip(&cfg_map.pred_map) {
        println!("{:<3}   preds {:<16}  succs {}",
                 mkBlockIx(n).show(), preds.show(), succs.show());
        n += 1;
    }

    let (livein_sets_per_block, liveout_sets_per_block) =
        cfg.calc_livein_and_liveout(&def_sets_per_block,
                                    &use_sets_per_block, &cfg_map);
    debug_assert!(livein_sets_per_block.len() == cfg.blocks.len());
    debug_assert!(liveout_sets_per_block.len() == cfg.blocks.len());

    n = 0;
    println!("");
    for (livein, liveout) in livein_sets_per_block.iter()
                                                  .zip(&liveout_sets_per_block) {
        println!("{:<3}   livein {:<16}  liveout {:<16}",
                 mkBlockIx(n).show(), livein.show(), liveout.show());
        n += 1;
    }

    let (fragIxs_per_reg, frag_env) =
        cfg.get_Frags(&livein_sets_per_block, &liveout_sets_per_block);

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

    let (mut rlr_env, mut vlr_env)
        = merge_Frags(&fragIxs_per_reg, &frag_env, &cfg_map);
    set_LR_metrics(&mut rlr_env, &frag_env, &cfg.blocks); // Pointless!
    set_LR_metrics(&mut vlr_env, &frag_env, &cfg.blocks); // Pointful!

    println!("");
    n = 0;
    for lr in &rlr_env {
        println!("rreg live range {}   {}", n, lr.show());
        n += 1;
    }

    println!("");
    n = 0;
    for lr in &vlr_env {
        println!("vreg live range {}   {}", n, lr.show());
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
        let rregNo = rlr.reg.get_usize();
        // Ignore RLRs for RRegs outside its allocation domain.  As far as the
        // allocator is concerned, such RRegs simply don't exist.
        if rregNo >= nRRegs {
            continue;
        }
        perRReg[rregNo].add_RLR(&rlr, &frag_env);
    }

    // let mut editList = Vec::<EditListElem>::new();
    println!("");
    print_RA_state("Initial", &prioQ, &perRReg, &vlr_env, &frag_env);

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
    while let Some(curr_vlrix) = prioQ.get_longest_VLR(&vlr_env) {
        let curr_vlr: &LR<VReg> = &vlr_env[curr_vlrix.get_usize()];

        println!("-- considering      {}", curr_vlr.show());

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
            println!("-- direct alloc to  {}", mkRReg(rregNo as u32).show());
            perRReg[rregNo].add_VLR(curr_vlrix, &vlr_env, &frag_env);
            continue;
        }

        // That didn't work out.  Next, try to see if we can allocate it by
        // evicting some existing allocation that has a lower spill weight.
        // Search all RRegs to find the candidate with the lowest spill
        // weight.  This could be expensive.

        // (rregNo for best cand, its LRIx, and its spill cost)
        let mut best_so_far: Option<(usize, LRIx, f32)> = None;
        for i in 0 .. nRRegs {
            let mut mb_better_cand: Option<(LRIx, f32)>;
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
                    // Either, this is the first possible candidate we've
                    // seen, or it's better than any previous one.  In either
                    // case, make note of it.
                    best_so_far = Some((i, cand_vlrix, cand_cost));
                }
            }
        }
        if let Some((rregNo, vlrix_to_evict, _)) = best_so_far {
            println!("-- evict            {}",
                     &vlr_env[vlrix_to_evict.get_usize()].show());
            perRReg[rregNo].del_VLR(vlrix_to_evict, &vlr_env, &frag_env);
            prioQ.add_VLR(vlrix_to_evict);
            println!("-- then alloc to    {}", mkRReg(rregNo as u32).show());
            perRReg[rregNo].add_VLR(curr_vlrix, &vlr_env, &frag_env);
            continue;
        }

        print_RA_state("At fail", &prioQ, &perRReg, &vlr_env, &frag_env);
        panic!("No clear reg");
    }

    print_RA_state("Final", &prioQ, &perRReg, &vlr_env, &frag_env);

    println!("");
}

/*
//=============================================================================
// Top level: the allocator's state

/*
struct RAState {
    // Results of initial analysis:
    preds_by_bix: Vec::</*BlockIx, */Set::<BlockIx>>,
    succs_by_bix: Vec::</*BlockIx, */Set::<BlockIx>>,

    defsets_by_bix: Vec::</*BlockIx, */Set::<Reg>>,
    usesets_by_bix: Vec::</*BlockIx, */Set::<Reg>>,

    liveins_by_bix:  Vec::</*BlockIx, */Set::<Reg>>,
    liveouts_by_bix: Vec::</*BlockIx, */Set::<Reg>>,

    frags_by_fix: Vec::</*FragIx */, Frag>,
    live_ranges_by_lrix: Vec::</*LRIx, */, LR>,

    // The running state of the core allocation algorithm

    // The current commitment per-register

    fixed_uses_by_rreg: Vec::</*RReg*/, Vec::<LRIx>>,
    nonfixed_uses
}

The live ranges must contain a sequence of nonoverlapping Frags, in
increasing order.  So they form a total order.

struct PerRReg {
    committed: Vec::<Frag>,   // non overlapping, in order

}

Questions for committed vector:
* does it have space for the LR (meaning, its Frags) ? (easy)
* if so add it (easy)
* and remove it (easy)
* does it have space for this LR if we eject some other LR
  (which it already has) ? (difficult)

Edit List
a vec of pairs (FragPoint, Insn) to be inserted there

SortedMFragVec:
   can another one be added?
   add another one, must not overlap
   remove one (must have been previously added)
   can another one be added if we first remove some third one
      (that was previously added?)

A list of LRIxes that have been committed to, ordered by increasing
  spill weight.  This is so that we can visit candidates to evict
  (un-commit) in O(not very much) time.
*/


//=============================================================================
// Top level
*/
fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        println!("usage: {} <name of CFG to use>", args[0]);
        return;
    }

    let cfg = match find_CFG(&args[1]) {
        Ok(cfg) => cfg,
        Err(available_cfg_names) => {
            println!("{}: can't find CFG with name '{}'", args[0], args[1]);
            println!("{}: available CFG names are:", args[0]);
            for name in available_cfg_names {
                println!("{}:     {}", args[0], name);
            }
            return;
        }
    };

    run_main(cfg, /*nRRegs=*/3);
}


//=============================================================================
// Test cases

#[test]
fn test_SortedFragIxs() {

    // Create a Frag and FragIx from two FragPoints.
    fn gen_fix(fenv: &mut Vec::<Frag>,
               first: FragPoint, last: FragPoint) -> FragIx {
        assert!(first <= last);
        let res = mkFragIx(fenv.len() as u32);
        let frag = Frag { bix: mkBlockIx(123),
                          kind: FragKind::Local, first, last, count: 0 };
        fenv.push(frag);
        res
    }

    fn getFrag<'a>(fenv: &'a Vec::<Frag>, fix: FragIx) -> &'a Frag {
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

    let fp_3u = FragPoint_U(iix3);
    let fp_3d = FragPoint_D(iix3);

    let fp_4u = FragPoint_U(iix4);

    let fp_5u = FragPoint_U(iix5);
    let fp_5d = FragPoint_D(iix5);

    let fp_6u = FragPoint_U(iix6);
    let fp_6d = FragPoint_D(iix6);

    let fp_7u = FragPoint_U(iix7);
    let fp_7d = FragPoint_D(iix7);

    let fp_10u = FragPoint_U(iix10);
    let fp_12u = FragPoint_U(iix12);
    let fp_15u = FragPoint_U(iix15);

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
// Example programs

// Returns either the requested CFG, or if not found, a list of the available
// ones.
fn find_CFG<'a>(name: &String) -> Result::<CFG<'a>, Vec::<&str>> {
    // This is really stupid.  Fortunately it's not performance critical :)
    let all_CFGs = vec![
        example_0(),
        example_1(),
    ];

    let mut all_names = Vec::new();
    for cand in &all_CFGs {
        all_names.push(cand.name);
    }

    for cand in all_CFGs {
        if cand.name == name {
            return Ok(cand);
        }
    }

    Err(all_names)
}

fn example_0<'a>() -> CFG<'a> {
    let mut cfg = CFG::new("straight_line", "b0");

    // Regs, virtual and real, that we want to use.
    let vA = cfg.vreg();

    cfg.block("b0", vec![
        i_print_s("Start\n"),
        i_imm(vA, 10),
        i_add(vA, vA, RI_I(7)),
        i_goto("b1"),
    ]);
    cfg.block("b1", vec![
        i_print_s("Result = "),
        i_print_i(vA),
        i_print_s("\n"),
        i_finish()
    ]);

    cfg.finish();
    cfg
}

fn example_1<'a>() -> CFG<'a> {
    let mut cfg = CFG::new("fill_then_sum", "set-loop-pre");

    // Regs, virtual and real, that we want to use.
    let vNENT = cfg.vreg();
    let vI    = cfg.vreg();
    let vSUM  = cfg.vreg();
    let rTMP  = Reg_R(mkRReg(2)); // "2" is arbitrary.
    let vTMP2 = cfg.vreg();

    // Loop pre-header for filling array with numbers.
    // This is also the entry point.
    cfg.block("set-loop-pre", vec![
        i_imm (vNENT, 10),
        i_imm (vI,    0),
        i_goto("set-loop")
    ]);

    // Filling loop
    cfg.block("set-loop", vec![
        i_store   (vI,   vI),
        i_add     (vI,   vI, RI_I(1)),
        i_cmp_lt  (rTMP, vI, RI_R(vNENT)),
        i_goto_ctf(rTMP, "set-loop", "sum-loop-pre")
    ]);

    // Loop pre-header for summing them
    cfg.block("sum-loop-pre", vec![
        i_imm(vSUM, 0),
        i_imm(vI,   0),
        i_goto("sum-loop")
    ]);

    // Summing loop
    cfg.block("sum-loop", vec![
        i_load  (rTMP,  vI),
        i_add   (vSUM,  vSUM, RI_R(rTMP)),
        i_add   (vI,    vI,   RI_I(1)),
        i_cmp_lt(vTMP2, vI,   RI_R(vNENT)),
        i_goto_ctf(vTMP2, "sum-loop", "print-result")
    ]);

    // After loop.  Print result and stop.
    cfg.block("print-result", vec![
        i_print_s("Sum = "),
        i_print_i(vSUM),
        i_print_s("\n"),
        i_finish()
    ]);

    cfg.finish();
    cfg
}
