
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
impl Show for Reg {
    fn show(&self) -> String {
        match self {
            Reg::RReg(rreg) => rreg.show(),
            Reg::VReg(vreg) => vreg.show()
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
     Suggested: u32, so that the subterm frag.#uses * frag.block.eef can 
       be calculated with a single 16 *u 16 -> 32 bit multiply.
     Also, u32::max (0xFFFF_FFFF) is reserved to mean "infinity"
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
    Block { name: name, start: start, len: len, eef: 0 }
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
        let mut bix = 0;
        for b in self.blocks.iter() {
            if bix > 0 {
                println!("");
            }
            println!("  {}:{}", bix, b.name);
            for i in b.start.get() .. b.start.get() + b.len {
                println!("      {:<2}    {}", i, self.insns[i as usize].show());
            }
            bix += 1;
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
// Representing and printing live ranges.  This is for both R and V regs.

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
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct Frag {
    bix:   BlockIx,
    kind:  FragKind,
    first: FragPoint,
    last:  FragPoint
}
impl Show for Frag {
    fn show(&self) -> String {
        self.kind.show() + &"-".to_string()
            + &self.first.show() + &"-" + &self.last.show()
    }
}
fn mk_Frag_Local(blocks: &Vec::<Block>, bix: BlockIx,
                 live_after: InsnIx, dead_after: InsnIx) -> Frag {
    let block = &blocks[bix.get_usize()];
    debug_assert!(block.containsInsnIx(live_after));
    debug_assert!(block.containsInsnIx(dead_after));
    debug_assert!(live_after <= dead_after);
    if live_after == dead_after {
        // A dead write, but we must represent it correctly.
        Frag { bix:   bix,
               kind:  FragKind::Local,
               first: FragPoint_D(live_after),
               last:  FragPoint_D(live_after) }
    } else {
        Frag { bix:   bix,
               kind:  FragKind::Local,
               first: FragPoint_D(live_after),
               last:  FragPoint_U(dead_after) }
    }
}
fn mk_Frag_LiveIn(blocks: &Vec::<Block>,
                  bix: BlockIx, dead_after: InsnIx) -> Frag {
    let block = &blocks[bix.get_usize()];
    debug_assert!(block.containsInsnIx(dead_after));
    Frag { bix:   bix,
           kind:  FragKind::LiveIn,
           first: FragPoint_U(block.start),
           last:  FragPoint_U(dead_after) }
}
fn mk_Frag_LiveOut(blocks: &Vec::<Block>,
                  bix: BlockIx, live_after: InsnIx) -> Frag {
    let block = &blocks[bix.get_usize()];
    debug_assert!(block.containsInsnIx(live_after));
    Frag { bix:   bix,
           kind:  FragKind::LiveOut,
           first: FragPoint_D(live_after),
           last:  FragPoint_D(block.start.plus(block.len - 1)) }
}
fn mk_Frag_Thru(blocks: &Vec::<Block>, bix: BlockIx) -> Frag {
    let block = &blocks[bix.get_usize()];
    Frag { bix:   bix,
           kind:  FragKind::Thru,
           first: FragPoint_U(block.start),
           last:  FragPoint_D(block.start.plus(block.len - 1)) }
}


// "Metricated Frags".  This a FragIx plus a u16 indicating how often the
// associated storage unit (Reg) is mentioned inside the Frag.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct MFrag {
    fix:   FragIx,
    count: u16
}
fn mkMFrag(fix: FragIx, count: u16) -> MFrag { MFrag { fix, count } }
impl Show for MFrag {
    fn show(&self) -> String {
        self.count.to_string() + &"x_".to_string()
            + &self.fix.show()
    }
}


// Indices into vectors of LRs (see below).
#[derive(Clone, Copy)]
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


// Finally, a live range.  This is the fundamental unit of allocation.  This
// pairs an Reg with a vector of MFrags in which it is live.
//
// I find it easier to think of a live range as a "renaming equivalence
// class".  That is, if you rename |reg| at some point inside |frags|, then
// you must rename *all* occurrences of |reg| inside |frags|, since otherwise
// the program will no longer work.
struct LR {
    reg:   Reg,
    frags: Vec::<MFrag>
}
impl Show for LR {
    fn show(&self) -> String {
        self.reg.show() + &" @ ".to_string() + &self.frags.show()
    }
}


//=============================================================================
// Computation of MFrags (Metricated Live Range Fragments)

// This is surprisingly complex, in part because of the need to correctly
// handle dead writes.

// MFrag_SME ("MFrag State Machine Entry") defines states for a state machine
// used to track states of Regs during MFrag construction.  Each state
// contains information for an MFrag that is currently under construction.
// There are really 3 states: NoInfo, Written and WrThenRd.  We don't
// represent NoInfo explicitly because most blocks don't reference most Regs,
// so in |get_MFrags_for_block|, it would be wasteful to have a mapping for
// all Regs most of which were just to NoInfo.  Instead, NoInfo is implied by
// a Reg not being mapped in |state|.

enum MFrag_SME {
    // So far we have seen no mention of the Reg, either in the block proper
    // or in livein.  This state is implied, per comments above, and not
    // represented.
    // NoInfo { .. },

    // Reg has been written.  Either prior to the block (iow, it is live-in),
    // if |wp| is None.  Or else |wp| is Some(live_after), to indicate the
    // defining insn.
    Written { uses: u16, wp: Option<InsnIx> },

    // Written, then read.  Meaning of |wp| is same as above.  |rp| is the
    // most recently observed read point, using the usual dead_after indexing.
    WrThenRd { uses: u16, wp: Option<InsnIx>, rp: InsnIx }
}


impl<'a> CFG<'a> {
    // Calculate all the MFrags for |bix|.  Add them to |outMap| and the new
    // Frags thaty they reference to outFrags.  |bix|, |livein| and |liveout|
    // are expected to be valid in the context of the CFG |self| (duh!)
    fn get_MFrags_for_block(&self, bix: BlockIx,
                            livein: &Set::<Reg>, liveout: &Set::<Reg>,
                            outMap: &mut HashMap::<Reg, Vec::<MFrag>>,
                            outFrags: &mut Vec::<Frag>)
    {
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
        let mut state = HashMap::<Reg, MFrag_SME>::new();

        // The generated MFrag components are initially are dumped in here.
        // We group them by Reg at the end of this function.
        let mut tmpResultVec = Vec::<(Reg, u16, Frag)>::new();

        // First, set up |state| as if all of |livein| had been written just
        // prior to the block.
        for r in livein.to_vec().iter() {
            state.insert(*r, MFrag_SME::Written { uses: 0, wp: None });
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
                let new_sme: MFrag_SME;
                match state.get(r) {
                    // First event for |r| is a read, but it's not listed
                    // in |livein|.
                    None => {
                        panic!("get_MFrags_for_block: fail #1");
                    },
                    // The first read after a write.  Note that the "write"
                    // can be either a real write, or due to the fact that |r|
                    // is listed in |livein|.  We don't care here.
                    Some(MFrag_SME::Written { uses, wp }) => {
                        new_sme = MFrag_SME::WrThenRd { uses: plus1(*uses),
                                                        wp: *wp, rp: iix };
                    },
                    // A subsequent read (== second or more read after a
                    // write).  Same comment as above re meaning of "write".
                    Some(MFrag_SME::WrThenRd { uses, wp, rp }) => {
                        debug_assert!(precedes(*wp, *rp));
                        debug_assert!(precedes(Some(*rp), iix));
                        new_sme = MFrag_SME::WrThenRd { uses: plus1(*uses),
                                                        wp: *wp, rp: iix };
                    }
                }
                state.insert(*r, new_sme);
            }

            // Examine writes.  The general idea is that a write causes us to
            // terminate the existing frag, if any, add it to |out|, and start
            // a new frag.  But we have to be careful to deal correctly with
            // dead writes.
            for r in regs_d.iter() {
                let new_sme: MFrag_SME;
                match state.get(r) {
                    // First mention of a Reg we've never heard of before.
                    // Note it and keep going.
                    None => {
                        new_sme = MFrag_SME::Written { uses: 1, wp: Some(iix) };
                    },
                    // |r| must be in |livein|, but the first event for it is
                    // a write.  That can't happen -- |livein| must be
                    // incorrect.
                    Some(MFrag_SME::Written { uses:_, wp: None }) => {
                        panic!("get_MFrags_for_block: fail #2");
                    },
                    // |r| has been written before in this block, but not
                    // subsequently read.  Hence the write is dead.  Emit a
                    // "point" frag, then note this new write instead.
                    Some(MFrag_SME::Written { uses, wp: Some(wp_iix) }) => {
                        debug_assert!(*uses == 1);
                        let frag = mk_Frag_Local(blocks, bix, *wp_iix, *wp_iix);
                        tmpResultVec.push((*r, 1, frag));
                        new_sme = MFrag_SME::Written { uses: 1, wp: Some(iix) };
                    },
                    // There's already a valid frag for |r|.  This write will
                    // start a new frag, so flush the existing one and note
                    // this write.
                    Some(MFrag_SME::WrThenRd { uses, wp, rp }) => {
                        let frag: Frag;
                        if let Some(wr_iix) = wp {
                            frag = mk_Frag_Local(blocks, bix, *wr_iix, *rp);
                        } else {
                            frag = mk_Frag_LiveIn(blocks, bix, *rp);
                        }
                        tmpResultVec.push((*r, *uses, frag));
                        new_sme = MFrag_SME::Written { uses: 1, wp: Some(iix) };
                    }
                }
                state.insert(*r, new_sme);
            }
        }

        // We are at the end of the block.  We still have to deal with
        // live-out Regs.  We must also deal with fragments in |state| that
        // are for registers not listed as live-out.

        // Deal with live-out regs.  Treat each one as if it is read just
        // after the block.
        for r in liveout.to_vec().iter() {
            match state.get(r) {
                // This can't happen.  It implies that |r| is in |liveout|,
                // but is neither defined in the block nor present in |livein|.
                None => {
                    panic!("get_MFrags_for_block: fail #3");
                },
                // |r| is "written", either literally or by virtue of being
                // present in |livein|, and may or may not subsequently be
                // read (we don't care).  Create a |LiveOut| or |Thru| frag
                // accordingly.
                Some(MFrag_SME::Written { uses, wp }) |
                Some(MFrag_SME::WrThenRd { uses, wp, rp:_ }) => {
                    let frag: Frag;
                    if let Some(wr_iix) = wp {
                        frag = mk_Frag_LiveOut(blocks, bix, *wr_iix);
                    } else {
                        frag = mk_Frag_Thru(blocks, bix);
                    }
                    tmpResultVec.push((*r, *uses, frag));
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
                MFrag_SME::Written { uses:_, wp: None } => {
                    panic!("get_MFrags_for_block: fail #4");
                },
                // This implies |r| has been written, but was never read,
                // either directly or by virtue of being in |liveout|.  So
                // just emit a "point" frag.
                MFrag_SME::Written { uses, wp: Some(wp_iix) } => {
                    debug_assert!(*uses == 1);
                    let frag = mk_Frag_Local(blocks, bix, *wp_iix, *wp_iix);
                    tmpResultVec.push((*r, 1, frag));
                },
                // This is a more normal case.  |r| is either in |livein| or
                // is first written inside the block, and later read, but is
                // not in |liveout|.
                MFrag_SME::WrThenRd { uses, wp, rp } => {
                    let frag: Frag;
                    if let Some(wr_iix) = wp {
                        frag = mk_Frag_Local(blocks, bix, *wr_iix, *rp);
                    } else {
                        frag = mk_Frag_LiveIn(blocks, bix, *rp);
                    }
                    tmpResultVec.push((*r, *uses, frag));
                }
            }
        }

        // Copy the entries in |tmpResultVec| into |outMap| and |outVec|.
        // TODO: do this as we go along, so as to avoid the use of a temporary
        // vector.
        for (r, uses, frag) in tmpResultVec {
            outFrags.push(frag);
            let new_fix = mkFragIx(outFrags.len() as u32 - 1);
            let new_mfrag = mkMFrag(new_fix, uses);
            match outMap.get_mut(&r) {
                None => { outMap.insert(r, vec![new_mfrag]); },
                Some(mfragVec) => { mfragVec.push(new_mfrag); }
            }
        }
    }

    fn get_MFrags(&self,
                  livein_sets_per_block:  &Vec::<Set<Reg>>,
                  liveout_sets_per_block: &Vec::<Set<Reg>>
                 ) -> (HashMap::<Reg, Vec<MFrag>>, Vec::<Frag>)
    {
        debug_assert!(livein_sets_per_block.len()  == self.blocks.len());
        debug_assert!(liveout_sets_per_block.len() == self.blocks.len());
        let mut resMap   = HashMap::<Reg, Vec<MFrag>>::new();
        let mut resFrags = Vec::<Frag>::new();
        for bix in 0 .. self.blocks.len() {
            self.get_MFrags_for_block(mkBlockIx(bix.try_into().unwrap()),
                                      &livein_sets_per_block[bix],
                                      &liveout_sets_per_block[bix],
                                      &mut resMap, &mut resFrags);
        }
        (resMap, resFrags)
    }
}


//=============================================================================
// Merging of MFrags, producing the final LRs

fn merge_MFrags(mfrag_vecs_per_reg: &HashMap::<Reg, Vec<MFrag>>,
                frag_table: &Vec::</*FragIx, */Frag>,
                cfg_map: &CFGMap) -> Vec::<LR>
{
    let mut res = Vec::<LR>::new();
    for (reg, all_mfrags_for_reg) in mfrag_vecs_per_reg.iter() {

        // BEGIN merge |all_mfrags_for_reg| entries as much as possible
        // |state| is a vector of four components:
        //    (1) An is-this-entry-still-valid flag
        //    (2) A vec of MFrags.  These I think should be disjoint.
        //    (3) A set of blocks, which are those corresponding to (2)
        //        that are LiveIn or Thru (== have an inbound value)
        //    (4) A set of blocks, which are the union of the successors of
        //        blocks corresponding to the (2) which are LiveOut or Thru
        //        (== have an outbound value)
        struct MergeGroup {
            valid: bool,
            mfrags: Vec::<MFrag>,
            live_in_blocks: Set::<BlockIx>,
            succs_of_live_out_blocks: Set::<BlockIx>
        }

        let mut state = Vec::<MergeGroup>::new();

        // Create the initial state by giving each MFrag its own Vec, and
        // tagging it with its interface blocks.
        for mfrag in all_mfrags_for_reg.iter() {
            let mut live_in_blocks = Set::<BlockIx>::empty();
            let mut succs_of_live_out_blocks = Set::<BlockIx>::empty();
            let frag = &frag_table[mfrag.fix.get_usize()];
            let mfrag_bix = frag.bix;
            let mfrag_succ_bixes = &cfg_map.succ_map[mfrag_bix.get_usize()];
            match frag.kind {
                FragKind::Local => {
                },
                FragKind::LiveIn => {
                    live_in_blocks.insert(mfrag_bix);
                },
                FragKind::LiveOut => {
                    succs_of_live_out_blocks.union(mfrag_succ_bixes);
                },
                FragKind::Thru => {
                    live_in_blocks.insert(mfrag_bix);
                    succs_of_live_out_blocks.union(mfrag_succ_bixes);
                }
            }

            let valid = true;
            let mfrags = vec![*mfrag];
            let mg = MergeGroup { valid, mfrags,
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
                    let do_merge = // block i feeds a value to block j
                        state[i].succs_of_live_out_blocks
                                .intersects(&state[j].live_in_blocks)
                        || // block j feeds a value to block i
                        state[j].succs_of_live_out_blocks
                                .intersects(&state[i].live_in_blocks);
                    if do_merge {
                        let mut tmp_mfrags = state[i].mfrags.clone();
                        state[j].mfrags.append(&mut tmp_mfrags);
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

        // Harvest the merged MFrag sets from |state|
        for MergeGroup { valid, mfrags, .. } in state {
            if valid {
                res.push(LR { reg: *reg, frags: mfrags.clone() });
            }
        }

        // END merge |all_mfrags_for_reg| entries as much as possible
    }

    res
}


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

The live ranges must contain a sequence of nonoverlapping MFrags, in
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

#[derive(PartialEq)]
enum FCR { LT, GT, EQ, UN }

fn cmpFrags(f1: &Frag, f2: &Frag) -> FCR {
    if f1.last < f2.first { return FCR::LT; }
    if f1.first > f2.last { return FCR::GT; }
    if f1.first == f2.first && f1.last == f2.last { return FCR::EQ; }
    FCR::UN
}

struct SortedMFragVec {
    vec: Vec::<MFrag>
}

impl SortedMFragVec {
    fn new(source: &Vec::<MFrag>, ctx: &Vec::<Frag>) -> Self {
        let res = SortedMFragVec { vec: source.clone() };
        // check the source is ordered, and clone (or sort it)
        res.check(ctx);
        res
    }

    fn getFrag<'a>(&self, ix: usize, ctx: &'a Vec::<Frag>) -> &'a Frag {
        &ctx[ self.vec[ix].fix.get_usize() ]
    }

    fn check(&self, ctx: &Vec::<Frag>) {
        let mut ok = true;
        for i in 1 .. self.vec.len() {
            let prev_frag = self.getFrag(i-1, ctx);
            let this_frag = self.getFrag(i-0, ctx);
            if cmpFrags(prev_frag, this_frag) != FCR::LT {
                ok = false;
                break;
            }
        }
        if !ok {
            panic!("SortedMFragVec::check: vector not ok");
        }
    }

    fn add(&mut self, to_add: &Self, ctx: &Vec::<Frag>) {
        self.check(ctx);
        to_add.check(ctx);
        let vx = &self.vec;
        let vy = &to_add.vec;
        let mut ix = 0;
        let mut iy = 0;
        let mut res = Vec::<MFrag>::new();
        while ix < vx.len() && iy < vy.len() {
            let fx = self.getFrag(ix, ctx);
            let fy = self.getFrag(iy, ctx);
            match cmpFrags(fx, fy) {
                FCR::LT => { res.push(vx[ix]); ix += 1; },
                FCR::GT => { res.push(vy[iy]); iy += 1; },
                FCR::EQ | FCR::UN
                    => panic!("SortedMFragVec::add: vectors intersect")
            }
        }
        // At this point, one or the other or both vectors are empty.  Hence
        // it doesn't matter in which order the following two while-loops
        // appear.
        debug_assert!(ix == vx.len() || iy == vy.len());
        while ix < vx.len() {
            res.push(vx[ix]);
            ix += 1;
        }
        while iy < vy.len() {
            res.push(vy[iy]);
            iy += 1;
        }
        self.vec = res;
        self.check(ctx);
    }

    fn can_add(&self, to_add: &Self, ctx: &Vec::<Frag>) -> bool {
        // This is merely a partial evaluation of add() which returns |false|
        // exactly in the cases where add() would have panic'd.
        self.check(ctx);
        to_add.check(ctx);
        let vx = &self.vec;
        let vy = &to_add.vec;
        let mut ix = 0;
        let mut iy = 0;
        while ix < vx.len() && iy < vy.len() {
            let fx = self.getFrag(ix, ctx);
            let fy = self.getFrag(iy, ctx);
            match cmpFrags(fx, fy) {
                FCR::LT => { ix += 1; },
                FCR::GT => { iy += 1; },
                FCR::EQ | FCR::UN => { return false; }
            }
        }
        // At this point, one or the other or both vectors are empty.  So
        // we're guaranteed to succeed.
        debug_assert!(ix == vx.len() || iy == vy.len());
        true
    }

    /*
    fn del(&mut self, other: &Self, ctx: &Vec::<Frag>) {
    }

    fn can_add_if_we_first_del(&mut self, to_add: &Self, to_del: &Self,
                               ctx: &Vec::<Frag>) -> bool {
    }
*/
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
    let rTMP  = Reg::RReg(mkRReg(2)); // "2" is arbitrary.
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


//=============================================================================
// Top level

//zzfn read_file(filename: &String) -> Vec<String> {
//zz    let f = fs::File::open(filename).expect("Can't open file");
//zz    let f = io::BufReader::new(f);
//zz    let mut v = vec![];
//zz    for line in f.lines() {
//zz        let line = line.expect("Unable to read line");
//zz        v.push(line);
//zz    }
//zz    v
//zz}

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

    cfg.print("Initial");

    cfg.run("Before allocation");

    let (def_sets_per_block, use_sets_per_block) = cfg.calc_def_and_use();
    debug_assert!(def_sets_per_block.len() == cfg.blocks.len());
    debug_assert!(use_sets_per_block.len() == cfg.blocks.len());

    let mut n = 0;
    println!("");
    for (def, uce) in def_sets_per_block.iter().zip(&use_sets_per_block) {
        println!("block {}:  def {:<16}  use {}", n, def.show(), uce.show());
        n += 1;
    }

    let cfg_map = CFGMap::create(&cfg);

    n = 0;
    println!("");
    for (preds, succs) in cfg_map.succ_map.iter().zip(&cfg_map.pred_map) {
        println!("block {}:  preds {:<16}  succs {}",
                 n, preds.show(), succs.show());
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
        println!("block {}:  livein {:<16}  liveout {:<16}",
                 n, livein.show(), liveout.show());
        n += 1;
    }

    println!("");
    let (mlrf_sets_per_reg, frag_table) =
        cfg.get_MFrags(&livein_sets_per_block, &liveout_sets_per_block);
    for (reg, mlrf) in mlrf_sets_per_reg.iter() {
        println!("mlrfs   for {}   {}", reg.show(), mlrf.show());
    }

    println!("");
    n = 0;
    for frag in &frag_table {
        println!("frag {}  {}", n, frag.show());
        n += 1;
    }

    println!("");
    let live_ranges = merge_MFrags(&mlrf_sets_per_reg, &frag_table, &cfg_map);
    n = 0;
    for lr in live_ranges {
        println!("live range {}  {}", n, lr.show());
        n += 1;
    }

    println!("");
}
