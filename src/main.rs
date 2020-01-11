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

mod analysis;
mod backtracking;
mod data_structures;
mod linear_scan;
mod tests;

use std::{fs, io};
use std::io::BufRead;
use std::env;
use std::collections::VecDeque;
use std::hash::Hash;
use std::convert::TryInto;
use std::cmp::Ordering;
use std::ops::Index;
use std::ops::IndexMut;
use std::ops::Range;
use std::slice::{Iter, IterMut};
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;

use data_structures::{
    RRegUniverse, make_universe,
    InsnIx, VReg, RReg, Block, Func, Label, Show, BlockIx, AM,
    Insn, Reg, Slot, RI, BinOp
};


//=============================================================================
// The interpreter

#[derive(Copy, Clone)]
enum Value {
    U32(u32),
    F32(f32)
}
fn mkU32(n: u32) -> Value { Value::U32(n) }
fn mkF32(n: f32) -> Value { Value::F32(n) }
impl Value {
    fn toU32(self) -> u32 {
        match self {
            Value::U32(n) => n,
            Value::F32(_) => panic!("Value::toU32: this is a F32")
        }
    }
    fn toF32(self) -> f32 {
        match self {
            Value::U32(_) => panic!("Value::toF32: this is a U32"),
            Value::F32(n) => n
        }
    }
}
impl Show for Value {
    fn show(&self) -> String {
        match self {
            Value::U32(n) => n.show(),
            Value::F32(n) => n.show()
        }
    }
}


struct IState<'a> {
    func:      &'a Func,
    nia:       InsnIx, // Program counter ("next instruction address")
    vregs:     Vec::<Option::<Value>>, // unlimited
    rregs:     Vec::<Option::<Value>>, // [0 .. maxRRegs)
    mem:       Vec::<Option::<Value>>, // [0 .. maxMem)
    slots:     Vec::<Option::<Value>>, // [0..] Spill slots, no upper limit
    n_insns:   usize,  // Stats: number of insns executed
    n_spills:  usize,  // Stats: .. of which are spills
    n_reloads: usize   // Stats: .. of which are reloads
}

impl<'a> IState<'a> {
    fn new(func: &'a Func, maxRRegs: usize, maxMem: usize) -> Self {
        let mut state =
            IState {
                func:      func,
                nia:       func.blocks[func.entry.getBlockIx()].start,
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

    fn getRReg(&self, rreg: RReg) -> Value {
        // No automatic resizing.  If the rreg doesn't exist, just fail.
        match self.rregs.get(rreg.getIndex()) {
            None =>
                panic!("IState::getRReg: invalid rreg {}", rreg.show()),
            Some(None) =>
                panic!("IState::getRReg: read of uninit rreg {}", rreg.show()),
            Some(Some(val))
                => *val
        }
    }

    fn setRReg(&mut self, rreg: RReg, val: Value) {
        // No automatic resizing.  If the rreg doesn't exist, just fail.
        match self.rregs.get_mut(rreg.getIndex()) {
            None =>
                panic!("IState::setRReg: invalid rreg {}", rreg.show()),
            Some(valP)
                => *valP = Some(val)
        }
    }

    fn getVReg(&self, vreg: VReg) -> Value {
        // The vector might be too small.  But in that case we'd be
        // reading the vreg uninitialised anyway, so just complain.
        match self.vregs.get(vreg.getIndex()) {
            None |          // indexing error
            Some(None) =>   // entry present, but has never been written
                panic!("IState::getVReg: read of uninit vreg {}", vreg.show()),
            Some(Some(val))
                => *val
        }
    }

    fn setVReg(&mut self, vreg: VReg, val: Value) {
        // Auto-resize the vector if necessary
        let ix = vreg.getIndex();
        if ix >= self.vregs.len() {
            self.vregs.resize(ix + 1, None);
        }
        debug_assert!(ix < self.vregs.len());
        self.vregs[ix] = Some(val);
    }

    fn getSlot(&self, slot: Slot) -> Value {
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

    fn setSlotU32(&mut self, slot: Slot, val: u32) {
        // Auto-resize the vector if necessary
        let ix = slot.get_usize();
        if ix >= self.slots.len() {
            self.slots.resize(ix + 1, None);
        }
        debug_assert!(ix < self.slots.len());
        self.slots[ix] = Some(mkU32(val));
    }

    fn setSlotF32(&mut self, slot: Slot, val: f32) {
        // Auto-resize the vector if necessary
        let ix = slot.get_usize();
        if ix >= self.slots.len() {
            self.slots.resize(ix + 1, None);
        }
        debug_assert!(ix < self.slots.len());
        self.slots[ix] = Some(mkF32(val));
    }

    fn getReg(&self, reg: Reg) -> Value {
        if reg.isVirtual() {
            self.getVReg(reg.toVReg())
        } else {
            self.getRReg(reg.toRReg())
        }
    }

    fn setRegU32(&mut self, reg: Reg, val: u32) {
        if reg.isVirtual() {
            self.setVReg(reg.toVReg(), mkU32(val));
        } else {
            self.setRReg(reg.toRReg(), mkU32(val));
        }
    }

    fn setRegF32(&mut self, reg: Reg, val: f32) {
        if reg.isVirtual() {
            self.setVReg(reg.toVReg(), mkF32(val));
        } else {
            self.setRReg(reg.toRReg(), mkF32(val));
        }
    }

    fn getMem(&self, addr: u32) -> Value {
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

    fn setMemU32(&mut self, addr: u32, val: u32) {
        // No auto resizing of the memory
        match self.mem.get_mut(addr as usize) {
            None =>
                panic!("IState::setMemU32: invalid addr {}", addr),
            Some(valP)
                => *valP = Some(mkU32(val))
        }
    }

    fn setMemF32(&mut self, addr: u32, val: f32) {
        // No auto resizing of the memory
        match self.mem.get_mut(addr as usize) {
            None =>
                panic!("IState::setMemF32: invalid addr {}", addr),
            Some(valP)
                => *valP = Some(mkF32(val))
        }
    }

    fn getRI(&self, ri: &RI) -> u32 {
        match ri {
            RI::Reg { reg } => self.getReg(*reg).toU32(),
            RI::Imm { imm } => *imm
        }
    }

    fn getAM(&self, am: &AM) -> u32 {
        match am {
            AM::RI { base, offset } => self.getReg(*base).toU32() + offset,
            AM::RR { base, offset } => self.getReg(*base).toU32()
                                       + self.getReg(*offset).toU32()
        }
    }

    // Move the interpreter one step forward
    fn step(&mut self) -> bool {
        let mut done = false;

        let iix = self.nia;
        self.nia = iix.plus(1);
        self.n_insns += 1;

        let insn = &self.func.insns[iix];
        match insn {
            Insn::Imm { dst, imm } =>
                self.setRegU32(*dst, *imm),
            Insn::Copy { dst, src } =>
                self.setRegU32(*dst, self.getReg(*src).toU32()),
            Insn::BinOp { op, dst, srcL, srcR } => {
                let srcL_v = self.getReg(*srcL).toU32();
                let srcR_v = self.getRI(srcR);
                let dst_v = op.calc(srcL_v, srcR_v);
                self.setRegU32(*dst, dst_v);
            },
            Insn::BinOpM { op, dst, srcR } => {
                let mut dst_v = self.getReg(*dst).toU32();
                let srcR_v = self.getRI(srcR);
                dst_v = op.calc(dst_v, srcR_v);
                self.setRegU32(*dst, dst_v);
            },
            Insn::Load { dst, addr } => {
                let addr_v = self.getAM(addr);
                let dst_v = self.getMem(addr_v).toU32();
                self.setRegU32(*dst, dst_v);
            },
            Insn::Store { addr, src } => {
                let addr_v = self.getAM(addr);
                let src_v  = self.getReg(*src).toU32();
                self.setMemU32(addr_v, src_v);
            },
            Insn::Spill { dst, src } => {
                let src_v = self.getRReg(*src).toU32();
                self.setSlotU32(*dst, src_v);
                self.n_spills += 1;
            },
            Insn::Reload { dst, src } => {
                let src_v = self.getSlot(*src).toU32();
                self.setRegU32(dst.toReg(), src_v);
                self.n_reloads += 1;
            },
            Insn::Goto { target } =>
                self.nia = self.func.blocks[target.getBlockIx()].start,
            Insn::GotoCTF { cond, targetT, targetF } => {
                let target = if self.getReg(*cond).toU32() != 0 { targetT }
                                                           else { targetF };
                self.nia = self.func.blocks[target.getBlockIx()].start;
            },
            Insn::PrintS { str } =>
                print!("{}", str),
            Insn::PrintI { reg } =>
                print!("{}", self.getReg(*reg).toU32().show()),
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
    fn run(&self, who: &str, reg_universe: &RRegUniverse) {
        println!("");
        println!("Running stage '{}': Func: name='{}' entry='{}'",
                 who, self.name, self.entry.show());

        let mut istate = IState::new(&self, reg_universe.regs.len(),
                                     /*maxMem=*/1000);
        let mut done = false;
        while !done {
            done = istate.step();
        }

        println!("Running stage '{}': done.  {} insns, {} spills, {} reloads",
                 who, istate.n_insns, istate.n_spills, istate.n_reloads);
    }
}


//=============================================================================
// Top level

enum RAAlgorithm {
    Backtracking,
    LinearScan,
}

fn usage(argv0: &String) {
    println!(
        "usage: {} <name_of_algorithm> <name_of_Func> <num_regs::I32> <num_regs::F32>",
        argv0);
    println!("usage: available algorithms:  bt  lsra");
    println!("usage: to get a list of available Funcs to try, run with args:");
    println!("usage:    bt bogus 0 0");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 5 {
        usage(&args[0]);
        return;
    }

    let mut func = match crate::tests::find_Func(&args[2]) {
        Ok(func) => func,
        Err(available_func_names) => {
            println!("{}: can't find Func with name '{}'", args[0], args[2]);
            println!("{}: available Func names are:", args[0]);
            for name in available_func_names {
                println!("{}:     {}", args[0], name);
            }
            return;
        }
    };

    let (nRegsI32, nRegsF32)
        = match (args[3].parse::<usize>(), args[4].parse::<usize>()) {
            (Ok(nI32), Ok(nF32))
                => (nI32, nF32),
            _other => {
                usage(&args[0]);
                return;
            }
        };

    let reg_alloc_kind =
        match args[1].as_str() {
            "bt" => {
                RAAlgorithm::Backtracking
            },
            "lsra" => {
                RAAlgorithm::LinearScan
            },
            _ => {
                usage(&args[0]);
                return;
            }
        };

    let reg_universe = make_universe(nRegsI32, nRegsF32);

    func.print("Initial");

    func.run("Before allocation", &reg_universe);

    // Just so we can run it later.  Not needed for actual allocation.
    let original_func = func.clone();

    let alloc_res = match reg_alloc_kind {
        RAAlgorithm::Backtracking => {
            println!("Using the backtracking allocator");
            crate::backtracking::alloc_main(&mut func, &reg_universe)
        }
        RAAlgorithm::LinearScan => {
            println!("Using the linear scan allocator.");
            crate::linear_scan::alloc_main(&mut func, &reg_universe)
        }
    };

    match alloc_res {
        Err(s) => {
            println!("{}: allocation failed: {}", args[0], s);
            return;
        }
        Ok(_) => { }
    }

    func.print("After allocation");

    original_func.run("Before allocation", &reg_universe);
    func.run("After allocation", &reg_universe);

    println!("");
}
