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

- Inst rewrite loop: don't clone mapD; just use it as soon as it's available.

- Inst rewrite loop: move cursors forwards at Point granularity so we don't
  have to repeatedly re-scan the groups looking for particular LR kinds?
*/

use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::env;
use std::fmt;
use std::hash::Hash;
use std::io::BufRead;
use std::ops::Index;
use std::ops::IndexMut;
use std::ops::Range;
use std::slice::{Iter, IterMut};
use std::{fs, io};

use minira::interface::{
  BlockIx, InstIx, RealReg, RealRegUniverse, Reg, SpillSlot, TypedIxVec,
  VirtualReg,
};
use minira::tests;
use minira::tests::{make_universe, BinOp, Block, Func, Inst, Label, AM, RI};
use minira::{backtracking, linear_scan};

use log::{self, error, info, warn};
use pretty_env_logger;

//=============================================================================
// The interpreter

#[derive(Copy, Clone)]
enum Value {
  U32(u32),
  F32(f32),
}
fn mkU32(n: u32) -> Value {
  Value::U32(n)
}
fn mkF32(n: f32) -> Value {
  Value::F32(n)
}
impl Value {
  fn toU32(self) -> u32 {
    match self {
      Value::U32(n) => n,
      Value::F32(_) => panic!("Value::toU32: this is a F32"),
    }
  }
  fn toF32(self) -> f32 {
    match self {
      Value::U32(_) => panic!("Value::toF32: this is a U32"),
      Value::F32(n) => n,
    }
  }
}
impl fmt::Debug for Value {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Value::U32(n) => write!(fmt, "{}", n),
      Value::F32(n) => write!(fmt, "{}", n),
    }
  }
}

#[derive(PartialEq)]
enum RunStage {
  BeforeRegalloc,
  AfterRegalloc,
}

struct IState<'a> {
  func: &'a Func,
  nia: InstIx, // Program counter ("next instruction address")
  vregs: Vec<Option<Value>>, // unlimited
  rregs: Vec<Option<Value>>, // [0 .. maxRealRegs)
  mem: Vec<Option<Value>>, // [0 .. maxMem)
  slots: Vec<Option<Value>>, // [0..] Spill slots, no upper limit
  n_insns: usize, // Stats: number of insns executed
  n_spills: usize, // Stats: .. of which are spills
  n_reloads: usize, // Stats: .. of which are reloads
  run_stage: RunStage,
}

impl<'a> IState<'a> {
  fn new(
    func: &'a Func, maxRealRegs: usize, maxMem: usize, run_stage: RunStage,
  ) -> Self {
    let mut state = IState {
      func,
      nia: func.blocks[func.entry.getBlockIx()].start,
      vregs: Vec::new(),
      rregs: Vec::new(),
      mem: Vec::new(),
      slots: Vec::new(),
      n_insns: 0,
      n_spills: 0,
      n_reloads: 0,
      run_stage,
    };
    state.rregs.resize(maxRealRegs, None);
    state.mem.resize(maxMem, None);
    state
  }

  fn get_real_reg(&self, rreg: RealReg) -> Value {
    // No automatic resizing.  If the rreg doesn't exist, just fail.
    match self.rregs.get(rreg.get_index()) {
      None => panic!("IState::get_real_reg: invalid rreg {:?}", rreg),
      Some(None) => panic!(
        "IState::get_real_reg: read of uninit rreg {:?} at nia {:?}",
        rreg, self.nia
      ),
      Some(Some(val)) => *val,
    }
  }

  fn setRealReg(&mut self, rreg: RealReg, val: Value) {
    // No automatic resizing.  If the rreg doesn't exist, just fail.
    match self.rregs.get_mut(rreg.get_index()) {
      None => panic!("IState::setRealReg: invalid rreg {:?}", rreg),
      Some(valP) => *valP = Some(val),
    }
  }

  fn get_virtual_reg(&self, vreg: VirtualReg) -> Value {
    debug_assert!(
      self.run_stage != RunStage::AfterRegalloc,
      "trying to get a vreg after regalloc"
    );
    // The vector might be too small.  But in that case we'd be
    // reading the vreg uninitialised anyway, so just complain.
    match self.vregs.get(vreg.get_index()) {
            None |          // indexing error
            Some(None) =>   // entry present, but has never been written
                panic!("IState::get_virtual_reg: read of uninit vreg {:?}",
                       vreg),
            Some(Some(val))
                => *val
        }
  }

  fn setVirtualReg(&mut self, vreg: VirtualReg, val: Value) {
    debug_assert!(
      self.run_stage != RunStage::AfterRegalloc,
      "trying to set a vreg after regalloc"
    );
    // Auto-resize the vector if necessary
    let ix = vreg.get_index();
    if ix >= self.vregs.len() {
      self.vregs.resize(ix + 1, None);
    }
    debug_assert!(ix < self.vregs.len());
    self.vregs[ix] = Some(val);
  }

  fn getSpillSlot(&self, slot: SpillSlot) -> Value {
    // The vector might be too small.  But in that case we'd be
    // reading the slot uninitialised anyway, so just complain.
    match self.slots.get(slot.get_usize()) {
            None |          // indexing error
            Some(None) =>   // entry present, but has never been written
                panic!("IState::getSpillSlot: read of uninit slot # {}",
                       slot.get()),
            Some(Some(val))
                => *val
        }
  }

  fn setSpillSlotU32(&mut self, slot: SpillSlot, val: u32) {
    // Auto-resize the vector if necessary
    let ix = slot.get_usize();
    if ix >= self.slots.len() {
      self.slots.resize(ix + 1, None);
    }
    debug_assert!(ix < self.slots.len());
    self.slots[ix] = Some(mkU32(val));
  }

  fn setSpillSlotF32(&mut self, slot: SpillSlot, val: f32) {
    // Auto-resize the vector if necessary
    let ix = slot.get_usize();
    if ix >= self.slots.len() {
      self.slots.resize(ix + 1, None);
    }
    debug_assert!(ix < self.slots.len());
    self.slots[ix] = Some(mkF32(val));
  }

  fn get_reg(&self, reg: Reg) -> Value {
    if reg.is_virtual() {
      self.get_virtual_reg(reg.to_virtual_reg())
    } else {
      self.get_real_reg(reg.to_real_reg())
    }
  }

  fn set_reg_u32(&mut self, reg: Reg, val: u32) {
    if reg.is_virtual() {
      self.setVirtualReg(reg.to_virtual_reg(), mkU32(val));
    } else {
      self.setRealReg(reg.to_real_reg(), mkU32(val));
    }
  }

  fn set_reg_f32(&mut self, reg: Reg, val: f32) {
    if reg.is_virtual() {
      self.setVirtualReg(reg.to_virtual_reg(), mkF32(val));
    } else {
      self.setRealReg(reg.to_real_reg(), mkF32(val));
    }
  }

  fn getMem(&self, addr: u32) -> Value {
    // No auto resizing of the memory
    match self.mem.get(addr as usize) {
      None => panic!("IState::getMem: invalid addr {}", addr),
      Some(None) => {
        panic!("IState::getMem: read of uninit mem at addr {}", addr)
      }
      Some(Some(val)) => *val,
    }
  }

  fn setMemU32(&mut self, addr: u32, val: u32) {
    // No auto resizing of the memory
    match self.mem.get_mut(addr as usize) {
      None => panic!("IState::setMemU32: invalid addr {}", addr),
      Some(valP) => *valP = Some(mkU32(val)),
    }
  }

  fn setMemF32(&mut self, addr: u32, val: f32) {
    // No auto resizing of the memory
    match self.mem.get_mut(addr as usize) {
      None => panic!("IState::setMemF32: invalid addr {}", addr),
      Some(valP) => *valP = Some(mkF32(val)),
    }
  }

  fn getRI(&self, ri: &RI) -> u32 {
    match ri {
      RI::Reg { reg } => self.get_reg(*reg).toU32(),
      RI::Imm { imm } => *imm,
    }
  }

  fn getAM(&self, am: &AM) -> u32 {
    match am {
      AM::RI { base, offset } => self.get_reg(*base).toU32() + offset,
      AM::RR { base, offset } => {
        self.get_reg(*base).toU32() + self.get_reg(*offset).toU32()
      }
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
      Inst::Imm { dst, imm } => self.set_reg_u32(*dst, *imm),
      Inst::Copy { dst, src } => {
        self.set_reg_u32(*dst, self.get_reg(*src).toU32())
      }
      Inst::BinOp { op, dst, srcL, srcR } => {
        let srcL_v = self.get_reg(*srcL).toU32();
        let srcR_v = self.getRI(srcR);
        let dst_v = op.calc(srcL_v, srcR_v);
        self.set_reg_u32(*dst, dst_v);
      }
      Inst::BinOpM { op, dst, srcR } => {
        let mut dst_v = self.get_reg(*dst).toU32();
        let srcR_v = self.getRI(srcR);
        dst_v = op.calc(dst_v, srcR_v);
        self.set_reg_u32(*dst, dst_v);
      }
      Inst::Load { dst, addr } => {
        let addr_v = self.getAM(addr);
        let dst_v = self.getMem(addr_v).toU32();
        self.set_reg_u32(*dst, dst_v);
      }
      Inst::Store { addr, src } => {
        let addr_v = self.getAM(addr);
        let src_v = self.get_reg(*src).toU32();
        self.setMemU32(addr_v, src_v);
      }
      Inst::Spill { dst, src } => {
        let src_v = self.get_real_reg(*src).toU32();
        self.setSpillSlotU32(*dst, src_v);
        self.n_spills += 1;
      }
      Inst::Reload { dst, src } => {
        let src_v = self.getSpillSlot(*src).toU32();
        self.set_reg_u32(dst.to_reg(), src_v);
        self.n_reloads += 1;
      }
      Inst::Goto { target } => {
        self.nia = self.func.blocks[target.getBlockIx()].start
      }
      Inst::GotoCTF { cond, targetT, targetF } => {
        let target =
          if self.get_reg(*cond).toU32() != 0 { targetT } else { targetF };
        self.nia = self.func.blocks[target.getBlockIx()].start;
      }
      Inst::PrintS { str } => print!("{}", str),
      Inst::PrintI { reg } => print!("{:?}", self.get_reg(*reg).toU32()),
      Inst::Finish {} => done = true,
      _ => {
        println!("Interp: unhandled: {:?}", insn);
        panic!("IState::step: unhandled insn");
      }
    }
    done
  }
}

fn run_func(
  f: &Func, who: &str, reg_universe: &RealRegUniverse, run_stage: RunStage,
) {
  println!("");
  println!(
    "Running stage '{}': Func: name='{}' entry='{:?}'",
    who, f.name, f.entry
  );

  let mut istate =
    IState::new(f, reg_universe.regs.len(), /*maxMem=*/ 1000, run_stage);
  let mut done = false;
  while !done {
    done = istate.step();
  }

  println!(
    "Running stage '{}': done.  {} insns, {} spills, {} reloads",
    who, istate.n_insns, istate.n_spills, istate.n_reloads
  );
}

//=============================================================================
// Top level

enum RegAllocAlgorithm {
  Backtracking,
  LinearScan,
}

fn usage(argv0: &String) {
  println!(
    "usage: {} <name_of_algorithm> <name_of_Func> \
     <num_regs::I32> <num_regs::F32>",
    argv0
  );
  println!("usage: available algorithms:  bt  lsra");
  println!("usage: to get a list of available Funcs to try, run with args:");
  println!("usage:    bt bogus 0 0");
}

fn main() {
  pretty_env_logger::init();

  let args: Vec<String> = env::args().collect();
  if args.len() != 5 {
    usage(&args[0]);
    return;
  }

  let mut func = match crate::tests::find_Func(&args[2]) {
    Ok(func) => func,
    Err(available_func_names) => {
      error!("can't find Func with name '{}'", args[2]);
      println!("{}: available Func names are:", args[0]);
      for name in available_func_names {
        println!("{}:     {}", args[0], name);
      }
      return;
    }
  };

  let (nRegsI32, nRegsF32) =
    match (args[3].parse::<usize>(), args[4].parse::<usize>()) {
      (Ok(nI32), Ok(nF32)) => (nI32, nF32),
      _other => {
        usage(&args[0]);
        return;
      }
    };

  let reg_alloc_kind = match args[1].as_str() {
    "bt" => RegAllocAlgorithm::Backtracking,
    "lsra" => RegAllocAlgorithm::LinearScan,
    _ => {
      usage(&args[0]);
      return;
    }
  };

  let reg_universe = make_universe(nRegsI32, nRegsF32);

  func.print("before allocation");

  // Just so we can run it later.  Not needed for actual allocation.
  let original_func = func.clone();

  match reg_alloc_kind {
    RegAllocAlgorithm::Backtracking => {
      info!("Using the backtracking allocator");
      let result = match backtracking::alloc_main(&mut func, &reg_universe) {
        Err(e) => {
          error!("{}: allocation failed: {}", args[0], e);
          return;
        }
        Ok(r) => r,
      };
      // Update the function itself. This bridges the gap from the generic
      // interface to our specific test ISA.
      func.update_from_alloc(result);
    }
    RegAllocAlgorithm::LinearScan => {
      info!("Using the linear scan allocator.");
      match linear_scan::alloc_main(&mut func, &reg_universe) {
        Err(e) => {
          error!("{}: allocation failed: {}", args[0], e);
          return;
        }
        Ok(_) => {}
      }
    }
  }

  func.print("after allocation");

  run_func(
    &original_func,
    "Before allocation",
    &reg_universe,
    RunStage::BeforeRegalloc,
  );
  run_func(&func, "After allocation", &reg_universe, RunStage::AfterRegalloc);

  println!("");
}

mod test_utils {
  use super::*;

  pub fn bt(func_name: &str, num_gpr: usize, num_fpu: usize) {
    let mut func = tests::find_Func(func_name).unwrap();
    let reg_universe = make_universe(num_gpr, num_fpu);
    let result = backtracking::alloc_main(&mut func, &reg_universe)
      .unwrap_or_else(|err| {
        panic!("allocation failed: {}", err);
      });
    func.update_from_alloc(result);
    run_func(&func, "After allocation", &reg_universe, RunStage::AfterRegalloc);
  }
}

#[test]
fn bt_badness() {
  test_utils::bt("badness", 1, 0);
}

#[test]
fn bt_straight_line() {
  test_utils::bt("straight_line", 1, 0);
}

#[test]
fn bt_fill_then_sum() {
  test_utils::bt("fill_then_sum", 8, 8);
}

#[test]
fn bt_ssort() {
  test_utils::bt("ssort", 8, 8);
}

#[test]
fn bt_3_loops() {
  test_utils::bt("3_loops", 8, 8);
}

#[test]
fn bt_stmts() {
  test_utils::bt("stmts", 8, 8);
}

#[test]
fn bt_needs_splitting() {
  test_utils::bt("needs_splitting", 8, 8);
}

#[test]
fn bt_needs_splitting2() {
  test_utils::bt("needs_splitting2", 8, 8);
}

#[test]
fn bt_qsort() {
  test_utils::bt("qsort", 8, 8);
}

#[test]
fn bt_fill_then_sum_2a() {
  test_utils::bt("fill_then_sum_2a", 8, 8);
}

#[test]
fn bt_ssort_2a() {
  test_utils::bt("ssort_2a", 8, 8);
}
