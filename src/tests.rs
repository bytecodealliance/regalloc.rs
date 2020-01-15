/// Test cases.  The list of them is right at the bottom, function |find_Func|.
/// Add new ones there.
///
/// As part of this set of test cases, we define a mini IR and implement the `Function` trait for
/// it so that we can use the regalloc public interface.
use crate::interface;
use crate::interface::{
  mkBlockIx, mkInstIx, mkRealReg, mkSpillSlot, mkVirtualReg, BlockIx, InstIx,
  Map, MyRange, RealReg, RealRegUniverse, Reg, RegClass, Set, SpillSlot,
  TypedIxVec, VirtualReg, NUM_REG_CLASSES,
};

use std::fmt;

//=============================================================================
// Definition of instructions, and printing thereof.  Destinations are on the
// left.

#[derive(Clone)]
pub enum Label {
  Unresolved { name: String },
  Resolved { name: String, bix: BlockIx },
}
impl fmt::Debug for Label {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Label::Unresolved { name } => write!(fmt, "??:{}", &name),
      Label::Resolved { name, bix } => write!(fmt, "{:?}:{:?}", bix, name),
    }
  }
}
impl Label {
  pub fn getBlockIx(&self) -> BlockIx {
    match self {
      Label::Resolved { name: _, bix } => *bix,
      Label::Unresolved { .. } => {
        panic!("Label::getBlockIx: unresolved label!")
      }
    }
  }

  pub fn remapControlFlow(&mut self, from: &String, to: &String) {
    match self {
      Label::Resolved { .. } => {
        panic!("Label::remapControlFlow on resolved label");
      }
      Label::Unresolved { name } => {
        if name == from {
          *name = to.clone();
        }
      }
    }
  }
}
pub fn mkTextLabel(n: usize) -> String {
  "L".to_string() + &n.to_string()
}
fn mkUnresolved(name: String) -> Label {
  Label::Unresolved { name }
}

#[derive(Copy, Clone)]
pub enum RI {
  Reg { reg: Reg },
  Imm { imm: u32 },
}
pub fn RI_R(reg: Reg) -> RI {
  debug_assert!(reg.get_class() == RegClass::I32);
  RI::Reg { reg }
}
pub fn RI_I(imm: u32) -> RI {
  RI::Imm { imm }
}
impl fmt::Debug for RI {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      RI::Reg { reg } => reg.fmt(fmt),
      RI::Imm { imm } => write!(fmt, "{}", imm),
    }
  }
}
impl RI {
  fn addRegReadsTo(&self, uce: &mut Set<Reg>) {
    match self {
      RI::Reg { reg } => uce.insert(*reg),
      RI::Imm { .. } => {}
    }
  }
  fn apply_D_or_U(&mut self, map: &Map<VirtualReg, RealReg>) {
    match self {
      RI::Reg { ref mut reg } => {
        reg.apply_D_or_U(map);
      }
      RI::Imm { .. } => {}
    }
  }
}

#[derive(Copy, Clone)]
pub enum AM {
  RI { base: Reg, offset: u32 },
  RR { base: Reg, offset: Reg },
}
pub fn AM_R(base: Reg) -> AM {
  debug_assert!(base.get_class() == RegClass::I32);
  AM::RI { base, offset: 0 }
}
pub fn AM_RI(base: Reg, offset: u32) -> AM {
  debug_assert!(base.get_class() == RegClass::I32);
  AM::RI { base, offset }
}
pub fn AM_RR(base: Reg, offset: Reg) -> AM {
  debug_assert!(base.get_class() == RegClass::I32);
  debug_assert!(offset.get_class() == RegClass::I32);
  AM::RR { base, offset }
}
impl fmt::Debug for AM {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      AM::RI { base, offset } => write!(fmt, "[{:?} {:?}]", base, offset),
      AM::RR { base, offset } => write!(fmt, "[{:?} {:?}]", base, offset),
    }
  }
}
impl AM {
  fn addRegReadsTo(&self, uce: &mut Set<Reg>) {
    match self {
      AM::RI { base, .. } => uce.insert(*base),
      AM::RR { base, offset } => {
        uce.insert(*base);
        uce.insert(*offset);
      }
    }
  }
  fn apply_D_or_U(&mut self, map: &Map<VirtualReg, RealReg>) {
    match self {
      AM::RI { ref mut base, .. } => {
        base.apply_D_or_U(map);
      }
      AM::RR { ref mut base, ref mut offset } => {
        base.apply_D_or_U(map);
        offset.apply_D_or_U(map);
      }
    }
  }
}

#[derive(Copy, Clone)]
pub enum BinOp {
  Add,
  Sub,
  Mul,
  Mod,
  Shr,
  And,
  CmpEQ,
  CmpLT,
  CmpLE,
  CmpGE,
  CmpGT,
}
impl fmt::Debug for BinOp {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt,
      "{}",
      match self {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Mod => "mod",
        BinOp::Shr => "shr",
        BinOp::And => "and",
        BinOp::CmpEQ => "cmpeq",
        BinOp::CmpLT => "cmplt",
        BinOp::CmpLE => "cmple",
        BinOp::CmpGE => "cmpge",
        BinOp::CmpGT => "cmpgt",
      }
    )
  }
}
impl fmt::Display for BinOp {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    (self as &dyn fmt::Debug).fmt(fmt)
  }
}
impl BinOp {
  pub fn calc(self, argL: u32, argR: u32) -> u32 {
    match self {
      BinOp::Add => u32::wrapping_add(argL, argR),
      BinOp::Sub => u32::wrapping_sub(argL, argR),
      BinOp::Mul => u32::wrapping_mul(argL, argR),
      BinOp::Mod => argL % argR,
      BinOp::Shr => argL >> (argR & 31),
      BinOp::And => argL & argR,
      BinOp::CmpEQ => {
        if argL == argR {
          1
        } else {
          0
        }
      }
      BinOp::CmpLT => {
        if argL < argR {
          1
        } else {
          0
        }
      }
      BinOp::CmpLE => {
        if argL <= argR {
          1
        } else {
          0
        }
      }
      BinOp::CmpGE => {
        if argL >= argR {
          1
        } else {
          0
        }
      }
      BinOp::CmpGT => {
        if argL > argR {
          1
        } else {
          0
        }
      }
    }
  }
}

#[derive(Copy, Clone)]
pub enum BinOpF {
  FAdd,
  FSub,
  FMul,
  FDiv,
}
impl fmt::Debug for BinOpF {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt,
      "{}",
      match self {
        BinOpF::FAdd => "fadd".to_string(),
        BinOpF::FSub => "fsub".to_string(),
        BinOpF::FMul => "fmul".to_string(),
        BinOpF::FDiv => "fdiv".to_string(),
      }
    )
  }
}
impl fmt::Display for BinOpF {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    (self as &dyn fmt::Debug).fmt(fmt)
  }
}
impl BinOpF {
  fn calc(self, argL: f32, argR: f32) -> f32 {
    match self {
      BinOpF::FAdd => argL + argR,
      BinOpF::FSub => argL - argR,
      BinOpF::FMul => argL * argR,
      BinOpF::FDiv => argL / argR,
    }
  }
}

#[derive(Clone)]
pub enum Inst {
  Imm { dst: Reg, imm: u32 },
  ImmF { dst: Reg, imm: f32 },
  Copy { dst: Reg, src: Reg },
  BinOp { op: BinOp, dst: Reg, srcL: Reg, srcR: RI },
  BinOpM { op: BinOp, dst: Reg, srcR: RI }, // "mod" semantics for |dst|
  BinOpF { op: BinOpF, dst: Reg, srcL: Reg, srcR: Reg },
  Load { dst: Reg, addr: AM },
  LoadF { dst: Reg, addr: AM },
  Store { addr: AM, src: Reg },
  StoreF { addr: AM, src: Reg },
  Spill { dst: SpillSlot, src: RealReg },
  SpillF { dst: SpillSlot, src: RealReg },
  Reload { dst: RealReg, src: SpillSlot },
  ReloadF { dst: RealReg, src: SpillSlot },
  Goto { target: Label },
  GotoCTF { cond: Reg, targetT: Label, targetF: Label },
  PrintS { str: String },
  PrintI { reg: Reg },
  PrintF { reg: Reg },
  Finish {},
}

pub fn i_imm(dst: Reg, imm: u32) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::Imm { dst, imm }
}
pub fn i_copy(dst: Reg, src: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(src.get_class() == RegClass::I32);
  Inst::Copy { dst, src }
}
// For BinOp variants see below

pub fn i_load(dst: Reg, addr: AM) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::Load { dst, addr }
}
pub fn i_store(addr: AM, src: Reg) -> Inst {
  debug_assert!(src.get_class() == RegClass::I32);
  Inst::Store { addr, src }
}
pub fn i_spill(dst: SpillSlot, src: RealReg) -> Inst {
  debug_assert!(src.get_class() == RegClass::I32);
  Inst::Spill { dst, src }
}
pub fn i_reload(dst: RealReg, src: SpillSlot) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::Reload { dst, src }
}
pub fn i_goto<'a>(target: &'a str) -> Inst {
  Inst::Goto { target: mkUnresolved(target.to_string()) }
}
pub fn i_goto_ctf<'a>(cond: Reg, targetT: &'a str, targetF: &'a str) -> Inst {
  debug_assert!(cond.get_class() == RegClass::I32);
  Inst::GotoCTF {
    cond,
    targetT: mkUnresolved(targetT.to_string()),
    targetF: mkUnresolved(targetF.to_string()),
  }
}
pub fn i_print_s<'a>(str: &'a str) -> Inst {
  Inst::PrintS { str: str.to_string() }
}
pub fn i_print_i(reg: Reg) -> Inst {
  debug_assert!(reg.get_class() == RegClass::I32);
  Inst::PrintI { reg }
}
pub fn i_finish() -> Inst {
  Inst::Finish {}
}

pub fn i_add(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Add, dst, srcL, srcR }
}
pub fn i_sub(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Sub, dst, srcL, srcR }
}
pub fn i_mul(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Mul, dst, srcL, srcR }
}
pub fn i_mod(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Mod, dst, srcL, srcR }
}
pub fn i_shr(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Shr, dst, srcL, srcR }
}
pub fn i_and(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::And, dst, srcL, srcR }
}
pub fn i_cmp_eq(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpEQ, dst, srcL, srcR }
}
pub fn i_cmp_lt(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpLT, dst, srcL, srcR }
}
pub fn i_cmp_le(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpLE, dst, srcL, srcR }
}
pub fn i_cmp_ge(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpGE, dst, srcL, srcR }
}
pub fn i_cmp_gt(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpGT, dst, srcL, srcR }
}

// 2-operand versions of i_add and i_sub, for experimentation
pub fn i_addm(dst: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::BinOpM { op: BinOp::Add, dst, srcR }
}
pub fn i_subm(dst: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::BinOpM { op: BinOp::Sub, dst, srcR }
}

pub fn i_fadd(dst: Reg, srcL: Reg, srcR: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  debug_assert!(srcL.get_class() == RegClass::F32);
  debug_assert!(srcR.get_class() == RegClass::F32);
  Inst::BinOpF { op: BinOpF::FAdd, dst, srcL, srcR }
}
pub fn i_fsub(dst: Reg, srcL: Reg, srcR: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  debug_assert!(srcL.get_class() == RegClass::F32);
  debug_assert!(srcR.get_class() == RegClass::F32);
  Inst::BinOpF { op: BinOpF::FSub, dst, srcL, srcR }
}
pub fn i_fmul(dst: Reg, srcL: Reg, srcR: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  debug_assert!(srcL.get_class() == RegClass::F32);
  debug_assert!(srcR.get_class() == RegClass::F32);
  Inst::BinOpF { op: BinOpF::FMul, dst, srcL, srcR }
}
pub fn i_fdiv(dst: Reg, srcL: Reg, srcR: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  debug_assert!(srcL.get_class() == RegClass::F32);
  debug_assert!(srcR.get_class() == RegClass::F32);
  Inst::BinOpF { op: BinOpF::FDiv, dst, srcL, srcR }
}

impl fmt::Debug for Inst {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    fn ljustify(s: String, w: usize) -> String {
      if s.len() >= w {
        s
      } else {
        // BEGIN hack
        let mut need = w - s.len();
        if need > 5 {
          need = 5;
        }
        let extra = [" ", "  ", "   ", "    ", "     "][need - 1];
        // END hack
        s + &extra.to_string()
      }
    }

    match self {
      Inst::Imm { dst, imm } => write!(fmt, "imm     {:?}, {:?}", dst, imm),
      Inst::ImmF { dst, imm } => write!(fmt, "immf    {:?}, {:?}", dst, imm),
      Inst::Copy { dst, src } => write!(fmt, "copy    {:?}, {:?}", dst, src),
      Inst::BinOp { op, dst, srcL, srcR } => write!(
        fmt,
        "{} {:?}, {:?}, {:?}",
        ljustify(op.to_string(), 7),
        dst,
        srcL,
        srcR
      ),
      Inst::BinOpM { op, dst, srcR } => write!(
        fmt,
        "{} {:?}, {:?}",
        ljustify(op.to_string() + &"m".to_string(), 7),
        dst,
        srcR
      ),
      Inst::BinOpF { op, dst, srcL, srcR } => write!(
        fmt,
        "{} {:?}, {:?}, {:?}",
        ljustify(op.to_string(), 7),
        dst,
        srcL,
        srcR
      ),
      Inst::Load { dst, addr } => write!(fmt, "load    {:?}, {:?}", dst, addr),
      Inst::LoadF { dst, addr } => write!(fmt, "loadf   {:?}, {:?}", dst, addr),
      Inst::Store { addr, src } => write!(fmt, "store   {:?}, {:?}", addr, src),
      Inst::StoreF { addr, src } => {
        write!(fmt, "storef  {:?}, {:?}", addr, src)
      }
      Inst::Spill { dst, src } => write!(fmt, "SPILL   {:?}, {:?}", dst, src),
      Inst::SpillF { dst, src } => write!(fmt, "SPILLF  {:?}, {:?}", dst, src),
      Inst::Reload { dst, src } => write!(fmt, "RELOAD  {:?}, {:?}", dst, src),
      Inst::ReloadF { dst, src } => write!(fmt, "RELOAD  {:?}, {:?}", dst, src),
      Inst::Goto { target } => write!(fmt, "goto    {:?}", target),
      Inst::GotoCTF { cond, targetT, targetF } => write!(
        fmt,
        "goto    if {:?} then {:?} else {:?}",
        cond, targetT, targetF
      ),
      Inst::PrintS { str } => {
        let mut res = "prints '".to_string();
        for c in str.chars() {
          res += &(if c == '\n' { "\\n".to_string() } else { c.to_string() });
        }
        write!(fmt, "{}'", res)
      }
      Inst::PrintI { reg } => write!(fmt, "printi {:?}", reg),
      Inst::PrintF { reg } => write!(fmt, "printf {:?}", reg),
      Inst::Finish {} => write!(fmt, "finish"),
    }
  }
}

impl Inst {
  // Returns a vector of BlockIxs, being those that this insn might jump to.
  // This might contain duplicates (although it would be pretty strange if
  // it did). This function should not be applied to non-control-flow
  // instructions.  The labels are assumed all to be "resolved".
  pub fn getTargets(&self) -> Vec<BlockIx> {
    match self {
      Inst::Goto { target } => vec![target.getBlockIx()],
      Inst::GotoCTF { cond: _, targetT, targetF } => {
        vec![targetT.getBlockIx(), targetF.getBlockIx()]
      }
      Inst::Finish {} => vec![],
      _other => panic!("Inst::getTargets: incorrectly applied to: {:?}", self),
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
  pub fn get_reg_usage(&self) -> (Set<Reg>, Set<Reg>, Set<Reg>) {
    let mut def = Set::<Reg>::empty();
    let mut m0d = Set::<Reg>::empty();
    let mut uce = Set::<Reg>::empty();
    match self {
      Inst::Imm { dst, imm: _ } => {
        def.insert(*dst);
      }
      Inst::Copy { dst, src } => {
        def.insert(*dst);
        uce.insert(*src);
      }
      Inst::BinOp { op: _, dst, srcL, srcR } => {
        def.insert(*dst);
        uce.insert(*srcL);
        srcR.addRegReadsTo(&mut uce);
      }
      Inst::BinOpM { op: _, dst, srcR } => {
        m0d.insert(*dst);
        srcR.addRegReadsTo(&mut uce);
      }
      Inst::Store { addr, src } => {
        addr.addRegReadsTo(&mut uce);
        uce.insert(*src);
      }
      Inst::Load { dst, addr } => {
        def.insert(*dst);
        addr.addRegReadsTo(&mut uce);
      }
      Inst::Goto { .. } => {}
      Inst::GotoCTF { cond, targetT: _, targetF: _ } => {
        uce.insert(*cond);
      }
      Inst::PrintS { .. } => {}
      Inst::PrintI { reg } => {
        uce.insert(*reg);
      }
      Inst::Finish {} => {}
      // Spill and Reload are seen here during the final pass over insts that computes clobbered
      // regs.
      Inst::Spill { src, .. } | Inst::SpillF { src, .. } => {
        uce.insert(src.to_reg());
      }
      Inst::Reload { dst, .. } | Inst::ReloadF { dst, .. } => {
        def.insert(dst.to_reg());
      }
      _other => panic!("Inst::get_reg_usage: unhandled: {:?}", self),
    }
    // Failure of either of these is serious and should be investigated.
    debug_assert!(!def.intersects(&m0d));
    debug_assert!(!uce.intersects(&m0d));
    (def, m0d, uce)
  }

  // Apply the specified VirtualReg->RealReg mappings to the instruction,
  // thusly:
  // * For registers mentioned in a read role, apply mapU.
  // * For registers mentioned in a write role, apply mapD.
  // * For registers mentioned in a modify role, mapU and mapD *must* agree
  //   (if not, our caller is buggy).  So apply either map to that register.
  pub fn mapRegs_D_U(
    &mut self, mapD: &Map<VirtualReg, RealReg>, mapU: &Map<VirtualReg, RealReg>,
  ) {
    let mut ok = true;
    match self {
      Inst::Imm { dst, imm: _ } => {
        dst.apply_D_or_U(mapD);
      }
      Inst::Copy { dst, src } => {
        dst.apply_D_or_U(mapD);
        src.apply_D_or_U(mapU);
      }
      Inst::BinOp { op: _, dst, srcL, srcR } => {
        dst.apply_D_or_U(mapD);
        srcL.apply_D_or_U(mapU);
        srcR.apply_D_or_U(mapU);
      }
      Inst::BinOpM { op: _, dst, srcR } => {
        dst.apply_M(mapD, mapU);
        srcR.apply_D_or_U(mapU);
      }
      Inst::Store { addr, src } => {
        addr.apply_D_or_U(mapU);
        src.apply_D_or_U(mapU);
      }
      Inst::Load { dst, addr } => {
        dst.apply_D_or_U(mapD);
        addr.apply_D_or_U(mapU);
      }
      Inst::Goto { .. } => {}
      Inst::GotoCTF { cond, targetT: _, targetF: _ } => {
        cond.apply_D_or_U(mapU);
      }
      Inst::PrintS { .. } => {}
      Inst::PrintI { reg } => {
        reg.apply_D_or_U(mapU);
      }
      Inst::Finish {} => {}
      _ => {
        ok = false;
      }
    }
    if !ok {
      panic!("Inst::mapRegs_D_U: unhandled: {:?}", self);
    }
  }
}

fn is_control_flow_insn(insn: &Inst) -> bool {
  match insn {
    Inst::Goto { .. } | Inst::GotoCTF { .. } | Inst::Finish {} => true,
    _ => false,
  }
}

pub fn is_goto_insn(insn: &Inst) -> Option<Label> {
  match insn {
    Inst::Goto { target } => Some(target.clone()),
    _ => None,
  }
}

pub fn remapControlFlowTarget(insn: &mut Inst, from: &String, to: &String) {
  match insn {
    Inst::Goto { ref mut target } => {
      target.remapControlFlow(from, to);
    }
    Inst::GotoCTF { cond: _, ref mut targetT, ref mut targetF } => {
      targetT.remapControlFlow(from, to);
      targetF.remapControlFlow(from, to);
    }
    _ => (),
  }
}

//=============================================================================
// Definition of Block and Func, and printing thereof.

#[derive(Debug)]
pub struct Block {
  pub name: String,
  pub start: InstIx,
  pub len: u32,
  pub estFreq: u16, // Estimated execution frequency
}
pub fn mkBlock(name: String, start: InstIx, len: u32) -> Block {
  Block { name, start, len, estFreq: 1 }
}
impl Clone for Block {
  // This is only needed for debug printing.
  fn clone(&self) -> Self {
    Block {
      name: self.name.clone(),
      start: self.start,
      len: self.len,
      estFreq: self.estFreq,
    }
  }
}
impl Block {
  pub fn containsInstIx(&self, iix: InstIx) -> bool {
    iix.get() >= self.start.get() && iix.get() < self.start.get() + self.len
  }
}

#[derive(Debug)]
pub struct Func {
  pub name: String,
  pub entry: Label,
  pub nVirtualRegs: u32,
  pub insns: TypedIxVec<InstIx, Inst>, // indexed by InstIx
  pub blocks: TypedIxVec<BlockIx, Block>, // indexed by BlockIx
                                       // Note that |blocks| must be in order of increasing |Block::start|
                                       // fields.  Code that wants to traverse the blocks in some other order
                                       // must represent the ordering some other way; rearranging Func::blocks is
                                       // not allowed.
}
impl Clone for Func {
  // This is only needed for debug printing.
  fn clone(&self) -> Self {
    Func {
      name: self.name.clone(),
      entry: self.entry.clone(),
      nVirtualRegs: self.nVirtualRegs,
      insns: self.insns.clone(),
      blocks: self.blocks.clone(),
    }
  }
}

// Find a block Ix for a block name
fn lookup(blocks: &TypedIxVec<BlockIx, Block>, name: String) -> BlockIx {
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
  pub fn new<'a>(name: &'a str, entry: &'a str) -> Self {
    Func {
      name: name.to_string(),
      entry: Label::Unresolved { name: entry.to_string() },
      nVirtualRegs: 0,
      insns: TypedIxVec::<InstIx, Inst>::new(),
      blocks: TypedIxVec::<BlockIx, Block>::new(),
    }
  }

  pub fn print(&self, who: &str) {
    println!("");
    println!("Func {}: name='{}' entry='{:?}' {{", who, self.name, self.entry);
    let mut ix = 0;
    for b in self.blocks.iter() {
      if ix > 0 {
        println!("");
      }
      println!("  {:?}:{}", mkBlockIx(ix), b.name);
      for i in b.start.get()..b.start.get() + b.len {
        let ixI = mkInstIx(i);
        println!("      {:<3?}   {:?}", ixI, self.insns[ixI]);
      }
      ix += 1;
    }
    println!("}}");
  }

  // Get a new VirtualReg name
  pub fn newVirtualReg(&mut self, rc: RegClass) -> Reg {
    let v = mkVirtualReg(rc, self.nVirtualRegs);
    self.nVirtualRegs += 1;
    v
  }

  // Add a block to the Func
  pub fn block<'a>(
    &mut self, name: &'a str, mut insns: TypedIxVec<InstIx, Inst>,
  ) {
    let start = self.insns.len();
    let len = insns.len() as u32;
    self.insns.append(&mut insns);
    let b = mkBlock(name.to_string(), mkInstIx(start), len);
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
  pub fn finish(&mut self) {
    for bix in mkBlockIx(0).dotdot(mkBlockIx(self.blocks.len())) {
      let b = &self.blocks[bix];
      if b.len == 0 {
        panic!("Func::done: a block is empty");
      }
      if bix > mkBlockIx(0)
        && self.blocks[bix.minus(1)].start >= self.blocks[bix].start
      {
        panic!("Func: blocks are not in increasing order of InstIx");
      }
      for i in 0..b.len {
        let iix = b.start.plus(i);
        if i == b.len - 1 && !is_control_flow_insn(&self.insns[iix]) {
          panic!("Func: block must end in control flow insn");
        }
        if i != b.len - 1 && is_control_flow_insn(&self.insns[iix]) {
          panic!("Func: block contains control flow insn not at end");
        }
      }
    }

    // Resolve all labels
    let blocks = &self.blocks;
    for i in self.insns.iter_mut() {
      resolveInst(i, |name| lookup(blocks, name));
    }
    resolveLabel(&mut self.entry, |name| lookup(blocks, name));
  }

  pub fn update_from_alloc(&mut self, result: interface::RegAllocResult<Func>) {
    self.insns = TypedIxVec::fromVec(result.insns);
    for bix in self.blocks.range() {
      let block = &mut self.blocks[bix];
      block.start = result.target_map[bix];
    }
  }
}

fn resolveLabel<F>(label: &mut Label, lookup: F)
where
  F: Fn(String) -> BlockIx,
{
  let resolved = match label {
    Label::Unresolved { name } => {
      Label::Resolved { name: name.clone(), bix: lookup(name.clone()) }
    }
    Label::Resolved { .. } => panic!("resolveLabel: is already resolved!"),
  };
  *label = resolved;
}

fn resolveInst<F>(insn: &mut Inst, lookup: F)
where
  F: Copy + Fn(String) -> BlockIx,
{
  match insn {
    Inst::Goto { ref mut target } => resolveLabel(target, lookup),
    Inst::GotoCTF { cond: _, ref mut targetT, ref mut targetF } => {
      resolveLabel(targetT, lookup);
      resolveLabel(targetF, lookup);
    }
    _ => (),
  }
}

enum Stmt {
  Vanilla { insn: Inst },
  IfThen { cond: Reg, stmts_t: Vec<Stmt> },
  IfThenElse { cond: Reg, stmts_t: Vec<Stmt>, stmts_e: Vec<Stmt> },
  RepeatUntil { stmts: Vec<Stmt>, cond: Reg },
  WhileDo { cond: Reg, stmts: Vec<Stmt> },
}

// Various handy wrappers, mostly wrappings of i_* functions
fn s_if_then_else(cond: Reg, stmts_t: Vec<Stmt>, stmts_e: Vec<Stmt>) -> Stmt {
  Stmt::IfThenElse { cond, stmts_t, stmts_e }
}
fn s_if_then(cond: Reg, stmts_t: Vec<Stmt>) -> Stmt {
  Stmt::IfThenElse { cond, stmts_t, stmts_e: vec![] }
}
fn s_repeat_until(stmts: Vec<Stmt>, cond: Reg) -> Stmt {
  Stmt::RepeatUntil { stmts, cond }
}
fn s_while_do(cond: Reg, stmts: Vec<Stmt>) -> Stmt {
  Stmt::WhileDo { cond, stmts }
}

fn s_vanilla(insn: Inst) -> Stmt {
  Stmt::Vanilla { insn }
}

fn s_imm(dst: Reg, imm: u32) -> Stmt {
  s_vanilla(i_imm(dst, imm))
}
fn s_copy(dst: Reg, src: Reg) -> Stmt {
  s_vanilla(i_copy(dst, src))
}
fn s_load(dst: Reg, addr: AM) -> Stmt {
  s_vanilla(i_load(dst, addr))
}
fn s_store(addr: AM, src: Reg) -> Stmt {
  s_vanilla(i_store(addr, src))
}
fn s_print_s<'a>(str: &'a str) -> Stmt {
  s_vanilla(i_print_s(str))
}
fn s_print_i(reg: Reg) -> Stmt {
  s_vanilla(i_print_i(reg))
}

fn s_add(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_add(dst, srcL, srcR))
}
fn s_sub(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_sub(dst, srcL, srcR))
}
fn s_mul(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_mul(dst, srcL, srcR))
}
fn s_mod(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_mod(dst, srcL, srcR))
}
fn s_shr(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_shr(dst, srcL, srcR))
}
fn s_and(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_and(dst, srcL, srcR))
}
fn s_cmp_eq(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_eq(dst, srcL, srcR))
}
fn s_cmp_lt(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_lt(dst, srcL, srcR))
}
fn s_cmp_le(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_le(dst, srcL, srcR))
}
fn s_cmp_ge(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_ge(dst, srcL, srcR))
}
fn s_cmp_gt(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_gt(dst, srcL, srcR))
}

fn s_addm(dst: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_addm(dst, srcR))
}
fn s_subm(dst: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_subm(dst, srcR))
}

//=============================================================================
// The "blockifier".  This is just to make it easier to write test cases, by
// allowing direct use of if-then-else, do-while and repeat-until.  It is
// otherwise entirely unrelated to the register allocator proper.

struct Blockifier {
  name: String,
  blocks: Vec<TypedIxVec<InstIx, Inst>>,
  currBNo: usize, // index into |blocks|
  nVirtualRegs: u32,
}

impl Blockifier {
  fn new<'a>(name: &'a str) -> Self {
    Self { name: name.to_string(), blocks: vec![], currBNo: 0, nVirtualRegs: 0 }
  }

  // Get a new VirtualReg name
  fn newVirtualReg(&mut self, rc: RegClass) -> Reg {
    let v = mkVirtualReg(rc, self.nVirtualRegs);
    self.nVirtualRegs += 1;
    v
  }

  // Recursive worker function, which flattens out the control flow,
  // producing a set of blocks
  fn blockify(&mut self, stmts: Vec<Stmt>) -> (usize, usize) {
    let entryBNo = self.blocks.len();
    let mut currBNo = entryBNo;
    self.blocks.push(TypedIxVec::<InstIx, Inst>::new());
    for s in stmts {
      match s {
        Stmt::Vanilla { insn } => {
          self.blocks[currBNo].push(insn);
        }
        Stmt::IfThenElse { cond, stmts_t, stmts_e } => {
          let (t_ent, t_exit) = self.blockify(stmts_t);
          let (e_ent, e_exit) = self.blockify(stmts_e);
          let cont = self.blocks.len();
          self.blocks.push(TypedIxVec::<InstIx, Inst>::new());
          self.blocks[t_exit].push(i_goto(&mkTextLabel(cont)));
          self.blocks[e_exit].push(i_goto(&mkTextLabel(cont)));
          self.blocks[currBNo].push(i_goto_ctf(
            cond,
            &mkTextLabel(t_ent),
            &mkTextLabel(e_ent),
          ));
          currBNo = cont;
        }
        Stmt::RepeatUntil { stmts, cond } => {
          let (s_ent, s_exit) = self.blockify(stmts);
          self.blocks[currBNo].push(i_goto(&mkTextLabel(s_ent)));
          let cont = self.blocks.len();
          self.blocks.push(TypedIxVec::<InstIx, Inst>::new());
          self.blocks[s_exit].push(i_goto_ctf(
            cond,
            &mkTextLabel(cont),
            &mkTextLabel(s_ent),
          ));
          currBNo = cont;
        }
        Stmt::WhileDo { cond, stmts } => {
          let condblock = self.blocks.len();
          self.blocks.push(TypedIxVec::<InstIx, Inst>::new());
          self.blocks[currBNo].push(i_goto(&mkTextLabel(condblock)));
          let (s_ent, s_exit) = self.blockify(stmts);
          self.blocks[s_exit].push(i_goto(&mkTextLabel(condblock)));
          let cont = self.blocks.len();
          self.blocks.push(TypedIxVec::<InstIx, Inst>::new());
          self.blocks[condblock].push(i_goto_ctf(
            cond,
            &mkTextLabel(s_ent),
            &mkTextLabel(cont),
          ));
          currBNo = cont;
        }
        _ => panic!("blockify: unhandled case"),
      }
    }
    (entryBNo, currBNo)
  }

  // The main external function.  Convert the given statements, into a Func.
  fn finish(&mut self, stmts: Vec<Stmt>) -> Func {
    let (ent_bno, exit_bno) = self.blockify(stmts);
    self.blocks[exit_bno].push(i_finish());

    let mut blockz = Vec::<TypedIxVec<InstIx, Inst>>::new();
    std::mem::swap(&mut self.blocks, &mut blockz);

    // BEGIN optionally, short out blocks that merely jump somewhere else
    let mut cleanedUp = Vec::<Option<TypedIxVec<InstIx, Inst>>>::new();
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
          Some(b) => b,
        };

        debug_assert!(b.len() > 0);
        if b.len() == 1 {
          if let Some(targetLabel) = is_goto_insn(&b[mkInstIx(0)]) {
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
          for i in 0..nnn {
            match cleanedUp[i] {
              None => {}
              Some(ref mut insns) => {
                let mmm = insns.len();
                for j in mkInstIx(0).dotdot(mkInstIx(mmm)) {
                  remapControlFlowTarget(
                    &mut insns[j],
                    &mkTextLabel(from),
                    &to,
                  );
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
    func.nVirtualRegs = 3; // or whatever
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

// --------------------------------------------------
// Implementation of `Function` trait for test cases.

impl interface::Function for Func {
  type Inst = Inst;

  fn insns(&self) -> &[Inst] {
    self.insns.elems()
  }

  fn insns_mut(&mut self) -> &mut [Inst] {
    self.insns.elems_mut()
  }

  fn get_insn(&self, iix: InstIx) -> &Inst {
    &self.insns[iix]
  }

  fn get_insn_mut(&mut self, iix: InstIx) -> &mut Inst {
    &mut self.insns[iix]
  }

  fn entry_block(&self) -> BlockIx {
    mkBlockIx(0)
  }

  fn blocks(&self) -> MyRange<BlockIx> {
    self.blocks.range()
  }

  /// Provide the range of instruction indices contained in each block.
  fn block_insns(&self, block: BlockIx) -> MyRange<InstIx> {
    MyRange::new(self.blocks[block].start, self.blocks[block].len as usize)
  }

  /// Get CFG successors: indexed by block, provide a list of successor blocks.
  fn block_succs(&self, block: BlockIx) -> Vec<BlockIx> {
    let last_insn = self.blocks[block].start.plus(self.blocks[block].len - 1);
    self.insns[last_insn].getTargets()
  }

  /// Provide the defined, used, and modified registers for an instruction.
  fn get_regs(&self, insn: &Self::Inst) -> interface::InstRegUses {
    let (d, m, u) = insn.get_reg_usage();
    interface::InstRegUses { used: u, defined: d, modified: m }
  }

  /// Map each register slot through a virt -> phys mapping indexed
  /// by virtual register. The two separate maps provide the
  /// mapping to use for uses (which semantically occur just prior
  /// to the instruction's effect) and defs (which semantically occur
  /// just after the instruction's effect). Regs that were "modified"
  /// can use either map; the vreg should be the same in both.
  fn map_regs(
    insn: &mut Self::Inst, pre_map: &Map<VirtualReg, RealReg>,
    post_map: &Map<VirtualReg, RealReg>,
  ) {
    insn.mapRegs_D_U(
      /* define-map = */ post_map, /* use-map = */ pre_map,
    );
  }

  /// Allow the regalloc to query whether this is a move.
  fn is_move(&self, insn: &Self::Inst) -> Option<(Reg, Reg)> {
    match insn {
      &Inst::Copy { dst, src } => Some((dst, src)),
      _ => None,
    }
  }

  /// How many logical spill slots does the given regclass require?  E.g., on a
  /// 64-bit machine, spill slots may nominally be 64-bit words, but a 128-bit
  /// vector value will require two slots.  The regalloc will always align on
  /// this size.
  fn get_spillslot_size(&self, regclass: RegClass) -> u32 {
    // For our simple test ISA, every value occupies one spill slot.
    1
  }

  /// Generate a spill instruction for insertion into the instruction sequence.
  fn gen_spill(&self, to_slot: SpillSlot, from_reg: RealReg) -> Self::Inst {
    match from_reg.get_class() {
      RegClass::I32 => Inst::Spill { dst: to_slot, src: from_reg },
      RegClass::F32 => Inst::SpillF { dst: to_slot, src: from_reg },
      _ => panic!("Unused register class in test ISA was used"),
    }
  }

  /// Generate a reload instruction for insertion into the instruction sequence.
  fn gen_reload(&self, to_reg: RealReg, from_slot: SpillSlot) -> Self::Inst {
    match to_reg.get_class() {
      RegClass::I32 => Inst::Reload { src: from_slot, dst: to_reg },
      RegClass::F32 => Inst::ReloadF { src: from_slot, dst: to_reg },
      _ => panic!("Unused register class in test ISA was used"),
    }
  }

  /// Generate a register-to-register move for insertion into the instruction sequence.
  fn gen_move(&self, to_reg: RealReg, from_reg: RealReg) -> Self::Inst {
    Inst::Copy { src: from_reg.to_reg(), dst: to_reg.to_reg() }
  }

  /// Try to alter an existing instruction to use a value directly in a
  /// spillslot (accessing memory directly) instead of the given register. May
  /// be useful on ISAs that have mem/reg ops, like x86.
  ///
  /// Note that this is not *quite* just fusing a load with the op; if the
  /// value is def'd or modified, it should be written back to the spill slot
  /// as well. In other words, it is just using the spillslot as if it were a
  /// real register, for reads and/or writes.
  fn maybe_direct_reload(
    &self, insn: &Self::Inst, reg: VirtualReg, slot: SpillSlot,
  ) -> Option<Self::Inst> {
    // test ISA does not have register-memory ALU instruction forms.
    None
  }
}

// Create a universe for testing, with nI32 |I32| class regs and nF32 |F32|
// class regs.

pub fn make_universe(nI32: usize, nF32: usize) -> RealRegUniverse {
  let total_regs = nI32 + nF32;
  if total_regs >= 256 {
    panic!("make_universe: too many regs, cannot represent");
  }

  let mut regs = Vec::<(RealReg, String)>::new();
  let mut allocable_by_class = [None; NUM_REG_CLASSES];
  let mut index = 0u8;

  if nI32 > 0 {
    let first = index as usize;
    for i in 0..nI32 {
      let name = format!("R{}", i).to_string();
      let reg = mkRealReg(RegClass::I32, /*enc=*/ 0, index).to_real_reg();
      regs.push((reg, name));
      index += 1;
    }
    let last = index as usize - 1;
    allocable_by_class[RegClass::I32.rc_to_usize()] = Some((first, last));
  }

  if nF32 > 0 {
    let first = index as usize;
    for i in 0..nF32 {
      let name = format!("F{}", i).to_string();
      let reg = mkRealReg(RegClass::F32, /*enc=*/ 0, index).to_real_reg();
      regs.push((reg, name));
      index += 1;
    }
    let last = index as usize - 1;
    allocable_by_class[RegClass::F32.rc_to_usize()] = Some((first, last));
  }

  debug_assert!(index as usize == total_regs);

  let allocable = regs.len();
  let univ = RealRegUniverse {
    regs,
    // for this example, all regs are allocable
    allocable,
    allocable_by_class,
  };
  univ.check_is_sane();

  univ
}

// Whatever the current badness is
fn test__badness() -> Func {
  let mut func = Func::new("badness", "start");

  func.block(
    "start",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_print_s("!!Badness!!\n"),
      i_finish(),
    ]),
  );

  func.finish();
  func
}

fn test__straight_line() -> Func {
  let mut func = Func::new("straight_line", "b0");

  // Regs, virtual and real, that we want to use.
  let vA = func.newVirtualReg(RegClass::I32);

  func.block(
    "b0",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_print_s("Start\n"),
      i_imm(vA, 10),
      i_add(vA, vA, RI_I(7)),
      i_goto("b1"),
    ]),
  );
  func.block(
    "b1",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_print_s("Result = "),
      i_print_i(vA),
      i_print_s("\n"),
      i_finish(),
    ]),
  );

  func.finish();
  func
}

fn test__fill_then_sum() -> Func {
  let mut func = Func::new("fill_then_sum", "set-loop-pre");

  // Regs, virtual and real, that we want to use.
  let vNENT = func.newVirtualReg(RegClass::I32);
  let vI = func.newVirtualReg(RegClass::I32);
  let vSUM = func.newVirtualReg(RegClass::I32);
  let rTMP = mkRealReg(RegClass::I32, /*enc=*/ 0x42, /*index=*/ 2); // "2" is arbitrary.
  let vTMP2 = func.newVirtualReg(RegClass::I32);

  // Loop pre-header for filling array with numbers.
  // This is also the entry point.
  func.block(
    "set-loop-pre",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_imm(vNENT, 10),
      i_imm(vI, 0),
      i_goto("set-loop"),
    ]),
  );

  // Filling loop
  func.block(
    "set-loop",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_store(AM_R(vI), vI),
      i_add(vI, vI, RI_I(1)),
      i_cmp_lt(rTMP, vI, RI_R(vNENT)),
      i_goto_ctf(rTMP, "set-loop", "sum-loop-pre"),
    ]),
  );

  // Loop pre-header for summing them
  func.block(
    "sum-loop-pre",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_imm(vSUM, 0),
      i_imm(vI, 0),
      i_goto("sum-loop"),
    ]),
  );

  // Summing loop
  func.block(
    "sum-loop",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_load(rTMP, AM_R(vI)),
      i_add(vSUM, vSUM, RI_R(rTMP)),
      i_add(vI, vI, RI_I(1)),
      i_cmp_lt(vTMP2, vI, RI_R(vNENT)),
      i_goto_ctf(vTMP2, "sum-loop", "print-result"),
    ]),
  );

  // After loop.  Print result and stop.
  func.block(
    "print-result",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_print_s("Sum = "),
      i_print_i(vSUM),
      i_print_s("\n"),
      i_finish(),
    ]),
  );

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

  let lo = func.newVirtualReg(RegClass::I32);
  let hi = func.newVirtualReg(RegClass::I32);
  let i = func.newVirtualReg(RegClass::I32);
  let j = func.newVirtualReg(RegClass::I32);
  let h = func.newVirtualReg(RegClass::I32);
  let bigN = func.newVirtualReg(RegClass::I32);
  let v = func.newVirtualReg(RegClass::I32);
  let hp = func.newVirtualReg(RegClass::I32);
  let t0 = func.newVirtualReg(RegClass::I32);
  let zero = func.newVirtualReg(RegClass::I32);

  func.block(
    "Lstart",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_imm(zero, 0),
      // Store the increment table
      i_imm(t0, 1),
      i_store(AM_RI(zero, 0), t0),
      i_imm(t0, 4),
      i_store(AM_RI(zero, 1), t0),
      i_imm(t0, 13),
      i_store(AM_RI(zero, 2), t0),
      i_imm(t0, 40),
      i_store(AM_RI(zero, 3), t0),
      i_imm(t0, 121),
      i_store(AM_RI(zero, 4), t0),
      // Store the numbers to be sorted
      i_imm(t0, 30),
      i_store(AM_RI(zero, 5), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 6), t0),
      i_imm(t0, 31),
      i_store(AM_RI(zero, 7), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 8), t0),
      i_imm(t0, 32),
      i_store(AM_RI(zero, 9), t0),
      i_imm(t0, 66),
      i_store(AM_RI(zero, 10), t0),
      i_imm(t0, 77),
      i_store(AM_RI(zero, 11), t0),
      i_imm(t0, 44),
      i_store(AM_RI(zero, 12), t0),
      i_imm(t0, 22),
      i_store(AM_RI(zero, 13), t0),
      i_imm(t0, 11),
      i_store(AM_RI(zero, 14), t0),
      i_imm(t0, 99),
      i_store(AM_RI(zero, 15), t0),
      i_imm(t0, 11),
      i_store(AM_RI(zero, 16), t0),
      i_imm(t0, 12),
      i_store(AM_RI(zero, 17), t0),
      i_imm(t0, 7),
      i_store(AM_RI(zero, 18), t0),
      i_imm(t0, 9),
      i_store(AM_RI(zero, 19), t0),
      i_imm(t0, 2),
      i_store(AM_RI(zero, 20), t0),
      i_imm(t0, 32),
      i_store(AM_RI(zero, 21), t0),
      i_imm(t0, 23),
      i_store(AM_RI(zero, 22), t0),
      i_imm(t0, 41),
      i_store(AM_RI(zero, 23), t0),
      i_imm(t0, 14),
      i_store(AM_RI(zero, 24), t0),
      // The real computation begins here
      i_imm(lo, 5),  // Lowest address of the range to sort
      i_imm(hi, 24), // Highest address of the range to sort
      i_sub(t0, hi, RI_R(lo)),
      i_add(bigN, t0, RI_I(1)),
      i_imm(hp, 0),
      i_goto("L11"),
    ]),
  );

  func.block(
    "L11",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_load(t0, AM_R(hp)),
      i_cmp_gt(t0, t0, RI_R(bigN)),
      i_goto_ctf(t0, "L20", "L11a"),
    ]),
  );

  func.block(
    "L11a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_add(hp, hp, RI_I(1)),
      i_goto("L11"),
    ]),
  );

  func.block(
    "L20",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_cmp_lt(t0, hp, RI_I(1)),
      i_goto_ctf(t0, "L60", "L21a"),
    ]),
  );

  func.block(
    "L21a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_sub(t0, hp, RI_I(1)),
      i_load(h, AM_R(t0)),
      //printf("h = %u\n", h),
      i_add(i, lo, RI_R(h)),
      i_goto("L30"),
    ]),
  );

  func.block(
    "L30",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_cmp_gt(t0, i, RI_R(hi)),
      i_goto_ctf(t0, "L50", "L30a"),
    ]),
  );

  func.block(
    "L30a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_load(v, AM_R(i)),
      i_add(j, i, RI_I(0)), // FIXME: is this a coalescable copy?
      i_goto("L40"),
    ]),
  );

  func.block(
    "L40",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_sub(t0, j, RI_R(h)),
      i_load(t0, AM_R(t0)),
      i_cmp_le(t0, t0, RI_R(v)),
      i_goto_ctf(t0, "L45", "L40a"),
    ]),
  );

  func.block(
    "L40a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_sub(t0, j, RI_R(h)),
      i_load(t0, AM_R(t0)),
      i_store(AM_R(j), t0),
      i_sub(j, j, RI_R(h)),
      i_add(t0, lo, RI_R(h)),
      i_sub(t0, t0, RI_I(1)),
      i_cmp_le(t0, j, RI_R(t0)),
      i_goto_ctf(t0, "L45", "L40"),
    ]),
  );

  func.block(
    "L45",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_store(AM_R(j), v),
      i_add(i, i, RI_I(1)),
      i_goto("L30"),
    ]),
  );

  func.block(
    "L50",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_sub(hp, hp, RI_I(1)),
      i_goto("L20"),
    ]),
  );

  func.block(
    "L60",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_add(i, lo, RI_I(0)), // FIXME: ditto
      i_goto("L61"),
    ]),
  );

  func.block(
    "L61",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_cmp_gt(t0, i, RI_R(hi)),
      i_goto_ctf(t0, "L62", "L61a"),
    ]),
  );

  func.block(
    "L61a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_load(t0, AM_R(i)),
      i_print_i(t0),
      i_print_s(" "),
      i_add(i, i, RI_I(1)),
      i_goto("L61"),
    ]),
  );

  func.block(
    "L62",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![i_print_s("\n"), i_finish()]),
  );

  func.finish();
  func
}

fn test__3_loops() -> Func {
  let mut func = Func::new("3_loops", "start");

  let v00 = func.newVirtualReg(RegClass::I32);
  let v01 = func.newVirtualReg(RegClass::I32);
  let v02 = func.newVirtualReg(RegClass::I32);
  let v03 = func.newVirtualReg(RegClass::I32);
  let v04 = func.newVirtualReg(RegClass::I32);
  let v05 = func.newVirtualReg(RegClass::I32);
  let v06 = func.newVirtualReg(RegClass::I32);
  let v07 = func.newVirtualReg(RegClass::I32);
  let v08 = func.newVirtualReg(RegClass::I32);
  let v09 = func.newVirtualReg(RegClass::I32);
  let v10 = func.newVirtualReg(RegClass::I32);
  let v11 = func.newVirtualReg(RegClass::I32);
  let vI = func.newVirtualReg(RegClass::I32);
  let vJ = func.newVirtualReg(RegClass::I32);
  let vSUM = func.newVirtualReg(RegClass::I32);
  let vTMP = func.newVirtualReg(RegClass::I32);

  // Loop pre-header for filling array with numbers.
  // This is also the entry point.
  func.block(
    "start",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
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
      i_goto("outer-loop-cond"),
    ]),
  );

  // Outer loop
  func.block(
    "outer-loop-cond",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_add(vI, vI, RI_I(1)),
      i_cmp_le(vTMP, vI, RI_I(20)),
      i_goto_ctf(vTMP, "outer-loop-1", "after-outer-loop"),
    ]),
  );

  func.block(
    "outer-loop-1",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_add(v00, v00, RI_I(1)),
      i_add(v01, v01, RI_I(1)),
      i_add(v02, v02, RI_I(1)),
      i_add(v03, v03, RI_I(1)),
      i_goto("outer-loop-cond"),
    ]),
  );

  // After loop.  Print result and stop.
  func.block(
    "after-outer-loop",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
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
      i_finish(),
    ]),
  );

  func.finish();
  func
}

fn test__stmts() -> Func {
  let mut bif = Blockifier::new("stmts");
  let vI = bif.newVirtualReg(RegClass::I32);
  let vJ = bif.newVirtualReg(RegClass::I32);
  let vSUM = bif.newVirtualReg(RegClass::I32);
  let vTMP = bif.newVirtualReg(RegClass::I32);
  let stmts = vec![
    s_imm(vSUM, 0),
    s_imm(vI, 0),
    s_repeat_until(
      vec![
        s_imm(vJ, 0),
        s_repeat_until(
          vec![
            s_mul(vTMP, vI, RI_R(vJ)),
            s_add(vSUM, vSUM, RI_R(vTMP)),
            s_add(vJ, vJ, RI_I(1)),
            s_cmp_gt(vTMP, vJ, RI_I(10)),
          ],
          vTMP,
        ),
        s_add(vSUM, vSUM, RI_R(vI)),
        s_add(vI, vI, RI_I(1)),
        s_cmp_gt(vTMP, vI, RI_I(10)),
      ],
      vTMP,
    ),
    s_print_s("Result is "),
    s_print_i(vSUM),
    s_print_s("\n"),
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
  let v10 = bif.newVirtualReg(RegClass::I32);
  let v11 = bif.newVirtualReg(RegClass::I32);
  let v12 = bif.newVirtualReg(RegClass::I32);

  let v20 = bif.newVirtualReg(RegClass::I32);
  let v21 = bif.newVirtualReg(RegClass::I32);
  let v22 = bif.newVirtualReg(RegClass::I32);

  let vI = bif.newVirtualReg(RegClass::I32);
  let vSUM = bif.newVirtualReg(RegClass::I32);
  let vTMP = bif.newVirtualReg(RegClass::I32);

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
    s_repeat_until(
      vec![
        s_add(v10, v10, RI_I(1)),
        s_add(v11, v11, RI_I(2)),
        s_add(v12, v12, RI_I(3)),
        s_add(vI, vI, RI_I(1)),
        s_cmp_ge(vTMP, vI, RI_I(100)),
      ],
      vTMP,
    ),
    // Conversely, v2x in this loop are hot, and v1x are unused, but still
    // need to stay alive across it.
    s_imm(vI, 0),
    s_repeat_until(
      vec![
        s_add(v20, v20, RI_I(1)),
        s_add(v21, v21, RI_I(2)),
        s_add(v22, v22, RI_I(3)),
        s_add(vI, vI, RI_I(1)),
        s_cmp_ge(vTMP, vI, RI_I(100)),
      ],
      vTMP,
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
    s_print_s("\n"),
  ];
  bif.finish(stmts)
}

// This is the same as needs_splitting, but with the live ranges split "manually"
fn test__needs_splitting2() -> Func {
  let mut bif = Blockifier::new("needs_splitting2");
  let v10 = bif.newVirtualReg(RegClass::I32);
  let v11 = bif.newVirtualReg(RegClass::I32);
  let v12 = bif.newVirtualReg(RegClass::I32);

  let v20 = bif.newVirtualReg(RegClass::I32);
  let v21 = bif.newVirtualReg(RegClass::I32);
  let v22 = bif.newVirtualReg(RegClass::I32);

  // Post-split versions of v10 .. v22
  let s1v10 = bif.newVirtualReg(RegClass::I32);
  let s1v11 = bif.newVirtualReg(RegClass::I32);
  let s1v12 = bif.newVirtualReg(RegClass::I32);

  let s1v20 = bif.newVirtualReg(RegClass::I32);
  let s1v21 = bif.newVirtualReg(RegClass::I32);
  let s1v22 = bif.newVirtualReg(RegClass::I32);

  let s2v20 = bif.newVirtualReg(RegClass::I32);
  let s2v21 = bif.newVirtualReg(RegClass::I32);
  let s2v22 = bif.newVirtualReg(RegClass::I32);

  let vI = bif.newVirtualReg(RegClass::I32);
  let vSUM = bif.newVirtualReg(RegClass::I32);
  let vTMP = bif.newVirtualReg(RegClass::I32);

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
    s_repeat_until(
      vec![
        s_add(v10, v10, RI_I(1)),
        s_add(v11, v11, RI_I(2)),
        s_add(v12, v12, RI_I(3)),
        s_add(vI, vI, RI_I(1)),
        s_cmp_ge(vTMP, vI, RI_I(100)),
      ],
      vTMP,
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
    s_repeat_until(
      vec![
        s_add(s2v20, s2v20, RI_I(1)),
        s_add(s2v21, s2v21, RI_I(2)),
        s_add(s2v22, s2v22, RI_I(3)),
        s_add(vI, vI, RI_I(1)),
        s_cmp_ge(vTMP, vI, RI_I(100)),
      ],
      vTMP,
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
    s_print_s("\n"),
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
  let offs_stackLo = bif.newVirtualReg(RegClass::I32);
  let offs_stackHi = bif.newVirtualReg(RegClass::I32);
  let offs_numbers = bif.newVirtualReg(RegClass::I32);
  let nNumbers = bif.newVirtualReg(RegClass::I32);
  let rand = bif.newVirtualReg(RegClass::I32);
  let loSt = bif.newVirtualReg(RegClass::I32);
  let hiSt = bif.newVirtualReg(RegClass::I32);
  let keepGoingI = bif.newVirtualReg(RegClass::I32);
  let keepGoingO = bif.newVirtualReg(RegClass::I32);
  let unLo = bif.newVirtualReg(RegClass::I32);
  let unHi = bif.newVirtualReg(RegClass::I32);
  let ltLo = bif.newVirtualReg(RegClass::I32);
  let gtHi = bif.newVirtualReg(RegClass::I32);
  let n = bif.newVirtualReg(RegClass::I32);
  let m = bif.newVirtualReg(RegClass::I32);
  let sp = bif.newVirtualReg(RegClass::I32);
  let lo = bif.newVirtualReg(RegClass::I32);
  let hi = bif.newVirtualReg(RegClass::I32);
  let med = bif.newVirtualReg(RegClass::I32);
  let r3 = bif.newVirtualReg(RegClass::I32);
  let yyp1 = bif.newVirtualReg(RegClass::I32);
  let yyp2 = bif.newVirtualReg(RegClass::I32);
  let yyn = bif.newVirtualReg(RegClass::I32);
  let t0 = bif.newVirtualReg(RegClass::I32);
  let t1 = bif.newVirtualReg(RegClass::I32);
  let t2 = bif.newVirtualReg(RegClass::I32);
  let zztmp1 = bif.newVirtualReg(RegClass::I32);
  let zztmp2 = bif.newVirtualReg(RegClass::I32);
  let taa = bif.newVirtualReg(RegClass::I32);
  let tbb = bif.newVirtualReg(RegClass::I32);
  let i = bif.newVirtualReg(RegClass::I32);
  let inOrder = bif.newVirtualReg(RegClass::I32);
  let sum = bif.newVirtualReg(RegClass::I32);
  let pass = bif.newVirtualReg(RegClass::I32);
  let sp_gt_zero = bif.newVirtualReg(RegClass::I32);
  let guard = bif.newVirtualReg(RegClass::I32);

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
    s_repeat_until(
      vec![
        s_mul(t0, rand, RI_I(7621)),
        s_add(t0, t0, RI_I(1)),
        s_mod(rand, t0, RI_I(32768)),
        s_mod(t0, rand, RI_I(10000)),
        s_store(AM_RR(offs_numbers, i), t0),
        s_add(i, i, RI_I(1)),
        s_cmp_ge(guard, i, RI_R(nNumbers)),
      ],
      guard,
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
        s_if_then(
          t0,
          vec![
            s_mul(t0, rand, RI_I(7621)),
            s_add(t0, t0, RI_I(1)),
            s_mod(rand, t0, RI_I(32768)),
            s_mod(r3, rand, RI_I(3)),
            s_cmp_eq(t0, r3, RI_I(0)),
            s_if_then_else(
              t0,
              vec![s_load(med, AM_R(lo))],
              vec![
                s_cmp_eq(t0, r3, RI_I(1)),
                s_if_then_else(
                  t0,
                  vec![
                    s_add(t0, lo, RI_R(hi)),
                    s_shr(t0, t0, RI_I(1)),
                    s_load(med, AM_R(t0)),
                  ],
                  vec![s_load(med, AM_R(hi))],
                ),
              ],
            ),
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
                    s_if_then_else(
                      t0,
                      vec![
                        s_load(zztmp1, AM_R(unLo)),
                        s_load(zztmp2, AM_R(ltLo)),
                        s_store(AM_R(unLo), zztmp2),
                        s_store(AM_R(ltLo), zztmp1),
                        s_add(ltLo, ltLo, RI_I(1)),
                        s_add(unLo, unLo, RI_I(1)),
                      ],
                      vec![
                        s_cmp_gt(t0, t1, RI_R(med)),
                        s_if_then_else(
                          t0,
                          vec![s_imm(keepGoingI, 0)],
                          vec![s_add(unLo, unLo, RI_I(1))],
                        ),
                      ],
                    ),
                    s_cmp_le(guard, unLo, RI_R(unHi)),
                    s_and(guard, guard, RI_R(keepGoingI)),
                  ],
                ),
                s_imm(keepGoingI, 1),
                s_cmp_le(guard, unLo, RI_R(unHi)),
                s_while_do(
                  guard,
                  vec![
                    s_load(t1, AM_R(unHi)),
                    s_cmp_eq(t0, t1, RI_R(med)),
                    s_if_then_else(
                      t0,
                      vec![
                        s_load(zztmp1, AM_R(unHi)),
                        s_load(zztmp2, AM_R(gtHi)),
                        s_store(AM_R(unHi), zztmp2),
                        s_store(AM_R(gtHi), zztmp1),
                        s_sub(gtHi, gtHi, RI_I(1)),
                        s_sub(unHi, unHi, RI_I(1)),
                      ],
                      vec![
                        s_cmp_lt(t0, t1, RI_R(med)),
                        s_if_then_else(
                          t0,
                          vec![s_imm(keepGoingI, 0)],
                          vec![s_sub(unHi, unHi, RI_I(1))],
                        ),
                      ],
                    ),
                    s_cmp_le(guard, unLo, RI_R(unHi)),
                    s_and(guard, guard, RI_R(keepGoingI)),
                  ],
                ),
                s_cmp_gt(t0, unLo, RI_R(unHi)),
                s_if_then_else(
                  t0,
                  vec![s_imm(keepGoingO, 0)],
                  vec![
                    s_load(zztmp1, AM_R(unLo)),
                    s_load(zztmp2, AM_R(unHi)),
                    s_store(AM_R(unLo), zztmp2),
                    s_store(AM_R(unHi), zztmp1),
                    s_add(unLo, unLo, RI_I(1)),
                    s_sub(unHi, unHi, RI_I(1)),
                  ],
                ),
              ],
            ),
            s_sub(t0, unLo, RI_I(1)),
            s_cmp_eq(t0, unHi, RI_R(t0)),
            //////assert( t0 ),
            s_cmp_ge(t0, gtHi, RI_R(ltLo)),
            s_if_then(
              t0,
              vec![
                s_sub(taa, ltLo, RI_R(lo)),
                s_sub(tbb, unLo, RI_R(ltLo)),
                s_cmp_lt(t0, taa, RI_R(tbb)),
                s_if_then_else(t0, vec![s_copy(n, taa)], vec![s_copy(n, tbb)]),
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
                  ],
                ),
                s_sub(taa, hi, RI_R(gtHi)),
                s_sub(tbb, gtHi, RI_R(unHi)),
                s_cmp_lt(t0, taa, RI_R(tbb)),
                s_if_then_else(t0, vec![s_copy(m, taa)], vec![s_copy(m, tbb)]),
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
                  ],
                ),
                s_add(n, lo, RI_R(unLo)),
                s_sub(n, n, RI_R(ltLo)),
                s_sub(n, n, RI_I(1)),
                s_sub(m, gtHi, RI_R(unHi)),
                s_sub(m, hi, RI_R(m)),
                s_add(m, m, RI_I(1)),
                s_sub(t1, n, RI_R(lo)),
                s_sub(t2, hi, RI_R(m)),
                s_cmp_gt(t0, t1, RI_R(t2)),
                s_if_then_else(
                  t0,
                  vec![
                    s_store(AM_RR(offs_stackLo, sp), lo),
                    s_store(AM_RR(offs_stackHi, sp), n),
                    s_add(sp, sp, RI_I(1)),
                    s_store(AM_RR(offs_stackLo, sp), m),
                    s_store(AM_RR(offs_stackHi, sp), hi),
                    s_add(sp, sp, RI_I(1)),
                  ],
                  vec![
                    s_store(AM_RR(offs_stackLo, sp), m),
                    s_store(AM_RR(offs_stackHi, sp), hi),
                    s_add(sp, sp, RI_I(1)),
                    s_store(AM_RR(offs_stackLo, sp), lo),
                    s_store(AM_RR(offs_stackHi, sp), n),
                    s_add(sp, sp, RI_I(1)),
                  ],
                ),
              ],
            ),
          ],
        ), // end "if this work unit has more than one item"
        s_cmp_gt(sp_gt_zero, sp, RI_I(0)),
      ],
    ), // end outer loop
    // Check the results, as much as we reasonably can.
    s_imm(sum, 0),
    s_imm(inOrder, 1),
    s_load(sum, AM_R(offs_numbers)),
    s_add(i, offs_numbers, RI_I(1)),
    s_repeat_until(
      vec![
        s_load(t0, AM_R(i)),
        s_add(sum, sum, RI_R(t0)),
        s_sub(t2, i, RI_I(1)),
        s_load(t1, AM_R(t2)),
        s_cmp_gt(t2, t1, RI_R(t0)),
        s_if_then(t2, vec![s_imm(inOrder, 0)]),
        s_add(i, i, RI_I(1)),
        s_add(guard, offs_numbers, RI_R(nNumbers)),
        s_cmp_ge(guard, i, RI_R(guard)),
      ],
      guard,
    ),
    s_cmp_eq(pass, sum, RI_I(4272946)),
    s_and(pass, inOrder, RI_R(pass)),
    s_if_then_else(
      pass,
      vec![s_print_s("PASS (in order, and correct checksum)")],
      vec![s_print_s("FAIL (not in order, or incorrect checksum)")],
    ),
    s_print_s("\n"),
  ];

  bif.finish(stmts)
}

// This is a version of fill_then_sum that uses some 2-operand insns.
fn test__fill_then_sum_2a() -> Func {
  let mut func = Func::new("fill_then_sum_2a", "set-loop-pre");

  // Regs, virtual and real, that we want to use.
  let vNENT = func.newVirtualReg(RegClass::I32);
  let vI = func.newVirtualReg(RegClass::I32);
  let vSUM = func.newVirtualReg(RegClass::I32);
  let rTMP = mkRealReg(RegClass::I32, /*enc=*/ 0x42, /*index=*/ 2); // "2" is arbitrary.
  let vTMP2 = func.newVirtualReg(RegClass::I32);

  // Loop pre-header for filling array with numbers.
  // This is also the entry point.
  func.block(
    "set-loop-pre",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_imm(vNENT, 10),
      i_imm(vI, 0),
      i_goto("set-loop"),
    ]),
  );

  // Filling loop
  func.block(
    "set-loop",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_store(AM_R(vI), vI),
      i_addm(vI, RI_I(1)),
      i_cmp_lt(rTMP, vI, RI_R(vNENT)),
      i_goto_ctf(rTMP, "set-loop", "sum-loop-pre"),
    ]),
  );

  // Loop pre-header for summing them
  func.block(
    "sum-loop-pre",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_imm(vSUM, 0),
      i_imm(vI, 0),
      i_goto("sum-loop"),
    ]),
  );

  // Summing loop
  func.block(
    "sum-loop",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_load(rTMP, AM_R(vI)),
      i_addm(vSUM, RI_R(rTMP)),
      i_addm(vI, RI_I(1)),
      i_cmp_lt(vTMP2, vI, RI_R(vNENT)),
      i_goto_ctf(vTMP2, "sum-loop", "print-result"),
    ]),
  );

  // After loop.  Print result and stop.
  func.block(
    "print-result",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_print_s("Sum = "),
      i_print_i(vSUM),
      i_print_s("\n"),
      i_finish(),
    ]),
  );

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

  let lo = func.newVirtualReg(RegClass::I32);
  let hi = func.newVirtualReg(RegClass::I32);
  let i = func.newVirtualReg(RegClass::I32);
  let j = func.newVirtualReg(RegClass::I32);
  let h = func.newVirtualReg(RegClass::I32);
  let bigN = func.newVirtualReg(RegClass::I32);
  let v = func.newVirtualReg(RegClass::I32);
  let hp = func.newVirtualReg(RegClass::I32);
  let t0 = func.newVirtualReg(RegClass::I32);
  let zero = func.newVirtualReg(RegClass::I32);

  func.block(
    "Lstart",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_imm(zero, 0),
      // Store the increment table
      i_imm(t0, 1),
      i_store(AM_RI(zero, 0), t0),
      i_imm(t0, 4),
      i_store(AM_RI(zero, 1), t0),
      i_imm(t0, 13),
      i_store(AM_RI(zero, 2), t0),
      i_imm(t0, 40),
      i_store(AM_RI(zero, 3), t0),
      i_imm(t0, 121),
      i_store(AM_RI(zero, 4), t0),
      // Store the numbers to be sorted
      i_imm(t0, 30),
      i_store(AM_RI(zero, 5), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 6), t0),
      i_imm(t0, 31),
      i_store(AM_RI(zero, 7), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 8), t0),
      i_imm(t0, 32),
      i_store(AM_RI(zero, 9), t0),
      i_imm(t0, 66),
      i_store(AM_RI(zero, 10), t0),
      i_imm(t0, 77),
      i_store(AM_RI(zero, 11), t0),
      i_imm(t0, 44),
      i_store(AM_RI(zero, 12), t0),
      i_imm(t0, 22),
      i_store(AM_RI(zero, 13), t0),
      i_imm(t0, 11),
      i_store(AM_RI(zero, 14), t0),
      i_imm(t0, 99),
      i_store(AM_RI(zero, 15), t0),
      i_imm(t0, 11),
      i_store(AM_RI(zero, 16), t0),
      i_imm(t0, 12),
      i_store(AM_RI(zero, 17), t0),
      i_imm(t0, 7),
      i_store(AM_RI(zero, 18), t0),
      i_imm(t0, 9),
      i_store(AM_RI(zero, 19), t0),
      i_imm(t0, 2),
      i_store(AM_RI(zero, 20), t0),
      i_imm(t0, 32),
      i_store(AM_RI(zero, 21), t0),
      i_imm(t0, 23),
      i_store(AM_RI(zero, 22), t0),
      i_imm(t0, 41),
      i_store(AM_RI(zero, 23), t0),
      i_imm(t0, 14),
      i_store(AM_RI(zero, 24), t0),
      // The real computation begins here
      i_imm(lo, 5),  // Lowest address of the range to sort
      i_imm(hi, 24), // Highest address of the range to sort
      i_copy(t0, hi),
      i_subm(t0, RI_R(lo)),
      i_add(bigN, t0, RI_I(1)),
      i_imm(hp, 0),
      i_goto("L11"),
    ]),
  );

  func.block(
    "L11",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_load(t0, AM_R(hp)),
      i_cmp_gt(t0, t0, RI_R(bigN)),
      i_goto_ctf(t0, "L20", "L11a"),
    ]),
  );

  func.block(
    "L11a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_addm(hp, RI_I(1)),
      i_goto("L11"),
    ]),
  );

  func.block(
    "L20",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_cmp_lt(t0, hp, RI_I(1)),
      i_goto_ctf(t0, "L60", "L21a"),
    ]),
  );

  func.block(
    "L21a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_copy(t0, hp),
      i_subm(t0, RI_I(1)),
      i_load(h, AM_R(t0)),
      //printf("h = %u\n", h),
      i_copy(i, lo),
      i_addm(i, RI_R(h)),
      i_goto("L30"),
    ]),
  );

  func.block(
    "L30",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_cmp_gt(t0, i, RI_R(hi)),
      i_goto_ctf(t0, "L50", "L30a"),
    ]),
  );

  func.block(
    "L30a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_load(v, AM_R(i)),
      i_copy(j, i), // FIXME: is this a coalescable copy?
      i_goto("L40"),
    ]),
  );

  func.block(
    "L40",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_copy(t0, j),
      i_subm(t0, RI_R(h)),
      i_load(t0, AM_R(t0)),
      i_cmp_le(t0, t0, RI_R(v)),
      i_goto_ctf(t0, "L45", "L40a"),
    ]),
  );

  func.block(
    "L40a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
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
    ]),
  );

  func.block(
    "L45",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_store(AM_R(j), v),
      i_addm(i, RI_I(1)),
      i_goto("L30"),
    ]),
  );

  func.block(
    "L50",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_subm(hp, RI_I(1)),
      i_goto("L20"),
    ]),
  );

  func.block(
    "L60",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_copy(i, lo), // FIXME: ditto
      i_goto("L61"),
    ]),
  );

  func.block(
    "L61",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_cmp_gt(t0, i, RI_R(hi)),
      i_goto_ctf(t0, "L62", "L61a"),
    ]),
  );

  func.block(
    "L61a",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![
      i_load(t0, AM_R(i)),
      i_print_i(t0),
      i_print_s(" "),
      i_addm(i, RI_I(1)),
      i_goto("L61"),
    ]),
  );

  func.block(
    "L62",
    TypedIxVec::<InstIx, Inst>::fromVec(vec![i_print_s("\n"), i_finish()]),
  );

  func.finish();
  func
}

// This is the list of available tests.  This function returns either the
// requested Func, or if not found, a list of the available ones.
pub fn find_Func(name: &str) -> Result<Func, Vec<String>> {
  // This is really stupid.  Fortunately it's not performance critical :)
  let all_Funcs = vec![
    test__badness(),          // Whatever the current badness is
    test__straight_line(),    // straight_line
    test__fill_then_sum(),    // fill_then_sum
    test__ssort(),            // shellsort
    test__3_loops(),          // three loops
    test__stmts(),            // a small Stmty test
    test__needs_splitting(),  // LR splitting might help here ..
    test__needs_splitting2(), // .. same, but with LRs split by hand
    test__qsort(),            // big qsort test, 3-operand only
    test__fill_then_sum_2a(), // 2-operand version of fill_then_sum
    test__ssort_2a(),         // 2-operand version of shellsort
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
