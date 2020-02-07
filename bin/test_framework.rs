/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

/// As part of this set of test cases, we define a mini IR and implement the
/// `Function` trait for it so that we can use the regalloc public interface.
use regalloc::{
  BlockIx, InstIx, Map, MyRange, RealReg, RealRegUniverse, Reg, RegClass, Set,
  SpillSlot, TypedIxVec, VirtualReg, NUM_REG_CLASSES,
};

use std::fmt;

//=============================================================================
// Definition of: Label, RI (reg-or-immediate operands), AM (address modes),
// and Inst (instructions).  Also the get-regs and map-regs operations for
// them.  Destinations are on the left.

#[derive(Clone)]
pub enum Label {
  Unresolved { name: String },
  Resolved { name: String, bix: BlockIx },
}
impl fmt::Debug for Label {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Label::Unresolved { name } => write!(fmt, "??:{}", &name),
      Label::Resolved { name, bix } => write!(fmt, "{:?}:{}", bix, name),
    }
  }
}
impl Label {
  pub fn newUnresolved(name: String) -> Label {
    Label::Unresolved { name }
  }
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
  fn apply_defs_or_uses(&mut self, map: &Map<VirtualReg, RealReg>) {
    match self {
      RI::Reg { ref mut reg } => {
        reg.apply_defs_or_uses(map);
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
      AM::RI { base, offset } => write!(fmt, "[{:?}, {:?}]", base, offset),
      AM::RR { base, offset } => write!(fmt, "[{:?}, {:?}]", base, offset),
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
  fn apply_defs_or_uses(&mut self, map: &Map<VirtualReg, RealReg>) {
    match self {
      AM::RI { ref mut base, .. } => {
        base.apply_defs_or_uses(map);
      }
      AM::RR { ref mut base, ref mut offset } => {
        base.apply_defs_or_uses(map);
        offset.apply_defs_or_uses(map);
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
  pub fn calc(self, argL: f32, argR: f32) -> f32 {
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
  CopyF { dst: Reg, src: Reg },
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
  Finish { reg: Option<Reg> },
}

pub fn i_imm(dst: Reg, imm: u32) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::Imm { dst, imm }
}
pub fn i_immf(dst: Reg, imm: f32) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  Inst::ImmF { dst, imm }
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
pub fn i_loadf(dst: Reg, addr: AM) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  Inst::LoadF { dst, addr }
}
pub fn i_store(addr: AM, src: Reg) -> Inst {
  debug_assert!(src.get_class() == RegClass::I32);
  Inst::Store { addr, src }
}
pub fn i_storef(addr: AM, src: Reg) -> Inst {
  debug_assert!(src.get_class() == RegClass::F32);
  Inst::StoreF { addr, src }
}
fn i_spill(dst: SpillSlot, src: RealReg) -> Inst {
  debug_assert!(src.get_class() == RegClass::I32);
  Inst::Spill { dst, src }
}
fn i_spillf(dst: SpillSlot, src: RealReg) -> Inst {
  debug_assert!(src.get_class() == RegClass::F32);
  Inst::SpillF { dst, src }
}
fn i_reload(dst: RealReg, src: SpillSlot) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::Reload { dst, src }
}
fn i_reloadf(dst: RealReg, src: SpillSlot) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  Inst::ReloadF { dst, src }
}
pub fn i_goto<'a>(target: &'a str) -> Inst {
  Inst::Goto { target: Label::newUnresolved(target.to_string()) }
}
pub fn i_goto_ctf<'a>(cond: Reg, targetT: &'a str, targetF: &'a str) -> Inst {
  debug_assert!(cond.get_class() == RegClass::I32);
  Inst::GotoCTF {
    cond,
    targetT: Label::newUnresolved(targetT.to_string()),
    targetF: Label::newUnresolved(targetF.to_string()),
  }
}
pub fn i_print_s<'a>(str: &'a str) -> Inst {
  Inst::PrintS { str: str.to_string() }
}
pub fn i_print_i(reg: Reg) -> Inst {
  debug_assert!(reg.get_class() == RegClass::I32);
  Inst::PrintI { reg }
}
pub fn i_print_f(reg: Reg) -> Inst {
  debug_assert!(reg.get_class() == RegClass::F32);
  Inst::PrintF { reg }
}
pub fn i_finish(reg: Option<Reg>) -> Inst {
  Inst::Finish { reg }
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
      Inst::CopyF { dst, src } => write!(fmt, "copyf   {:?}, {:?}", dst, src),
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
        let mut res = "prints  '".to_string();
        for c in str.chars() {
          res += &(if c == '\n' { "\\n".to_string() } else { c.to_string() });
        }
        write!(fmt, "{}'", res)
      }
      Inst::PrintI { reg } => write!(fmt, "printi  {:?}", reg),
      Inst::PrintF { reg } => write!(fmt, "printf  {:?}", reg),
      Inst::Finish { reg } => write!(fmt, "finish  {:?}", reg),
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
      Inst::Finish { reg: _ } => vec![],
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
      Inst::ImmF { dst, imm: _ } => {
        def.insert(*dst);
      }
      Inst::Copy { dst, src } => {
        def.insert(*dst);
        uce.insert(*src);
      }
      Inst::CopyF { dst, src } => {
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
      Inst::BinOpF { op: _, dst, srcL, srcR } => {
        def.insert(*dst);
        uce.insert(*srcL);
        uce.insert(*srcR);
      }
      Inst::Store { addr, src } => {
        addr.addRegReadsTo(&mut uce);
        uce.insert(*src);
      }
      Inst::StoreF { addr, src } => {
        addr.addRegReadsTo(&mut uce);
        uce.insert(*src);
      }
      Inst::Load { dst, addr } => {
        def.insert(*dst);
        addr.addRegReadsTo(&mut uce);
      }
      Inst::LoadF { dst, addr } => {
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
      Inst::PrintF { reg } => {
        uce.insert(*reg);
      }
      Inst::Finish { reg } => {
        if let Some(reg) = reg {
          uce.insert(*reg);
        }
      }
      // Spill and Reload are seen here during the final pass over insts that
      // computes clobbered regs.
      Inst::Spill { src, .. } | Inst::SpillF { src, .. } => {
        uce.insert(src.to_reg());
      }
      Inst::Reload { dst, .. } | Inst::ReloadF { dst, .. } => {
        def.insert(dst.to_reg());
      }
    }
    // Failure of either of these is serious and should be investigated.
    debug_assert!(!def.intersects(&m0d));
    debug_assert!(!uce.intersects(&m0d));
    (def, m0d, uce)
  }

  // Apply the specified VirtualReg->RealReg mappings to the instruction,
  // thusly:
  // * For registers mentioned in a read role, apply map_uses.
  // * For registers mentioned in a write role, apply map_defs.
  // * For registers mentioned in a modify role, map_uses and map_defs *must* agree
  //   (if not, our caller is buggy).  So apply either map to that register.
  pub fn mapRegs_D_U(
    &mut self, map_defs: &Map<VirtualReg, RealReg>,
    map_uses: &Map<VirtualReg, RealReg>,
  ) {
    let mut ok = true;
    match self {
      Inst::Imm { dst, imm: _ } => {
        dst.apply_defs_or_uses(map_defs);
      }
      Inst::ImmF { dst, imm: _ } => {
        dst.apply_defs_or_uses(map_defs);
      }
      Inst::Copy { dst, src } => {
        dst.apply_defs_or_uses(map_defs);
        src.apply_defs_or_uses(map_uses);
      }
      Inst::BinOp { op: _, dst, srcL, srcR } => {
        dst.apply_defs_or_uses(map_defs);
        srcL.apply_defs_or_uses(map_uses);
        srcR.apply_defs_or_uses(map_uses);
      }
      Inst::BinOpM { op: _, dst, srcR } => {
        dst.apply_mods(map_defs, map_uses);
        srcR.apply_defs_or_uses(map_uses);
      }
      Inst::BinOpF { op: _, dst, srcL, srcR } => {
        dst.apply_defs_or_uses(map_defs);
        srcL.apply_defs_or_uses(map_uses);
        srcR.apply_defs_or_uses(map_uses);
      }
      Inst::Store { addr, src } => {
        addr.apply_defs_or_uses(map_uses);
        src.apply_defs_or_uses(map_uses);
      }
      Inst::StoreF { addr, src } => {
        addr.apply_defs_or_uses(map_uses);
        src.apply_defs_or_uses(map_uses);
      }
      Inst::Load { dst, addr } => {
        dst.apply_defs_or_uses(map_defs);
        addr.apply_defs_or_uses(map_uses);
      }
      Inst::LoadF { dst, addr } => {
        dst.apply_defs_or_uses(map_defs);
        addr.apply_defs_or_uses(map_uses);
      }
      Inst::Goto { .. } => {}
      Inst::GotoCTF { cond, targetT: _, targetF: _ } => {
        cond.apply_defs_or_uses(map_uses);
      }
      Inst::PrintS { .. } => {}
      Inst::PrintI { reg } => {
        reg.apply_defs_or_uses(map_uses);
      }
      Inst::PrintF { reg } => {
        reg.apply_defs_or_uses(map_uses);
      }
      Inst::Finish { reg } => {
        if let Some(reg) = reg {
          reg.apply_defs_or_uses(map_uses);
        }
      }
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
    Inst::Goto { .. } | Inst::GotoCTF { .. } | Inst::Finish { reg: _ } => true,
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
// The interpreter

#[derive(Copy, Clone, PartialEq)]
pub enum Value {
  U32(u32),
  F32(f32),
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
pub enum RunStage {
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
  ret_value: Option<Value>,
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
      ret_value: None,
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

  fn set_real_reg(&mut self, rreg: RealReg, val: Value) {
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

  fn set_virtual_reg(&mut self, vreg: VirtualReg, val: Value) {
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

  fn get_spill_slot(&self, slot: SpillSlot) -> Value {
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

  fn set_spill_slot_u32(&mut self, slot: SpillSlot, val: u32) {
    // Auto-resize the vector if necessary
    let ix = slot.get_usize();
    if ix >= self.slots.len() {
      self.slots.resize(ix + 1, None);
    }
    debug_assert!(ix < self.slots.len());
    self.slots[ix] = Some(Value::U32(val));
  }

  fn set_spill_slot_f32(&mut self, slot: SpillSlot, val: f32) {
    // Auto-resize the vector if necessary
    let ix = slot.get_usize();
    if ix >= self.slots.len() {
      self.slots.resize(ix + 1, None);
    }
    debug_assert!(ix < self.slots.len());
    self.slots[ix] = Some(Value::F32(val));
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
      self.set_virtual_reg(reg.to_virtual_reg(), Value::U32(val));
    } else {
      self.set_real_reg(reg.to_real_reg(), Value::U32(val));
    }
  }

  fn set_reg_f32(&mut self, reg: Reg, val: f32) {
    if reg.is_virtual() {
      self.set_virtual_reg(reg.to_virtual_reg(), Value::F32(val));
    } else {
      self.set_real_reg(reg.to_real_reg(), Value::F32(val));
    }
  }

  fn get_mem(&self, addr: u32) -> Value {
    // No auto resizing of the memory
    match self.mem.get(addr as usize) {
      None => panic!("IState::getMem: invalid addr {}", addr),
      Some(None) => {
        panic!("IState::getMem: read of uninit mem at addr {}", addr)
      }
      Some(Some(val)) => *val,
    }
  }

  fn set_mem_u32(&mut self, addr: u32, val: u32) {
    // No auto resizing of the memory
    match self.mem.get_mut(addr as usize) {
      None => panic!("IState::setMemU32: invalid addr {}", addr),
      Some(valP) => *valP = Some(Value::U32(val)),
    }
  }

  fn set_mem_f32(&mut self, addr: u32, val: f32) {
    // No auto resizing of the memory
    match self.mem.get_mut(addr as usize) {
      None => panic!("IState::setMemF32: invalid addr {}", addr),
      Some(valP) => *valP = Some(Value::F32(val)),
    }
  }

  fn get_RI(&self, ri: &RI) -> u32 {
    match ri {
      RI::Reg { reg } => self.get_reg(*reg).toU32(),
      RI::Imm { imm } => *imm,
    }
  }

  fn get_AM(&self, am: &AM) -> u32 {
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
      Inst::ImmF { dst, imm } => self.set_reg_f32(*dst, *imm),
      Inst::Copy { dst, src } => {
        self.set_reg_u32(*dst, self.get_reg(*src).toU32())
      }
      Inst::CopyF { dst, src } => {
        self.set_reg_f32(*dst, self.get_reg(*src).toF32())
      }
      Inst::BinOp { op, dst, srcL, srcR } => {
        let srcL_v = self.get_reg(*srcL).toU32();
        let srcR_v = self.get_RI(srcR);
        let dst_v = op.calc(srcL_v, srcR_v);
        self.set_reg_u32(*dst, dst_v);
      }
      Inst::BinOpM { op, dst, srcR } => {
        let mut dst_v = self.get_reg(*dst).toU32();
        let srcR_v = self.get_RI(srcR);
        dst_v = op.calc(dst_v, srcR_v);
        self.set_reg_u32(*dst, dst_v);
      }
      Inst::BinOpF { op, dst, srcL, srcR } => {
        let srcL_v = self.get_reg(*srcL).toF32();
        let srcR_v = self.get_reg(*srcR).toF32();
        let dst_v = op.calc(srcL_v, srcR_v);
        self.set_reg_f32(*dst, dst_v);
      }
      Inst::Load { dst, addr } => {
        let addr_v = self.get_AM(addr);
        let dst_v = self.get_mem(addr_v).toU32();
        self.set_reg_u32(*dst, dst_v);
      }
      Inst::LoadF { dst, addr } => {
        let addr_v = self.get_AM(addr);
        let dst_v = self.get_mem(addr_v).toF32();
        self.set_reg_f32(*dst, dst_v);
      }
      Inst::Store { addr, src } => {
        let addr_v = self.get_AM(addr);
        let src_v = self.get_reg(*src).toU32();
        self.set_mem_u32(addr_v, src_v);
      }
      Inst::StoreF { addr, src } => {
        let addr_v = self.get_AM(addr);
        let src_v = self.get_reg(*src).toF32();
        self.set_mem_f32(addr_v, src_v);
      }
      Inst::Spill { dst, src } => {
        let src_v = self.get_real_reg(*src).toU32();
        self.set_spill_slot_u32(*dst, src_v);
        self.n_spills += 1;
      }
      Inst::SpillF { dst, src } => {
        let src_v = self.get_real_reg(*src).toF32();
        self.set_spill_slot_f32(*dst, src_v);
        self.n_spills += 1;
      }
      Inst::Reload { dst, src } => {
        let src_v = self.get_spill_slot(*src).toU32();
        self.set_reg_u32(dst.to_reg(), src_v);
        self.n_reloads += 1;
      }
      Inst::ReloadF { dst, src } => {
        let src_v = self.get_spill_slot(*src).toF32();
        self.set_reg_f32(dst.to_reg(), src_v);
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
      Inst::PrintF { reg } => print!("{:?}", self.get_reg(*reg).toF32()),
      Inst::Finish { reg } => {
        self.ret_value = reg.map(|reg| self.get_reg(reg));
        done = true;
      }
    }
    done
  }
}

pub fn run_func(
  f: &Func, who: &str, reg_universe: &RealRegUniverse, run_stage: RunStage,
) -> Option<Value> {
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

  istate.ret_value
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
impl Block {
  pub fn new(name: String, start: InstIx, len: u32) -> Self {
    Self { name, start, len, estFreq: 1 }
  }
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

#[derive(Debug)]
pub struct Func {
  pub name: String,
  pub entry: Label,
  pub nVirtualRegs: u32,
  pub insns: TypedIxVec<InstIx, Inst>, // indexed by InstIx

  // Note that |blocks| must be in order of increasing |Block::start|
  // fields.  Code that wants to traverse the blocks in some other order
  // must represent the ordering some other way; rearranging Func::blocks is
  // not allowed.
  pub blocks: TypedIxVec<BlockIx, Block>, // indexed by BlockIx
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
      return BlockIx::new(bix);
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
      println!("  {:?}:{}", BlockIx::new(ix), b.name);
      for i in b.start.get()..b.start.get() + b.len {
        let ixI = InstIx::new(i);
        println!("      {:<3?}   {:?}", ixI, self.insns[ixI]);
      }
      ix += 1;
    }
    println!("}}");
  }

  // Get a new VirtualReg name
  pub fn new_virtual_reg(&mut self, rc: RegClass) -> Reg {
    let v = Reg::new_virtual(rc, self.nVirtualRegs);
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
    let b = Block::new(name.to_string(), InstIx::new(start), len);
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
    for bix in BlockIx::new(0).dotdot(BlockIx::new(self.blocks.len())) {
      let b = &self.blocks[bix];
      if b.len == 0 {
        panic!("Func::done: a block is empty");
      }
      if bix > BlockIx::new(0)
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

  pub fn update_from_alloc(&mut self, result: regalloc::RegAllocResult<Func>) {
    self.insns = TypedIxVec::from_vec(result.insns);
    let num_blocks = self.blocks.len();
    let mut i = 0;
    for bix in self.blocks.range() {
      let block = &mut self.blocks[bix];
      block.start = result.target_map[bix];
      block.len = if i + 1 < num_blocks {
        result.target_map[BlockIx::new(i + 1)].get()
      } else {
        self.insns.len()
      } - block.start.get();
      i += 1;
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

pub enum Stmt {
  Vanilla { insn: Inst },
  IfThenElse { cond: Reg, stmts_t: Vec<Stmt>, stmts_e: Vec<Stmt> },
  RepeatUntil { stmts: Vec<Stmt>, cond: Reg },
  WhileDo { cond: Reg, stmts: Vec<Stmt> },
}

// Various handy wrappers, mostly wrappings of i_* functions
pub fn s_if_then_else(
  cond: Reg, stmts_t: Vec<Stmt>, stmts_e: Vec<Stmt>,
) -> Stmt {
  Stmt::IfThenElse { cond, stmts_t, stmts_e }
}
pub fn s_if_then(cond: Reg, stmts_t: Vec<Stmt>) -> Stmt {
  Stmt::IfThenElse { cond, stmts_t, stmts_e: vec![] }
}
pub fn s_repeat_until(stmts: Vec<Stmt>, cond: Reg) -> Stmt {
  Stmt::RepeatUntil { stmts, cond }
}
pub fn s_while_do(cond: Reg, stmts: Vec<Stmt>) -> Stmt {
  Stmt::WhileDo { cond, stmts }
}

fn s_vanilla(insn: Inst) -> Stmt {
  Stmt::Vanilla { insn }
}

pub fn s_imm(dst: Reg, imm: u32) -> Stmt {
  s_vanilla(i_imm(dst, imm))
}
pub fn s_immf(dst: Reg, imm: f32) -> Stmt {
  s_vanilla(i_immf(dst, imm))
}
pub fn s_copy(dst: Reg, src: Reg) -> Stmt {
  s_vanilla(i_copy(dst, src))
}
pub fn s_load(dst: Reg, addr: AM) -> Stmt {
  s_vanilla(i_load(dst, addr))
}
pub fn s_loadf(dst: Reg, addr: AM) -> Stmt {
  s_vanilla(i_loadf(dst, addr))
}
pub fn s_store(addr: AM, src: Reg) -> Stmt {
  s_vanilla(i_store(addr, src))
}
pub fn s_storef(addr: AM, src: Reg) -> Stmt {
  s_vanilla(i_storef(addr, src))
}
pub fn s_print_s<'a>(str: &'a str) -> Stmt {
  s_vanilla(i_print_s(str))
}
pub fn s_print_i(reg: Reg) -> Stmt {
  s_vanilla(i_print_i(reg))
}
pub fn s_print_f(reg: Reg) -> Stmt {
  s_vanilla(i_print_f(reg))
}

pub fn s_add(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_add(dst, srcL, srcR))
}
pub fn s_sub(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_sub(dst, srcL, srcR))
}
pub fn s_mul(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_mul(dst, srcL, srcR))
}
pub fn s_mod(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_mod(dst, srcL, srcR))
}
pub fn s_shr(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_shr(dst, srcL, srcR))
}
pub fn s_and(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_and(dst, srcL, srcR))
}
pub fn s_cmp_eq(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_eq(dst, srcL, srcR))
}
pub fn s_cmp_lt(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_lt(dst, srcL, srcR))
}
pub fn s_cmp_le(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_le(dst, srcL, srcR))
}
pub fn s_cmp_ge(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_ge(dst, srcL, srcR))
}
pub fn s_cmp_gt(dst: Reg, srcL: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_cmp_gt(dst, srcL, srcR))
}

pub fn s_addm(dst: Reg, srcR: RI) -> Stmt {
  s_vanilla(i_addm(dst, srcR))
}
//fn s_subm(dst: Reg, srcR: RI) -> Stmt {
//  s_vanilla(i_subm(dst, srcR))
//}

pub fn s_fadd(dst: Reg, srcL: Reg, srcR: Reg) -> Stmt {
  s_vanilla(i_fadd(dst, srcL, srcR))
}
pub fn s_fsub(dst: Reg, srcL: Reg, srcR: Reg) -> Stmt {
  s_vanilla(i_fsub(dst, srcL, srcR))
}
pub fn s_fmul(dst: Reg, srcL: Reg, srcR: Reg) -> Stmt {
  s_vanilla(i_fmul(dst, srcL, srcR))
}
pub fn s_fdiv(dst: Reg, srcL: Reg, srcR: Reg) -> Stmt {
  s_vanilla(i_fdiv(dst, srcL, srcR))
}

//=============================================================================
// The "blockifier".  This is just to make it easier to write test cases, by
// allowing direct use of if-then-else, do-while and repeat-until.  It is
// otherwise entirely unrelated to the register allocator proper.

pub struct Blockifier {
  name: String,
  blocks: Vec<TypedIxVec<InstIx, Inst>>,
  nVirtualRegs: u32,
}

fn makeTextLabelStr(n: usize) -> String {
  "L".to_string() + &n.to_string()
}

impl Blockifier {
  pub fn new<'a>(name: &'a str) -> Self {
    Self { name: name.to_string(), blocks: vec![], nVirtualRegs: 0 }
  }

  // Get a new VirtualReg name
  pub fn new_virtual_reg(&mut self, rc: RegClass) -> Reg {
    let v = Reg::new_virtual(rc, self.nVirtualRegs);
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
          self.blocks[t_exit].push(i_goto(&makeTextLabelStr(cont)));
          self.blocks[e_exit].push(i_goto(&makeTextLabelStr(cont)));
          self.blocks[currBNo].push(i_goto_ctf(
            cond,
            &makeTextLabelStr(t_ent),
            &makeTextLabelStr(e_ent),
          ));
          currBNo = cont;
        }
        Stmt::RepeatUntil { stmts, cond } => {
          let (s_ent, s_exit) = self.blockify(stmts);
          self.blocks[currBNo].push(i_goto(&makeTextLabelStr(s_ent)));
          let cont = self.blocks.len();
          self.blocks.push(TypedIxVec::<InstIx, Inst>::new());
          self.blocks[s_exit].push(i_goto_ctf(
            cond,
            &makeTextLabelStr(cont),
            &makeTextLabelStr(s_ent),
          ));
          currBNo = cont;
        }
        Stmt::WhileDo { cond, stmts } => {
          let condblock = self.blocks.len();
          self.blocks.push(TypedIxVec::<InstIx, Inst>::new());
          self.blocks[currBNo].push(i_goto(&makeTextLabelStr(condblock)));
          let (s_ent, s_exit) = self.blockify(stmts);
          self.blocks[s_exit].push(i_goto(&makeTextLabelStr(condblock)));
          let cont = self.blocks.len();
          self.blocks.push(TypedIxVec::<InstIx, Inst>::new());
          self.blocks[condblock].push(i_goto_ctf(
            cond,
            &makeTextLabelStr(s_ent),
            &makeTextLabelStr(cont),
          ));
          currBNo = cont;
        }
      }
    }
    (entryBNo, currBNo)
  }

  // The main external function.  Convert the given statements, into a Func.
  pub fn finish(&mut self, stmts: Vec<Stmt>) -> Func {
    let (ent_bno, exit_bno) = self.blockify(stmts);
    self.blocks[exit_bno].push(i_finish(None));

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
          if let Some(targetLabel) = is_goto_insn(&b[InstIx::new(0)]) {
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
                for j in InstIx::new(0).dotdot(InstIx::new(mmm)) {
                  remapControlFlowTarget(
                    &mut insns[j],
                    &makeTextLabelStr(from),
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
    let mut func = Func::new(&self.name, &makeTextLabelStr(ent_bno));
    func.nVirtualRegs = 3; // or whatever
    let mut n = 0;
    for mb_ivec in cleanedUp {
      if let Some(ivec) = mb_ivec {
        func.block(&makeTextLabelStr(n), ivec);
      }
      n += 1;
    }

    func.finish();

    func
  }
}

// --------------------------------------------------
// Implementation of `Function` trait for test cases.

impl regalloc::Function for Func {
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
    BlockIx::new(0)
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

  fn is_ret(&self, insn: InstIx) -> bool {
    match &self.insns[insn] {
      &Inst::Finish { .. } => true,
      _ => false,
    }
  }

  /// Provide the defined, used, and modified registers for an instruction.
  fn get_regs(&self, insn: &Self::Inst) -> regalloc::InstRegUses {
    let (d, m, u) = insn.get_reg_usage();
    regalloc::InstRegUses { used: u, defined: d, modified: m }
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
  fn get_spillslot_size(
    &self, _regclass: RegClass, _for_vreg: VirtualReg,
  ) -> u32 {
    // For our simple test ISA, every value occupies one spill slot.
    1
  }

  /// Generate a spill instruction for insertion into the instruction sequence.
  fn gen_spill(
    &self, to_slot: SpillSlot, from_reg: RealReg, _for_vreg: VirtualReg,
  ) -> Vec<Self::Inst> {
    match from_reg.get_class() {
      RegClass::I32 => vec![i_spill(to_slot, from_reg)],
      RegClass::F32 => vec![i_spillf(to_slot, from_reg)],
      _ => panic!("Unused register class in test ISA was used"),
    }
  }

  /// Generate a reload instruction for insertion into the instruction sequence.
  fn gen_reload(
    &self, to_reg: RealReg, from_slot: SpillSlot, _for_vreg: VirtualReg,
  ) -> Vec<Self::Inst> {
    match to_reg.get_class() {
      RegClass::I32 => vec![i_reload(to_reg, from_slot)],
      RegClass::F32 => vec![i_reloadf(to_reg, from_slot)],
      _ => panic!("Unused register class in test ISA was used"),
    }
  }

  /// Generate a register-to-register move for insertion into the instruction
  /// sequence.
  fn gen_move(
    &self, to_reg: RealReg, from_reg: RealReg, _for_vreg: VirtualReg,
  ) -> Self::Inst {
    match to_reg.get_class() {
      RegClass::I32 => {
        Inst::Copy { src: from_reg.to_reg(), dst: to_reg.to_reg() }
      }
      RegClass::F32 => {
        Inst::CopyF { src: from_reg.to_reg(), dst: to_reg.to_reg() }
      }
      _ => unimplemented!("gen_move for non i32/f32"),
    }
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
    &self, _insn: &Self::Inst, _reg: VirtualReg, _slot: SpillSlot,
  ) -> Option<Self::Inst> {
    // test ISA does not have register-memory ALU instruction forms.
    None
  }

  fn func_liveins(&self) -> Set<RealReg> {
    Set::empty()
  }

  fn func_liveouts(&self) -> Set<RealReg> {
    Set::empty()
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
      let reg = Reg::new_real(RegClass::I32, /*enc=*/ 0, index).to_real_reg();
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
      let reg = Reg::new_real(RegClass::F32, /*enc=*/ 0, index).to_real_reg();
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
