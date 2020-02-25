//! Implements fuzzing primitives for everything.

use arbitrary::{Arbitrary, Result, Unstructured};
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

use crate::test_framework::{self as ir, *};
use regalloc::*;

pub const NUM_REAL_REGS_PER_RC: u8 = 8;
const NUM_REG_CLASSES: u32 = 5;

struct FuzzingEnv {
  num_blocks: u8,
  num_virtual_regs: u16,
  /// Map of virtual register index to register class. None means the register hasn't been ever defined.
  vregs: HashMap<u16, RegClass>,
  /// Really a hashmap from rc to HashSet<Reg>.
  regs_by_rc: Vec<HashSet<Reg>>,
  vregs_by_rc: Vec<HashSet<u16>>,
}

impl FuzzingEnv {
  fn block(&self, u: &mut Unstructured) -> Result<BlockIx> {
    Ok(BlockIx::new((u8::arbitrary(u)? % self.num_blocks) as u32))
  }

  fn label(&self, u: &mut Unstructured) -> Result<Label> {
    Ok(Label::Resolved { name: "(label???)".to_string(), bix: self.block(u)? })
  }

  fn has_reg_with_rc(&self, rc: RegClass) -> bool {
    !self.regs_by_rc[rc as usize].is_empty()
  }

  fn can_have_reg(&self, rc: RegClass) -> bool {
    self.has_reg_with_rc(rc)
      || self.vregs.len() != (self.num_virtual_regs as usize)
  }

  fn can_have_vreg(&self, rc: RegClass) -> bool {
    !self.vregs_by_rc[rc as usize].is_empty()
      || self.vregs.len() != (self.num_virtual_regs as usize)
  }

  fn def_reg(&mut self, rc: RegClass, u: &mut Unstructured) -> Result<Reg> {
    debug_assert!(self.can_have_reg(rc));
    let reg = if self.can_have_vreg(rc) && bool::arbitrary(u)? {
      // virtual.
      let mut index = u16::arbitrary(u)? % self.num_virtual_regs;
      while self.vregs.contains_key(&index) && self.vregs[&index] != rc {
        // linear probing!
        index = (index + 1) % self.num_virtual_regs;
      }
      self.vregs.insert(index, rc);
      self.vregs_by_rc[rc as usize].insert(index);
      Reg::new_virtual(rc, index as u32)
    } else {
      // real.
      // TODO there's insider knowledge about the real reg universe stuck here.
      let index = match rc {
        RegClass::I32 => 0,
        RegClass::F32 => 8,
        _ => panic!("unexpected rc"),
      } + u8::arbitrary(u)? % NUM_REAL_REGS_PER_RC;
      Reg::new_real(rc, 0x0, index)
    };
    self.regs_by_rc[rc as usize].insert(reg);
    Ok(reg)
  }

  fn mod_reg(&mut self, rc: RegClass, u: &mut Unstructured) -> Result<Reg> {
    let reg = self.get_reg(rc, u)?;
    if reg.is_virtual() {
      self.vregs.insert(reg.get_index() as u16, rc);
    }
    self.regs_by_rc[rc as usize].insert(reg);
    Ok(reg)
  }

  fn get_reg(&self, rc: RegClass, u: &mut Unstructured) -> Result<Reg> {
    debug_assert!(self.has_reg_with_rc(rc));
    let regs = Vec::from_iter(self.regs_by_rc[rc as usize].iter());
    let reg = *regs[usize::arbitrary(u)? % regs.len()];
    Ok(reg)
  }

  fn get_ri(&self, u: &mut Unstructured) -> Result<RI> {
    Ok(if self.has_reg_with_rc(RegClass::I32) && bool::arbitrary(u)? {
      RI::Reg { reg: self.get_reg(RegClass::I32, u)? }
    } else {
      RI::Imm { imm: u32::arbitrary(u)? }
    })
  }

  fn get_am(&self, u: &mut Unstructured) -> Result<AM> {
    debug_assert!(self.has_reg_with_rc(RegClass::I32));
    let base = self.get_reg(RegClass::I32, u)?;
    Ok(if bool::arbitrary(u)? {
      // RI
      AM::RI { base, offset: u32::arbitrary(u)? }
    } else {
      // RR
      let offset = self.get_reg(RegClass::I32, u)?;
      AM::RR { base, offset }
    })
  }

  fn inst(&mut self, u: &mut Unstructured) -> Result<Inst> {
    use Inst::*;
    use RegClass::*;

    enum AllowedInst {
      Imm,
      ImmF,
      Copy,
      CopyF,
      BinOp,
      BinOpM,
      BinOpF,
      Load,
      LoadF,
      Store,
      StoreF,
    }

    let mut allowed_insts = Vec::new();
    if self.can_have_reg(I32) {
      allowed_insts.push(AllowedInst::Imm);
    }
    if self.can_have_reg(F32) {
      allowed_insts.push(AllowedInst::ImmF);
    }
    if self.has_reg_with_rc(I32) {
      allowed_insts.push(AllowedInst::Copy);
      allowed_insts.push(AllowedInst::BinOp);
      allowed_insts.push(AllowedInst::BinOpM);
      allowed_insts.push(AllowedInst::Load);
      allowed_insts.push(AllowedInst::Store);
      if self.can_have_reg(F32) {
        allowed_insts.push(AllowedInst::LoadF);
      }
      if self.has_reg_with_rc(F32) {
        allowed_insts.push(AllowedInst::StoreF);
      }
    }
    if self.has_reg_with_rc(F32) {
      allowed_insts.push(AllowedInst::CopyF);
      allowed_insts.push(AllowedInst::BinOpF);
    }

    debug_assert!(!allowed_insts.is_empty());

    let index = u8::arbitrary(u)? as usize % (allowed_insts.len() + 1);
    if index == allowed_insts.len() {
      return self.inst_control_flow(u);
    }

    Ok(match allowed_insts[index] {
      AllowedInst::Imm => {
        Imm { dst: self.def_reg(I32, u)?, imm: u32::arbitrary(u)? }
      }
      AllowedInst::ImmF => {
        ImmF { dst: self.def_reg(F32, u)?, imm: f32::arbitrary(u)? }
      }
      AllowedInst::Copy => {
        Copy { dst: self.def_reg(I32, u)?, src: self.get_reg(I32, u)? }
      }
      AllowedInst::CopyF => {
        CopyF { dst: self.def_reg(F32, u)?, src: self.get_reg(F32, u)? }
      }
      AllowedInst::BinOp => BinOp {
        op: ir::BinOp::arbitrary(u)?,
        dst: self.def_reg(I32, u)?,
        src_left: self.get_reg(I32, u)?,
        src_right: self.get_ri(u)?,
      },
      AllowedInst::BinOpM => BinOpM {
        op: ir::BinOp::arbitrary(u)?,
        dst: self.mod_reg(I32, u)?,
        src_right: self.get_ri(u)?,
      },
      AllowedInst::BinOpF => BinOpF {
        op: ir::BinOpF::arbitrary(u)?,
        dst: self.def_reg(F32, u)?,
        src_left: self.get_reg(F32, u)?,
        src_right: self.get_reg(F32, u)?,
      },
      AllowedInst::Load => {
        Load { dst: self.def_reg(I32, u)?, addr: self.get_am(u)? }
      }
      AllowedInst::LoadF => {
        LoadF { dst: self.def_reg(F32, u)?, addr: self.get_am(u)? }
      }
      AllowedInst::Store => {
        Store { addr: self.get_am(u)?, src: self.get_reg(I32, u)? }
      }
      AllowedInst::StoreF => {
        StoreF { addr: self.get_am(u)?, src: self.get_reg(F32, u)? }
      }
    })
  }

  fn inst_control_flow(&self, u: &mut Unstructured) -> Result<Inst> {
    use Inst::*;
    use RegClass::*;

    enum AllowedInst {
      Goto,
      GotoCtf,
      Finish,
    }

    let mut allowed_insts = vec![AllowedInst::Goto, AllowedInst::Finish];
    if self.has_reg_with_rc(I32) {
      allowed_insts.push(AllowedInst::GotoCtf);
    }

    Ok(match allowed_insts[u8::arbitrary(u)? as usize % allowed_insts.len()] {
      AllowedInst::GotoCtf => GotoCTF {
        cond: self.get_reg(I32, u)?,
        target_true: self.label(u)?,
        target_false: self.label(u)?,
      },
      AllowedInst::Goto => Goto { target: self.label(u)? },
      AllowedInst::Finish => {
        let ret_value = if bool::arbitrary(u)? {
          if self.has_reg_with_rc(I32) {
            Some(self.get_reg(I32, u)?)
          } else if self.has_reg_with_rc(F32) {
            Some(self.get_reg(F32, u)?)
          } else {
            None
          }
        } else {
          None
        };
        Finish { reg: ret_value }
      }
    })
  }
}

impl Arbitrary for Func {
  fn arbitrary(u: &mut Unstructured) -> arbitrary::Result<Func> {
    let num_virtual_regs = 1 + (u16::arbitrary(u)? % u16::max_value());
    let mut num_blocks = 1 + (u8::arbitrary(u)? % u8::max_value());

    let mut env = FuzzingEnv {
      num_blocks,
      num_virtual_regs,
      vregs: HashMap::new(),
      regs_by_rc: vec![HashSet::new(); NUM_REG_CLASSES as usize],
      vregs_by_rc: vec![HashSet::new(); NUM_REG_CLASSES as usize],
    };

    let entry =
      Some(Label::Resolved { name: "entry".to_string(), bix: BlockIx::new(0) });

    let mut insts = TypedIxVec::new();
    let mut blocks = TypedIxVec::new();

    let mut cur_block = 0;

    while num_blocks > 0 {
      let start = insts.len();

      let mut num_block_insts = 1 + (u8::arbitrary(u)? % 255);

      while num_block_insts > 0 {
        let inst = if num_block_insts == 1 {
          env.inst_control_flow(u)?
        } else {
          env.inst(u)?
        };
        let is_control_flow = inst.is_control_flow();
        insts.push(inst);
        num_block_insts -= 1;
        if is_control_flow {
          break;
        }
      }

      debug_assert!(insts.len() > start);
      let len = insts.len() - start;
      let block = Block {
        name: format!("b{}", cur_block),
        start: InstIx::new(start),
        len,
        estimated_execution_frequency: 0,
      };
      blocks.push(block);

      cur_block += 1;
      num_blocks -= 1;
    }

    Ok(Func {
      name: "funk".to_string(),
      entry,
      num_virtual_regs: num_virtual_regs as u32,
      insns: insts,
      blocks,
    })
  }
}
