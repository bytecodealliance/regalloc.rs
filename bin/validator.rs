use crate::test_framework::*;
use regalloc::*;
use std::collections::HashMap;

pub struct Context<'rru> {
  pub num_vregs: usize,
  pub num_blocks: u32,
  real_reg_universe: &'rru RealRegUniverse,
  vreg_types: HashMap<usize, RegClass>,
}

impl<'rru> Context<'rru> {
  fn new(func: &Func, real_reg_universe: &'rru RealRegUniverse) -> Self {
    Self {
      num_vregs: func.num_virtual_regs as usize,
      real_reg_universe,
      num_blocks: func.blocks.len(),
      vreg_types: HashMap::new(),
    }
  }

  pub fn check_reg(&mut self, reg: Reg) -> bool {
    // If the register has been mentioned earlier, check that it didn't change type in the
    // meanwhile.
    let rc = reg.get_class();
    let index = reg.get_index();
    if let Some(prev_rc) = self.vreg_types.insert(index, rc) {
      if prev_rc != rc {
        return false;
      }
    }

    if reg.is_virtual() {
      // If it's virtual, it must be in range.
      index < self.num_vregs
    } else {
      debug_assert!(reg.is_real());
      // If it's real, it must:
      // - exist in the array of real registers,
      // - have the same encoding as in the real register universe,
      // - be in the range of its register class.
      if index >= self.real_reg_universe.regs.len() {
        return false;
      }
      if self.real_reg_universe.regs[index].0 != reg.as_real_reg().unwrap() {
        return false;
      }
      match self.real_reg_universe.allocable_by_class[rc as usize] {
        Some(ref reg_info) => index >= reg_info.first && index <= reg_info.last,
        None => false,
      }
    }
  }
}

pub fn validate(
  func: &Func, real_reg_universe: &RealRegUniverse,
) -> Result<(), String> {
  let mut cx = Context::new(func, real_reg_universe);

  // Function entry must exist and point to a valid block.
  match &func.entry {
    None => {
      return Err("missing entry label".into());
    }
    Some(label) => {
      if !label.type_checks(&cx) {
        return Err("invalid or unresolved entry label".into());
      }
    }
  };

  // Blocks must not be empty.
  for b in func.blocks.iter() {
    if b.len == 0 {
      return Err(format!("block {} is empty", b.name));
    }
    if b.start.get().checked_add(b.len).is_none() {
      return Err(format!("too many instructions in block {}", b.name));
    }
  }

  let last_block = &func.blocks[BlockIx::new(func.blocks.len() - 1)];
  if func.insns.len() != last_block.start.get() + last_block.len {
    return Err(format!("unused instructions"));
  }

  // Check that blocks are ordered in increasing block start.
  for i in 1..func.blocks.len() {
    let prev = BlockIx::new(i - 1);
    let cur = BlockIx::new(i);

    let prev_block = &func.blocks[prev];
    if prev_block.start >= func.blocks[cur].start {
      return Err(format!(
        "blocks {:?} and {:?} not ordered in strictly increasing start",
        prev, cur
      ));
    }

    let prev_start: u32 = prev_block.start.into();
    let cur_start: u32 = func.blocks[cur].start.into();
    if prev_start + prev_block.len != cur_start {
      return Err(format!("block {:?} is incorrectly specified", prev));
    }
  }

  // Check instructions.
  for b in func.blocks.iter() {
    if b.start.get().checked_add(b.len).is_none() {
      return Err("too many block instructions".into());
    }
    for i in b.start.dotdot(b.start.plus(b.len)) {
      if i.get() >= func.insns.len() {
        return Err(format!(
          "invalid instruction number {:?} in block {}",
          i, b.name
        ));
      }

      let inst = &func.insns[i];

      if !inst.is_user() {
        return Err(format!(
          "unexpected regalloc inst {:?} in block {}",
          inst, b.name
        ));
      }
      if !inst.type_checks(&mut cx) {
        return Err(format!(
          "inst {:?} in block {} does not type check",
          inst, b.name
        ));
      }

      // No control flow instructions in the middle, but it must be one at the end.
      if i == b.start.plus(b.len - 1) {
        if !inst.is_control_flow() {
          return Err(format!(
            "final inst {:?} of block {} must be a control flow inst",
            inst, b.name
          ));
        }
      } else {
        if inst.is_control_flow() {
          return Err(format!(
            "control flow inst {:?} in the middle of block {}",
            inst, b.name
          ));
        }
      }
    }
  }

  Ok(())
}
