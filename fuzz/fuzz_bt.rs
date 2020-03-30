#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{self, test_framework as ir};
use regalloc;

fuzz_target!(|func: ir::Func| {
  let mut func = func;

  let num_regs = minira::fuzzing::NUM_REAL_REGS_PER_RC as usize;
  let reg_universe = ir::make_universe(num_regs, num_regs);

  let func_backup = func.clone();

  let result = match regalloc::allocate_registers(
    &mut func,
    regalloc::RegAllocAlgorithm::BacktrackingChecked,
    &reg_universe,
  ) {
    Ok(result) => result,
    Err(err) => {
      if let regalloc::RegAllocError::RegChecker(_) = &err {
        panic!(err);
      }
      let mut rendered = String::new();
      func_backup.render("validation error", &mut rendered).unwrap();
      println!("{}", rendered);
      println!("allocation error: {}", err);
      return;
    }
  };

  func.update_from_alloc(result);
});
