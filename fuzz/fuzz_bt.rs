/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{self, test_framework as ir};
use regalloc;

static mut COUNTER: usize = 0;

fuzz_target!(|func: ir::Func| {
  let n = unsafe { COUNTER += 1; COUNTER };
  println!("==== BEGIN fuzz_bt.rs fuzz_target! {:?} =========================",
           n);
  let mut func = func;

  let num_regs = minira::fuzzing::NUM_REAL_REGS_PER_RC as usize;
  let reg_universe = ir::make_universe(num_regs, num_regs);

  let func_backup = func.clone();

  let ra_result = regalloc::allocate_registers(
    &mut func,
    regalloc::RegAllocAlgorithm::BacktrackingChecked,
    &reg_universe,
  );

  match ra_result {
    Ok(result) => {
      func.update_from_alloc(result);
      return;
    }
    Err(err) => {
      let mut stop = false;
      if let regalloc::RegAllocError::RegChecker(_) = &err {
        stop = true;
        println!("==== fuzz_bt.rs: checker error: {:?}", err);
      }
      if stop {
        let mut rendered = String::new();
        func_backup.render("==== fuzz_bt.rs: failing input:",
                           &mut rendered).unwrap();
        println!("{}", rendered);
      }
      println!("==== fuzz_bt.rs: failure reason: {}", err);
      if stop {
        println!("==== fuzz_bt.rs:");
        println!("==== fuzz_bt.rs: to repro, use flags '-f {} -i {}'",
                num_regs, num_regs);
        println!("==== fuzz_bt.rs:");
        panic!("==== fuzz_bt.rs: STOPPING.  Bye! ====");
      }
    }
  };
});
