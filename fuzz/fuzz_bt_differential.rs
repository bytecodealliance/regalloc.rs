#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{self, test_framework as ir, validator};
use regalloc;

fuzz_target!(|func: ir::Func| {
  let mut func = func;

  let num_regs = minira::fuzzing::NUM_REAL_REGS_PER_RC as usize;
  let reg_universe = ir::make_universe(num_regs, num_regs);

  let cloned_func = func.clone();

  let mut rendered = String::new();
  func.render("before allocation", &mut rendered).unwrap();
  println!("{}", rendered);

  let result = match regalloc::allocate_registers(
    &mut func,
    regalloc::RegAllocAlgorithm::Backtracking,
    &reg_universe,
  ) {
    Ok(result) => result,
    Err(err) => {
      println!("allocation error: {}", err);
      return;
    }
  };

  func.update_from_alloc(result);
  func.print("after allocation");

  let expected = ir::run_func(
    &cloned_func,
    "Before allocation",
    &reg_universe,
    ir::RunStage::BeforeRegalloc,
  );

  let observed = ir::run_func(
    &func,
    "After allocation",
    &reg_universe,
    ir::RunStage::AfterRegalloc,
  );

  validator::check_results(&expected, &observed);
});
