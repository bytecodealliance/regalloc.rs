#![no_main]
use libfuzzer_sys::fuzz_target;

use regalloc;
use minira::{self, test_framework as ir};

fuzz_target!(|func: ir::Func| {
    let mut func = func;

    let num_regs = minira::fuzzing::NUM_REAL_REGS_PER_RC as usize;
    let reg_universe = ir::make_universe(num_regs, num_regs);

    let cloned_func = func.clone();
    func.print("before allocation");

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

    let expected_ret_value = ir::run_func(
      &cloned_func,
      "Before allocation",
      &reg_universe,
      ir::RunStage::BeforeRegalloc,
    );

    let observed_ret_value = ir::run_func(
      &func,
      "After allocation",
      &reg_universe,
      ir::RunStage::AfterRegalloc,
    );

    assert_eq!(
      expected_ret_value, observed_ret_value,
      "Incorrect interpreter result: expected {:?}, observed {:?}",
      expected_ret_value, observed_ret_value
    );
});
