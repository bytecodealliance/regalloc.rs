#![no_main]
use libfuzzer_sys::fuzz_target;

use regalloc;
use minira::{self, test_framework as ir};

fuzz_target!(|func: ir::Func| {
    let mut func = func;

    // 8 FP registers and 8 GP registers are enough for everyone.
    let reg_universe = ir::make_universe(8, 8);

    let expected_ret_value = match ir::run_func(
      &func,
      "Before allocation",
      &reg_universe,
      ir::RunStage::BeforeRegalloc,
    ) {
        Ok(ret_value) => ret_value,
        Err(err) => {
            println!("can't interpret func: {}", err);
            return;
        }
    };

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

    let observed_ret_value = ir::run_func(
      &func,
      "After allocation",
      &reg_universe,
      ir::RunStage::AfterRegalloc,
    ).expect("should have run correctly the second time!");

    assert_eq!(
      expected_ret_value, observed_ret_value,
      "Incorrect interpreter result: expected {:?}, observed {:?}",
      expected_ret_value, observed_ret_value
    );
});
