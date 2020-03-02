#![no_main]
use libfuzzer_sys::fuzz_target;

use regalloc;
use minira::{self, test_framework as ir, validator};

fuzz_target!(|func: ir::Func| {
    let mut func = func;

    // Add one register to be used as a scratch.
    let num_regs = minira::fuzzing::NUM_REAL_REGS_PER_RC as usize + 1;
    let reg_universe = ir::make_universe(num_regs, num_regs);

    let cloned_func = func.clone();
    let expected = ir::run_func(
      &cloned_func,
      "Before allocation",
      &reg_universe,
      ir::RunStage::BeforeRegalloc,
    );
    if expected.is_err() {
        return;
    }

    func.print("before allocation");

    let result = match regalloc::allocate_registers(
      &mut func,
      regalloc::RegAllocAlgorithm::LinearScan,
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

    let observed = ir::run_func(
      &func,
      "After allocation",
      &reg_universe,
      ir::RunStage::AfterRegalloc,
    );

    validator::check_results(&expected, &observed);
});
