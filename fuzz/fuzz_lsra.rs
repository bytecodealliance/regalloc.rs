#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{self, test_framework as ir};
use regalloc;

fuzz_target!(|func: ir::Func| {
    let mut func = func;

    // Add one register to be used as a scratch.
    let num_regs = minira::fuzzing::NUM_REAL_REGS_PER_RC as usize + 1;
    let reg_universe = ir::make_universe(num_regs, num_regs);

    let mut rendered = String::new();
    func.render("func:", &mut rendered).unwrap();
    println!("{}", rendered);

    let result = match regalloc::allocate_registers(
        &mut func,
        &reg_universe,
        regalloc::AlgorithmWithDefaults::LinearScan,
    ) {
        Ok(result) => result,
        Err(err) => {
            if let regalloc::RegAllocError::RegChecker(_) = &err {
                panic!(format!(
                    "fuzz_lsra_differential.rs: checker error: {:?}",
                    err
                ));
            }
            println!("allocation error: {}", err);
            return;
        }
    };

    func.update_from_alloc(result);
});
