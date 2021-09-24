#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{self, test_framework as ir, validator};
use regalloc;

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

    let mut rendered = String::new();
    func.render("before allocation", &mut rendered).unwrap();
    println!("{}", rendered);

    let opts = regalloc::Options {
        run_checker: true,

        algorithm: regalloc::Algorithm::LinearScan(Default::default()),
    };

    let env = regalloc::RegEnv::from_rru_and_opts(reg_universe.clone(), &opts);
    let result = match regalloc::allocate_registers_with_opts(&mut func, &env, None, opts) {
        Ok(result) => result,
        Err(err) => {
            if let regalloc::RegAllocError::RegChecker(_) = &err {
                panic!("fuzz_lsra_differential.rs: checker error: {:?}", err);
            }
            println!("allocation error: {}", err);
            return;
        }
    };

    func.update_from_alloc(result);
    func.print("after allocation", &None);

    let observed = ir::run_func(
        &func,
        "After allocation",
        &reg_universe,
        ir::RunStage::AfterRegalloc,
    );

    validator::check_results(&expected, &observed);
});
