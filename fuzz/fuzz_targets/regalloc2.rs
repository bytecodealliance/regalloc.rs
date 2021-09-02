#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{self, test_framework as ir};
use regalloc;

fuzz_target!(|func: ir::Func| {
    let _ = env_logger::try_init();

    log::debug!("BEGIN INPUT:");
    let mut rendered = String::new();
    func.render("==== fuzz_regalloc2.rs: input:", &mut rendered)
        .unwrap();
    log::debug!("{}", rendered);
    log::debug!("END INPUT:");

    let mut func = func;

    let num_regs = minira::fuzzing::NUM_REAL_REGS_PER_RC as usize;
    let reg_universe = ir::make_universe(num_regs, num_regs);

    let func_backup = func.clone();

    let opts = regalloc::Options {
        run_checker: true,

        algorithm: regalloc::Algorithm::Regalloc2(regalloc::Regalloc2Options {
            num_int_preferred: 4,
            num_float_preferred: 4,
            ignore_scratch_reg_mentions: false,
            verbose_log: true,
        }),
    };

    let env = regalloc::RegEnv::from_rru_and_opts(reg_universe, &opts);
    let sri = func.get_stackmap_request();
    let ra_result = regalloc::allocate_registers_with_opts(&mut func, &env, sri.as_ref(), opts);

    match ra_result {
        Ok(result) => {
            func.update_from_alloc(result);
        }
        Err(err) => {
            let mut stop = false;
            if let regalloc::RegAllocError::RegChecker(_) = &err {
                stop = true;
                eprintln!("==== fuzz_regalloc2.rs: checker error: {:?}", err);
            }
            if stop {
                let mut rendered = String::new();
                func_backup
                    .render("==== fuzz_regalloc2.rs: failing input:", &mut rendered)
                    .unwrap();
                eprintln!("{}", rendered);

                eprintln!("==== fuzz_regalloc2.rs:");
                eprintln!(
                    "==== fuzz_regalloc2.rs: to repro, use flags '-f {} -i {}'",
                    num_regs, num_regs
                );
                eprintln!("==== fuzz_regalloc2.rs:");

                log::debug!("FAIL INPUT:");
                let mut rendered = String::new();
                func.render("==== fuzz_regalloc2.rs: input:", &mut rendered)
                    .unwrap();
                log::debug!("{}", rendered);
                log::debug!("END FAIL INPUT:");
            }
            assert!(!stop);
        }
    };
});
