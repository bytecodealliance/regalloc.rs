#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{fuzzing, test_framework as ir, validator::validate};

fuzz_target!(|func: ir::Func| {
    let reg_universe = ir::make_universe(
        fuzzing::NUM_REAL_REGS_PER_RC as usize,
        fuzzing::NUM_REAL_REGS_PER_RC as usize,
    );

    validate(&func, &reg_universe).unwrap_or_else(|err| {
        let mut rendered = String::new();
        func.render("validation error", &mut rendered).unwrap();
        println!("{}", rendered);
        panic!(err);
    });
});
