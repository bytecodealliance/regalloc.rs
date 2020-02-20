#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{validator::validate, test_framework as ir};

fuzz_target!(|func: ir::Func| {
    // 8 FP registers and 8 GP registers are enough for everyone.
    let reg_universe = ir::make_universe(8, 8);

    if let Err(err) = validate(&func, &reg_universe) {
        println!("validation error: {}", err);
    }
});
