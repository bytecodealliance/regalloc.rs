#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{test_framework as ir, validator::validate};

fuzz_target!(|func: ir::Func| {
  // 8 FP registers and 8 GP registers are enough for everyone.
  let reg_universe = ir::make_universe(8, 8);

  validate(&func, &reg_universe).unwrap_or_else(|err| {
    func.print("");
    panic!(err);
  });
});
