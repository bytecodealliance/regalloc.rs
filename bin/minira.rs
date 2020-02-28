/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

/* TODOs, 11 Dec 2019

MVP (without these, the implementation is useless in practice):

- add a spill-slot allocation mechanism, even if it is pretty crude

- support multiple register classes

- add a random-Func generator and maybe some way to run it in a loop
  (a.k.a a differential fuzzer)

Post-MVP:

- Move Coalescing

- Live Range Splitting

Tidyings:

- (should do) fn CFGInfo::create::dfs: use an explicit stack instead of
  recursion.

- (minor) add an LR classifier (Spill/Reload/Normal) and use that instead
  of current in-line tests

- Is it really necessary to have both SpillAndOrReloadInfo and EditListItem?
  Can we get away with just one?

Performance:

- Collect typical use data for each Set<T> instance and replace with a
  suitable optimised replacement.

- Ditto FxHashMap (if we have to have it at all)

- Replace SortedFragIxs with something more efficient

- Currently we call getRegUsage three times for each insn.  Just do this
  once and cache the results.

- Inst rewrite loop: don't clone map_defs; just use it as soon as it's available.

- Inst rewrite loop: move cursors forwards at Point granularity so we don't
  have to repeatedly re-scan the groups looking for particular LR kinds?
*/

mod fuzzing;
mod parser;
mod test_cases;
mod test_framework;
mod validator;

use regalloc::{allocate_registers, RegAllocAlgorithm};
use test_framework::{make_universe, run_func, RunResult, RunStage};

use clap;
use log::{self, error, info};
use pretty_env_logger;

//=============================================================================
// Top level

fn main() {
  pretty_env_logger::init();

  let app = clap::App::new("minira")
    .about("a simple program to allow separate testing of regalloc.rs")
    .arg(
      clap::Arg::with_name("iregs")
        .short("i")
        .takes_value(true)
        .help("number of integer registers available (0 if not set)"),
    )
    .arg(
      clap::Arg::with_name("fregs")
        .short("f")
        .takes_value(true)
        .help("number of floating-point registers available (0 if not set)"),
    )
    .arg(
      clap::Arg::with_name("test")
        .short("t")
        .takes_value(true)
        .required(true)
        .help("test case name"),
    )
    .arg(
      clap::Arg::with_name("algorithm")
        .short("a")
        .takes_value(true)
        .required(true)
        .possible_values(&["bt", "lsra"])
        .help("algorithm name"),
    );
  let matches = app.get_matches();

  let func_name = matches.value_of("test").unwrap();
  let mut func = match crate::test_cases::find_func(func_name) {
    Ok(func) => func,
    Err(available_func_names) => {
      error!("can't find Func with name '{}'", func_name);
      println!("available func names are:");
      for name in available_func_names {
        println!("     {}", name);
      }
      return;
    }
  };

  let (num_regs_i32, num_regs_f32) = match (
    matches.value_of("iregs").unwrap_or("0").parse::<usize>(),
    matches.value_of("fregs").unwrap_or("0").parse::<usize>(),
  ) {
    (Ok(num_i32), Ok(num_f32)) => (num_i32, num_f32),
    _other => {
      println!("invalid iregs/fregs values: {}", matches.usage());
      return;
    }
  };

  let reg_alloc_kind = match matches.value_of("algorithm").unwrap() {
    "bt" => {
      info!("Using the backtracking allocator");
      RegAllocAlgorithm::Backtracking
    }
    "lsra" => {
      info!("Using the linear scan allocator.");
      RegAllocAlgorithm::LinearScan
    }
    // Unreachable because of defined "possible_values".
    _ => unreachable!(),
  };

  let reg_universe = make_universe(num_regs_i32, num_regs_f32);

  func.print("before allocation");

  // Just so we can run it later.  Not needed for actual allocation.
  let original_func = func.clone();

  let result =
    match allocate_registers(&mut func, reg_alloc_kind, &reg_universe) {
      Err(e) => {
        println!("allocation failed: {}", e);
        return;
      }
      Ok(r) => r,
    };

  // Update the function itself. This bridges the gap from the generic
  // interface to our specific test ISA.
  func.update_from_alloc(result);

  func.print("after allocation");

  let before_regalloc_result = run_func(
    &original_func,
    "Before allocation",
    &reg_universe,
    RunStage::BeforeRegalloc,
  );

  let after_regalloc_result =
    run_func(&func, "After allocation", &reg_universe, RunStage::AfterRegalloc);

  println!("");

  check_results(before_regalloc_result, after_regalloc_result);
}

fn check_results(
  before_regalloc_result: Result<RunResult, String>,
  after_regalloc_result: Result<RunResult, String>,
) {
  match before_regalloc_result {
    Ok(before_regalloc_result) => {
      let after_regalloc_result = after_regalloc_result
        .expect("code after regalloc should have succeeded");

      // The interpreted result number of dynamic steps is a lower bound on the
      // number of dynamic steps executed after regalloc.
      assert!(
        before_regalloc_result.num_steps <= after_regalloc_result.num_steps,
        "inconsistent trace"
      );

      assert_eq!(
        before_regalloc_result.ret_value, after_regalloc_result.ret_value,
        "Incorrect interpreter result: expected {:?}, observed {:?}",
        before_regalloc_result.ret_value, after_regalloc_result.ret_value
      );

      assert_eq!(
        before_regalloc_result.stdout, after_regalloc_result.stdout,
        r#"Different stdout values before/after regalloc:
- before:
{}
-after:
{}
        "#,
        before_regalloc_result.stdout, after_regalloc_result.stdout
      );
    }

    Err(err) => {
      assert_eq!(err, after_regalloc_result.unwrap_err());
    }
  }
}

#[cfg(test)]
mod test_utils {
  use regalloc::RegAllocResult;

  use super::*;
  use crate::test_framework::Func;

  pub fn check_bt(func_name: &str, num_gpr: usize, num_fpu: usize) {
    let _ = pretty_env_logger::try_init();
    let mut func = test_cases::find_func(func_name).unwrap();
    let reg_universe = make_universe(num_gpr, num_fpu);
    let before_regalloc_result = run_func(
      &func,
      "Before allocation",
      &reg_universe,
      RunStage::BeforeRegalloc,
    );
    let result = allocate_registers(
      &mut func,
      RegAllocAlgorithm::Backtracking,
      &reg_universe,
    )
    .unwrap_or_else(|err| {
      panic!("allocation failed: {}", err);
    });
    func.update_from_alloc(result);
    let after_regalloc_result = run_func(
      &func,
      "After allocation",
      &reg_universe,
      RunStage::AfterRegalloc,
    );
    check_results(before_regalloc_result, after_regalloc_result);
  }

  pub fn run_lsra(
    func_name: &str, num_gpr: usize, num_fpu: usize,
  ) -> Result<RegAllocResult<Func>, String> {
    let _ = pretty_env_logger::try_init();
    let mut func = test_cases::find_func(func_name).unwrap();
    let reg_universe = make_universe(num_gpr, num_fpu);
    allocate_registers(&mut func, RegAllocAlgorithm::LinearScan, &reg_universe)
  }

  pub fn check_lsra(func_name: &str, num_gpr: usize, num_fpu: usize) {
    let _ = pretty_env_logger::try_init();
    let mut func = test_cases::find_func(func_name).unwrap();
    let reg_universe = make_universe(num_gpr, num_fpu);
    let before_regalloc_result = run_func(
      &func,
      "Before allocation",
      &reg_universe,
      RunStage::BeforeRegalloc,
    );
    func.print("BEFORE");
    let result = allocate_registers(
      &mut func,
      RegAllocAlgorithm::LinearScan,
      &reg_universe,
    )
    .unwrap_or_else(|err| {
      panic!("allocation failed: {}", err);
    });
    func.update_from_alloc(result);
    func.print("AFTER");
    let after_regalloc_result = run_func(
      &func,
      "After allocation",
      &reg_universe,
      RunStage::AfterRegalloc,
    );
    check_results(before_regalloc_result, after_regalloc_result);
  }
}

// At some point we'll want to repeat all these tests with the number of
// registers iterating down to 3, so as to stress the spilling machinery as
// much as we can.

#[test]
fn bt_badness() {
  test_utils::check_bt("badness", 1, 0);
}
#[test]
fn lsra_badness() {
  test_utils::check_lsra("badness", 1, 0);
}

#[test]
fn bt_straight_line() {
  test_utils::check_bt("straight_line", 1, 0);
}
#[test]
fn lsra_straight_line() {
  test_utils::check_lsra("straight_line", 2, 0);
}

#[test]
fn bt_fill_then_sum() {
  test_utils::check_bt("fill_then_sum", 8, 8);
}
#[test]
fn lsra_fill_then_sum() {
  assert!(test_utils::run_lsra("fill_then_sum", 1, 0).is_err());
  assert!(test_utils::run_lsra("fill_then_sum", 2, 0).is_err());
  for i in 3..8 {
    test_utils::check_lsra("fill_then_sum", i, 0);
  }
}

#[test]
fn bt_ssort() {
  test_utils::check_bt("ssort", 8, 8);
}
#[test]
fn lsra_ssort() {
  test_utils::check_lsra("ssort", 8, 8);
}

#[test]
fn bt_3_loops() {
  test_utils::check_bt("3_loops", 8, 8);
}
#[test]
fn lsra_3_loops() {
  assert!(test_utils::run_lsra("3_loops", 1, 0).is_err());
  for i in 2..9 {
    test_utils::check_lsra("3_loops", i, 0);
  }
}

#[test]
fn bt_stmts() {
  test_utils::check_bt("stmts", 8, 8);
}
#[test]
fn lsra_stmts() {
  test_utils::check_lsra("stmts", 8, 8);
}

#[test]
fn bt_needs_splitting() {
  test_utils::check_bt("needs_splitting", 8, 8);
}
#[test]
fn lsra_needs_splitting() {
  test_utils::check_lsra("needs_splitting", 8, 8);
}

#[test]
fn bt_needs_splitting2() {
  test_utils::check_bt("needs_splitting2", 8, 8);
}
#[test]
fn lsra_needs_splitting2() {
  test_utils::check_lsra("needs_splitting2", 8, 8);
}

#[test]
fn bt_qsort() {
  test_utils::check_bt("qsort", 8, 8);
}
#[test]
fn lsra_qsort() {
  test_utils::check_lsra("qsort", 8, 8);
}

#[test]
fn bt_fill_then_sum_2a() {
  test_utils::check_bt("fill_then_sum_2a", 8, 8);
}
#[test]
fn lsra_2a_fill_then_sum_2a() {
  for i in 3..8 {
    test_utils::check_lsra("fill_then_sum", i, 0);
  }
}

#[test]
fn bt_ssort_2a() {
  test_utils::check_bt("ssort_2a", 8, 8);
}
#[test]
fn lsra_2a_ssort() {
  test_utils::check_lsra("ssort_2a", 8, 8);
}

#[test]
fn bt_fp1() {
  test_utils::check_bt("fp1", 8, 8);
}
#[test]
fn lsra_fp1() {
  test_utils::check_lsra("fp1", 8, 8);
}

#[test]
fn bt_fp2() {
  test_utils::check_bt("fp2", 8, 8);
}
#[test]
fn lsra_fp2() {
  test_utils::check_lsra("fp2", 8, 8);
}

#[test]
fn lsra_simple_spill() {
  test_utils::check_lsra("simple_spill", 1, 0);
}

#[test]
fn lsra_simple_loop() {
  assert!(test_utils::run_lsra("simple_loop", 1, 0).is_err());
  test_utils::check_lsra("simple_loop", 2, 0);
}

#[test]
fn lsra_stmt_loop() {
  assert!(test_utils::run_lsra("stmt_loop", 1, 0).is_err());
  for i in 2..5 {
    test_utils::check_lsra("stmt_loop", i, 0);
  }
}

#[test]
fn any_use_modified() {
  test_utils::check_bt("use_mod", 1, 0);
}
