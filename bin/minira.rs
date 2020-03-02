/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

/* TODOs, 02 Mar 2020

MVP (without these, the implementation is useless in practice):

- add a spill-slot allocation mechanism, even if it is pretty crude

Post-MVP:

- Backtracking allocator: Live Range Splitting (but see next point)

- Backtracking allocator: rewrite the main live-range allocation loop, so as
  to make it perform copy coalescing more robustly.

  Currently the loop processes one VirtualRange at a time, and makes a
  best-effort to honour the coalescing hints available.  However, this is all
  rather ad hoc.  It would be better to change the structure so that the basic
  unit of allocation is a *group* of VirtualRanges, where VirtualRanges are
  put into the same group if they are connected by V-V copies.  Hence:

  * coalescing analysis computes:
    - for each VLR, a weighted set of register prefs, based on V-R and R-V
      copies only
    - the grouping of VLRs, based on V-V copies

  * the allocation loop then allocates/evicts entire groups at a time.
    Allocating an entire group at once guarantees that all V-V copies between
    VLRs in the group will disappear, since by definition all group members
    have the same real register.

  * when allocating a group, draw up a weighted list of preferred candidates
    by checking the V-R/R-V derived prefs of all its members, and try first to
    use those (as the present logic does).

  * if a group can't be allocated, and contains more than one VLR, then it is
    split up into multiple groups, each containing one VLR, and these are put
    back into the allocation queue.  Note that this doesn't have to happen in
    a single step; it would be ok to gradually split the groups into smaller
    groups, with the proviso that the eventual end-point of the process must
    result in each group containing only a single VLR.

    The result of splitting up a group is that we can no longer guarantee to
    remove V-V copies between the group's VLRs, but that's unavoidable.

  * if a group can't be allocated, and contains only a single VLR, then either
    - it must be spilled, as at present
    - it must be split into multiple smaller VLRs, each of which is put into
      its own group. (Not yet implemented).

  This design has some nice properties:

  * It maximally coalesces virtual groups to the extent it can.

  * Imagine the situation where a group has a real-reg preference, as a result
    of one of its members (VLRs) having that preference.  Suppose further that
    the group cannot be allocated, and must be split, so it is split into two
    smaller groups.  The group that does *not* inherit the preferred register
    is now unconstrained by the preference, and the group that does inherit
    the preference is smaller.  Both of these effects potentially remove
    interferences and so increase the chances of the two smaller groups being
    successfully allocated.

  * It integrates nicely with the idea of splitting.  If a single-element
    group (a VLR) cannot be allocated, we could choose to split it into
    multiple single-element groups.  The only difficulty is to decide how to
    place the splits in such a way that it is unnecessary to add explicit
    copies to the instruction stream (since that sounds complex and expensive)
    and yet is profitable.

    The no-changes-to-the-insn stream idea may be a tradeoff that is worth
    persuing in an allocator intended for use in a JIT.  It reduces the
    splitter's possibilities but means it doesn't have to deal with the
    complexity of adding copies at the dominance frontiers, etc.  If done
    carefully it could mean we never need to change the instruction stream at
    all.  The restriction basically has the effect that any split point must
    divide the blocks in the VLR into two disjoint groups, those dominated by
    the "split point" and those postdominated by the "split point", so that in
    effect all "traffic" in the VLR flows through the split point.

    Another opportunistic-split possibility is to add two splits at the start
    and end of a single basic block that has high register pressure, perhaps
    due to a call.  Then we wouldn't even have to bother checking the
    dominates/postdominates condition.

    These are complex tradeoffs to evaluate.  Perhaps in 2H2020.

Tidyings:

- (should do) fn CFGInfo::create::dfs: use an explicit stack instead of
  recursion.

- (minor) add an LR classifier (Spill/Reload/Normal) and use that instead
  of current in-line tests

Performance:

- Iterative liveness analysis: only put blocks in the work queue if they are
  not already present in it.  This could reduce the number of evaluations by
  quite a lot.

- Collect typical use data for each Set<T> instance and replace with a
  suitable optimised replacement.

- Ditto FxHashMap (if we have to have it at all)

- Replace SortedFragIxs with something more efficient

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
