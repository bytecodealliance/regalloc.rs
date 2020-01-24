/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

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

use std::env;

mod test_cases;
mod test_framework;

use minira::{allocate_registers, RegAllocAlgorithm};
use test_framework::{make_universe, run_func, RunStage};

use log::{self, error, info};
use pretty_env_logger;

//=============================================================================
// Top level

fn usage(argv0: &String) {
  println!(
    "usage: {} <name_of_algorithm> <name_of_Func> \
     <num_regs::I32> <num_regs::F32>",
    argv0
  );
  println!("usage: available algorithms:  bt  lsra");
  println!("usage: to get a list of available Funcs to try, run with args:");
  println!("usage:    bt bogus 0 0");
}

fn main() {
  pretty_env_logger::init();

  let args: Vec<String> = env::args().collect();
  if args.len() != 5 {
    usage(&args[0]);
    return;
  }

  let mut func = match crate::test_cases::find_Func(&args[2]) {
    Ok(func) => func,
    Err(available_func_names) => {
      error!("can't find Func with name '{}'", args[2]);
      println!("{}: available Func names are:", args[0]);
      for name in available_func_names {
        println!("{}:     {}", args[0], name);
      }
      return;
    }
  };

  let (nRegsI32, nRegsF32) =
    match (args[3].parse::<usize>(), args[4].parse::<usize>()) {
      (Ok(nI32), Ok(nF32)) => (nI32, nF32),
      _other => {
        usage(&args[0]);
        return;
      }
    };

  let reg_alloc_kind = match args[1].as_str() {
    "bt" => {
      info!("Using the backtracking allocator");
      RegAllocAlgorithm::Backtracking
    }
    "lsra" => {
      info!("Using the linear scan allocator.");
      RegAllocAlgorithm::LinearScan
    }
    _ => {
      usage(&args[0]);
      return;
    }
  };

  let reg_universe = make_universe(nRegsI32, nRegsF32);

  func.print("before allocation");

  // Just so we can run it later.  Not needed for actual allocation.
  let original_func = func.clone();

  let result =
    match allocate_registers(&mut func, reg_alloc_kind, &reg_universe) {
      Err(e) => {
        error!("{}: allocation failed: {}", args[0], e);
        return;
      }
      Ok(r) => r,
    };

  // Update the function itself. This bridges the gap from the generic
  // interface to our specific test ISA.
  func.update_from_alloc(result);

  func.print("after allocation");

  run_func(
    &original_func,
    "Before allocation",
    &reg_universe,
    RunStage::BeforeRegalloc,
  );
  run_func(&func, "After allocation", &reg_universe, RunStage::AfterRegalloc);

  println!("");
}

#[cfg(test)]
mod test_utils {
  use super::*;

  pub fn bt(func_name: &str, num_gpr: usize, num_fpu: usize) {
    let _ = pretty_env_logger::try_init();
    let mut func = test_cases::find_Func(func_name).unwrap();
    let reg_universe = make_universe(num_gpr, num_fpu);
    let result = allocate_registers(
      &mut func,
      RegAllocAlgorithm::Backtracking,
      &reg_universe,
    )
    .unwrap_or_else(|err| {
      panic!("allocation failed: {}", err);
    });
    func.update_from_alloc(result);
    run_func(&func, "After allocation", &reg_universe, RunStage::AfterRegalloc);
  }

  pub fn lsra(func_name: &str, num_gpr: usize, num_fpu: usize) {
    let _ = pretty_env_logger::try_init();
    let mut func = test_cases::find_Func(func_name).unwrap();
    let reg_universe = make_universe(num_gpr, num_fpu);
    let result = allocate_registers(
      &mut func,
      RegAllocAlgorithm::LinearScan,
      &reg_universe,
    )
    .unwrap_or_else(|err| {
      panic!("allocation failed: {}", err);
    });
    func.update_from_alloc(result);
    run_func(&func, "After allocation", &reg_universe, RunStage::AfterRegalloc);
  }
}

// At some point we'll want to repeat all these tests with the number of
// registers iterating down to 3, so as to stress the spilling machinery as
// much as we can.

#[test]
fn bt__badness() {
  test_utils::bt("badness", 1, 0);
}
#[test]
fn lsra__badness() {
  test_utils::lsra("badness", 1, 0);
}

#[test]
fn bt__straight_line() {
  test_utils::bt("straight_line", 1, 0);
}
#[test]
fn lsra__straight_line() {
  test_utils::lsra("straight_line", 2, 0);
}

#[test]
fn bt__fill_then_sum() {
  test_utils::bt("fill_then_sum", 8, 8);
}
#[test]
fn lsra__fill_then_sum() {
  test_utils::lsra("fill_then_sum", 32, 32);
  //test_utils::lsra("fill_then_sum", 8, 8);
}

#[test]
fn bt__ssort() {
  test_utils::bt("ssort", 8, 8);
}
#[test]
fn lsra__ssort() {
  test_utils::lsra("ssort", 10, 10);
  //test_utils::lsra("ssort", 8, 8);
}

#[test]
fn bt__3_loops() {
  test_utils::bt("3_loops", 8, 8);
}
#[test]
fn lsra__3_loops() {
  test_utils::lsra("3_loops", 8, 8);
}

#[test]
fn bt__stmts() {
  test_utils::bt("stmts", 8, 8);
}
#[test]
fn lsra__stmts() {
  test_utils::lsra("stmts", 8, 8);
}

#[test]
fn bt__needs_splitting() {
  test_utils::bt("needs_splitting", 8, 8);
}
#[test]
fn lsra__needs_splitting() {
  test_utils::lsra("needs_splitting", 8, 8);
}

#[test]
fn bt__needs_splitting2() {
  test_utils::bt("needs_splitting2", 8, 8);
}
#[test]
fn lsra__needs_splitting2() {
  test_utils::lsra("needs_splitting2", 8, 8);
}

#[test]
fn bt__qsort() {
  test_utils::bt("qsort", 8, 8);
}
#[test]
fn lsra__qsort() {
  test_utils::lsra("qsort", 8, 8);
}

#[test]
fn bt__fill_then_sum_2a() {
  test_utils::bt("fill_then_sum_2a", 8, 8);
}
#[test]
fn lsra__2a_fill_then_sum_2a() {
  test_utils::lsra("fill_then_sum_2a", 8, 8);
}

#[test]
fn bt__ssort_2a() {
  test_utils::bt("ssort_2a", 8, 8);
}
#[test]
fn lsra__2a_ssort() {
  test_utils::lsra("ssort_2a", 8, 8);
}

#[test]
fn bt__fp1() {
  test_utils::bt("fp1", 8, 8);
}
#[test]
fn lsra__fp1() {
  test_utils::lsra("fp1", 8, 8);
}

#[test]
fn bt__fp2() {
  test_utils::bt("fp2", 8, 8);
}
#[test]
fn lsra__fp2() {
  test_utils::lsra("fp2", 8, 8);
}
