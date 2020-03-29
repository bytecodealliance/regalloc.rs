/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

/// Test cases.  The list of them is right at the bottom, function |find_Func|.
/// Add new ones there.
use regalloc::{Reg, RegClass};

use crate::parser;
use crate::test_framework::*;

use std::path::{Path, PathBuf};

/// Reduced sort test.
fn test_sort2() -> Func {
  let mut func = Func::new("ssort2");
  func.set_entry("Lstart");

  let lo = func.new_virtual_reg(RegClass::I32);
  let hi = func.new_virtual_reg(RegClass::I32);
  let i = func.new_virtual_reg(RegClass::I32);
  let j = func.new_virtual_reg(RegClass::I32);
  let h = func.new_virtual_reg(RegClass::I32);
  let big_n = func.new_virtual_reg(RegClass::I32);
  let v = func.new_virtual_reg(RegClass::I32);
  let hp = func.new_virtual_reg(RegClass::I32);
  let t0 = func.new_virtual_reg(RegClass::I32);
  let zero = func.new_virtual_reg(RegClass::I32);

  func.block(
    "Lstart",
    vec![
      i_imm(zero, 0),
      i_imm(t0, 1),
      i_store(AM_RI(zero, 0), t0),
      i_imm(t0, 4),
      i_store(AM_RI(zero, 1), t0),
      i_imm(t0, 13),
      i_store(AM_RI(zero, 2), t0),
      i_imm(t0, 30),
      i_store(AM_RI(zero, 3), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 4), t0),
      i_imm(t0, 31),
      i_store(AM_RI(zero, 5), t0),
      i_imm(lo, 3),
      i_imm(hi, 5),
      i_sub(t0, hi, RI_R(lo)),
      i_add(big_n, t0, RI_I(1)),
      i_imm(hp, 0),
      i_goto("L11"),
    ],
  );
  func.block(
    "L11",
    vec![
      i_load(t0, AM_R(hp)),
      i_cmp_gt(t0, t0, RI_R(big_n)),
      i_goto_ctf(t0, "L19", "L11a"),
    ],
  );
  func.block("L19", vec![i_goto("L20")]);
  func.block("L11a", vec![i_add(hp, hp, RI_I(1)), i_goto("L11")]);
  func.block(
    "L20",
    vec![i_cmp_lt(t0, hp, RI_I(1)), i_goto_ctf(t0, "L60", "L21a")],
  );
  func.block(
    "L21a",
    vec![
      i_sub(t0, hp, RI_I(1)),
      i_load(h, AM_R(t0)),
      i_add(i, lo, RI_R(h)),
      i_goto("L30"),
    ],
  );
  func.block(
    "L30",
    vec![i_cmp_gt(t0, i, RI_R(hi)), i_goto_ctf(t0, "L50", "L30a")],
  );
  func.block(
    "L30a",
    vec![i_load(v, AM_R(i)), i_add(j, i, RI_I(0)), i_goto("L40")],
  );
  func.block(
    "L40",
    vec![
      i_sub(t0, j, RI_R(h)),
      i_load(t0, AM_R(t0)),
      //i_print_i(t0),
      i_cmp_le(t0, t0, RI_R(v)),
      i_goto_ctf(t0, "L41", "L40a"),
    ],
  );
  func.block("L41", vec![i_goto("L45")]);
  func.block("L40a", vec![i_goto("fin")]);
  func.block("L45", vec![i_goto("L30")]);
  func.block("L50", vec![i_goto("L20")]);
  func.block("L60", vec![i_goto("fin")]);
  func.block("fin", vec![i_print_s("\n"), i_finish(None)]);
  func.finish();
  func
}

fn test_sort() -> Func {
  let mut func = Func::new("ssort");
  func.set_entry("Lstart");

  // This is a simple "shellsort" test.  An array of numbers to sort is
  // placed in mem[5..24] and an increment table is placed in mem[0..4].
  // mem[5..24] is then sorted and the result is printed.
  //
  // This test features 15 basic blocks, 10 virtual registers, at least one
  // of which has multiple independent live ranges, a 3-deep loop nest, and
  // some live ranges which span parts of the loop nest.  So it's an
  // interesting test case.

  let lo = func.new_virtual_reg(RegClass::I32);
  let hi = func.new_virtual_reg(RegClass::I32);
  let i = func.new_virtual_reg(RegClass::I32);
  let j = func.new_virtual_reg(RegClass::I32);
  let h = func.new_virtual_reg(RegClass::I32);
  let big_n = func.new_virtual_reg(RegClass::I32);
  let v = func.new_virtual_reg(RegClass::I32);
  let hp = func.new_virtual_reg(RegClass::I32);
  let t0 = func.new_virtual_reg(RegClass::I32);
  let zero = func.new_virtual_reg(RegClass::I32);

  func.block(
    "Lstart",
    vec![
      i_imm(zero, 0),
      // Store the increment table
      i_imm(t0, 1),
      i_store(AM_RI(zero, 0), t0),
      i_imm(t0, 4),
      i_store(AM_RI(zero, 1), t0),
      i_imm(t0, 13),
      i_store(AM_RI(zero, 2), t0),
      i_imm(t0, 40),
      i_store(AM_RI(zero, 3), t0),
      i_imm(t0, 121),
      i_store(AM_RI(zero, 4), t0),
      // Store the numbers to be sorted
      i_imm(t0, 30),
      i_store(AM_RI(zero, 5), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 6), t0),
      i_imm(t0, 31),
      i_store(AM_RI(zero, 7), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 8), t0),
      i_imm(t0, 32),
      i_store(AM_RI(zero, 9), t0),
      i_imm(t0, 66),
      i_store(AM_RI(zero, 10), t0),
      i_imm(t0, 77),
      i_store(AM_RI(zero, 11), t0),
      i_imm(t0, 44),
      i_store(AM_RI(zero, 12), t0),
      i_imm(t0, 22),
      i_store(AM_RI(zero, 13), t0),
      i_imm(t0, 11),
      i_store(AM_RI(zero, 14), t0),
      i_imm(t0, 99),
      i_store(AM_RI(zero, 15), t0),
      i_imm(t0, 11),
      i_store(AM_RI(zero, 16), t0),
      i_imm(t0, 12),
      i_store(AM_RI(zero, 17), t0),
      i_imm(t0, 7),
      i_store(AM_RI(zero, 18), t0),
      i_imm(t0, 9),
      i_store(AM_RI(zero, 19), t0),
      i_imm(t0, 2),
      i_store(AM_RI(zero, 20), t0),
      i_imm(t0, 32),
      i_store(AM_RI(zero, 21), t0),
      i_imm(t0, 23),
      i_store(AM_RI(zero, 22), t0),
      i_imm(t0, 41),
      i_store(AM_RI(zero, 23), t0),
      i_imm(t0, 14),
      i_store(AM_RI(zero, 24), t0),
      // The real computation begins here
      i_imm(lo, 5),  // Lowest address of the range to sort
      i_imm(hi, 24), // Highest address of the range to sort
      i_sub(t0, hi, RI_R(lo)),
      i_add(big_n, t0, RI_I(1)),
      i_imm(hp, 0),
      i_goto("L11"),
    ],
  );

  func.block(
    "L11",
    vec![
      i_load(t0, AM_R(hp)),
      i_cmp_gt(t0, t0, RI_R(big_n)),
      i_goto_ctf(t0, "L19", "L11a"),
    ],
  );

  func.block("L19", vec![i_goto("L20")]);

  func.block("L11a", vec![i_add(hp, hp, RI_I(1)), i_goto("L11")]);

  func.block(
    "L20",
    vec![i_cmp_lt(t0, hp, RI_I(1)), i_goto_ctf(t0, "L60", "L21a")],
  );

  func.block(
    "L21a",
    vec![
      i_sub(t0, hp, RI_I(1)),
      i_load(h, AM_R(t0)),
      //printf("h = %u\n", h),
      i_add(i, lo, RI_R(h)),
      i_goto("L30"),
    ],
  );

  func.block(
    "L30",
    vec![i_cmp_gt(t0, i, RI_R(hi)), i_goto_ctf(t0, "L50", "L30a")],
  );

  func.block(
    "L30a",
    vec![
      i_load(v, AM_R(i)),
      i_add(j, i, RI_I(0)), // FIXME: is this a coalescable copy?
      i_goto("L40"),
    ],
  );

  func.block(
    "L40",
    vec![
      i_sub(t0, j, RI_R(h)),
      i_load(t0, AM_R(t0)),
      i_cmp_le(t0, t0, RI_R(v)),
      i_goto_ctf(t0, "L41", "L40a"),
    ],
  );

  func.block("L41", vec![i_goto("L45")]);

  func.block(
    "L40a",
    vec![
      i_sub(t0, j, RI_R(h)),
      i_load(t0, AM_R(t0)),
      i_store(AM_R(j), t0),
      i_sub(j, j, RI_R(h)),
      i_add(t0, lo, RI_R(h)),
      i_sub(t0, t0, RI_I(1)),
      i_cmp_le(t0, j, RI_R(t0)),
      i_goto_ctf(t0, "L40a1", "L40a2"),
    ],
  );

  func.block("L40a1", vec![i_goto("L45")]);
  func.block("L40a2", vec![i_goto("L40")]);

  func.block(
    "L45",
    vec![i_store(AM_R(j), v), i_add(i, i, RI_I(1)), i_goto("L30")],
  );

  func.block("L50", vec![i_sub(hp, hp, RI_I(1)), i_goto("L20")]);

  func.block(
    "L60",
    vec![
      i_add(i, lo, RI_I(0)), // FIXME: ditto
      i_goto("L61"),
    ],
  );

  func.block(
    "L61",
    vec![i_cmp_gt(t0, i, RI_R(hi)), i_goto_ctf(t0, "L62", "L61a")],
  );

  func.block(
    "L61a",
    vec![
      i_load(t0, AM_R(i)),
      i_print_i(t0),
      i_print_s(" "),
      i_add(i, i, RI_I(1)),
      i_goto("L61"),
    ],
  );

  func.block("L62", vec![i_print_s("\n"), i_finish(None)]);

  func.finish();
  func
}

fn test_3_loops() -> Func {
  let mut func = Func::new("3_loops");
  func.set_entry("start");

  let v00 = func.new_virtual_reg(RegClass::I32);
  let v01 = func.new_virtual_reg(RegClass::I32);
  let v02 = func.new_virtual_reg(RegClass::I32);
  let v03 = func.new_virtual_reg(RegClass::I32);
  let v04 = func.new_virtual_reg(RegClass::I32);
  let v05 = func.new_virtual_reg(RegClass::I32);
  let v06 = func.new_virtual_reg(RegClass::I32);
  let v07 = func.new_virtual_reg(RegClass::I32);
  let v08 = func.new_virtual_reg(RegClass::I32);
  let v09 = func.new_virtual_reg(RegClass::I32);
  let v10 = func.new_virtual_reg(RegClass::I32);
  let v11 = func.new_virtual_reg(RegClass::I32);
  let v_i = func.new_virtual_reg(RegClass::I32);
  let v_sum = func.new_virtual_reg(RegClass::I32);
  let v_tmp = func.new_virtual_reg(RegClass::I32);

  // Loop pre-header for filling array with numbers.
  // This is also the entry point.
  func.block(
    "start",
    vec![
      i_imm(v00, 0),
      i_imm(v01, 0),
      i_imm(v02, 0),
      i_imm(v03, 0),
      i_imm(v04, 0),
      i_imm(v05, 0),
      i_imm(v06, 0),
      i_imm(v07, 0),
      i_imm(v08, 0),
      i_imm(v09, 0),
      i_imm(v10, 0),
      i_imm(v11, 0),
      i_imm(v_i, 0),
      i_goto("outer-loop-cond"),
    ],
  );

  // Outer loop
  func.block(
    "outer-loop-cond",
    vec![
      i_add(v_i, v_i, RI_I(1)),
      i_cmp_le(v_tmp, v_i, RI_I(20)),
      i_goto_ctf(v_tmp, "outer-loop-1", "after-outer-loop"),
    ],
  );

  func.block(
    "outer-loop-1",
    vec![
      i_add(v00, v00, RI_I(1)),
      i_add(v01, v01, RI_I(1)),
      i_add(v02, v02, RI_I(1)),
      i_add(v03, v03, RI_I(1)),
      i_goto("outer-loop-cond"),
    ],
  );

  // After loop.  Print result and stop.
  func.block(
    "after-outer-loop",
    vec![
      i_imm(v_sum, 0),
      i_add(v_sum, v_sum, RI_R(v00)),
      i_add(v_sum, v_sum, RI_R(v01)),
      i_add(v_sum, v_sum, RI_R(v02)),
      i_add(v_sum, v_sum, RI_R(v03)),
      i_add(v_sum, v_sum, RI_R(v04)),
      i_add(v_sum, v_sum, RI_R(v05)),
      i_add(v_sum, v_sum, RI_R(v06)),
      i_add(v_sum, v_sum, RI_R(v07)),
      i_add(v_sum, v_sum, RI_R(v08)),
      i_add(v_sum, v_sum, RI_R(v09)),
      i_add(v_sum, v_sum, RI_R(v10)),
      i_add(v_sum, v_sum, RI_R(v11)),
      i_print_s("Sum = "),
      i_print_i(v_sum),
      i_print_s("\n"),
      i_finish(Some(v_sum)),
    ],
  );

  func.finish();
  func
}

fn test_stmts() -> Func {
  let mut bif = Blockifier::new("stmts");
  let v_i = bif.new_virtual_reg(RegClass::I32);
  let v_j = bif.new_virtual_reg(RegClass::I32);
  let v_sum = bif.new_virtual_reg(RegClass::I32);
  let v_tmp = bif.new_virtual_reg(RegClass::I32);
  let stmts = vec![
    s_imm(v_sum, 0),
    s_imm(v_i, 0),
    s_repeat_until(
      vec![
        s_imm(v_j, 0),
        s_repeat_until(
          vec![
            s_mul(v_tmp, v_i, RI_R(v_j)),
            s_add(v_sum, v_sum, RI_R(v_tmp)),
            s_add(v_j, v_j, RI_I(1)),
            s_cmp_gt(v_tmp, v_j, RI_I(10)),
          ],
          v_tmp,
        ),
        s_add(v_sum, v_sum, RI_R(v_i)),
        s_add(v_i, v_i, RI_I(1)),
        s_cmp_gt(v_tmp, v_i, RI_I(10)),
      ],
      v_tmp,
    ),
    s_print_s("Result is "),
    s_print_i(v_sum),
    s_print_s("\n"),
  ];
  /*
  let stmts = vec![
      s_imm(v0, 0),
      s_imm(v1, 0),
      s_imm(v2, 0),
      s_add(v0, v1, RI_R(v2)),
      s_add(v2, v1, RI_R(v0)),
      s_ite(v0, vec![
                s_add(v2, v2, RI_I(0)),
                s_ite(v2, vec![
                          s_add(v2, v2, RI_I(1))
                      ], vec![
                          s_add(v2, v2, RI_I(2))
                      ],
                ),
            ], vec![
                s_add(v1, v1, RI_I(3))
            ]
      ),
      s_add(v0, v0, RI_I(4)),
      s_repeat_until(
          vec![
                s_add(v1, v1, RI_I(5)),
                s_add(v1, v1, RI_I(6)),
                s_add(v1, v1, RI_I(7))
          ],
          v0
      ),
      s_add(v0, v0, RI_I(10)),
      s_add(v0, v0, RI_I(11)),
      s_while_do(
          v2,
          vec![
              s_add(v2, v2, RI_I(12))
          ]
      )
  ];
   */
  bif.finish(stmts, Some(v_sum))
}

// Test cases where live range splitting might obviously help

fn test_needs_splitting() -> Func {
  let mut bif = Blockifier::new("needs_splitting");
  let v10 = bif.new_virtual_reg(RegClass::I32);
  let v11 = bif.new_virtual_reg(RegClass::I32);
  let v12 = bif.new_virtual_reg(RegClass::I32);

  let v20 = bif.new_virtual_reg(RegClass::I32);
  let v21 = bif.new_virtual_reg(RegClass::I32);
  let v22 = bif.new_virtual_reg(RegClass::I32);

  let v_i = bif.new_virtual_reg(RegClass::I32);
  let v_sum = bif.new_virtual_reg(RegClass::I32);
  let v_tmp = bif.new_virtual_reg(RegClass::I32);

  let stmts = vec![
    // Both the v1x and the v2x set become live at this point
    s_imm(v10, 1),
    s_imm(v11, 2),
    s_imm(v12, 3),
    s_imm(v20, 4),
    s_imm(v21, 5),
    s_imm(v22, 6),
    // In this loop, v1x are hot, but v2x are unused.  In an ideal world,
    // the v2x set would be spilled across the loop and reloaded after
    // that.
    s_imm(v_i, 0),
    s_repeat_until(
      vec![
        s_add(v10, v10, RI_I(1)),
        s_add(v11, v11, RI_I(2)),
        s_add(v12, v12, RI_I(3)),
        s_add(v_i, v_i, RI_I(1)),
        s_cmp_ge(v_tmp, v_i, RI_I(100)),
      ],
      v_tmp,
    ),
    // Conversely, v2x in this loop are hot, and v1x are unused, but still
    // need to stay alive across it.
    s_imm(v_i, 0),
    s_repeat_until(
      vec![
        s_add(v20, v20, RI_I(1)),
        s_add(v21, v21, RI_I(2)),
        s_add(v22, v22, RI_I(3)),
        s_add(v_i, v_i, RI_I(1)),
        s_cmp_ge(v_tmp, v_i, RI_I(100)),
      ],
      v_tmp,
    ),
    // All in all, the v1x and v2x set are both still live down to here.
    s_imm(v_sum, 0),
    s_add(v_sum, v_sum, RI_R(v10)),
    s_add(v_sum, v_sum, RI_R(v11)),
    s_add(v_sum, v_sum, RI_R(v12)),
    s_add(v_sum, v_sum, RI_R(v20)),
    s_add(v_sum, v_sum, RI_R(v21)),
    s_add(v_sum, v_sum, RI_R(v22)),
    s_print_s("Result is "),
    s_print_i(v_sum),
    s_print_s("\n"),
  ];
  bif.finish(stmts, Some(v_sum))
}

// This is the same as needs_splitting, but with the live ranges split
// "manually"
fn test_needs_splitting2() -> Func {
  let mut bif = Blockifier::new("needs_splitting2");
  let v10 = bif.new_virtual_reg(RegClass::I32);
  let v11 = bif.new_virtual_reg(RegClass::I32);
  let v12 = bif.new_virtual_reg(RegClass::I32);

  let v20 = bif.new_virtual_reg(RegClass::I32);
  let v21 = bif.new_virtual_reg(RegClass::I32);
  let v22 = bif.new_virtual_reg(RegClass::I32);

  // Post-split versions of v10 .. v22
  let s1v10 = bif.new_virtual_reg(RegClass::I32);
  let s1v11 = bif.new_virtual_reg(RegClass::I32);
  let s1v12 = bif.new_virtual_reg(RegClass::I32);

  let s1v20 = bif.new_virtual_reg(RegClass::I32);
  let s1v21 = bif.new_virtual_reg(RegClass::I32);
  let s1v22 = bif.new_virtual_reg(RegClass::I32);

  let s2v20 = bif.new_virtual_reg(RegClass::I32);
  let s2v21 = bif.new_virtual_reg(RegClass::I32);
  let s2v22 = bif.new_virtual_reg(RegClass::I32);

  let v_i = bif.new_virtual_reg(RegClass::I32);
  let v_sum = bif.new_virtual_reg(RegClass::I32);
  let v_tmp = bif.new_virtual_reg(RegClass::I32);

  let stmts = vec![
    // Both the v1x and the v2x set become live at this point
    s_imm(v10, 0),
    s_imm(v11, 0),
    s_imm(v12, 0),
    s_imm(v20, 0),
    s_imm(v21, 0),
    s_imm(v22, 0),
    s_copy(s1v20, v20),
    s_copy(s1v21, v21),
    s_copy(s1v22, v22),
    // In this loop, v1x are hot, but v2x are unused.  In an ideal world,
    // the v2x set would be spilled across the loop and reloaded after
    // that.
    s_imm(v_i, 0),
    s_repeat_until(
      vec![
        s_add(v10, v10, RI_I(1)),
        s_add(v11, v11, RI_I(2)),
        s_add(v12, v12, RI_I(3)),
        s_add(v_i, v_i, RI_I(1)),
        s_cmp_ge(v_tmp, v_i, RI_I(100)),
      ],
      v_tmp,
    ),
    s_copy(s1v10, v10),
    s_copy(s1v11, v11),
    s_copy(s1v12, v12),
    s_copy(s2v20, s1v20),
    s_copy(s2v21, s1v21),
    s_copy(s2v22, s1v22),
    // Conversely, v2x in this loop are hot, and v1x are unused, but still
    // need to stay alive across it.
    s_imm(v_i, 0),
    s_repeat_until(
      vec![
        s_add(s2v20, s2v20, RI_I(1)),
        s_add(s2v21, s2v21, RI_I(2)),
        s_add(s2v22, s2v22, RI_I(3)),
        s_add(v_i, v_i, RI_I(1)),
        s_cmp_ge(v_tmp, v_i, RI_I(100)),
      ],
      v_tmp,
    ),
    // All in all, the v1x and v2x set are both still live down to here.
    s_imm(v_sum, 0),
    s_add(v_sum, v_sum, RI_R(s1v10)),
    s_add(v_sum, v_sum, RI_R(s1v11)),
    s_add(v_sum, v_sum, RI_R(s1v12)),
    s_add(v_sum, v_sum, RI_R(s2v20)),
    s_add(v_sum, v_sum, RI_R(s2v21)),
    s_add(v_sum, v_sum, RI_R(s2v22)),
    s_print_s("Result is "),
    s_print_i(v_sum),
    s_print_s("\n"),
  ];
  bif.finish(stmts, Some(v_sum))
}

fn test_stmt_loop() -> Func {
  let mut bif = Blockifier::new("stmt_loop");
  let v_x = bif.new_virtual_reg(RegClass::I32);
  let v_y = bif.new_virtual_reg(RegClass::I32);
  let v_i = bif.new_virtual_reg(RegClass::I32);
  let v_tmp = bif.new_virtual_reg(RegClass::I32);
  let stmts = vec![
    s_imm(v_x, 1),
    s_imm(v_y, 2),
    s_imm(v_i, 0),
    s_repeat_until(
      vec![
        s_add(v_x, v_x, RI_I(3)),
        s_add(v_y, v_y, RI_I(4)),
        s_add(v_i, v_i, RI_I(1)),
        s_cmp_ge(v_tmp, v_i, RI_I(10)),
      ],
      v_tmp,
    ),
    s_add(v_x, v_x, RI_R(v_y)),
  ];
  bif.finish(stmts, Some(v_x))
}

// A big test.  This is derived from function fallbackQSort3 in the bzip2
// sources.  Just be glad it was me and not you that had to translate it by
// hand into machine code.  It generates 900 pseudo-random numbers, and then
// sorts them using a Bentley-Sedgewick style 3-way-partitioning quicksort.
// The result is checked for in-orderness and checksummed.  This is not
// recursive (it can't be) so it maintains an explicit stack of
// yet-to-be-processed subranges.  (Two stacks, really).
//
// This test has: 56 basic blocks, 215 insns, 36 virtual registers, 17
// simultaneously live values, 735 live range fragments, 100 vreg live ranges.
/*
   Dynamic results by number of regs available, 2019Dec19:
   17  224440 insns, 0 spills, 0 reloads
   16  226241 insns, 1 spills, 1800 reloads
   15  228045 insns, 2 spills, 3603 reloads
   14  229804 insns, 589 spills, 4775 reloads
   13  232127 insns, 590 spills, 7097 reloads
   12  234450 insns, 591 spills, 9419 reloads
   11  241229 insns, 1752 spills, 15037 reloads
   10  248034 insns, 2913 spills, 20681 reloads
   9   257322 insns, 4655 spills, 28227 reloads
   8   265026 insns, 7508 spills, 33078 reloads
   7   269598 insns, 8509 spills, 36649 reloads
   6   276782 insns, 10453 spills, 41889 reloads
   5   305031 insns, 14401 spills, 66190 reloads
   4   384631 insns, 25980 spills, 134211 reloads
   3   410510 insns, 36512 spills, 149558 reloads
   2  out of regs in spill/reload (load and store insns can reference 3 regs)
*/
fn test_qsort() -> Func {
  let mut bif = Blockifier::new("qsort");

  // All your virtual register are belong to me.  Bwahaha.  Ha.  Ha.
  let offs_stack_lo = bif.new_virtual_reg(RegClass::I32);
  let offs_stack_hi = bif.new_virtual_reg(RegClass::I32);
  let offs_numbers = bif.new_virtual_reg(RegClass::I32);
  let num_numbers = bif.new_virtual_reg(RegClass::I32);
  let rand = bif.new_virtual_reg(RegClass::I32);
  let lo_st = bif.new_virtual_reg(RegClass::I32);
  let hi_st = bif.new_virtual_reg(RegClass::I32);
  let keep_going_i = bif.new_virtual_reg(RegClass::I32);
  let keep_going_o = bif.new_virtual_reg(RegClass::I32);
  let un_lo = bif.new_virtual_reg(RegClass::I32);
  let un_hi = bif.new_virtual_reg(RegClass::I32);
  let lt_lo = bif.new_virtual_reg(RegClass::I32);
  let gt_hi = bif.new_virtual_reg(RegClass::I32);
  let n = bif.new_virtual_reg(RegClass::I32);
  let m = bif.new_virtual_reg(RegClass::I32);
  let sp = bif.new_virtual_reg(RegClass::I32);
  let lo = bif.new_virtual_reg(RegClass::I32);
  let hi = bif.new_virtual_reg(RegClass::I32);
  let med = bif.new_virtual_reg(RegClass::I32);
  let r3 = bif.new_virtual_reg(RegClass::I32);
  let yyp1 = bif.new_virtual_reg(RegClass::I32);
  let yyp2 = bif.new_virtual_reg(RegClass::I32);
  let yyn = bif.new_virtual_reg(RegClass::I32);
  let t0 = bif.new_virtual_reg(RegClass::I32);
  let t1 = bif.new_virtual_reg(RegClass::I32);
  let t2 = bif.new_virtual_reg(RegClass::I32);
  let zztmp1 = bif.new_virtual_reg(RegClass::I32);
  let zztmp2 = bif.new_virtual_reg(RegClass::I32);
  let taa = bif.new_virtual_reg(RegClass::I32);
  let tbb = bif.new_virtual_reg(RegClass::I32);
  let i = bif.new_virtual_reg(RegClass::I32);
  let in_order = bif.new_virtual_reg(RegClass::I32);
  let sum = bif.new_virtual_reg(RegClass::I32);
  let pass = bif.new_virtual_reg(RegClass::I32);
  let sp_gt_zero = bif.new_virtual_reg(RegClass::I32);
  let guard = bif.new_virtual_reg(RegClass::I32);

  let stmts = vec![
    // mem[] layout and base offsets
    //
    // stackLo is [0..49]   (actually only needs 10 entries)
    // stackHi is [50..99]  (ditto)
    // array to sort is [100..999]
    s_imm(offs_stack_lo, 0),
    s_imm(offs_stack_hi, 50),
    s_imm(offs_numbers, 100),
    s_imm(num_numbers, 900),
    // Fill mem[100..999] with "random" numbers
    s_imm(rand, 0),
    s_imm(i, 0),
    s_repeat_until(
      vec![
        s_mul(t0, rand, RI_I(7621)),
        s_add(t0, t0, RI_I(1)),
        s_mod(rand, t0, RI_I(32768)),
        s_mod(t0, rand, RI_I(10000)),
        s_store(AM_RR(offs_numbers, i), t0),
        s_add(i, i, RI_I(1)),
        s_cmp_ge(guard, i, RI_R(num_numbers)),
      ],
      guard,
    ),
    s_imm(rand, 0),
    s_imm(sp, 0),
    s_copy(lo_st, offs_numbers),
    s_sub(t0, offs_numbers, RI_I(1)),
    s_add(hi_st, t0, RI_R(num_numbers)),
    // Push initial stack entry
    s_store(AM_RR(offs_stack_lo, sp), lo_st),
    s_store(AM_RR(offs_stack_hi, sp), hi_st),
    s_add(sp, sp, RI_I(1)),
    s_cmp_gt(sp_gt_zero, sp, RI_I(0)),
    s_while_do(
      sp_gt_zero,
      vec![
        s_cmp_lt(t0, sp, RI_I(10)),
        //////assert(t0),
        s_sub(sp, sp, RI_I(1)),
        s_load(lo, AM_RR(offs_stack_lo, sp)),
        s_load(hi, AM_RR(offs_stack_hi, sp)),
        s_cmp_lt(t0, lo, RI_R(hi)),
        s_if_then(
          t0,
          vec![
            s_mul(t0, rand, RI_I(7621)),
            s_add(t0, t0, RI_I(1)),
            s_mod(rand, t0, RI_I(32768)),
            s_mod(r3, rand, RI_I(3)),
            s_cmp_eq(t0, r3, RI_I(0)),
            s_if_then_else(
              t0,
              vec![s_load(med, AM_R(lo))],
              vec![
                s_cmp_eq(t0, r3, RI_I(1)),
                s_if_then_else(
                  t0,
                  vec![
                    s_add(t0, lo, RI_R(hi)),
                    s_shr(t0, t0, RI_I(1)),
                    s_load(med, AM_R(t0)),
                  ],
                  vec![s_load(med, AM_R(hi))],
                ),
              ],
            ),
            s_copy(un_lo, lo),
            s_copy(lt_lo, lo),
            s_copy(un_hi, hi),
            s_copy(gt_hi, hi),
            s_imm(keep_going_o, 1),
            s_while_do(
              keep_going_o,
              vec![
                s_imm(keep_going_i, 1),
                s_cmp_le(guard, un_lo, RI_R(un_hi)),
                s_while_do(
                  guard,
                  vec![
                    s_load(t1, AM_R(un_lo)),
                    s_cmp_eq(t0, t1, RI_R(med)),
                    s_if_then_else(
                      t0,
                      vec![
                        s_load(zztmp1, AM_R(un_lo)),
                        s_load(zztmp2, AM_R(lt_lo)),
                        s_store(AM_R(un_lo), zztmp2),
                        s_store(AM_R(lt_lo), zztmp1),
                        s_add(lt_lo, lt_lo, RI_I(1)),
                        s_add(un_lo, un_lo, RI_I(1)),
                      ],
                      vec![
                        s_cmp_gt(t0, t1, RI_R(med)),
                        s_if_then_else(
                          t0,
                          vec![s_imm(keep_going_i, 0)],
                          vec![s_add(un_lo, un_lo, RI_I(1))],
                        ),
                      ],
                    ),
                    s_cmp_le(guard, un_lo, RI_R(un_hi)),
                    s_and(guard, guard, RI_R(keep_going_i)),
                  ],
                ),
                s_imm(keep_going_i, 1),
                s_cmp_le(guard, un_lo, RI_R(un_hi)),
                s_while_do(
                  guard,
                  vec![
                    s_load(t1, AM_R(un_hi)),
                    s_cmp_eq(t0, t1, RI_R(med)),
                    s_if_then_else(
                      t0,
                      vec![
                        s_load(zztmp1, AM_R(un_hi)),
                        s_load(zztmp2, AM_R(gt_hi)),
                        s_store(AM_R(un_hi), zztmp2),
                        s_store(AM_R(gt_hi), zztmp1),
                        s_sub(gt_hi, gt_hi, RI_I(1)),
                        s_sub(un_hi, un_hi, RI_I(1)),
                      ],
                      vec![
                        s_cmp_lt(t0, t1, RI_R(med)),
                        s_if_then_else(
                          t0,
                          vec![s_imm(keep_going_i, 0)],
                          vec![s_sub(un_hi, un_hi, RI_I(1))],
                        ),
                      ],
                    ),
                    s_cmp_le(guard, un_lo, RI_R(un_hi)),
                    s_and(guard, guard, RI_R(keep_going_i)),
                  ],
                ),
                s_cmp_gt(t0, un_lo, RI_R(un_hi)),
                s_if_then_else(
                  t0,
                  vec![s_imm(keep_going_o, 0)],
                  vec![
                    s_load(zztmp1, AM_R(un_lo)),
                    s_load(zztmp2, AM_R(un_hi)),
                    s_store(AM_R(un_lo), zztmp2),
                    s_store(AM_R(un_hi), zztmp1),
                    s_add(un_lo, un_lo, RI_I(1)),
                    s_sub(un_hi, un_hi, RI_I(1)),
                  ],
                ),
              ],
            ),
            s_sub(t0, un_lo, RI_I(1)),
            s_cmp_eq(t0, un_hi, RI_R(t0)),
            //////assert( t0 ),
            s_cmp_ge(t0, gt_hi, RI_R(lt_lo)),
            s_if_then(
              t0,
              vec![
                s_sub(taa, lt_lo, RI_R(lo)),
                s_sub(tbb, un_lo, RI_R(lt_lo)),
                s_cmp_lt(t0, taa, RI_R(tbb)),
                s_if_then_else(t0, vec![s_copy(n, taa)], vec![s_copy(n, tbb)]),
                s_copy(yyp1, lo),
                s_sub(yyp2, un_lo, RI_R(n)),
                s_copy(yyn, n),
                s_cmp_gt(guard, yyn, RI_I(0)),
                s_while_do(
                  guard,
                  vec![
                    s_load(zztmp1, AM_R(yyp1)),
                    s_load(zztmp2, AM_R(yyp2)),
                    s_store(AM_R(yyp1), zztmp2),
                    s_store(AM_R(yyp2), zztmp1),
                    s_add(yyp1, yyp1, RI_I(1)),
                    s_add(yyp2, yyp2, RI_I(1)),
                    s_sub(yyn, yyn, RI_I(1)),
                    s_cmp_gt(guard, yyn, RI_I(0)),
                  ],
                ),
                s_sub(taa, hi, RI_R(gt_hi)),
                s_sub(tbb, gt_hi, RI_R(un_hi)),
                s_cmp_lt(t0, taa, RI_R(tbb)),
                s_if_then_else(t0, vec![s_copy(m, taa)], vec![s_copy(m, tbb)]),
                s_copy(yyp1, un_lo),
                s_sub(yyp2, hi, RI_R(m)),
                s_add(yyp2, yyp2, RI_I(1)),
                s_copy(yyn, m),
                s_cmp_gt(guard, yyn, RI_I(0)),
                s_while_do(
                  guard,
                  vec![
                    s_load(zztmp1, AM_R(yyp1)),
                    s_load(zztmp2, AM_R(yyp2)),
                    s_store(AM_R(yyp1), zztmp2),
                    s_store(AM_R(yyp2), zztmp1),
                    s_add(yyp1, yyp1, RI_I(1)),
                    s_add(yyp2, yyp2, RI_I(1)),
                    s_sub(yyn, yyn, RI_I(1)),
                    s_cmp_gt(guard, yyn, RI_I(0)),
                  ],
                ),
                s_add(n, lo, RI_R(un_lo)),
                s_sub(n, n, RI_R(lt_lo)),
                s_sub(n, n, RI_I(1)),
                s_sub(m, gt_hi, RI_R(un_hi)),
                s_sub(m, hi, RI_R(m)),
                s_add(m, m, RI_I(1)),
                s_sub(t1, n, RI_R(lo)),
                s_sub(t2, hi, RI_R(m)),
                s_cmp_gt(t0, t1, RI_R(t2)),
                s_if_then_else(
                  t0,
                  vec![
                    s_store(AM_RR(offs_stack_lo, sp), lo),
                    s_store(AM_RR(offs_stack_hi, sp), n),
                    s_add(sp, sp, RI_I(1)),
                    s_store(AM_RR(offs_stack_lo, sp), m),
                    s_store(AM_RR(offs_stack_hi, sp), hi),
                    s_add(sp, sp, RI_I(1)),
                  ],
                  vec![
                    s_store(AM_RR(offs_stack_lo, sp), m),
                    s_store(AM_RR(offs_stack_hi, sp), hi),
                    s_add(sp, sp, RI_I(1)),
                    s_store(AM_RR(offs_stack_lo, sp), lo),
                    s_store(AM_RR(offs_stack_hi, sp), n),
                    s_add(sp, sp, RI_I(1)),
                  ],
                ),
              ],
            ),
          ],
        ), // end "if this work unit has more than one item"
        s_cmp_gt(sp_gt_zero, sp, RI_I(0)),
      ],
    ), // end outer loop
    // Check the results, as much as we reasonably can.
    s_imm(sum, 0),
    s_imm(in_order, 1),
    s_load(sum, AM_R(offs_numbers)),
    s_add(i, offs_numbers, RI_I(1)),
    s_repeat_until(
      vec![
        s_load(t0, AM_R(i)),
        s_add(sum, sum, RI_R(t0)),
        s_sub(t2, i, RI_I(1)),
        s_load(t1, AM_R(t2)),
        s_cmp_gt(t2, t1, RI_R(t0)),
        s_if_then(t2, vec![s_imm(in_order, 0)]),
        s_add(i, i, RI_I(1)),
        s_add(guard, offs_numbers, RI_R(num_numbers)),
        s_cmp_ge(guard, i, RI_R(guard)),
      ],
      guard,
    ),
    s_cmp_eq(pass, sum, RI_I(4272946)),
    s_and(pass, in_order, RI_R(pass)),
    s_if_then_else(
      pass,
      vec![s_print_s("PASS (in order, and correct checksum)")],
      vec![s_print_s("FAIL (not in order, or incorrect checksum)")],
    ),
    s_print_s("\n"),
  ];

  bif.finish(stmts, None)
}

// This is a version of fill_then_sum that uses some 2-operand insns.
fn test_fill_then_sum_2a() -> Func {
  let mut func = Func::new("fill_then_sum_2a");
  func.set_entry("set-loop-pre");

  // Regs, virtual and real, that we want to use.
  let v_nent = func.new_virtual_reg(RegClass::I32);
  let v_i = func.new_virtual_reg(RegClass::I32);
  let v_sum = func.new_virtual_reg(RegClass::I32);
  // "index=2" is arbitrary.
  let r_tmp = Reg::new_real(RegClass::I32, 0x0, /*index=*/ 2);
  let v_tmp2 = func.new_virtual_reg(RegClass::I32);

  // Loop pre-header for filling array with numbers.
  // This is also the entry point.
  func.block(
    "set-loop-pre",
    vec![i_imm(v_nent, 10), i_imm(v_i, 0), i_goto("set-loop-header")],
  );

  func.block("set-loop-header", vec![i_goto("set-loop")]);

  // Filling loop
  func.block(
    "set-loop",
    vec![
      i_store(AM_R(v_i), v_i),
      i_addm(v_i, RI_I(1)),
      i_cmp_lt(r_tmp, v_i, RI_R(v_nent)),
      i_goto_ctf(r_tmp, "set-loop-continue", "sum-loop-pre"),
    ],
  );

  func.block("set-loop-continue", vec![i_goto("set-loop-header")]);

  // Loop pre-header for summing them
  func.block(
    "sum-loop-pre",
    vec![i_imm(v_sum, 0), i_imm(v_i, 0), i_goto("sum-loop-header")],
  );

  func.block("sum-loop-header", vec![i_goto("sum-loop")]);

  // Summing loop
  func.block(
    "sum-loop",
    vec![
      i_load(r_tmp, AM_R(v_i)),
      i_addm(v_sum, RI_R(r_tmp)),
      i_addm(v_i, RI_I(1)),
      i_cmp_lt(v_tmp2, v_i, RI_R(v_nent)),
      i_goto_ctf(v_tmp2, "sum-loop-continue", "print-result"),
    ],
  );

  func.block("sum-loop-continue", vec![i_goto("sum-loop-header")]);

  // After loop.  Print result and stop.
  func.block(
    "print-result",
    vec![
      i_print_s("Sum = "),
      i_print_i(v_sum),
      i_print_s("\n"),
      i_finish(Some(v_sum)),
    ],
  );

  func.finish();
  func
}

// This is a version of ssort that uses some 2-operand insns.
fn test_ssort_2a() -> Func {
  let mut func = Func::new("ssort_2a");
  func.set_entry("Lstart");

  // This is a simple "shellsort" test.  An array of numbers to sort is
  // placed in mem[5..24] and an increment table is placed in mem[0..4].
  // mem[5..24] is then sorted and the result is printed.
  //
  // This test features 15 basic blocks, 10 virtual registers, at least one
  // of which has multiple independent live ranges, a 3-deep loop nest, and
  // some live ranges which span parts of the loop nest.  So it's an
  // interesting test case.

  let lo = func.new_virtual_reg(RegClass::I32);
  let hi = func.new_virtual_reg(RegClass::I32);
  let i = func.new_virtual_reg(RegClass::I32);
  let j = func.new_virtual_reg(RegClass::I32);
  let h = func.new_virtual_reg(RegClass::I32);
  let big_n = func.new_virtual_reg(RegClass::I32);
  let v = func.new_virtual_reg(RegClass::I32);
  let hp = func.new_virtual_reg(RegClass::I32);
  let t0 = func.new_virtual_reg(RegClass::I32);
  let zero = func.new_virtual_reg(RegClass::I32);

  func.block(
    "Lstart",
    vec![
      i_imm(zero, 0),
      // Store the increment table
      i_imm(t0, 1),
      i_store(AM_RI(zero, 0), t0),
      i_imm(t0, 4),
      i_store(AM_RI(zero, 1), t0),
      i_imm(t0, 13),
      i_store(AM_RI(zero, 2), t0),
      i_imm(t0, 40),
      i_store(AM_RI(zero, 3), t0),
      i_imm(t0, 121),
      i_store(AM_RI(zero, 4), t0),
      // Store the numbers to be sorted
      i_imm(t0, 30),
      i_store(AM_RI(zero, 5), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 6), t0),
      i_imm(t0, 31),
      i_store(AM_RI(zero, 7), t0),
      i_imm(t0, 29),
      i_store(AM_RI(zero, 8), t0),
      i_imm(t0, 32),
      i_store(AM_RI(zero, 9), t0),
      i_imm(t0, 66),
      i_store(AM_RI(zero, 10), t0),
      i_imm(t0, 77),
      i_store(AM_RI(zero, 11), t0),
      i_imm(t0, 44),
      i_store(AM_RI(zero, 12), t0),
      i_imm(t0, 22),
      i_store(AM_RI(zero, 13), t0),
      i_imm(t0, 11),
      i_store(AM_RI(zero, 14), t0),
      i_imm(t0, 99),
      i_store(AM_RI(zero, 15), t0),
      i_imm(t0, 11),
      i_store(AM_RI(zero, 16), t0),
      i_imm(t0, 12),
      i_store(AM_RI(zero, 17), t0),
      i_imm(t0, 7),
      i_store(AM_RI(zero, 18), t0),
      i_imm(t0, 9),
      i_store(AM_RI(zero, 19), t0),
      i_imm(t0, 2),
      i_store(AM_RI(zero, 20), t0),
      i_imm(t0, 32),
      i_store(AM_RI(zero, 21), t0),
      i_imm(t0, 23),
      i_store(AM_RI(zero, 22), t0),
      i_imm(t0, 41),
      i_store(AM_RI(zero, 23), t0),
      i_imm(t0, 14),
      i_store(AM_RI(zero, 24), t0),
      // The real computation begins here
      i_imm(lo, 5),  // Lowest address of the range to sort
      i_imm(hi, 24), // Highest address of the range to sort
      i_copy(t0, hi),
      i_subm(t0, RI_R(lo)),
      i_add(big_n, t0, RI_I(1)),
      i_imm(hp, 0),
      i_goto("L11"),
    ],
  );

  func.block(
    "L11",
    vec![
      i_load(t0, AM_R(hp)),
      i_cmp_gt(t0, t0, RI_R(big_n)),
      i_goto_ctf(t0, "L19", "L11a"),
    ],
  );

  func.block("L19", vec![i_goto("L20")]);

  func.block("L11a", vec![i_addm(hp, RI_I(1)), i_goto("L11")]);

  func.block(
    "L20",
    vec![i_cmp_lt(t0, hp, RI_I(1)), i_goto_ctf(t0, "L60", "L21a")],
  );

  func.block(
    "L21a",
    vec![
      i_copy(t0, hp),
      i_subm(t0, RI_I(1)),
      i_load(h, AM_R(t0)),
      //printf("h = %u\n", h),
      i_copy(i, lo),
      i_addm(i, RI_R(h)),
      i_goto("L30"),
    ],
  );

  func.block(
    "L30",
    vec![i_cmp_gt(t0, i, RI_R(hi)), i_goto_ctf(t0, "L50", "L30a")],
  );

  func.block(
    "L30a",
    vec![
      i_load(v, AM_R(i)),
      i_copy(j, i), // FIXME: is this a coalescable copy?
      i_goto("L40"),
    ],
  );

  func.block(
    "L40",
    vec![
      i_copy(t0, j),
      i_subm(t0, RI_R(h)),
      i_load(t0, AM_R(t0)),
      i_cmp_le(t0, t0, RI_R(v)),
      i_goto_ctf(t0, "L41", "L40a"),
    ],
  );

  func.block("L41", vec![i_goto("L45")]);

  func.block(
    "L40a",
    vec![
      i_copy(t0, j),
      i_subm(t0, RI_R(h)),
      i_load(t0, AM_R(t0)),
      i_store(AM_R(j), t0),
      i_subm(j, RI_R(h)),
      i_copy(t0, lo),
      i_addm(t0, RI_R(h)),
      i_subm(t0, RI_I(1)),
      i_cmp_le(t0, j, RI_R(t0)),
      i_goto_ctf(t0, "L40a1", "L40a2"),
    ],
  );

  func.block("L40a1", vec![i_goto("L45")]);
  func.block("L40a2", vec![i_goto("L40")]);

  func
    .block("L45", vec![i_store(AM_R(j), v), i_addm(i, RI_I(1)), i_goto("L30")]);

  func.block("L50", vec![i_subm(hp, RI_I(1)), i_goto("L20")]);

  func.block(
    "L60",
    vec![
      i_copy(i, lo), // FIXME: ditto
      i_goto("L61"),
    ],
  );

  func.block(
    "L61",
    vec![i_cmp_gt(t0, i, RI_R(hi)), i_goto_ctf(t0, "L62", "L61a")],
  );

  func.block(
    "L61a",
    vec![
      i_load(t0, AM_R(i)),
      i_print_i(t0),
      i_print_s(" "),
      i_addm(i, RI_I(1)),
      i_goto("L61"),
    ],
  );

  func.block("L62", vec![i_print_s("\n"), i_finish(None)]);

  func.finish();
  func
}

fn test_fp1() -> Func {
  let mut bif = Blockifier::new("fp1");
  let zz = bif.new_virtual_reg(RegClass::I32);
  let f0 = bif.new_virtual_reg(RegClass::F32);
  let f1 = bif.new_virtual_reg(RegClass::F32);
  let f2 = bif.new_virtual_reg(RegClass::F32);
  // Do some extremely lame FP things.  This tests insns (storef, loadf) that
  // use more than one register class.

  let stmts = vec![
    s_immf(f0, 0.123),
    s_immf(f1, 0.456),
    s_fadd(f0, f0, f1),
    s_fmul(f0, f0, f1),
    s_fsub(f0, f0, f1),
    s_fdiv(f0, f0, f1),
    s_imm(zz, 0),
    s_storef(AM_RI(zz, 0), f0),
    s_loadf(f2, AM_RI(zz, 0)),
    s_print_f(f2),
    s_print_s("\n"),
  ];

  bif.finish(stmts, Some(f2))
}

fn test_fp2() -> Func {
  let mut bif = Blockifier::new("fp2");
  let num_items = bif.new_virtual_reg(RegClass::I32);
  let num_items_m2 = bif.new_virtual_reg(RegClass::I32);
  let zero = bif.new_virtual_reg(RegClass::I32);
  let i = bif.new_virtual_reg(RegClass::I32);
  let j = bif.new_virtual_reg(RegClass::I32);
  let k = bif.new_virtual_reg(RegClass::I32);
  let bi = bif.new_virtual_reg(RegClass::I32);
  let bj = bif.new_virtual_reg(RegClass::I32);
  let f0 = bif.new_virtual_reg(RegClass::F32);
  let f1 = bif.new_virtual_reg(RegClass::F32);
  let f2 = bif.new_virtual_reg(RegClass::F32);

  // This test has a double-nested loop with a bit of FP register action in
  // the innermost loop.

  let stmts = vec![
    s_imm(num_items, 10),
    s_sub(num_items_m2, num_items, RI_I(2)),
    // Park initial numbers in mem[0..9]
    s_imm(zero, 0),
    s_immf(f0, 3.0),
    s_storef(AM_RI(zero, 0), f0),
    s_immf(f0, 1.0),
    s_storef(AM_RI(zero, 1), f0),
    s_immf(f0, 4.0),
    s_storef(AM_RI(zero, 2), f0),
    s_immf(f0, 1.0),
    s_storef(AM_RI(zero, 3), f0),
    s_immf(f0, 5.0),
    s_storef(AM_RI(zero, 4), f0),
    s_immf(f0, 9.0),
    s_storef(AM_RI(zero, 5), f0),
    s_immf(f0, 2.0),
    s_storef(AM_RI(zero, 6), f0),
    s_immf(f0, 6.0),
    s_storef(AM_RI(zero, 7), f0),
    s_immf(f0, 5.0),
    s_storef(AM_RI(zero, 8), f0),
    s_immf(f0, 4.0),
    s_storef(AM_RI(zero, 9), f0),
    // Do the following 10 times:
    //   "smooth" the array by doing a moving average on it
    //     = replace each mem[i] for i in 2 ..= nItemsM2 with
    //       (mem[i-2] + mem[i-1] + mem[i] + mem[i+1] + mem[i+2]) / 5.0
    //   print it out
    s_imm(j, 0),
    s_repeat_until(
      vec![
        // smooth
        s_imm(i, 2),
        s_repeat_until(
          vec![
            s_sub(k, i, RI_I(2)),
            s_loadf(f0, AM_RI(k, 0)),
            s_loadf(f1, AM_RI(k, 1)),
            s_loadf(f2, AM_RI(k, 2)),
            s_fadd(f0, f0, f1),
            s_fadd(f0, f0, f2),
            s_loadf(f1, AM_RI(k, 3)),
            s_loadf(f2, AM_RI(k, 4)),
            s_fadd(f0, f0, f1),
            s_fadd(f0, f0, f2),
            s_immf(f1, 5.0),
            s_fdiv(f0, f0, f1),
            s_storef(AM_RI(k, 2), f0),
            s_addm(i, RI_I(1)),
            s_cmp_ge(bi, i, RI_R(num_items_m2)),
          ],
          bi,
        ),
        // print the array
        s_imm(i, 0),
        s_repeat_until(
          vec![
            s_loadf(f0, AM_RI(i, 0)),
            s_print_f(f0),
            s_print_s(" "),
            s_addm(i, RI_I(1)),
            s_cmp_ge(bi, i, RI_R(num_items)),
          ],
          bi,
        ),
        s_print_s("\n"),
        s_addm(j, RI_I(1)),
        s_cmp_ge(bj, j, RI_R(num_items)),
      ],
      bj,
    ),
  ];

  bif.finish(stmts, None)
}

fn test_stmt_repeat() -> Func {
  let mut bif = Blockifier::new("stmt_repeat");

  let max_j = bif.new_virtual_reg(RegClass::I32);
  let i = bif.new_virtual_reg(RegClass::I32);
  let j = bif.new_virtual_reg(RegClass::I32);
  let k = bif.new_virtual_reg(RegClass::I32);
  let bi = bif.new_virtual_reg(RegClass::I32);

  let stmts = vec![
    s_imm(max_j, 3),
    s_imm(i, 0),
    s_imm(j, 0),
    s_repeat_until(
      vec![
        s_imm(i, 0),
        s_repeat_until(
          vec![
            s_sub(k, i, RI_I(1)),
            s_addm(i, RI_I(1)),
            s_print_i(i),
            s_cmp_ge(bi, i, RI_I(2)),
          ],
          bi,
        ),
        s_imm(i, 0),
        s_addm(j, RI_I(1)),
        s_cmp_ge(bi, j, RI_R(max_j)),
      ],
      bi,
    ),
  ];

  bif.finish(stmts, None)
}

// This is the list of available tests.  This function returns either the
// requested Func, or if not found, a list of the available ones.
pub fn find_func(name: &str) -> Result<Func, Vec<String>> {
  // This is really stupid.  Fortunately it's not performance critical :)
  let all_funcs = vec![
    test_sort(), // shellsort
    test_sort2(),
    test_3_loops(),          // three loops
    test_stmts(),            // a small Stmty test
    test_needs_splitting(),  // LR splitting might help here ..
    test_needs_splitting2(), // .. same, but with LRs split by hand
    test_qsort(),            // big qsort test, 3-operand only
    test_fill_then_sum_2a(), // 2-operand version of fill_then_sum
    test_ssort_2a(),         // 2-operand version of shellsort
    test_fp1(),              // very feeble floating point
    test_fp2(),              // floating point with loops and arrays
    test_stmt_repeat(),
    test_stmt_loop(),
  ];

  let mut all_names = Vec::new();
  for cand in &all_funcs {
    all_names.push(cand.name.clone());
  }

  for cand in all_funcs {
    if cand.name == *name {
      return Ok(cand);
    }
  }

  fn ends_in_tilde(path: &PathBuf) -> bool {
    if let Some(strr) = path.to_str() {
      let n = strr.len();
      if n >= 2 && strr[n - 1..n - 0] == *"~" {
        return true;
      }
    }
    false
  }

  let test_dir = Path::new("tests");
  match test_dir.read_dir() {
    Err(err) => {
      println!("can't read test directory: {}", err);
    }
    Ok(entries) => {
      for entry in entries {
        if let Ok(entry) = entry {
          let path = entry.path();
          // Skip emacs backup files.  These have names ending in '~'.  Not
          // skipping them it impossible to edit .rat files with emacs,
          // because this logic will often read the backup file in preference
          // to the the real one.
          if ends_in_tilde(&path) {
            continue;
          }
          let basename = path.file_stem().unwrap().to_str().unwrap();
          if basename == name {
            let func = parser::parse_file(path).expect("unparseable test file");
            return Ok(func);
          } else {
            all_names.push(basename.to_string())
          }
        }
      }
    }
  }

  all_names.sort();
  Err(all_names)
}
