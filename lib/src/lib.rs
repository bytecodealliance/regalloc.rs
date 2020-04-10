/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

//! Main file / top-level module for regalloc library.

// Make the analysis module public for fuzzing.
#[cfg(feature = "fuzzing")]
pub mod analysis;
#[cfg(not(feature = "fuzzing"))]
mod analysis;

mod avl_tree;
mod backtracking;
mod checker;
mod data_structures;
mod inst_stream;
mod interface;
mod linear_scan;
mod trees_maps_sets;

pub use crate::interface::*;
