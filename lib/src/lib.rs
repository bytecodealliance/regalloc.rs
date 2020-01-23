/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

//! Main file / top-level module for minira library.

mod analysis;
mod backtracking;
mod data_structures;
mod inst_stream;
pub mod interface;
mod linear_scan;

pub use crate::interface::*;
