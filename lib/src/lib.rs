/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![allow(non_snake_case)]
#![allow(unused_imports)]
#![allow(non_camel_case_types)]

//! Main file / top-level module for minira library.

mod analysis;
mod backtracking;
mod data_structures;
pub mod interface;
mod linear_scan;

pub use crate::interface::*;
