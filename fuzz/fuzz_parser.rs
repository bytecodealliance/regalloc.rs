#![no_main]
use libfuzzer_sys::fuzz_target;

use minira::{parser, test_framework as ir};

fuzz_target!(|func: ir::Func| {
  func.print("generated func");

  let mut printed = String::new();
  func.render("func", &mut printed).expect("error when printing the first time");

  let parsed_func = parser::parse_content("funk", &printed).expect("parser error");

  let mut reprinted = String::new();
  parsed_func.render("func", &mut reprinted).unwrap();

  let reparsed_func = parser::parse_content("funk", &reprinted).expect("shouldn't error on the second parse!");
  let mut rereprinted = String::new();
  reparsed_func.render("func", &mut rereprinted).unwrap();

  assert_eq!(reprinted, rereprinted);
});
