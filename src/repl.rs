#![feature(libc)]
extern crate libc;
extern crate readline;

use readline::*;

pub fn main() {
  unsafe {
    loop {
      let line = readline(from_str("\x1b[33mtkm> \x1b[0m"));
      if line.is_null() {
        break;
      }
      add_history(line);
    }
  }
}