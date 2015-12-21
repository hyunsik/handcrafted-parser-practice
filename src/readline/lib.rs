#![feature(libc)] extern crate libc;

use libc::c_char;

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[link(name = "readline")]
extern "C" {
  /// Reads a line from the command line
  ///
  /// **Arguments**
  /// prompt: prompt to prompt the user with
  ///
  /// **Returns**
  /// returns a cstr if it succeeds, NULL if EOF
  pub fn readline(prompt: *const c_char) -> *const c_char;
  /// Allows a person to press the up arrow, getting their history
  ///
  /// Useful if you're making an interpreter, or a shell, for example
  ///
  /// **Arguments**
  /// line: the actual line to add to history
  pub fn add_history(line: *const c_char);
}

use std::ffi::{CString};

#[inline]
pub fn from_str(s: &str) -> *const c_char {
  CString::new(s.as_bytes()).unwrap().as_ptr()
}