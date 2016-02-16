#![feature(unicode)]
#![feature(convert)]
#![feature(libc)]

extern crate libc;
extern crate env_logger;
#[macro_use]
extern crate log;

mod ast;
mod codemap;
mod interner;
pub mod token;
pub mod lexer;