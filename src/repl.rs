#![feature(libc)]
extern crate libc;
extern crate parser;
extern crate readline;

use std::rc::Rc;

use readline::*;
use parser::*;
use parser::token::Token;

pub fn main() {
  unsafe {
    loop {
      let line = readline(from_str("\x1b[33mtkm> \x1b[0m"));
      if line.is_null() {
        break;
      }
      
      let mut sr = StringReader::new(Rc::new(to_str(line).to_string()));
      loop {
        let toksp = sr.next_token();
        print!("{} ", toksp.tok);
        
        if toksp.tok == Token::Eof {
          println!("");
          break;
        }
      }
            
      add_history(line);
    }
  }
}