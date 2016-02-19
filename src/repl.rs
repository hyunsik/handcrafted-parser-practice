#![feature(libc)]
extern crate libc;
extern crate syntax;
extern crate rl_sys;

use std::rc::Rc;

use rl_sys::readline;
use syntax::parse::ParseSess;
use syntax::parse::lexer::{Reader, StringReader};
use syntax::parse::token::Token;

pub fn main() {
  /*
    loop {
      match readline::readline("\x1b[33mtkm> \x1b[0m") {
        Ok(Some(line)) => {
          let mut sr = StringReader::new(&ParseSess::new(), Rc::new(line));
          loop {
            let toksp = sr.next_token();
            print!("{} ", toksp.tok);

            if toksp.tok == Token::Eof {
              println!("");
              break;
            }
          }
        }
        Ok(None) => { break; }
        Err(msg) => panic!("{}", msg)
      }
    }
*/
}