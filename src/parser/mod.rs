mod parser;
pub mod token;
pub mod lexer;

use std::rc::Rc;
use std::cell::RefCell;
use std::path::{PathBuf};

use ast;
use codemap::{self, Span, CodeMap};

pub struct Handler;

/// Info about a parsing session.
pub struct ParseSess {
  pub span_diagnostic: Handler, // better be the same as the one in the reader!
  /// Used to determine and report recursive mod inclusions
  included_mod_stack: RefCell<Vec<PathBuf>>,
  code_map: Rc<CodeMap>,
}

impl ParseSess {
    pub fn new() -> ParseSess {
        let cm = Rc::new(CodeMap::new());
        ParseSess::with_span_handler(Handler, cm)
    }

    pub fn with_span_handler(handler: Handler, code_map: Rc<CodeMap>) -> ParseSess {
        ParseSess {
            span_diagnostic: handler,
            included_mod_stack: RefCell::new(vec![]),
            code_map: code_map
        }
    }

    pub fn codemap(&self) -> &CodeMap {
        &self.code_map
    }
}

/*
// Create a new parser from a source string
pub fn new_parser_from_source_str<'a>(sess: &'a ParseSess,
                                      name: String,
                                      source: String)
                                      -> Parser<'a> {
    filemap_to_parser(sess, sess.codemap().new_filemap(name, source))
}

/// Given a filemap and config, return a parser
pub fn filemap_to_parser<'a>(sess: &'a ParseSess,
                             filemap: Rc<FileMap>) -> Parser<'a> {
    let end_pos = filemap.end_pos;
    let mut parser = tts_to_parser(sess, filemap_to_tts(sess, filemap), cfg);

    if parser.token == token::Eof && parser.span == codemap::DUMMY_SP {
        parser.span = codemap::mk_sp(end_pos, end_pos);
    }

    parser
}
*/

#[cfg(test)]
mod tests {
  use super::*;
  use codemap::{Span, BytePos, Pos};

  // produce a codemap::span
  fn sp(a: u32, b: u32) -> Span {
    Span {lo: BytePos(a), hi: BytePos(b)}
  }
  /*
  #[test] fn parse_exprs () {
    // just make sure that they parse....
    string_to_expr("3 + 4".to_string());
  }*/
}