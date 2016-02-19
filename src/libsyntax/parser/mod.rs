use ast;
use codemap::{self, Span, CodeMap, FileMap};
use errors::{ColorConfig, Handler, DiagnosticBuilder};
use parser::parser::Parser;

use std::cell::RefCell;
use std::path::{PathBuf};
use std::rc::Rc;

pub type PResult<'a, T> = Result<T, DiagnosticBuilder<'a>>;

#[macro_use]
pub mod parser;

pub mod lexer;
pub mod token;
pub mod obsolete;


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
        let handler = Handler::with_tty_emitter(ColorConfig::Auto, None, true, false, cm.clone());
        ParseSess::with_span_handler(handler, cm)
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

/// Given a filemap, produce a sequence of token-trees
pub fn filemap_to_tts(sess: &ParseSess, filemap: Rc<FileMap>)
    -> Vec<ast::TokenTree> {
    // it appears to me that the cfg doesn't matter here... indeed,
    // parsing tt's probably shouldn't require a parser at all.
    let srdr = lexer::StringReader::new(&sess.span_diagnostic, filemap);
    let mut p1 = Parser::new(sess, Box::new(srdr));
    panictry!(p1.parse_all_token_trees())
}

/*
/// Given a filemap, produce a sequence of token-trees
pub fn filemap_to_tts(sess: &ParseSess, filemap: Rc<FileMap>)
    -> Vec<ast::TokenTree> {
    // it appears to me that the cfg doesn't matter here... indeed,
    // parsing tt's probably shouldn't require a parser at all.
    let cfg = Vec::new();
    let srdr = lexer::StringReader::new(&sess.span_diagnostic, filemap);
    let mut p1 = Parser::new(sess, cfg, Box::new(srdr));
    panictry!(p1.parse_all_token_trees())
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