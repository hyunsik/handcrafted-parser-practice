use ast;
use codemap::{self, Span, CodeMap, FileMap};
use errors::{ColorConfig, Handler, DiagnosticBuilder};
use parse::parser::Parser;

use std::cell::RefCell;
use std::path::{Path, PathBuf};
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

// Create a new parser, handling errors as appropriate
/// if the file doesn't exist
pub fn new_parser_from_file<'a>(sess: &'a ParseSess,
                                path: &Path) -> Parser<'a> {
    filemap_to_parser(sess, file_to_filemap(sess, path, None))
}

/// Given a session, a crate config, a path, and a span, add
/// the file at the given path to the codemap, and return a parser.
/// On an error, use the given span as the source of the problem.
pub fn new_sub_parser_from_file<'a>(sess: &'a ParseSess,
                                    path: &Path,
                                    owns_directory: bool,
                                    module_name: Option<String>,
                                    sp: Span) -> Parser<'a> {
    let mut p = filemap_to_parser(sess, file_to_filemap(sess, path, Some(sp)));
    p.owns_directory = owns_directory;
    p.root_module_name = module_name;
    p
}

/// Given a filemap and config, return a parser
pub fn filemap_to_parser<'a>(sess: &'a ParseSess,
                             filemap: Rc<FileMap>) -> Parser<'a> {
    let end_pos = filemap.end_pos;
    let mut parser = tts_to_parser(sess, filemap_to_tts(sess, filemap));

    if parser.token == token::Eof && parser.span == codemap::DUMMY_SP {
        parser.span = codemap::mk_sp(end_pos, end_pos);
    }

    parser
}

// must preserve old name for now, because quote! from the *existing*
// compiler expands into it
pub fn new_parser_from_tts<'a>(sess: &'a ParseSess,
                               tts: Vec<ast::TokenTree>) -> Parser<'a> {
    tts_to_parser(sess, tts)
}

// base abstractions

/// Given a session and a path and an optional span (for error reporting),
/// add the path to the session's codemap and return the new filemap.
fn file_to_filemap(sess: &ParseSess, path: &Path, spanopt: Option<Span>)
                   -> Rc<FileMap> {
    match sess.codemap().load_file(path) {
        Ok(filemap) => filemap,
        Err(e) => {
            let msg = format!("couldn't read {:?}: {}", path.display(), e);
            match spanopt {
                Some(sp) => panic!(sess.span_diagnostic.span_fatal(sp, &msg)),
                None => panic!(sess.span_diagnostic.fatal(&msg))
            }
        }
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

/// Given tts and produce a parser
pub fn tts_to_parser<'a>(sess: &'a ParseSess,
                         tts: Vec<ast::TokenTree>) -> Parser<'a> {
    let trdr = lexer::TtReader::new(&sess.span_diagnostic, tts);
    let mut p = Parser::new(sess, Box::new(trdr));
    p
}


#[cfg(test)]
mod tests {
  use super::*;
  use codemap::{Span, BytePos, Pos};
  use util::parser_testing::{string_to_tts};

  // produce a codemap::span
  fn sp(a: u32, b: u32) -> Span {
    Span {lo: BytePos(a), hi: BytePos(b)}
  }

  #[test] fn string_to_tts_1() {
    let tts = string_to_tts("fn a (b : i32) { b; }".to_string());
  }
}