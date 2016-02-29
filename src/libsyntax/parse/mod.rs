use ast;
use codemap::{self, Span, CodeMap, FileMap};
use errors::{ColorConfig, Handler, DiagnosticBuilder};
use parse::parser::Parser;
use ptr::P;

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::rc::Rc;

pub type PResult<'a, T> = Result<T, DiagnosticBuilder<'a>>;

#[macro_use]
pub mod parser;

pub mod lexer;
pub mod token;
pub mod attr;

pub mod common;
pub mod classify;
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

// a bunch of utility functions of the form parse_<thing>_from_<source>
// where <thing> includes crate, expr, item, stmt, tts, and one that
// uses a HOF to parse anything, and <source> includes file and
// source_str.

pub fn parse_crate_from_file(
    input: &Path,
    cfg: ast::CrateConfig,
    sess: &ParseSess
) -> ast::Crate {
    let mut parser = new_parser_from_file(sess, cfg, input);
    abort_if_errors(parser.parse_crate_mod(), &parser)
}

pub fn parse_crate_attrs_from_file(
    input: &Path,
    cfg: ast::CrateConfig,
    sess: &ParseSess
) -> Vec<ast::Attribute> {
    let mut parser = new_parser_from_file(sess, cfg, input);
    abort_if_errors(parser.parse_inner_attributes(), &parser)
}

pub fn parse_crate_from_source_str(name: String,
                                   source: String,
                                   cfg: ast::CrateConfig,
                                   sess: &ParseSess)
                                   -> ast::Crate {
    let mut p = new_parser_from_source_str(sess,
                                           cfg,
                                           name,
                                           source);
    panictry!(p.parse_crate_mod())
}

pub fn parse_crate_attrs_from_source_str(name: String,
                                         source: String,
                                         cfg: ast::CrateConfig,
                                         sess: &ParseSess)
                                         -> Vec<ast::Attribute> {
    let mut p = new_parser_from_source_str(sess,
                                           cfg,
                                           name,
                                           source);
    panictry!(p.parse_inner_attributes())
}

pub fn parse_expr_from_source_str(name: String,
                                  source: String,
                                  cfg: ast::CrateConfig,
                                  sess: &ParseSess)
                                  -> P<ast::Expr> {
    let mut p = new_parser_from_source_str(sess, cfg, name, source);
    panictry!(p.parse_expr())
}

pub fn parse_item_from_source_str(name: String,
                                  source: String,
                                  cfg: ast::CrateConfig,
                                  sess: &ParseSess)
                                  -> Option<P<ast::Item>> {
    let mut p = new_parser_from_source_str(sess, cfg, name, source);
    panictry!(p.parse_item())
}

pub fn parse_meta_from_source_str(name: String,
                                  source: String,
                                  cfg: ast::CrateConfig,
                                  sess: &ParseSess)
                                  -> P<ast::MetaItem> {
    let mut p = new_parser_from_source_str(sess, cfg, name, source);
    panictry!(p.parse_meta_item())
}

pub fn parse_stmt_from_source_str(name: String,
                                  source: String,
                                  cfg: ast::CrateConfig,
                                  sess: &ParseSess)
                                  -> Option<ast::Stmt> {
    let mut p = new_parser_from_source_str(
        sess,
        cfg,
        name,
        source
    );
    panictry!(p.parse_stmt())
}

// Warning: This parses with quote_depth > 0, which is not the default.
pub fn parse_tts_from_source_str(name: String,
                                 source: String,
                                 cfg: ast::CrateConfig,
                                 sess: &ParseSess)
                                 -> Vec<ast::TokenTree> {
    let mut p = new_parser_from_source_str(
        sess,
        cfg,
        name,
        source
    );
    p.quote_depth += 1;
    // right now this is re-creating the token trees from ... token trees.
    panictry!(p.parse_all_token_trees())
}

// Create a new parser from a source string
pub fn new_parser_from_source_str<'a>(sess: &'a ParseSess,
                                      cfg: ast::CrateConfig,
                                      name: String,
                                      source: String)
                                      -> Parser<'a> {
    filemap_to_parser(sess, sess.codemap().new_filemap(name, source), cfg)
}

/// Create a new parser, handling errors as appropriate
/// if the file doesn't exist
pub fn new_parser_from_file<'a>(sess: &'a ParseSess,
                                cfg: ast::CrateConfig,
                                path: &Path) -> Parser<'a> {
    filemap_to_parser(sess, file_to_filemap(sess, path, None), cfg)
}

/// Given a session, a crate config, a path, and a span, add
/// the file at the given path to the codemap, and return a parser.
/// On an error, use the given span as the source of the problem.
pub fn new_sub_parser_from_file<'a>(sess: &'a ParseSess,
                                    cfg: ast::CrateConfig,
                                    path: &Path,
                                    owns_directory: bool,
                                    module_name: Option<String>,
                                    sp: Span) -> Parser<'a> {
    let mut p = filemap_to_parser(sess, file_to_filemap(sess, path, Some(sp)), cfg);
    p.owns_directory = owns_directory;
    p.root_module_name = module_name;
    p
}

/// Given a filemap and config, return a parser
pub fn filemap_to_parser<'a>(sess: &'a ParseSess,
                             filemap: Rc<FileMap>,
                             cfg: ast::CrateConfig) -> Parser<'a> {
    let end_pos = filemap.end_pos;
    let mut parser = tts_to_parser(sess, filemap_to_tts(sess, filemap), cfg);

    if parser.token == token::Eof && parser.span == codemap::DUMMY_SP {
        parser.span = codemap::mk_sp(end_pos, end_pos);
    }

    parser
}

// must preserve old name for now, because quote! from the *existing*
// compiler expands into it
pub fn new_parser_from_tts<'a>(sess: &'a ParseSess,
                               cfg: ast::CrateConfig,
                               tts: Vec<ast::TokenTree>) -> Parser<'a> {
    tts_to_parser(sess, tts, cfg)
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
    let cfg = Vec::new();
    let srdr = lexer::StringReader::new(&sess.span_diagnostic, filemap);
    let mut p1 = Parser::new(sess, cfg, Box::new(srdr));
    panictry!(p1.parse_all_token_trees())
}

/// Given tts and produce a parser
pub fn tts_to_parser<'a>(sess: &'a ParseSess,
                         tts: Vec<ast::TokenTree>,
                         cfg: ast::CrateConfig) -> Parser<'a> {
    let trdr = lexer::new_tt_reader(&sess.span_diagnostic, None, tts);
    let mut p = Parser::new(sess, cfg, Box::new(trdr));
    p
}

fn abort_if_errors<'a, T>(result: PResult<'a, T>, p: &Parser) -> T {
    match result {
        Ok(c) => {
            c
        }
        Err(mut e) => {
            e.emit();
            p.abort_if_errors();
            unreachable!();
        }
    }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ast::{self, TokenTree};
  use parse::token::{Token, str_to_ident};
  use codemap::{Span, BytePos, Pos};
  use util::parser_testing::{string_to_tts, string_to_item};
  use parse::lexer::{Reader, StringReader};
  use parse::parser::Parser;

  use std::rc::Rc;

  // produce a codemap::span
  fn sp(a: u32, b: u32) -> Span {
    Span {lo: BytePos(a), hi: BytePos(b)}
  }

  #[test] fn items_1() {
    let x = string_to_item("fn xyz() { }".to_string());
  }

  #[test] fn items_2() {
    let x = string_to_item("fn xyz(x: i32) { }".to_string());
  }

  #[test]
    fn string_to_tts_1() {
        let tts = string_to_tts("fn a (b : i32) { b; }".to_string());

        let expected = vec![
            TokenTree::Token(sp(0, 2),
                         token::Ident(str_to_ident("fn"),
                         token::IdentStyle::Plain)),
            TokenTree::Token(sp(3, 4),
                         token::Ident(str_to_ident("a"),
                         token::IdentStyle::Plain)),
            TokenTree::Delimited(
                sp(5, 14),
                Rc::new(ast::Delimited {
                    delim: token::DelimToken::Paren,
                    open_span: sp(5, 6),
                    tts: vec![
                        TokenTree::Token(sp(6, 7),
                                     token::Ident(str_to_ident("b"),
                                     token::IdentStyle::Plain)),
                        TokenTree::Token(sp(8, 9),
                                     token::Colon),
                        TokenTree::Token(sp(10, 13),
                                     token::Ident(str_to_ident("i32"),
                                     token::IdentStyle::Plain)),
                    ],
                    close_span: sp(13, 14),
                })),
            TokenTree::Delimited(
                sp(15, 21),
                Rc::new(ast::Delimited {
                    delim: token::DelimToken::Brace,
                    open_span: sp(15, 16),
                    tts: vec![
                        TokenTree::Token(sp(17, 18),
                                     token::Ident(str_to_ident("b"),
                                     token::IdentStyle::Plain)),
                        TokenTree::Token(sp(18, 19),
                                     token::Semi)
                    ],
                    close_span: sp(20, 21),
                }))
        ];

        assert_eq!(tts, expected);
    }
}