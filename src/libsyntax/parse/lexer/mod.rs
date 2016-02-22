use std::mem::replace;
use std::ops::{Add, Sub};
use std::rc::Rc;

use ast::{self, TokenTree};
use codemap::{self, BytePos, CharPos, DUMMY_SP, Pos, Span};
use errors::{FatalError, Handler, DiagnosticBuilder};
use parse::token::{self, str_to_ident};

pub trait Reader {
    fn is_eof(&self) -> bool;
    fn next_token(&mut self) -> TokenAndSpan;
    /// Report a fatal error with the current span.
    fn fatal(&self, &str) -> FatalError;
    /// Report a non-fatal error with the current span.
    fn err(&self, &str);
    fn peek(&self) -> TokenAndSpan;
    /// Get a token the parser cares about.
    fn real_token(&mut self) -> TokenAndSpan {
      let mut t = self.next_token();
      loop {
        match t.tok {
          token::Whitespace => {
            t = self.next_token();
          },
          _ => break
        }
      }
      t
    }
}

pub struct TtReader<'a> {
  pub sp_diag: &'a Handler,
  tt: Vec<ast::TokenTree>,
  cur_idx: usize,

  /* cached: */
  pub cur_tok: token::Token,
  pub cur_span: Span,
}

impl<'a> TtReader<'a> {
  pub fn new(sp_diag: &'a Handler, tt: Vec<ast::TokenTree>) -> TtReader<'a> {
    TtReader {
      sp_diag: sp_diag,
      tt: tt,
      cur_idx: 0,
      /* dummy values, never read: */
      cur_tok: token::Eof,
      cur_span: DUMMY_SP,
    }
  }
}

impl<'a> Reader for TtReader<'a> {
    fn is_eof(&self) -> bool {
      self.cur_tok == token::Eof
    }

    fn next_token(&mut self) -> TokenAndSpan {
      let ret_val = TokenAndSpan {
        tok: self.cur_tok.clone(),
        sp: self.cur_span.clone(),
      };

      let cur_idx = self.cur_idx;

      if cur_idx <= self.tt.len() {
        match self.tt[cur_idx].clone() {
          TokenTree::Token(sp, token) => {
            self.cur_tok = token;
            self.cur_span = sp;
          }
          _ => panic!("not TokenTree::Token")
        }

        self.cur_idx += 1;
      }

      ret_val
    }

    /// Report a fatal error with the current span.
    fn fatal(&self, m: &str) -> FatalError {
      self.sp_diag.span_fatal(self.cur_span, m)
    }

    /// Report a non-fatal error with the current span.
    fn err(&self, m: &str) {
      self.sp_diag.span_fatal(self.cur_span, m);
    }

    fn peek(&self) -> TokenAndSpan {
      TokenAndSpan {
        tok: self.cur_tok.clone(),
        sp: self.cur_span,
      }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TokenAndSpan {
  pub tok: token::Token,
  pub sp: Span,
}

pub struct StringReader<'a> {
  pub span_diagnostic: &'a Handler,
    /// The absolute offset within the codemap of the next character to read
    pub pos: BytePos,
    /// The absolute offset within the codemap of the last character read(curr)
    pub last_pos: BytePos,
    /// The column of the next character to read
    pub col: CharPos,
    /// The last character to be read
    pub curr: Option<char>,
    pub filemap: Rc<codemap::FileMap>,
    // cached:
    pub peek_tok: token::Token,
    pub peek_span: Span,

    // cache a direct reference to the source text, so that we don't have to
    // retrieve it via `self.filemap.src.as_ref().unwrap()` all the time.
    source_text: Rc<String>,
}

pub fn char_at(s: &str, byte: usize) -> char {
  s[byte..].chars().next().unwrap()
}

fn in_range(c: Option<char>, lo: char, hi: char) -> bool {
  match c {
    Some(c) => lo <= c && c <= hi,
    _ => false
  }
}

fn is_dec_digit(c: Option<char>) -> bool { return in_range(c, '0', '9'); }

pub fn is_whitespace(c: Option<char>) -> bool {
  match c.unwrap_or('\x00') { // None can be null for now... it's not whitespace
    ' ' | '\n' | '\t' | '\r' => true,
    _ => false
  }
}

fn ident_start(c: Option<char>) -> bool {
  let c = match c { Some(c) => c, None => return false };

  (c >= 'a' && c <= 'z')
    || (c >= 'A' && c <= 'Z')
    || c == '_'
    || (c > '\x7f' && c.is_xid_start())
}

fn ident_continue(c: Option<char>) -> bool {
  let c = match c { Some(c) => c, None => return false };

  (c >= 'a' && c <= 'z')
    || (c >= 'A' && c <= 'Z')
    || (c >= '0' && c <= '9')
    || c == '_'
    || (c > '\x7f' && c.is_xid_continue())
}

impl<'a> Reader for StringReader<'a> {
  fn is_eof(&self) -> bool { self.curr.is_none() }

  fn next_token(&mut self) -> TokenAndSpan {
    let ret_val = TokenAndSpan {
      tok: replace(&mut self.peek_tok, token::Underscore),
      sp: self.peek_span,
    };
    self.advance_token();
    ret_val
  }

  fn fatal(&self, m: &str) -> FatalError {
    self.fatal_span(self.peek_span, m)
  }
  fn err(&self, m: &str) {
    self.err_span(self.peek_span, m)
  }

  fn peek(&self) -> TokenAndSpan {
        // FIXME(pcwalton): Bad copy!
    TokenAndSpan {
      tok: self.peek_tok.clone(),
      sp: self.peek_span,
    }
  }
}

impl<'a> StringReader<'a> {

  /// For comments.rs, which hackily pokes into pos and curr
    pub fn new_raw<'b>(span_diagnostic: &'b Handler,
                       filemap: Rc<codemap::FileMap>)
                       -> StringReader<'b> {
        if filemap.src.is_none() {
            span_diagnostic.bug(&format!("Cannot lex filemap \
                                          without source: {}",
                                         filemap.name)[..]);
        }

        let source_text = (*filemap.src.as_ref().unwrap()).clone();

        let mut sr = StringReader {
            span_diagnostic: span_diagnostic,
            pos: filemap.start_pos,
            last_pos: filemap.start_pos,
            col: CharPos(0),
            curr: Some('\n'),
            filemap: filemap,
            // dummy values; not read
            peek_tok: token::Eof,
            peek_span: codemap::DUMMY_SP,
            source_text: source_text,
        };
        sr.bump();
        sr
    }

  pub fn new<'b>(span_diagnostic: &'b Handler,
                   filemap: Rc<codemap::FileMap>)
                   -> StringReader<'b> {
        let mut sr = StringReader::new_raw(span_diagnostic, filemap);
        sr.advance_token();
        sr
    }

  pub fn curr_is(&self, c: char) -> bool {
    self.curr == Some(c)
  }

  /// Report a fatal lexical error with a given span.
    pub fn fatal_span(&self, sp: Span, m: &str) -> FatalError {
        self.span_diagnostic.span_fatal(sp, m)
    }

    /// Report a lexical error with a given span.
    pub fn err_span(&self, sp: Span, m: &str) {
        self.span_diagnostic.span_err(sp, m)
    }

  /// Advance peek_tok and peek_span to refer to the next token, and
  /// possibly update the interner.
  fn advance_token(&mut self) {
    match self.scan_whitespace_or_comment() {
      Some(comment) => {
        self.peek_span = comment.sp;
        self.peek_tok = comment.tok;
      },
      None => {
        if self.is_eof() {
          self.peek_tok = token::Eof;
          self.peek_span = codemap::mk_sp(self.last_pos, self.last_pos);
        } else {
          let start_bytepos = self.last_pos;
          self.peek_tok = self.next_token_inner();
          self.peek_span = codemap::mk_sp(start_bytepos,
                                          self.last_pos);
        };
      }
    }
  }

  fn byte_offset(&self, pos: BytePos) -> BytePos {
    (pos - BytePos(0))
  }

  /// Calls `f` with a string slice of the source text spanning from `start`
  /// up to but excluding `self.last_pos`, meaning the slice does not include
  /// the character `self.curr`.
  pub fn with_str_from<T, F>(&self, start: BytePos, f: F) -> T
      where F: FnOnce(&str) -> T {
    self.with_str_from_to(start, self.last_pos, f)
  }

  /// Create a Name from a given offset to the current offset, each
  /// adjusted 1 towards each other (assumes that on either side there is a
  /// single-byte delimiter).
  pub fn name_from(&self, start: BytePos) -> ast::Name {
    debug!("taking an ident from {:?} to {:?}", start, self.last_pos);
    self.with_str_from(start, token::intern)
  }

  /// Calls `f` with a string slice of the source text spanning from `start`
  /// up to but excluding `end`.
  fn with_str_from_to<T, F>(&self, start: BytePos, end: BytePos, f: F) -> T where
      F: FnOnce(&str) -> T {
    f(&self.source_text[self.byte_offset(start).to_usize()..
                        self.byte_offset(end).to_usize()])
  }

  pub fn nextch(&self) -> Option<char> {
    let offset = self.byte_offset(self.pos).to_usize();
    if offset < self.source_text.len() {
      Some(char_at(&self.source_text, offset))
    } else {
      None
    }
  }

  pub fn nextch_is(&self, c: char) -> bool {
    self.nextch() == Some(c)
  }

  pub fn nextnextch(&self) -> Option<char> {
    let offset = self.byte_offset(self.pos).to_usize();
    let s = &self.source_text[..];

    if offset >= s.len() { return None }
    let next = offset + char_at(s, offset).len_utf8();
    if next < s.len() {
      Some(char_at(s, next))
    } else {
       None
    }
  }

  fn binop(&mut self, op: token::BinOpToken) -> token::Token {
    self.bump();
    if self.curr_is('=') {
      self.bump();
      return token::BinOpEq(op);
    } else {
      return token::BinOp(op);
    }
  }

  /// Return the next token from the string, advances the input past that
  /// token, and updates the interner
  fn next_token_inner(&mut self) -> token::Token {
    let c = self.curr;

    if ident_start(c) && match (c.unwrap(), self.nextch(), self.nextnextch()) {
      // Note: r as in r" or r#" is part of a raw string literal,
      // b as in b' is part of a byte literal.
      // They are not identifiers, and are handled further down.

      // exception identifier should be here
      ('r', Some('"'), _) | ('r', Some('#'), _) |
      ('b', Some('"'), _) | ('b', Some('\''), _) |
      ('b', Some('r'), Some('"')) | ('b', Some('r'), Some('#')) => false,
      _ => true

    } {
      let start = self.last_pos;
      while ident_continue(self.curr) {
        self.bump();
      }

      return self.with_str_from(start, |string| {
        if string == "_" {
          token::Underscore
        } else {
          token::Ident(str_to_ident(string), token::Plain)
        }
      });
    }

    if is_dec_digit(c) {
      let num = self.scan_number(c.unwrap());
      let suffix = self.scan_optional_raw_name();
      debug!("next_token_inner: scanned number {:?}, {:?}", num, suffix);
      return token::Literal(num, suffix)
    }

    match c.expect("next_token_inner called at EOF") {
      // =, ==
      '=' => {
        self.bump();
        if self.curr_is('=') {
          self.bump();
          return token::EqEq;
        } else {
          return token::Eq;
        }
      }

      // <, <=, <-
      '<' => {
        self.bump();
        match self.curr.unwrap_or('\x00') {
          '=' => { self.bump(); return token::Le; }
          '-' => {
            self.bump();
            match self.curr.unwrap_or('\x00') {
              _ => { return token::LArrow; }
              }
          }
          _ => { return token::Lt; }
        }
      }

      // !, !=
      '!' => {
        self.bump();
        if self.curr_is('=') {
          self.bump();
          return token::Ne;
        } else { return token::Not; }
      }

      // >, >=
      '>' => {
        self.bump();
        match self.curr.unwrap_or('\x00') {
          '=' => { self.bump(); return token::Ge; }
          '>' => { return self.binop(token::Shr); }
          _ => { return token::Gt; }
        }
      }

      ';' => { self.bump(); return token::Semi; },
      ',' => { self.bump(); return token::Comma; },
      '.' => {
        self.bump();
        return if self.curr_is('.') {
          self.bump();
          if self.curr_is('.') {
            self.bump();
            token::DotDotDot
          } else {
            token::DotDot
          }
        } else {
          token::Dot
        };
      },

      '@' => { self.bump(); return token::At; }
      '#' => { self.bump(); return token::Pound; }
      '~' => { self.bump(); return token::Tilde; }
      '?' => { self.bump(); return token::Question; }


      c => { // unknown start of token
        let last_bpos = self.last_pos;
        let bpos = self.pos;
        // unicode_chars::check_for_substitution(&self, c);
        panic!("unknown start of token: {:?} to {:?}", last_bpos, bpos);
        // TODO - change it to err_span
        //panic!(self.fatal_span_char(last_bpos, bpos, "unknown start of token", c))
      }
    }
  }

  /// Scan over a float exponent.
  fn scan_float_exponent(&mut self) {
    if self.curr_is('e') || self.curr_is('E') {
      self.bump();
      if self.curr_is('-') || self.curr_is('+') {
        self.bump();
      }
      if self.scan_digits(10, 10) == 0 {
        panic!("expected at least one digit in exponent: {:?} to {:?}",
          self.last_pos, self.pos);
        // TODO - change it to err_span
        //self.err_span_(self.last_pos, self.pos, "expected at least one digit in exponent")
      }
    }
  }

  /// Check that a base is valid for a floating literal, emitting a nice
  /// error if it isn't.
  fn check_float_base(&mut self, start_bpos: BytePos, last_bpos: BytePos, base: usize) {
    // TODO - change it to err_span
    /*
    match base {
      16 => self.err_span_(start_bpos, last_bpos, "hexadecimal float literal is not \
                           supported"),
      8 => self.err_span_(start_bpos, last_bpos, "octal float literal is not supported"),
      2 => self.err_span_(start_bpos, last_bpos, "binary float literal is not supported"),
      _   => ()
    }*/

    match base {
      16 => panic!("hexadecimal float literal is not supported: {:?} to {:?}",
              start_bpos, last_bpos),
      8 => panic!("octal float literal is not supported: {:?} to {:?}",
              start_bpos, last_bpos),
      2 => panic!("binary float literal is not supported: {:?} to {:?}",
              start_bpos, last_bpos),
      _   => ()
    }
  }

  /// Eats <XID_start><XID_continue>*, if possible.
  fn scan_optional_raw_name(&mut self) -> Option<ast::Name> {
    if !ident_start(self.curr) {
      return None
    }
    let start = self.last_pos;
    while ident_continue(self.curr) {
      self.bump();
    }

    self.with_str_from(start, |string| {
      if string == "_" {
        None
      } else {
        Some(token::intern(string))
      }
    })
  }

  /// If there is whitespace, shebang, or a comment, scan it. Otherwise,
  /// return None.
  pub fn scan_whitespace_or_comment(&mut self) -> Option<TokenAndSpan> {
    match self.curr.unwrap_or('\0') {
      // # to handle shebang at start of file -- this is the entry point
      // for skipping over all "junk"
      c if is_whitespace(Some(c)) => {
        let start_bpos = self.last_pos;
        while is_whitespace(self.curr) { self.bump(); }
        let c = Some(TokenAndSpan {
          tok: token::Whitespace,
          sp: codemap::mk_sp(start_bpos, self.last_pos)
        });
        debug!("scanning whitespace: {:?}", c);
        c
      },
      _ => None
    }
  }

  /// Scan through any digits (base `scan_radix`) or underscores,
  /// and return how many digits there were.
  ///
  /// `real_radix` represents the true radix of the number we're
  /// interested in, and errors will be emitted for any digits
  /// between `real_radix` and `scan_radix`.
  fn scan_digits(&mut self, real_radix: u32, scan_radix: u32) -> usize {
    assert!(real_radix <= scan_radix);
    let mut len = 0;
    loop {
      let c = self.curr;
      if c == Some('_') { debug!("skipping a _"); self.bump(); continue; }
      match c.and_then(|cc| cc.to_digit(scan_radix)) {
        Some(_) => {
          debug!("{:?} in scan_digits", c);
          // check that the hypothetical digit is actually
          // in range for the true radix
          if c.unwrap().to_digit(real_radix).is_none() {
            panic!("{}: {:?} to {:?}",
              &format!("invalid digit for a base {} literal", real_radix),
              self.last_pos, self.pos);
            // TODO - to change err_span
            // self.err_span_(self.last_pos, self.pos,
            //                &format!("invalid digit for a base {} literal",
            //                real_radix));
          }
          len += 1;
          self.bump();
        }
        _ => return len
      }
    };
  }

  /// Lex a LIT_INTEGER or a LIT_FLOAT
  fn scan_number(&mut self, c: char) -> token::Lit {
    let num_digits;
    let mut base = 10;
    let start_bpos = self.last_pos;

    self.bump();

    if c == '0' {
      match self.curr.unwrap_or('\0') {
        'b' => { self.bump(); base = 2; num_digits = self.scan_digits(2, 10); }
        'o' => { self.bump(); base = 8; num_digits = self.scan_digits(8, 10); }
        'x' => { self.bump(); base = 16; num_digits = self.scan_digits(16, 16); }
        '0'...'9' | '_' | '.' => {
          num_digits = self.scan_digits(10, 10) + 1;
        }
        _ => {
          // just a 0
          return token::Integer(self.name_from(start_bpos));
        }
      }
    } else if c.is_digit(10) {
      num_digits = self.scan_digits(10, 10) + 1;
    } else {
      num_digits = 0;
    }

    if num_digits == 0 {
      panic!("no valid digits found for number: {:?} to {:?}",
        start_bpos, self.last_pos);
      // TODO - change it to err_span
      //self.err_span_(start_bpos, self.last_pos, "no valid digits found for number");
      return token::Integer(token::intern("0"));
    }

    // might be a float, but don't be greedy if this is actually an
    // integer literal followed by field/method access or a range pattern
    // (`0..2` and `12.foo()`)
    if self.curr_is('.') && !self.nextch_is('.') && !self.nextch().unwrap_or('\0')
                                                         .is_xid_start() {
      // might have stuff after the ., and if it does, it needs to start
      // with a number
      self.bump();
      if self.curr.unwrap_or('\0').is_digit(10) {
        self.scan_digits(10, 10);
        self.scan_float_exponent();
      }
      let last_pos = self.last_pos;
      self.check_float_base(start_bpos, last_pos, base);
      return token::Float(self.name_from(start_bpos));
    } else {
      // it might be a float if it has an exponent
      if self.curr_is('e') || self.curr_is('E') {
        self.scan_float_exponent();
        let last_pos = self.last_pos;
        self.check_float_base(start_bpos, last_pos, base);
        return token::Float(self.name_from(start_bpos));
      }

      // but we certainly have an integer!
      return token::Integer(self.name_from(start_bpos));
    }
  }

  /// Advance the StringReader by one character. If a newline is
  /// discovered, add it to the FileMap's list of line start offsets.
  pub fn bump(&mut self) {
    self.last_pos = self.pos;
    let current_byte_offset = self.byte_offset(self.pos).to_usize();
    if current_byte_offset < self.source_text.len() {
      assert!(self.curr.is_some());
      let last_char = self.curr.unwrap();
      let ch = char_at(&self.source_text, current_byte_offset);
      let next = current_byte_offset + ch.len_utf8();
      let byte_offset_diff = next - current_byte_offset;
      self.pos = self.pos + Pos::from_usize(byte_offset_diff);
      self.curr = Some(ch);
      self.col = self.col + CharPos(1);

      if last_char == '\n' {
        self.col = CharPos(0);
      }

    } else {
      self.curr = None;
    }

    debug!("ch {}", self.curr.as_ref().unwrap());
  }
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use parse::ParseSess;
  use parse::token::{self, Token};
  use super::*;
  use env_logger;

  fn assert_tok_stream(expected: &[Token], reader: &mut Reader) {
    let mut tokens: Vec<Token> = Vec::new();

    loop {
      let tok = reader.next_token().tok;
      tokens.push(tok.clone());

      if reader.is_eof() {
        break;
      }
    }

    assert_eq!(expected, tokens.as_slice());
  }

  #[test]
  fn test_scan() {
    env_logger::init().unwrap();
    let sess = ParseSess::new();
    //let mut r = StringReader::new(&sess, Rc::new("let x = 10;".to_string()));

    /*
    match r.scan_whitespace_or_comment() {
      Some(Token::Whitespace) => println!("Whitespace"),
      _ => panic!("No whitespace")
    };*/

    //assert_tok_stream(&vec![Token::Eof], &mut r);
  }
}