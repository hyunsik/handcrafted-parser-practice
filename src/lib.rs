#![feature(unicode)]

#[macro_use]
extern crate log;

mod ast;
mod interner;
mod token;

use std::ops::{Add, Sub};
use std::rc::Rc;

use token::{IdentStyle, Token, str_to_ident};

pub struct FatalError;

pub trait Reader {
    fn is_eof(&self) -> bool;
    fn next_token(&mut self) -> Token;
    /// Report a fatal error with the current span.
    fn fatal(&self, &str) -> FatalError;
    /// Report a non-fatal error with the current span.
    fn err(&self, &str);
    fn peek(&self) -> Token;
    /// Get a token the parser cares about.
    fn real_token(&mut self) -> Token {
        let mut t = self.next_token();
        loop {
            match t {
                Token::Whitespace => {
                    t = self.next_token();
                },
                _ => break
            }
        }
        t
    }
}


pub trait Pos {
    fn from_usize(n: usize) -> Self;
    fn to_usize(&self) -> usize;
}

/// A byte offset. Keep this small (currently 32-bits), as AST contains
/// a lot of them.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Debug)]
pub struct BytePos(pub u32);

/// A character offset. Because of multibyte utf8 characters, a byte offset
/// is not equivalent to a character offset. The CodeMap will convert BytePos
/// values to CharPos values as necessary.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Debug)]
pub struct CharPos(pub usize);

impl Pos for BytePos {
    fn from_usize(n: usize) -> BytePos { BytePos(n as u32) }
    fn to_usize(&self) -> usize { let BytePos(n) = *self; n as usize }
}

impl Add for BytePos {
    type Output = BytePos;

    fn add(self, rhs: BytePos) -> BytePos {
        BytePos((self.to_usize() + rhs.to_usize()) as u32)
    }
}

impl Sub for BytePos {
    type Output = BytePos;

    fn sub(self, rhs: BytePos) -> BytePos {
        BytePos((self.to_usize() - rhs.to_usize()) as u32)
    }
}

impl Pos for CharPos {
    fn from_usize(n: usize) -> CharPos { CharPos(n) }
    fn to_usize(&self) -> usize { let CharPos(n) = *self; n }
}

impl Add for CharPos {
    type Output = CharPos;

    fn add(self, rhs: CharPos) -> CharPos {
        CharPos(self.to_usize() + rhs.to_usize())
    }
}

impl Sub for CharPos {
    type Output = CharPos;

    fn sub(self, rhs: CharPos) -> CharPos {
        CharPos(self.to_usize() - rhs.to_usize())
    }
}

pub struct StringReader {  
  /// The absolute offset within the codemap of the next character to read
  pub pos: BytePos,
  /// The absolute offset within the codemap of the last character read(curr)
  pub last_pos: BytePos,
  /// The column of the next character to read
  pub col: CharPos,
  /// The last character to be read  
  pub curr: Option<char>,
  
  /* cached: */
  pub peek_tok: Token,
  pub source_text: Rc<String>
}

pub fn char_at(s: &str, byte: usize) -> char {
  s[byte..].chars().next().unwrap()
}

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

impl<'a> Reader for StringReader {
  fn is_eof(&self) -> bool { self.curr.is_none() }
  
  fn next_token(&mut self) -> Token {
    Token::Whitespace
  }
  
  fn fatal(&self, err: &str) -> FatalError {
    FatalError
  }
  
  fn err(&self, err: &str) {    
  }
  
  fn peek(&self) -> Token {
    Token::Whitespace
  }
}

impl StringReader {
  pub fn new(source_text: Rc<String>) -> StringReader {
    
    StringReader {
      pos: BytePos(0),
      last_pos: BytePos(0),
      col: CharPos(0),
      curr: Some('\n'),
      peek_tok: Token::Eof,
      source_text: source_text 
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
  
  /// Return the next token from the string, advances the input past that
  /// token, and updates the interner
  fn next_token_inner(&mut self) -> Token {
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
          Token::Underscore
        } else {        
          Token::Ident(str_to_ident(string), IdentStyle::Plain)        
        }
      });
    }
    
    Token::Whitespace
  }  
  
  /// If there is whitespace, shebang, or a comment, scan it. Otherwise,
  /// return None.
  pub fn scan_whitespace_or_comment(&mut self) -> Option<Token> {
    match self.curr.unwrap_or('\0') {
      // # to handle shebang at start of file -- this is the entry point
      // for skipping over all "junk"      
      c if is_whitespace(Some(c)) => {
        let start_bpos = self.last_pos;
        while is_whitespace(self.curr) { self.bump(); }
        let c = Some(Token::Whitespace);
        debug!("scanning whitespace: {:?}", c);
        c
      },
      _ => None
    }
  }
  
  /// Advance the StringReader by one character. If a newline is
  /// discovered, add it to the FileMap's list of line start offsets.
  pub fn bump(&mut self) {
    println!("char({}), pos: {:?}, col: {:?}, last_pos: {:?}", 
      self.curr.as_ref().unwrap(), self.pos, self.col, self.last_pos);
    
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
  }
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use token::Token;
  use super::*;  
  
  #[test]
  fn test_scan() {
    let mut r = StringReader::new(Rc::new("  fn".to_string()));
    
    r.bump();
    /*
    match r.scan_whitespace_or_comment() {
      Some(Token::Whitespace) => println!("Whitespace"),
      _ => panic!("No whitespace")
    };*/
    
    match r.next_token_inner() {
      Token::Whitespace => println!("Whitespace"),
      Token::Ident(_, _) => println!("Ident"),
      _ => panic!("No whitespace")
    };
    
    r.bump();
    match r.next_token_inner() {
      Token::Whitespace => println!("Whitespace"),
      Token::Ident(_, _) => println!("Ident"),
      _ => panic!("No whitespace")
    };
    
    r.bump();
    match r.next_token_inner() {
      Token::Whitespace => println!("Whitespace"),
      Token::Ident(n, _) => println!("Ident: {}", n),
      _ => panic!("No whitespace")
    };
  }
}
