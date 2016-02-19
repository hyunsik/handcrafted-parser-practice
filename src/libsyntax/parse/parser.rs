use std::collections::HashSet;
use std::slice;
use std::mem;
use std::rc::Rc;

use ast::{Delimited, TokenTree};
use codemap::Span;
use errors::DiagnosticBuilder;
use print::pprust;
use parse;
use parse::common::{SeqSep, seq_sep_none, seq_sep_trailing_allowed};
use parse::obsolete::ObsoleteSyntax;
use parse::ParseSess;
use parse::token::{self, keywords};
use parse::token::Token;
use parse::lexer::{Reader, TokenAndSpan};
use parse::PResult;

bitflags! {
    flags Restrictions: u8 {
        const RESTRICTION_STMT_EXPR         = 1 << 0,
        const RESTRICTION_NO_STRUCT_LITERAL = 1 << 1,
    }
}

pub struct Parser<'a> {
    pub sess: &'a ParseSess,
    /// the current token:
    pub token: token::Token,
    /// the span of the current token:
    pub span: Span,
    /// the span of the prior token:
    pub last_span: Span,

    /// the previous token or None (only stashed sometimes).
    pub last_token: Option<Box<token::Token>>,
    last_token_interpolated: bool,
    pub buffer: [TokenAndSpan; 4],
    pub buffer_start: isize,
    pub buffer_end: isize,
    pub tokens_consumed: usize,
    pub restrictions: Restrictions,
    pub quote_depth: usize, // not (yet) related to the quasiquoter
    pub reader: Box<Reader+'a>,
    pub interner: Rc<token::IdentInterner>,
    /// The set of seen errors about obsolete syntax. Used to suppress
    /// extra detail when the same error is seen twice
    pub obsolete_set: HashSet<ObsoleteSyntax>,
    /// Used to determine the path to externally loaded source files
    pub mod_path_stack: Vec<token::InternedString>,
    /// Stack of spans of open delimiters. Used for error message.
    pub open_braces: Vec<Span>,
    /// Flag if this parser "owns" the directory that it is currently parsing
    /// in. This will affect how nested files are looked up.
    pub owns_directory: bool,
    /// Name of the root module this parser originated from. If `None`, then the
    /// name is not known. This does not change while the parser is descending
    /// into modules, and sub-parsers have new values for this name.
    pub root_module_name: Option<String>,
    pub expected_tokens: Vec<TokenType>,
}

#[derive(PartialEq, Eq, Clone)]
pub enum TokenType {
    Token(token::Token),
    Keyword(keywords::Keyword),
    Operator,
}

impl TokenType {
    fn to_string(&self) -> String {
        match *self {
            TokenType::Token(ref t) => format!("`{}`", Parser::token_to_string(t)),
            TokenType::Operator => "an operator".to_string(),
            TokenType::Keyword(kw) => format!("`{}`", kw.to_name()),
        }
    }
}

fn is_plain_ident_or_underscore(t: &token::Token) -> bool {
    t.is_plain_ident() || *t == token::Underscore
}

impl<'a> Parser<'a> {
    pub fn new(sess: &'a ParseSess,
               mut rdr: Box<Reader+'a>)
               -> Parser<'a>
    {
        let tok0 = rdr.real_token();
        let span = tok0.sp;
        let placeholder = TokenAndSpan {
            tok: Token::Underscore,
            sp: span,
        };

        Parser {
            reader: rdr,
            interner: token::get_ident_interner(),
            sess: sess,
            token: tok0.tok,
            span: span,
            last_span: span,
            last_token: None,
            last_token_interpolated: false,
            buffer: [
                placeholder.clone(),
                placeholder.clone(),
                placeholder.clone(),
                placeholder.clone(),
            ],
            buffer_start: 0,
            buffer_end: 0,
            tokens_consumed: 0,
            restrictions: Restrictions::empty(),
            quote_depth: 0,
            obsolete_set: HashSet::new(),
            mod_path_stack: Vec::new(),
            open_braces: Vec::new(),
            owns_directory: true,
            root_module_name: None,
            expected_tokens: Vec::new(),
        }
    }

    /// Convert a token to a string using self's reader
    pub fn token_to_string(token: &token::Token) -> String {
        pprust::token_to_string(token)
    }

    /// Convert the current token to a string using self's reader
    pub fn this_token_to_string(&self) -> String {
        Parser::token_to_string(&self.token)
    }

    /// parse a single token tree from the input.
    pub fn parse_token_tree(&mut self) -> PResult<'a, TokenTree> {
      println!("Enter parse_token_tree");

        // this is the fall-through for the 'match' below.
        // invariants: the current token is not a left-delimiter,
        // not an EOF, and not the desired right-delimiter (if
        // it were, parse_seq_to_before_end would have prevented
        // reaching this point.
        fn parse_non_delim_tt_tok<'b>(p: &mut Parser<'b>) -> PResult<'b,  TokenTree> {
          println!("Enter parse_non_delim_tt_tok");
            match p.token {
                token::CloseDelim(_) => {
                  println!("Enter CloseDelim in parse_non_delim_tt_tok");
                    let token_str = p.this_token_to_string();
                    let mut err = p.fatal(
                        &format!("incorrect close delimiter: `{}`", token_str));
                    // This is a conservative error: only report the last unclosed delimiter. The
                    // previous unclosed delimiters could actually be closed! The parser just hasn't
                    // gotten to them yet.
                    if let Some(&sp) = p.open_braces.last() {
                        err.span_note(sp, "unclosed delimiter");
                    };
                    Err(err)
                },
                /* we ought to allow different depths of unquotation */
                token::Dollar if p.quote_depth > 0 => {
                  println!("Enter Dollor in parse_non_delim_tt_tok");
                    //p.parse_unquoted()
                    unimplemented!()
                }
                _ => {
                  println!("Enter _ in parse_non_delim_tt_tok");
                    Ok(TokenTree::Token(p.span, p.bump_and_get()))
                }
            }
        }

        match self.token {
            token::Eof => {
              println!("Enter token::Eof");
                let open_braces = self.open_braces.clone();
                let mut err: DiagnosticBuilder<'a> =
                    self.fatal("this file contains an un-closed delimiter");
                for sp in &open_braces {
                    err.span_help(*sp, "did you mean to close this delimiter?");
                }
                return Err(err);
            },
            token::OpenDelim(delim) => {
              println!("Enter OpenDelim");
                // The span for beginning of the delimited section
                let pre_span = self.span;

                // Parse the open delimiter.
                self.open_braces.push(self.span);
                let open_span = self.span;
                self.bump();

                // Parse the token trees within the delimiters
                let tts = try!(self.parse_seq_to_before_end(
                    &token::CloseDelim(delim),
                    seq_sep_none(),
                    |p| p.parse_token_tree()
                ));

                // Parse the close delimiter.
                let close_span = self.span;
                self.bump();
                self.open_braces.pop().unwrap();

                // Expand to cover the entire delimited token tree
                let span = Span { hi: close_span.hi, ..pre_span };

                Ok(TokenTree::Delimited(span, Rc::new(Delimited {
                    delim: delim,
                    open_span: open_span,
                    tts: tts,
                    close_span: close_span,
                })))
            },
            _ => parse_non_delim_tt_tok(self),
        }
    }

    /// Advance the parser by one token
    pub fn bump(&mut self) {
        self.last_span = self.span;
        // Stash token for error recovery (sometimes; clone is not necessarily cheap).
        self.last_token = if self.token.is_ident() ||
                          self.token == token::Comma {
            Some(Box::new(self.token.clone()))
        } else {
            None
        };

        let next = if self.buffer_start == self.buffer_end {
            self.reader.real_token()
        } else {
            // Avoid token copies with `replace`.
            let buffer_start = self.buffer_start as usize;
            let next_index = (buffer_start + 1) & 3;
            self.buffer_start = next_index as isize;

            let placeholder = TokenAndSpan {
                tok: token::Underscore,
                sp: self.span,
            };
            mem::replace(&mut self.buffer[buffer_start], placeholder)
        };
        self.span = next.sp;
        self.token = next.tok;
        self.tokens_consumed += 1;
        self.expected_tokens.clear();
    }

    /// Advance the parser by one token and return the bumped token.
    pub fn bump_and_get(&mut self) -> token::Token {
        let old_token = mem::replace(&mut self.token, token::Underscore);
        self.bump();
        old_token
    }


    // parse a stream of tokens into a list of TokenTree's,
    // up to EOF.
    pub fn parse_all_token_trees(&mut self) -> PResult<'a, Vec<TokenTree>> {
        let mut tts = Vec::new();
        while self.token != Token::Eof {
            tts.push(try!(self.parse_token_tree()));
        }
        Ok(tts)
    }

    /// Parse a sequence, not including the closing delimiter. The function
    /// f must consume tokens until reaching the next separator or
    /// closing bracket.
    pub fn parse_seq_to_before_end<T, F>(&mut self,
                                         ket: &token::Token,
                                         sep: SeqSep,
                                         mut f: F)
                                         -> PResult<'a, Vec<T>> where
        F: FnMut(&mut Parser<'a>) -> PResult<'a,  T>,
    {
        let mut first: bool = true;
        let mut v = vec!();
        while self.token != *ket {
            match sep.sep {
              Some(ref t) => {
                if first { first = false; }
                else { try!(self.expect(t)); }
              }
              _ => ()
            }
            if sep.trailing_sep_allowed && self.check(ket) { break; }
            v.push(try!(f(self)));
        }
        return Ok(v);
    }

    /// Expect and consume the token t. Signal an error if
    /// the next token is not t.
    pub fn expect(&mut self, t: &token::Token) -> PResult<'a,  ()> {
        if self.expected_tokens.is_empty() {
            if self.token == *t {
                self.bump();
                Ok(())
            } else {
                let token_str = Parser::token_to_string(t);
                let this_token_str = self.this_token_to_string();
                Err(self.fatal(&format!("expected `{}`, found `{}`",
                                   token_str,
                                   this_token_str)))
            }
        } else {
            self.expect_one_of(unsafe { slice::from_raw_parts(t, 1) }, &[])
        }
    }

    /// Expect next token to be edible or inedible token.  If edible,
    /// then consume it; if inedible, then return without consuming
    /// anything.  Signal a fatal error if next token is unexpected.
    pub fn expect_one_of(&mut self,
                         edible: &[token::Token],
                         inedible: &[token::Token]) -> PResult<'a,  ()>{
        fn tokens_to_string(tokens: &[TokenType]) -> String {
            let mut i = tokens.iter();
            // This might be a sign we need a connect method on Iterator.
            let b = i.next()
                     .map_or("".to_string(), |t| t.to_string());
            i.enumerate().fold(b, |mut b, (i, ref a)| {
                if tokens.len() > 2 && i == tokens.len() - 2 {
                    b.push_str(", or ");
                } else if tokens.len() == 2 && i == tokens.len() - 2 {
                    b.push_str(" or ");
                } else {
                    b.push_str(", ");
                }
                b.push_str(&a.to_string());
                b
            })
        }
        if edible.contains(&self.token) {
            self.bump();
            Ok(())
        } else if inedible.contains(&self.token) {
            // leave it in the input
            Ok(())
        } else {
            let mut expected = edible.iter()
                .map(|x| TokenType::Token(x.clone()))
                .chain(inedible.iter().map(|x| TokenType::Token(x.clone())))
                .chain(self.expected_tokens.iter().cloned())
                .collect::<Vec<_>>();
            expected.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
            expected.dedup();
            let expect = tokens_to_string(&expected[..]);
            let actual = self.this_token_to_string();
            Err(self.fatal(
                &(if expected.len() > 1 {
                    (format!("expected one of {}, found `{}`",
                             expect,
                             actual))
                } else if expected.is_empty() {
                    (format!("unexpected token: `{}`",
                             actual))
                } else {
                    (format!("expected {}, found `{}`",
                             expect,
                             actual))
                })[..]
            ))
        }
    }

    /// Check if the next token is `tok`, and return `true` if so.
    ///
    /// This method is will automatically add `tok` to `expected_tokens` if `tok` is not
    /// encountered.
    pub fn check(&mut self, tok: &token::Token) -> bool {
        let is_present = self.token == *tok;
        if !is_present { self.expected_tokens.push(TokenType::Token(tok.clone())); }
        is_present
    }

    /// Consume token 'tok' if it exists. Returns true if the given
    /// token was present, false otherwise.
    pub fn eat(&mut self, tok: &token::Token) -> bool {
        let is_present = self.check(tok);
        if is_present { self.bump() }
        is_present
    }

    pub fn check_keyword(&mut self, kw: keywords::Keyword) -> bool {
        self.expected_tokens.push(TokenType::Keyword(kw));
        self.token.is_keyword(kw)
    }

    pub fn fatal(&self, m: &str) -> DiagnosticBuilder<'a> {
        self.sess.span_diagnostic.struct_span_fatal(self.span, m)
    }
}