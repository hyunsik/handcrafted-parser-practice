pub use self::PathParsingMode::*;

use std::collections::HashSet;
use std::slice;
use std::mem;
use std::rc::Rc;

use abi::{self, Abi};
use ast::Unsafety;
use ast::{Mod, Arg, Arm, Attribute};
use ast::Block;
use ast::{BlockCheckMode, CaptureBy};
use ast::{Constness, Crate, CrateConfig};
use ast::{Decl, DeclKind};
use ast::{Expr, ExprKind};
use ast::{FnDecl, FunctionRetTy};
use ast::{Ident, Item, ItemKind};
use ast::{Lit, LitKind, UintTy};
use ast::Local;
use ast::{Delimited, SequenceRepetition, TokenTree};
use ast::{BindingMode, Mutability, Pat, PatKind};
use ast::{Stmt, StmtKind};
use ast::{Ty, TyKind};
use ast::{Visibility, WhereClause};
use ast::{BinOpKind, UnOp};
use ast;
use ast_util;
use attr::{ThinAttributes, ThinAttributesExt, AttributesExt};
use codemap::{self, Span, BytePos, Spanned, spanned, mk_sp, CodeMap};
use errors::DiagnosticBuilder;
use errors;
use print::pprust;
use parse;
use parse::classify;
use parse::common::{SeqSep};
use parse::obsolete::ObsoleteSyntax;
use parse::ParseSess;
use parse::token::{self, keywords, special_idents};
use parse::token::{intern, Token, InternedString};
use parse::lexer::{Reader, TokenAndSpan};
use parse::PResult;
use ptr::P;
use util::parser::{AssocOp, Fixity};

bitflags! {
    flags Restrictions: u8 {
        const RESTRICTION_STMT_EXPR         = 1 << 0,
        const RESTRICTION_NO_STRUCT_LITERAL = 1 << 1,
        const NO_NONINLINE_MOD  = 1 << 2,
    }
}

type ItemInfo = (Ident, ItemKind, Option<Vec<Attribute> >);

/// How to parse a path. There are four different kinds of paths, all of which
/// are parsed somewhat differently.
#[derive(Copy, Clone, PartialEq)]
pub enum PathParsingMode {
    /// A path with no type parameters; e.g. `foo::bar::Baz`
    NoTypesAllowed,
    /// A path with a lifetime and type parameters, with no double colons
    /// before the type parameters; e.g. `foo::bar<'a>::Baz<T>`
    LifetimeAndTypesWithoutColons,
    /// A path with a lifetime and type parameters with double colons before
    /// the type parameters; e.g. `foo::bar::<'a>::Baz::<T>`
    LifetimeAndTypesWithColons,
}

/// How to parse a bound, whether to allow bound modifiers such as `?`.
#[derive(Copy, Clone, PartialEq)]
pub enum BoundParsingMode {
    Bare,
    Modified,
}

#[derive(Clone, Copy, PartialEq)]
pub enum SemiColonMode {
    Break,
    Ignore,
}

pub struct Parser<'a> {
    pub sess: &'a ParseSess,
    /// the current token:
    pub token: token::Token,
    /// the span of the current token:
    pub span: Span,
    /// the span of the prior token:
    pub last_span: Span,
    pub cfg: CrateConfig,
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

fn maybe_append(mut lhs: Vec<Attribute>, rhs: Option<Vec<Attribute>>)
                -> Vec<Attribute> {
    if let Some(ref attrs) = rhs {
        lhs.extend(attrs.iter().cloned())
    }
    lhs
}

pub enum LhsExpr {
    NotYetParsed,
    AttributesParsed(ThinAttributes),
    AlreadyParsed(P<Expr>),
}

impl From<Option<ThinAttributes>> for LhsExpr {
    fn from(o: Option<ThinAttributes>) -> Self {
        if let Some(attrs) = o {
            LhsExpr::AttributesParsed(attrs)
        } else {
            LhsExpr::NotYetParsed
        }
    }
}

impl From<P<Expr>> for LhsExpr {
    fn from(expr: P<Expr>) -> Self {
        LhsExpr::AlreadyParsed(expr)
    }
}

impl<'a> Parser<'a> {
    pub fn new(sess: &'a ParseSess,
               cfg: ast::CrateConfig,
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
            cfg: cfg,
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

    pub fn unexpected<T>(&mut self) -> PResult<'a, T> {
        match self.expect_one_of(&[], &[]) {
            Err(e) => Err(e),
            Ok(_) => unreachable!(),
        }
    }

    /// Expect and consume the token t. Signal an error if
    /// the next token is not t.
    pub fn expect(&mut self, t: &token::Token) -> PResult<'a,  ()> {
      println!("Enter expect");
        let res = if self.expected_tokens.is_empty() {
          println!("Enter expected_tokens.empty");
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
          println!("Before expect_one_of");
          let res = self.expect_one_of(unsafe { slice::from_raw_parts(t, 1) }, &[]);
          println!("After expect_one_of");
          res
        };
        println!("Leave expect");
        res
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

    /// Check for erroneous `ident { }`; if matches, signal error and
    /// recover (without consuming any expected input token).  Returns
    /// true if and only if input was consumed for recovery.
    pub fn check_for_erroneous_unit_struct_expecting(&mut self,
                                                     expected: &[token::Token])
                                                     -> bool {
        if self.token == token::OpenDelim(token::Brace)
            && expected.iter().all(|t| *t != token::OpenDelim(token::Brace))
            && self.look_ahead(1, |t| *t == token::CloseDelim(token::Brace)) {
            // matched; signal non-fatal error and recover.
            let span = self.span;
            self.span_err(span, "unit-like struct construction is written with no trailing `{ }`");
            self.eat(&token::OpenDelim(token::Brace));
            self.eat(&token::CloseDelim(token::Brace));
            true
        } else {
            false
        }
    }

    /// Commit to parsing a complete statement `s`, which expects to be
    /// followed by some token from the set edible + inedible.  Check
    /// for recoverable input errors, discarding erroneous characters.
    pub fn commit_stmt(&mut self, edible: &[token::Token],
                       inedible: &[token::Token]) -> PResult<'a, ()> {
        if self.last_token
               .as_ref()
               .map_or(false, |t| t.is_ident() || t.is_path()) {
            let expected = edible.iter()
                .cloned()
                .chain(inedible.iter().cloned())
                .collect::<Vec<_>>();
            self.check_for_erroneous_unit_struct_expecting(&expected);
        }
        self.expect_one_of(edible, inedible)
    }

    pub fn commit_stmt_expecting(&mut self, edible: token::Token) -> PResult<'a, ()> {
        self.commit_stmt(&[edible], &[])
    }

    pub fn parse_ident(&mut self) -> PResult<'a, ast::Ident> {
      self.check_strict_keywords();
      self.check_reserved_keywords();

      match self.token {
        token::Ident(i, _) => {
          self.bump();
          Ok(i)
        }
        _ => {
          let token_str = self.this_token_to_string();
          Err(self.fatal(&format!("expected ident, found `{}`", token_str)))
        }
      }
    }

    pub fn parse_ident_or_self_type(&mut self) -> PResult<'a, ast::Ident> {
        if self.is_self_type_ident() {
            self.expect_self_type_ident()
        } else {
            self.parse_ident()
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

    /// If the next token is the given keyword, eat it and return
    /// true. Otherwise, return false.
    pub fn eat_keyword(&mut self, kw: keywords::Keyword) -> bool {
        if self.check_keyword(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    pub fn eat_keyword_noexpect(&mut self, kw: keywords::Keyword) -> bool {
        if self.token.is_keyword(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// If the given word is not a keyword, signal an error.
    /// If the next token is not the given word, signal an error.
    /// Otherwise, eat it.
    pub fn expect_keyword(&mut self, kw: keywords::Keyword) -> PResult<'a, ()> {
        if !self.eat_keyword(kw) {
            self.unexpected()
        } else {
            Ok(())
        }
    }

    /// Signal an error if the given string is a strict keyword
    pub fn check_strict_keywords(&mut self) {
        if self.token.is_strict_keyword() {
            let token_str = self.this_token_to_string();
            let span = self.span;
            self.span_err(span,
                          &format!("expected identifier, found keyword `{}`",
                                  token_str));
        }
    }

    /// Signal an error if the current token is a reserved keyword
    pub fn check_reserved_keywords(&mut self) {
        if self.token.is_reserved_keyword() {
            let token_str = self.this_token_to_string();
            self.fatal(&format!("`{}` is a reserved keyword", token_str)).emit()
        }
    }

    /// Attempt to consume a `<`. If `<<` is seen, replace it with a single
    /// `<` and continue. If a `<` is not seen, return false.
    ///
    /// This is meant to be used when parsing generics on a path to get the
    /// starting token.
    fn eat_lt(&mut self) -> bool {
        self.expected_tokens.push(TokenType::Token(token::Lt));
        match self.token {
            token::Lt => {
                self.bump();
                true
            }
            token::BinOp(token::Shl) => {
                let span = self.span;
                let lo = span.lo + BytePos(1);
                self.bump_with(token::Lt, lo, span.hi);
                true
            }
            _ => false,
        }
    }

    /// Eat and discard tokens until one of `kets` is encountered. Respects token trees,
    /// passes through any errors encountered. Used for error recovery.
    pub fn eat_to_tokens(&mut self, kets: &[&token::Token]) {
        self.parse_seq_to_before_tokens(kets,
                                        SeqSep::none(),
                                        |p| p.parse_token_tree(),
                                        |mut e| e.cancel());
    }

    /// Parse a sequence, not including the closing delimiter. The function
    /// f must consume tokens until reaching the next separator or
    /// closing bracket.
    pub fn parse_seq_to_before_end<T, F>(&mut self,
                                         ket: &token::Token,
                                         sep: SeqSep,
                                         f: F)
                                         -> Vec<T>
        where F: FnMut(&mut Parser<'a>) -> PResult<'a,  T>,
    {
        self.parse_seq_to_before_tokens(&[ket], sep, f, |mut e| e.emit())
    }

    // `fe` is an error handler.
    fn parse_seq_to_before_tokens<T, F, Fe>(&mut self,
                                            kets: &[&token::Token],
                                            sep: SeqSep,
                                            mut f: F,
                                            mut fe: Fe)
                                            -> Vec<T>
        where F: FnMut(&mut Parser<'a>) -> PResult<'a,  T>,
              Fe: FnMut(DiagnosticBuilder)
    {
        let mut first: bool = true;
        let mut v = vec!();
        while !kets.contains(&&self.token) {
            match sep.sep {
                Some(ref t) => {
                    if first {
                        first = false;
                    } else {
                        if let Err(e) = self.expect(t) {
                            fe(e);
                            break;
                        }
                    }
                }
                _ => ()
            }
            if sep.trailing_sep_allowed && kets.iter().any(|k| self.check(k)) {
                break;
            }

            match f(self) {
                Ok(t) => v.push(t),
                Err(e) => {
                    fe(e);
                    break;
                }
            }
        }

        v
    }

    /// Parse a sequence, including the closing delimiter. The function
    /// f must consume tokens until reaching the next separator or
    /// closing bracket.
    pub fn parse_unspanned_seq<T, F>(&mut self,
                                     bra: &token::Token,
                                     ket: &token::Token,
                                     sep: SeqSep,
                                     f: F)
                                     -> PResult<'a, Vec<T>> where
        F: FnMut(&mut Parser<'a>) -> PResult<'a,  T>,
    {
        try!(self.expect(bra));
        let result = self.parse_seq_to_before_end(ket, sep, f);
        self.bump();
        Ok(result)
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

    /// Advance the parser using provided token as a next one. Use this when
    /// consuming a part of a token. For example a single `<` from `<<`.
    pub fn bump_with(&mut self,
                     next: token::Token,
                     lo: BytePos,
                     hi: BytePos) {
        self.last_span = mk_sp(self.span.lo, lo);
        // It would be incorrect to just stash current token, but fortunately
        // for tokens currently using `bump_with`, last_token will be of no
        // use anyway.
        self.last_token = None;
        self.last_token_interpolated = false;
        self.span = mk_sp(lo, hi);
        self.token = next;
        self.expected_tokens.clear();
    }

    pub fn buffer_length(&mut self) -> isize {
        if self.buffer_start <= self.buffer_end {
            return self.buffer_end - self.buffer_start;
        }
        return (4 - self.buffer_start) + self.buffer_end;
    }
    pub fn look_ahead<R, F>(&mut self, distance: usize, f: F) -> R where
        F: FnOnce(&token::Token) -> R,
    {
        let dist = distance as isize;
        while self.buffer_length() < dist {
            self.buffer[self.buffer_end as usize] = self.reader.real_token();
            self.buffer_end = (self.buffer_end + 1) & 3;
        }
        f(&self.buffer[((self.buffer_start + dist - 1) & 3) as usize].tok)
    }

    pub fn fatal(&self, m: &str) -> DiagnosticBuilder<'a> {
        self.sess.span_diagnostic.struct_span_fatal(self.span, m)
    }
    pub fn span_fatal(&self, sp: Span, m: &str) -> DiagnosticBuilder<'a> {
        self.sess.span_diagnostic.struct_span_fatal(sp, m)
    }
    pub fn span_fatal_help(&self, sp: Span, m: &str, help: &str) -> DiagnosticBuilder<'a> {
        let mut err = self.sess.span_diagnostic.struct_span_fatal(sp, m);
        err.fileline_help(sp, help);
        err
    }
    pub fn bug(&self, m: &str) -> ! {
        self.sess.span_diagnostic.span_bug(self.span, m)
    }
    pub fn warn(&self, m: &str) {
        self.sess.span_diagnostic.span_warn(self.span, m)
    }
    pub fn span_warn(&self, sp: Span, m: &str) {
        self.sess.span_diagnostic.span_warn(sp, m)
    }
    pub fn span_err(&self, sp: Span, m: &str) {
        self.sess.span_diagnostic.span_err(sp, m)
    }
    pub fn span_bug(&self, sp: Span, m: &str) -> ! {
        self.sess.span_diagnostic.span_bug(sp, m)
    }
    pub fn abort_if_errors(&self) {
        self.sess.span_diagnostic.abort_if_errors();
    }

    pub fn diagnostic(&self) -> &'a errors::Handler {
        &self.sess.span_diagnostic
    }

    pub fn id_to_interned_str(&mut self, id: Ident) -> InternedString {
        id.name.as_str()
    }

    /// Is the current token one of the keywords that signals a bare function
    /// type?
    pub fn token_is_bare_fn_keyword(&mut self) -> bool {
        self.check_keyword(keywords::Fn) ||
            self.check_keyword(keywords::Unsafe) ||
            self.check_keyword(keywords::Extern)
    }

    /// Parse optional return type [ -> TY ] in function decl
    pub fn parse_ret_ty(&mut self) -> PResult<'a, FunctionRetTy> {
        if self.eat(&token::RArrow) {
            if self.eat(&token::Not) {
                Ok(FunctionRetTy::None(self.last_span))
            } else {
                Ok(FunctionRetTy::Ty(try!(self.parse_ty())))
            }
        } else {
            let pos = self.span.lo;
            Ok(FunctionRetTy::Default(mk_sp(pos, pos)))
        }
    }

    pub fn parse_ty(&mut self) -> PResult<'a, P<Ty>> {

      let lo = self.span.lo;

      let t = if self.check(&token::OpenDelim(token::Paren)) {
        debug!("OpenDelim");
        TyKind::Infer
      } else if self.check(&token::BinOp(token::Star)) {
        TyKind::Infer
      } else if self.check(&token::OpenDelim(token::Bracket)) {
        TyKind::Infer
      } else if self.check(&token::BinOp(token::And)) ||
                self.token == token::AndAnd {
        TyKind::Infer
      } else if self.check_keyword(keywords::For) {
        TyKind::Infer
      } else if self.token_is_bare_fn_keyword() {
        TyKind::Infer
      } else if self.eat_keyword_noexpect(keywords::Typeof) {
        TyKind::Infer
      } else if self.eat_lt() {
        TyKind::Infer
      } else if self.check(&token::ModSep) ||
                self.token.is_ident() ||
                self.token.is_path() {
        println!("is_ident");
        let path = try!(self.parse_path(NoTypesAllowed));
        // NAMED TYPE
        TyKind::Path(None, path)
      } else if self.eat(&token::Underscore) {
        TyKind::Infer
      } else {
        TyKind::Infer
      };

      let sp = mk_sp(lo, self.last_span.hi);
        Ok(P(Ty {id: ast::DUMMY_NODE_ID, node: t, span: sp}))
    }

    pub fn is_named_argument(&mut self) -> bool {
        let offset = match self.token {
            token::BinOp(token::And) => 1,
            token::AndAnd => 1,
            _ if self.token.is_keyword(keywords::Mut) => 1,
            _ => 0
        };

        debug!("parser is_named_argument offset:{}", offset);

        if offset == 0 {
            is_plain_ident_or_underscore(&self.token)
                && self.look_ahead(1, |t| *t == token::Colon)
        } else {
            self.look_ahead(offset, |t| is_plain_ident_or_underscore(t))
                && self.look_ahead(offset + 1, |t| *t == token::Colon)
        }
    }

    /// This version of parse arg doesn't necessarily require
    /// identifier names.
    pub fn parse_arg_general(&mut self, require_name: bool) -> PResult<'a, Arg> {
        let pat = if require_name || self.is_named_argument() {
            debug!("parse_arg_general parse_pat (require_name:{})",
                   require_name);
            let pat = try!(self.parse_pat());

            try!(self.expect(&token::Colon));
            pat
        } else {
            debug!("parse_arg_general ident_to_pat");
            ast_util::ident_to_pat(ast::DUMMY_NODE_ID,
                                   self.last_span,
                                   special_idents::invalid)
        };

        let t = try!(self.parse_ty());

        Ok(Arg {
            ty: t,
            pat: pat,
            id: ast::DUMMY_NODE_ID,
        })
    }

    /// Parse a single function argument
    pub fn parse_arg(&mut self) -> PResult<'a, Arg> {
        self.parse_arg_general(true)
    }

    /// Parses a path and optional type parameter bounds, depending on the
    /// mode. The `mode` parameter determines whether lifetimes, types, and/or
    /// bounds are permitted and whether `::` must precede type parameter
    /// groups.
    pub fn parse_path(&mut self, mode: PathParsingMode) -> PResult<'a, ast::Path> {

        let lo = self.span.lo;
        let is_global = self.eat(&token::ModSep);

        // Parse any number of segments and bound sets. A segment is an
        // identifier followed by an optional lifetime and a set of types.
        // A bound set is a set of type parameter bounds.
        let segments = match mode {
            LifetimeAndTypesWithoutColons => {
                panic!("LifetimeAndTypesWithoutColons is not supported")
            }
            LifetimeAndTypesWithColons => {
                panic!("LifetimeAndTypesWithColons is not supported")
            }
            NoTypesAllowed => {
                try!(self.parse_path_segments_without_types())
            }
        };

        // Assemble the span.
        let span = mk_sp(lo, self.last_span.hi);

        // Assemble the result.
        Ok(ast::Path {
            span: span,
            global: is_global,
            segments: segments,
        })
    }

    /// Examples:
    /// - `a::b::c`
    pub fn parse_path_segments_without_types(&mut self) -> PResult<'a, Vec<ast::PathSegment>> {
        let mut segments = Vec::new();
        loop {
            // First, parse an identifier.
            let identifier = try!(self.parse_ident_or_self_type());

            // Assemble and push the result.
            segments.push(ast::PathSegment {
                identifier: identifier,
                parameters: ast::PathParameters::none()
            });

            // If we do not see a `::`, stop.
            if !self.eat(&token::ModSep) {
                return Ok(segments);
            }
        }
    }

    pub fn parse_mutability(&mut self) -> PResult<'a, Mutability> {
      unimplemented!()
    }

    pub fn mk_expr(&mut self, lo: BytePos, hi: BytePos,
                   node: ExprKind, attrs: ThinAttributes) -> P<Expr> {
        P(Expr {
            id: ast::DUMMY_NODE_ID,
            node: node,
            span: mk_sp(lo, hi),
            attrs: attrs,
        })
    }

    pub fn mk_unary(&mut self, unop: ast::UnOp, expr: P<Expr>) -> ast::ExprKind {
        ExprKind::Unary(unop, expr)
    }

    pub fn mk_binary(&mut self, binop: ast::BinOp, lhs: P<Expr>, rhs: P<Expr>) -> ast::ExprKind {
        ExprKind::Binary(binop, lhs, rhs)
    }

    pub fn mk_call(&mut self, f: P<Expr>, args: Vec<P<Expr>>) -> ast::ExprKind {
        ExprKind::Call(f, args)
    }

    pub fn mk_index(&mut self, expr: P<Expr>, idx: P<Expr>) -> ast::ExprKind {
        ExprKind::Index(expr, idx)
    }

    pub fn mk_range(&mut self,
                    start: Option<P<Expr>>,
                    end: Option<P<Expr>>)
                    -> ast::ExprKind {
        ExprKind::Range(start, end)
    }

    pub fn mk_field(&mut self, expr: P<Expr>, ident: ast::SpannedIdent) -> ast::ExprKind {
        ExprKind::Field(expr, ident)
    }

    pub fn mk_tup_field(&mut self, expr: P<Expr>, idx: codemap::Spanned<usize>) -> ast::ExprKind {
        ExprKind::TupField(expr, idx)
    }

    pub fn mk_assign_op(&mut self, binop: ast::BinOp,
                        lhs: P<Expr>, rhs: P<Expr>) -> ast::ExprKind {
        ExprKind::AssignOp(binop, lhs, rhs)
    }

    fn parse_unquoted(&mut self) -> PResult<'a, TokenTree> {
      unimplemented!()
    }

    fn parse_or_use_outer_attributes(&mut self,
                                     already_parsed_attrs: Option<ThinAttributes>)
                                     -> PResult<'a, ThinAttributes> {
        if let Some(attrs) = already_parsed_attrs {
            Ok(attrs)
        } else {
            self.parse_outer_attributes().map(|a| a.into_thin_attrs())
        }
    }

    /// parse a single token tree from the input.
    pub fn parse_token_tree(&mut self) -> PResult<'a, TokenTree> {
        match self.token {
            token::Eof => {
                let mut err: DiagnosticBuilder<'a> =
                    self.diagnostic().struct_span_err(self.span,
                                                      "this file contains an un-closed delimiter");
                for sp in &self.open_braces {
                    err.span_help(*sp, "did you mean to close this delimiter?");
                }

                Err(err)
            },
            token::OpenDelim(delim) => {
                // The span for beginning of the delimited section
                let pre_span = self.span;

                // Parse the open delimiter.
                self.open_braces.push(self.span);
                let open_span = self.span;
                self.bump();

                // Parse the token trees within the delimiters
                let tts = self.parse_seq_to_before_end(&token::CloseDelim(delim),
                                                       SeqSep::none(),
                                                       |p| p.parse_token_tree());

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
            _ => {
                // invariants: the current token is not a left-delimiter,
                // not an EOF, and not the desired right-delimiter (if
                // it were, parse_seq_to_before_end would have prevented
                // reaching this point.
                match self.token {
                    token::CloseDelim(_) => {
                        let token_str = self.this_token_to_string();
                        let mut err = self.diagnostic().struct_span_err(self.span,
                            &format!("incorrect close delimiter: `{}`", token_str));
                        // This is a conservative error: only report the last unclosed delimiter.
                        // The previous unclosed delimiters could actually be closed! The parser
                        // just hasn't gotten to them yet.
                        if let Some(&sp) = self.open_braces.last() {
                            err.span_note(sp, "unclosed delimiter");
                        };

                        Err(err)
                    },
                    /* we ought to allow different depths of unquotation */
                    token::Dollar => {
                        self.parse_unquoted()
                    }
                    _ => {
                        Ok(TokenTree::Token(self.span, self.bump_and_get()))
                    }
                }
            }
        }
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

    /// Parse a prefix-unary-operator expr
    pub fn parse_prefix_expr(&mut self,
                             already_parsed_attrs: Option<ThinAttributes>)
                             -> PResult<'a, P<Expr>> {
      unimplemented!()
    }

    /// Parse an associative expression
    ///
    /// This parses an expression accounting for associativity and precedence of the operators in
    /// the expression.
    pub fn parse_assoc_expr(&mut self,
                            already_parsed_attrs: Option<ThinAttributes>)
                            -> PResult<'a, P<Expr>> {
        self.parse_assoc_expr_with(0, already_parsed_attrs.into())
    }

    /// Parse an associative expression with operators of at least `min_prec` precedence
    pub fn parse_assoc_expr_with(&mut self,
                                 min_prec: usize,
                                 lhs: LhsExpr)
                                 -> PResult<'a, P<Expr>> {
        let mut lhs = if let LhsExpr::AlreadyParsed(expr) = lhs {
            expr
        } else {
            let attrs = match lhs {
                LhsExpr::AttributesParsed(attrs) => Some(attrs),
                _ => None,
            };
            if self.token == token::DotDot {
                return self.parse_prefix_range_expr(attrs);
            } else {
                try!(self.parse_prefix_expr(attrs))
            }
        };


        if self.expr_is_complete(&lhs) {
            // Semi-statement forms are odd. See https://github.com/rust-lang/rust/issues/29071
            return Ok(lhs);
        }
        self.expected_tokens.push(TokenType::Operator);
        while let Some(op) = AssocOp::from_token(&self.token) {

            let lhs_span = if self.last_token_interpolated {
                self.last_span
            } else {
                lhs.span
            };

            let cur_op_span = self.span;
            let restrictions = if op.is_assign_like() {
                self.restrictions & RESTRICTION_NO_STRUCT_LITERAL
            } else {
                self.restrictions
            };
            if op.precedence() < min_prec {
                break;
            }
            self.bump();
            if op.is_comparison() {
                self.check_no_chained_comparison(&lhs, &op);
            }
            // Special cases:
            if op == AssocOp::As {
                let rhs = try!(self.parse_ty());
                lhs = self.mk_expr(lhs_span.lo, rhs.span.hi,
                                   ExprKind::Cast(lhs, rhs), None);
                continue
            } else if op == AssocOp::Colon {
                let rhs = try!(self.parse_ty());
                lhs = self.mk_expr(lhs_span.lo, rhs.span.hi,
                                   ExprKind::Type(lhs, rhs), None);
                continue
            } else if op == AssocOp::DotDot {
                    // If we didn’t have to handle `x..`, it would be pretty easy to generalise
                    // it to the Fixity::None code.
                    //
                    // We have 2 alternatives here: `x..y` and `x..` The other two variants are
                    // handled with `parse_prefix_range_expr` call above.
                    let rhs = if self.is_at_start_of_range_notation_rhs() {
                        let rhs = self.parse_assoc_expr_with(op.precedence() + 1,
                                                             LhsExpr::NotYetParsed);
                        match rhs {
                            Ok(e) => Some(e),
                            Err(mut e) => {
                                e.cancel();
                                None
                            }
                        }
                    } else {
                        None
                    };
                    let (lhs_span, rhs_span) = (lhs_span, if let Some(ref x) = rhs {
                        x.span
                    } else {
                        cur_op_span
                    });
                    let r = self.mk_range(Some(lhs), rhs);
                    lhs = self.mk_expr(lhs_span.lo, rhs_span.hi, r, None);
                    break
            }

            let rhs = try!(match op.fixity() {
                Fixity::Right => self.with_res(
                    restrictions - RESTRICTION_STMT_EXPR,
                    |this| {
                        this.parse_assoc_expr_with(op.precedence(),
                            LhsExpr::NotYetParsed)
                }),
                Fixity::Left => self.with_res(
                    restrictions - RESTRICTION_STMT_EXPR,
                    |this| {
                        this.parse_assoc_expr_with(op.precedence() + 1,
                            LhsExpr::NotYetParsed)
                }),
                // We currently have no non-associative operators that are not handled above by
                // the special cases. The code is here only for future convenience.
                Fixity::None => self.with_res(
                    restrictions - RESTRICTION_STMT_EXPR,
                    |this| {
                        this.parse_assoc_expr_with(op.precedence() + 1,
                            LhsExpr::NotYetParsed)
                }),
            });

            lhs = match op {
                AssocOp::Add | AssocOp::Subtract | AssocOp::Multiply | AssocOp::Divide |
                AssocOp::Modulus | AssocOp::LAnd | AssocOp::LOr | AssocOp::BitXor |
                AssocOp::BitAnd | AssocOp::BitOr | AssocOp::ShiftLeft | AssocOp::ShiftRight |
                AssocOp::Equal | AssocOp::Less | AssocOp::LessEqual | AssocOp::NotEqual |
                AssocOp::Greater | AssocOp::GreaterEqual => {
                    let ast_op = op.to_ast_binop().unwrap();
                    let (lhs_span, rhs_span) = (lhs_span, rhs.span);
                    let binary = self.mk_binary(codemap::respan(cur_op_span, ast_op), lhs, rhs);
                    self.mk_expr(lhs_span.lo, rhs_span.hi, binary, None)
                }
                AssocOp::Assign =>
                    self.mk_expr(lhs_span.lo, rhs.span.hi, ExprKind::Assign(lhs, rhs), None),
                AssocOp::Inplace =>
                    self.mk_expr(lhs_span.lo, rhs.span.hi, ExprKind::InPlace(lhs, rhs), None),
                AssocOp::AssignOp(k) => {
                    let aop = match k {
                        token::Plus =>    BinOpKind::Add,
                        token::Minus =>   BinOpKind::Sub,
                        token::Star =>    BinOpKind::Mul,
                        token::Slash =>   BinOpKind::Div,
                        token::Percent => BinOpKind::Rem,
                        token::Caret =>   BinOpKind::BitXor,
                        token::And =>     BinOpKind::BitAnd,
                        token::Or =>      BinOpKind::BitOr,
                        token::Shl =>     BinOpKind::Shl,
                        token::Shr =>     BinOpKind::Shr,
                    };
                    let (lhs_span, rhs_span) = (lhs_span, rhs.span);
                    let aopexpr = self.mk_assign_op(codemap::respan(cur_op_span, aop), lhs, rhs);
                    self.mk_expr(lhs_span.lo, rhs_span.hi, aopexpr, None)
                }
                AssocOp::As | AssocOp::Colon | AssocOp::DotDot => {
                    self.bug("As, Colon or DotDot branch reached")
                }
            };

            if op.fixity() == Fixity::None { break }
        }
        Ok(lhs)
    }

    /// Produce an error if comparison operators are chained (RFC #558).
    /// We only need to check lhs, not rhs, because all comparison ops
    /// have same precedence and are left-associative
    fn check_no_chained_comparison(&mut self, lhs: &Expr, outer_op: &AssocOp) {
        debug_assert!(outer_op.is_comparison());
        match lhs.node {
            ExprKind::Binary(op, _, _) if op.node.is_comparison() => {
                // respan to include both operators
                let op_span = mk_sp(op.span.lo, self.span.hi);
                let mut err = self.diagnostic().struct_span_err(op_span,
                    "chained comparison operators require parentheses");
                if op.node == BinOpKind::Lt && *outer_op == AssocOp::Greater {
                    err.fileline_help(op_span,
                        "use `::<...>` instead of `<...>` if you meant to specify type arguments");
                }
                err.emit();
            }
            _ => {}
        }
    }

    /// Parse prefix-forms of range notation: `..expr` and `..`
    fn parse_prefix_range_expr(&mut self,
                               already_parsed_attrs: Option<ThinAttributes>)
                               -> PResult<'a, P<Expr>> {
        debug_assert!(self.token == token::DotDot);
        let attrs = try!(self.parse_or_use_outer_attributes(already_parsed_attrs));
        let lo = self.span.lo;
        let mut hi = self.span.hi;
        self.bump();
        let opt_end = if self.is_at_start_of_range_notation_rhs() {
            // RHS must be parsed with more associativity than DotDot.
            let next_prec = AssocOp::from_token(&token::DotDot).unwrap().precedence() + 1;
            Some(try!(self.parse_assoc_expr_with(next_prec,
                                                 LhsExpr::NotYetParsed)
            .map(|x|{
                hi = x.span.hi;
                x
            })))
         } else {
            None
        };
        let r = self.mk_range(None, opt_end);
        Ok(self.mk_expr(lo, hi, r, attrs))
    }

    fn is_at_start_of_range_notation_rhs(&self) -> bool {
        if self.token.can_begin_expr() {
            // parse `for i in 1.. { }` as infinite loop, not as `for i in (1..{})`.
            if self.token == token::OpenDelim(token::Brace) {
                return !self.restrictions.contains(RESTRICTION_NO_STRUCT_LITERAL);
            }
            true
        } else {
            false
        }
    }

    /// Parse an expression
    pub fn parse_expr(&mut self) -> PResult<'a, P<Expr>> {
        unimplemented!()
    }

    /// Evaluate the closure with restrictions in place.
    ///
    /// After the closure is evaluated, restrictions are reset.
    pub fn with_res<F, T>(&mut self, r: Restrictions, f: F) -> T
        where F: FnOnce(&mut Self) -> T
    {
        let old = self.restrictions;
        self.restrictions = r;
        let r = f(self);
        self.restrictions = old;
        return r;

    }

    /// Parse an expression, subject to the given restrictions
    pub fn parse_expr_res(&mut self, r: Restrictions,
                          already_parsed_attrs: Option<ThinAttributes>)
                          -> PResult<'a, P<Expr>> {
        unimplemented!()
    }

    /// Parse the RHS of a local variable declaration (e.g. '= 14;')
    fn parse_initializer(&mut self) -> PResult<'a, Option<P<Expr>>> {
        if self.check(&token::Eq) {
            self.bump();
            Ok(Some(try!(self.parse_expr())))
        } else {
            Ok(None)
        }
    }

    fn is_path_start(&self) -> bool {
        (self.token == token::Lt || self.token == token::ModSep
            || self.token.is_ident() || self.token.is_path())
            && !self.token.is_keyword(keywords::True) && !self.token.is_keyword(keywords::False)
    }

    pub fn parse_pat(&mut self) -> PResult<'a, P<Pat>> {
      let lo = self.span.lo;

      let pat;

      match self.token {
        token::Underscore => {
          // Parse _
          self.bump();
          pat = PatKind::Wild;
        }
        token::BinOp(token::And) | token::AndAnd => {
          // Parse _
          self.bump();
          pat = PatKind::Wild;
        }
        token::OpenDelim(token::Paren) => {
          // Parse _
          self.bump();
          pat = PatKind::Wild;
        }
        token::OpenDelim(token::Bracket) => {
          // Parse _
          self.bump();
          pat = PatKind::Wild;
        }
        _ => {
          // At this point, token != _, &, &&, (, [
          if self.eat_keyword(keywords::Mut) {
            // Parse mut ident @ pat
            pat = try!(self.parse_pat_ident(BindingMode::ByValue(Mutability::Mutable)));
          } else if self.eat_keyword(keywords::Ref) {
            // Parse ref ident @ pat / ref mut ident @ pat
            let mutbl = try!(self.parse_mutability());
            pat = try!(self.parse_pat_ident(BindingMode::ByRef(mutbl)));
          } else if self.eat_keyword(keywords::Box) {
            // Parse box pat
            let subpat = try!(self.parse_pat());
            pat = PatKind::Box(subpat);
          } else if self.is_path_start() {
            // Parse pattern starting with a path
            if self.token.is_plain_ident() && self.look_ahead(1, |t| *t != token::DotDotDot &&
                    *t != token::OpenDelim(token::Brace) &&
                    *t != token::OpenDelim(token::Paren) &&
                    // Contrary to its definition, a plain ident can be followed by :: in macros
                    *t != token::ModSep) {
              // Plain idents have some extra abilities here compared to general paths
              if self.look_ahead(1, |t| *t == token::Not) {
                // TODO
                pat = PatKind::Wild;
              } else {
                // Parse ident @ pat
                // This can give false positives and parse nullary enums,
                // they are dealt with later in resolve
                let binding_mode = BindingMode::ByValue(Mutability::Immutable);
                pat = try!(self.parse_pat_ident(binding_mode));
              }
            } else {
              // TODO
              pat = PatKind::Wild;
            }
          } else {
            // TODO
            pat = PatKind::Wild;
          }
        }
      };

      let hi = self.last_span.hi;
      Ok(P(ast::Pat {
          id: ast::DUMMY_NODE_ID,
          node: pat,
          span: mk_sp(lo, hi),
      }))
    }

    /// Parse ident or ident @ pat
    /// used by the copy foo and ref foo patterns to give a good
    /// error message when parsing mistakes like ref foo(a,b)
    fn parse_pat_ident(&mut self,
                       binding_mode: ast::BindingMode)
                       -> PResult<'a, PatKind> {
      if !self.token.is_plain_ident() {
            let span = self.span;
            let tok_str = self.this_token_to_string();
            return Err(self.span_fatal(span,
                            &format!("expected identifier, found `{}`", tok_str)))
        }
        let ident = try!(self.parse_ident());
        let last_span = self.last_span;
        let name = codemap::Spanned{span: last_span, node: ident};
        let sub = if self.eat(&token::At) {
            Some(try!(self.parse_pat()))
        } else {
            None
        };

        // just to be friendly, if they write something like
        //   ref Some(i)
        // we end up here with ( as the current token.  This shortly
        // leads to a parse error.  Note that if there is no explicit
        // binding mode then we do not end up here, because the lookahead
        // will direct us over to parse_enum_variant()
        if self.token == token::OpenDelim(token::Paren) {
            let last_span = self.last_span;
            return Err(self.span_fatal(
                last_span,
                "expected identifier, found enum pattern"))
        }

        Ok(PatKind::Ident(binding_mode, name, sub))
    }

    /// Parse a local variable declaration
    fn parse_local(&mut self, attrs: ThinAttributes) -> PResult<'a, P<Local>> {
        let lo = self.span.lo;
        let pat = try!(self.parse_pat());

        let mut ty = None;
        if self.eat(&token::Colon) {
            ty = Some(try!(self.parse_ty()));
        }
        let init = try!(self.parse_initializer());
        Ok(P(ast::Local {
            ty: ty,
            pat: pat,
            init: init,
            id: ast::DUMMY_NODE_ID,
            span: mk_sp(lo, self.last_span.hi),
            attrs: attrs,
        }))
    }

    /// Parse a "let" stmt
    fn parse_let(&mut self, attrs: ThinAttributes) -> PResult<'a, P<Decl>> {
        let lo = self.span.lo;
        let local = try!(self.parse_local(attrs));
        Ok(P(spanned(lo, self.last_span.hi, DeclKind::Local(local))))
    }

    /// Parse a statement. may include decl.
    pub fn parse_stmt(&mut self) -> PResult<'a, Option<Stmt>> {
        unimplemented!()
    }

    // Eat tokens until we can be relatively sure we reached the end of the
    // statement. This is something of a best-effort heuristic.
    //
    // We terminate when we find an unmatched `}` (without consuming it).
    fn recover_stmt(&mut self) {
        self.recover_stmt_(SemiColonMode::Ignore)
    }
    // If `break_on_semi` is `Break`, then we will stop consuming tokens after
    // finding (and consuming) a `;` outside of `{}` or `[]` (note that this is
    // approximate - it can mean we break too early due to macros, but that
    // shoud only lead to sub-optimal recovery, not inaccurate parsing).
    fn recover_stmt_(&mut self, break_on_semi: SemiColonMode) {
        let mut brace_depth = 0;
        let mut bracket_depth = 0;
        loop {
            match self.token {
                token::OpenDelim(token::DelimToken::Brace) => {
                    brace_depth += 1;
                    self.bump();
                }
                token::OpenDelim(token::DelimToken::Bracket) => {
                    bracket_depth += 1;
                    self.bump();
                }
                token::CloseDelim(token::DelimToken::Brace) => {
                    if brace_depth == 0 {
                        return;
                    }
                    brace_depth -= 1;
                    self.bump();
                }
                token::CloseDelim(token::DelimToken::Bracket) => {
                    bracket_depth -= 1;
                    if bracket_depth < 0 {
                        bracket_depth = 0;
                    }
                    self.bump();
                }
                token::Eof => return,
                token::Semi => {
                    self.bump();
                    if break_on_semi == SemiColonMode::Break &&
                       brace_depth == 0 &&
                       bracket_depth == 0 {
                        return;
                    }
                }
                _ => {
                    self.bump()
                }
            }
        }
    }


    fn parse_stmt_(&mut self) -> Option<Stmt> {
        self.parse_stmt_without_recovery().unwrap_or_else(|mut e| {
            e.emit();
            self.recover_stmt_(SemiColonMode::Break);
            None
        })
    }

    fn parse_stmt_without_recovery(&mut self) -> PResult<'a, Option<Stmt>> {

        let attrs = try!(self.parse_outer_attributes());
        let lo = self.span.lo;

        Ok(Some(if self.check_keyword(keywords::Let) {
            try!(self.expect_keyword(keywords::Let));
            let decl = try!(self.parse_let(attrs.into_thin_attrs()));
            let hi = decl.span.hi;
            let stmt = StmtKind::Decl(decl, ast::DUMMY_NODE_ID);
            spanned(lo, hi, stmt)
        } else {
            // FIXME: Bad copy of attrs
            let restrictions = self.restrictions | NO_NONINLINE_MOD;
            match try!(self.with_res(restrictions,
                                     |this| this.parse_item_(attrs.clone(), false, true))) {
                Some(i) => {
                    let hi = i.span.hi;
                    let decl = P(spanned(lo, hi, DeclKind::Item(i)));
                    spanned(lo, hi, StmtKind::Decl(decl, ast::DUMMY_NODE_ID))
                }
                None => {
                    let unused_attrs = |attrs: &[_], s: &mut Self| {
                        if attrs.len() > 0 {
                            s.span_err(s.span,
                                "expected statement after outer attribute");
                        }
                    };

                    // Do not attempt to parse an expression if we're done here.
                    if self.token == token::Semi {
                        unused_attrs(&attrs, self);
                        self.bump();
                        return Ok(None);
                    }

                    if self.token == token::CloseDelim(token::Brace) {
                        unused_attrs(&attrs, self);
                        return Ok(None);
                    }

                    // Remainder are line-expr stmts.
                    let e = try!(self.parse_expr_res(
                        RESTRICTION_STMT_EXPR, Some(attrs.into_thin_attrs())));
                    let hi = e.span.hi;
                    let stmt = StmtKind::Expr(e, ast::DUMMY_NODE_ID);
                    spanned(lo, hi, stmt)
                }
            }
        }))
    }

    /// Is this expression a successfully-parsed statement?
    fn expr_is_complete(&mut self, e: &Expr) -> bool {
        self.restrictions.contains(RESTRICTION_STMT_EXPR) &&
            !classify::expr_requires_semi_to_be_stmt(e)
    }

    /// Parse a block. No inner attrs are allowed.
    pub fn parse_block(&mut self) -> PResult<'a, P<Block>> {
      unimplemented!()
    }

    /// Parse a block. Inner attrs are allowed.
    fn parse_inner_attrs_and_block(&mut self) -> PResult<'a, (Vec<Attribute>, P<Block>)> {
      println!("Enter parse_inner_attrs_and_block");
        let lo = self.span.lo;
        try!(self.expect(&token::OpenDelim(token::Brace)));
        println!("after self.expect");

        let attrs = try!(self.parse_inner_attributes());
        println!("after parse_inner_attributes");
        let block_tail = try!(self.parse_block_tail(lo, BlockCheckMode::Default));
        println!("after parse_block_tail");
        /*
        Ok((try!(self.parse_inner_attributes()),
            try!(self.parse_block_tail(lo, BlockCheckMode::Default))))*/
        Ok((attrs, block_tail))
    }

    /// Parse the rest of a block expression or function body
    /// Precondition: already parsed the '{'.
    fn parse_block_tail(&mut self, lo: BytePos, s: BlockCheckMode) -> PResult<'a, P<Block>> {
      println!("Enter parse_block_tail");
        let mut stmts = vec![];
        let mut expr = None;

        while !self.eat(&token::CloseDelim(token::Brace)) {
            let Spanned {node, span} = if let Some(s) = self.parse_stmt_() {
                s
            } else {
                // Found only `;` or `}`.
                continue;
            };
            match node {
                StmtKind::Expr(e, _) => {
                    try!(self.handle_expression_like_statement(e, span, &mut stmts, &mut expr));
                }
                _ => { // all other kinds of statements:
                    let mut hi = span.hi;
                    if classify::stmt_ends_with_semi(&node) {
                        try!(self.commit_stmt_expecting(token::Semi));
                        hi = self.last_span.hi;
                    }

                    stmts.push(Spanned {
                        node: node,
                        span: mk_sp(span.lo, hi)
                    });
                }
            }
        }

        println!("Leave parse_block_tail");
        Ok(P(ast::Block {
            stmts: stmts,
            expr: expr,
            id: ast::DUMMY_NODE_ID,
            rules: s,
            span: mk_sp(lo, self.last_span.hi),
        }))
    }

    fn handle_expression_like_statement(&mut self,
                                        e: P<Expr>,
                                        span: Span,
                                        stmts: &mut Vec<Stmt>,
                                        last_block_expr: &mut Option<P<Expr>>)
                                        -> PResult<'a, ()> {
        // expression without semicolon
        if classify::expr_requires_semi_to_be_stmt(&e) {
            // Just check for errors and recover; do not eat semicolon yet.
            if let Err(mut e) =
                self.commit_stmt(&[], &[token::Semi, token::CloseDelim(token::Brace)])
            {
                e.emit();
                self.recover_stmt();
            }
        }

        match self.token {
            token::Semi => {
                self.bump();
                let span_with_semi = Span {
                    lo: span.lo,
                    hi: self.last_span.hi,
                };
                stmts.push(Spanned {
                    node: StmtKind::Semi(e, ast::DUMMY_NODE_ID),
                    span: span_with_semi,
                });
            }
            token::CloseDelim(token::Brace) => *last_block_expr = Some(e),
            _ => {
                stmts.push(Spanned {
                    node: StmtKind::Expr(e, ast::DUMMY_NODE_ID),
                    span: span
                });
            }
        }
        Ok(())
    }

    /// Parse a set of optional generic type parameter declarations. Where
    /// clauses are not parsed here, and must be added later via
    /// `parse_where_clause()`.
    ///
    /// matches generics = ( ) | ( < > ) | ( < typaramseq ( , )? > ) | ( < lifetimes ( , )? > )
    ///                  | ( < lifetimes , typaramseq ( , )? > )
    /// where   typaramseq = ( typaram ) | ( typaram , typaramseq )
    pub fn parse_generics(&mut self) -> PResult<'a, ast::Generics> {
      if self.eat(&token::Lt) {
        // TODO
        Ok(ast::Generics::default())
      } else {
        Ok(ast::Generics::default())
      }
    }

    /// Parses an optional `where` clause and places it in `generics`.
    ///
    /// ```ignore
    /// where T : Clone, V : Copy
    /// ```
    pub fn parse_where_clause(&mut self) -> PResult<'a, ast::WhereClause> {

        let mut where_clause = WhereClause {
            id: ast::DUMMY_NODE_ID,
            predicates: Vec::new(),
        };

        if !self.eat_keyword(keywords::Where) {
            return Ok(where_clause);
        } else {
          panic!("Where clause is not allowed")
        }
    }

    fn parse_fn_args(&mut self, named_args: bool, allow_variadic: bool)
                     -> PResult<'a, (Vec<Arg> , bool)> {
        let sp = self.span;
        let mut variadic = false;
        let args: Vec<Option<Arg>> =
            try!(self.parse_unspanned_seq(
                &token::OpenDelim(token::Paren),
                &token::CloseDelim(token::Paren),
                SeqSep::trailing_allowed(token::Comma),
                |p| {
                    if p.token == token::DotDotDot {
                        p.bump();
                        if allow_variadic {
                            if p.token != token::CloseDelim(token::Paren) {
                                let span = p.span;
                                p.span_err(span,
                                    "`...` must be last in argument list for variadic function");
                            }
                        } else {
                            let span = p.span;
                            p.span_err(span,
                                       "only foreign functions are allowed to be variadic");
                        }
                        variadic = true;
                        Ok(None)
                    } else {
                        match p.parse_arg_general(named_args) {
                            Ok(arg) => Ok(Some(arg)),
                            Err(mut e) => {
                                e.emit();
                                p.eat_to_tokens(&[&token::Comma, &token::CloseDelim(token::Paren)]);
                                Ok(None)
                            }
                        }
                    }
                }
            ));

        let args: Vec<_> = args.into_iter().filter_map(|x| x).collect();

        if variadic && args.is_empty() {
            self.span_err(sp,
                          "variadic function must be declared with at least one named argument");
        }

        Ok((args, variadic))
    }

    /// Parse the argument list and result type of a function declaration
    pub fn parse_fn_decl(&mut self, allow_variadic: bool) -> PResult<'a, P<FnDecl>> {
      println!("Before prase_fn_args");
      let (args, variadic) = try!(self.parse_fn_args(true, allow_variadic));
      println!("After prase_fn_args");
      let ret_ty = try!(self.parse_ret_ty());
      println!("After parse_ret_ty");

      Ok(P(FnDecl {
        inputs: args,
        output: ret_ty,
        variadic: variadic
      }))
    }

    fn is_self_type_ident(&mut self) -> bool {
        match self.token {
          token::Ident(id, token::Plain) => id.name == special_idents::type_self.name,
          _ => false
        }
    }

    fn expect_self_type_ident(&mut self) -> PResult<'a, ast::Ident> {
        match self.token {
            token::Ident(id, token::Plain) if id.name == special_idents::type_self.name => {
                self.bump();
                Ok(id)
            },
            _ => {
                let token_str = self.this_token_to_string();
                Err(self.fatal(&format!("expected `Self`, found `{}`",
                                   token_str)))
            }
        }
    }

    fn parse_fn_header(&mut self) -> PResult<'a, (Ident, ast::Generics)> {
      let id = try!(self.parse_ident());
      let generics = try!(self.parse_generics());
      Ok((id, generics))
    }

    fn mk_item(&mut self, lo: BytePos, hi: BytePos, ident: Ident,
               node: ItemKind, vis: Visibility,
               attrs: Vec<Attribute>) -> P<Item> {
        P(Item {
            ident: ident,
            attrs: attrs,
            id: ast::DUMMY_NODE_ID,
            node: node,
            vis: vis,
            span: mk_sp(lo, hi)
        })
    }

    fn parse_item_fn(&mut self,
                     unsafety: Unsafety,
                     constness: Constness,
                     abi: abi::Abi)
                     -> PResult<'a, ItemInfo> {
      let (ident, mut generics) = try!(self.parse_fn_header());
      let decl = try!(self.parse_fn_decl(false));
      println!("After parse_fn_decl!");
      generics.where_clause = try!(self.parse_where_clause());
      println!("After parse_where_clause!");
      let (inner_attrs, body) = try!(self.parse_inner_attrs_and_block());
      println!("After parse_inner_attrs_and_block!");
      Ok((ident, ItemKind::Fn(decl, unsafety, constness, abi, generics, body), Some(inner_attrs)))
    }

    /// Parse one of the items allowed by the flags.
    /// NB: this function no longer parses the items inside an
    /// extern crate.
    fn parse_item_(&mut self, attrs: Vec<Attribute>,
                   macros_allowed: bool, attributes_allowed: bool) -> PResult<'a, Option<P<Item>>> {
      let lo = self.span.lo;

      let visibility = try!(self.parse_visibility());
      println!("Visibility: {:?}", visibility);

      if self.eat_keyword(keywords::Use) {
        println!("Keyword: Use");
      }

      if self.eat_keyword(keywords::Extern) {
        println!("Keyword: Extern");
      }

      if self.eat_keyword(keywords::Static) {
        println!("Keyword: Static");
      }

      if self.eat_keyword(keywords::Const) {
        println!("Keyword: Const");
      }

      if self.check_keyword(keywords::Fn) {
        println!("Keyword: Fn");
        // FUNCTION ITEM
        self.bump();
        let (ident, item_, extra_attrs) =
                try!(self.parse_item_fn(Unsafety::Normal, Constness::NotConst, Abi::Rust));
        let last_span = self.last_span;
        let item = self.mk_item(lo,
                                last_span.hi,
                                ident,
                                item_,
                                visibility,
                                maybe_append(attrs, extra_attrs));
        return Ok(Some(item));
      }

      if self.eat_keyword(keywords::Mod) {
        println!("Keyword: Mod");
      }

      if self.eat_keyword(keywords::Type) {
        println!("Keyword: Type");
      }

      if self.eat_keyword(keywords::Enum) {
        println!("Keyword: Enum");
      }

      if self.eat_keyword(keywords::Struct) {
        println!("Keyword: Struct");
      }

      unimplemented!()
    }

    pub fn parse_item(&mut self) -> PResult<'a, Option<P<Item>>> {
      let attrs = try!(self.parse_outer_attributes());
      self.parse_item_(attrs, true, false)
    }

    /// Parse visibility: PUB or nothing
    fn parse_visibility(&mut self) -> PResult<'a, Visibility> {
        if self.eat_keyword(keywords::Pub) { Ok(Visibility::Public) }
        else { Ok(Visibility::Inherited) }
    }

    /// Given a termination token, parse all of the items in a module
    fn parse_mod_items(&mut self, term: &token::Token, inner_lo: BytePos) -> PResult<'a, Mod> {
      unimplemented!()
    }

    pub fn parse_crate_mod(&mut self) -> PResult<'a, Crate> {
      unimplemented!()
    }
}