pub use self::BinOpToken::*;
pub use self::DelimToken::*;
pub use self::Lit::*;
pub use self::Token::*;
pub use self::IdentStyle::*;

use std::fmt;
use std::ops::Deref;
use std::rc::Rc;
use rustc_serialize::{Encodable, Decodable, Encoder, Decoder};

use ast::BinOpKind;
use ast;
use util::interner::{self, StrInterner, RcStr};

#[allow(non_camel_case_types)]
#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Hash, Debug, Copy)]
pub enum BinOpToken {
  Plus,
  Minus,
  Star,
  Slash,
  Percent,
  Caret,
  And,
  Or,
  Shl,
  Shr,
}

/// A delimiter token
#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Hash, Debug, Copy)]
pub enum DelimToken {
    /// A round parenthesis: `(` or `)`
    Paren,
    /// A square bracket: `[` or `]`
    Bracket,
    /// A curly brace: `{` or `}`
    Brace,
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Hash, Debug, Copy)]
pub enum IdentStyle {
  /// `::` follows the identifier with no whitespace in-between.
  ModName,
  Plain,
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Hash, Debug, Copy)]
pub enum Lit {
  Byte(ast::Name),
  Char(ast::Name),
  Integer(ast::Name),
  Float(ast::Name),
  Str_(ast::Name),
  StrRaw(ast::Name, usize), /* raw str delimited by n hash symbols */
  ByteStr(ast::Name),
  ByteStrRaw(ast::Name, usize), /* raw byte str delimited by n hash symbols */
}

impl Lit {
    pub fn short_name(&self) -> &'static str {
        match *self {
            Byte(_) => "byte",
            Char(_) => "char",
            Integer(_) => "integer",
            Float(_) => "float",
            Str_(_) | StrRaw(..) => "string",
            ByteStr(_) | ByteStrRaw(..) => "byte string"
        }
    }
}

#[allow(non_camel_case_types)]
#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Hash, Debug)]
pub enum Token {
    /* Expression-operator symbols. */
    Eq,
    Lt,
    Le,
    EqEq,
    Ne,
    Ge,
    Gt,
    AndAnd,
    OrOr,
    Not,
    Tilde,
    BinOp(BinOpToken),
    BinOpEq(BinOpToken),

    /* Structural symbols */
    At,
    Dot,
    DotDot,
    DotDotDot,
    Comma,
    Semi,
    Colon,
    ModSep,
    RArrow,
    LArrow,
    FatArrow,
    Pound,
    Dollar,
    Question,
    /// An opening delimiter, eg. `{`
    OpenDelim(DelimToken),
    /// A closing delimiter, eg. `}`
    CloseDelim(DelimToken),

    /* Literals */
    Literal(Lit, Option<ast::Name>),

    /* Name components */
    Ident(ast::Ident, IdentStyle),
    Underscore,
    Lifetime(ast::Ident),

    // Can be expanded into several tokens.
    /// Doc comment
    DocComment(ast::Name),

    // Junk. These carry no data because we don't really care about the data
    // they *would* carry, and don't really want to allocate a new ident for
    // them. Instead, users could extract that from the associated span.

    /// Whitespace
    Whitespace,
    /// Comment
    Comment,
    Shebang(ast::Name),

    Eof,
}

impl Token {
    /// Returns `true` if the token starts with '>'.
    pub fn is_like_gt(&self) -> bool {
        match *self {
            BinOp(Shr) | BinOpEq(Shr) | Gt | Ge => true,
            _ => false,
        }
    }

    /// Returns `true` if the token can appear at the start of an expression.
    pub fn can_begin_expr(&self) -> bool {
        match *self {
            OpenDelim(_)                => true,
            Ident(_, _)                 => true,
            Underscore                  => true,
            Tilde                       => true,
            Literal(_, _)               => true,
            Not                         => true,
            BinOp(Minus)                => true,
            BinOp(Star)                 => true,
            BinOp(And)                  => true,
            BinOp(Or)                   => true, // in lambda syntax
            OrOr                        => true, // in lambda syntax
            AndAnd                      => true, // double borrow
            DotDot                      => true, // range notation
            ModSep                      => true,
            Pound                       => true, // for expression attributes
            _                           => false,
        }
    }

    /// Returns `true` if the token is any literal
    pub fn is_lit(&self) -> bool {
        match *self {
            Literal(_, _) => true,
            _          => false,
        }
    }

    /// Returns `true` if the token is an identifier.
    pub fn is_ident(&self) -> bool {
        match *self {
            Ident(_, _) => true,
            _           => false,
        }
    }

    /// Returns `true` if the token is an interpolated path.
    pub fn is_path(&self) -> bool {
      // TODO - how can I handle it?
      false
    }

    /// Returns `true` if the token is a path that is not followed by a `::`
    /// token.
    #[allow(non_upper_case_globals)]
    pub fn is_plain_ident(&self) -> bool {
        match *self {
            Ident(_, Plain) => true,
            _               => false,
        }
    }

    /// Returns `true` if the token is a lifetime.
    pub fn is_lifetime(&self) -> bool {
        match *self {
            Lifetime(..) => true,
            _            => false,
        }
    }

    /// Returns `true` if the token is either the `mut` or `const` keyword.
    pub fn is_mutability(&self) -> bool {
        self.is_keyword(keywords::Mut) ||
        self.is_keyword(keywords::Const)
    }

    /// Maps a token to its corresponding binary operator.
    pub fn to_binop(&self) -> Option<BinOpKind> {
        match *self {
            BinOp(Star)     => Some(BinOpKind::Mul),
            BinOp(Slash)    => Some(BinOpKind::Div),
            BinOp(Percent)  => Some(BinOpKind::Rem),
            BinOp(Plus)     => Some(BinOpKind::Add),
            BinOp(Minus)    => Some(BinOpKind::Sub),
            BinOp(Shl)      => Some(BinOpKind::Shl),
            BinOp(Shr)      => Some(BinOpKind::Shr),
            BinOp(And)      => Some(BinOpKind::BitAnd),
            BinOp(Caret)    => Some(BinOpKind::BitXor),
            BinOp(Or)       => Some(BinOpKind::BitOr),
            Lt              => Some(BinOpKind::Lt),
            Le              => Some(BinOpKind::Le),
            Ge              => Some(BinOpKind::Ge),
            Gt              => Some(BinOpKind::Gt),
            EqEq            => Some(BinOpKind::Eq),
            Ne              => Some(BinOpKind::Ne),
            AndAnd          => Some(BinOpKind::And),
            OrOr            => Some(BinOpKind::Or),
            _               => None,
        }
    }

    /// Returns `true` if the token is a given keyword, `kw`.
    #[allow(non_upper_case_globals)]
    pub fn is_keyword(&self, kw: keywords::Keyword) -> bool {
        match *self {
            Ident(sid, Plain) => kw.to_name() == sid.name,
            _                      => false,
        }
    }

    pub fn is_keyword_allow_following_colon(&self, kw: keywords::Keyword) -> bool {
        match *self {
            Ident(sid, _) => { kw.to_name() == sid.name }
            _ => { false }
        }
    }

    /// Returns `true` if the token is either a special identifier, or a strict
    /// or reserved keyword.
    #[allow(non_upper_case_globals)]
    pub fn is_any_keyword(&self) -> bool {
        match *self {
            Ident(sid, Plain) => {
                let n = sid.name;

                   n == SELF_KEYWORD_NAME
                || n == STATIC_KEYWORD_NAME
                || n == SUPER_KEYWORD_NAME
                || n == SELF_TYPE_KEYWORD_NAME
                || STRICT_KEYWORD_START <= n
                && n <= RESERVED_KEYWORD_FINAL
            },
            _ => false
        }
    }

    /// Returns `true` if the token may not appear as an identifier.
    #[allow(non_upper_case_globals)]
    pub fn is_strict_keyword(&self) -> bool {
        match *self {
            Ident(sid, Plain) => {
                let n = sid.name;

                   n == SELF_KEYWORD_NAME
                || n == STATIC_KEYWORD_NAME
                || n == SUPER_KEYWORD_NAME
                || n == SELF_TYPE_KEYWORD_NAME
                || STRICT_KEYWORD_START <= n
                && n <= STRICT_KEYWORD_FINAL
            },
            Ident(sid, ModName) => {
                let n = sid.name;

                   n != SELF_KEYWORD_NAME
                && n != SUPER_KEYWORD_NAME
                && STRICT_KEYWORD_START <= n
                && n <= STRICT_KEYWORD_FINAL
            }
            _ => false,
        }
    }

    /// Returns `true` if the token is a keyword that has been reserved for
    /// possible future use.
    #[allow(non_upper_case_globals)]
    pub fn is_reserved_keyword(&self) -> bool {
        match *self {
            Ident(sid, Plain) => {
                let n = sid.name;

                    RESERVED_KEYWORD_START <= n
                && n <= RESERVED_KEYWORD_FINAL
            },
            _ => false,
        }
    }
}

// Get the first "argument"
macro_rules! first {
    ( $first:expr, $( $remainder:expr, )* ) => ( $first )
}

// Get the last "argument" (has to be done recursively to avoid phoney local ambiguity error)
macro_rules! last {
    ( $first:expr, $( $remainder:expr, )+ ) => ( last!( $( $remainder, )+ ) );
    ( $first:expr, ) => ( $first )
}

// In this macro, there is the requirement that the name (the number) must be monotonically
// increasing by one in the special identifiers, starting at 0; the same holds for the keywords,
// except starting from the next number instead of zero, and with the additional exception that
// special identifiers are *also* allowed (they are deduplicated in the important place, the
// interner), an exception which is demonstrated by "static" and "self".
macro_rules! declare_special_idents_and_keywords {(
    // So now, in these rules, why is each definition parenthesised?
    // Answer: otherwise we get a spurious local ambiguity bug on the "}"
    pub mod special_idents {
        $( ($si_name:expr, $si_static:ident, $si_str:expr); )*
    }

    pub mod keywords {
        'strict:
        $( ($sk_name:expr, $sk_variant:ident, $sk_str:expr); )*
        'reserved:
        $( ($rk_name:expr, $rk_variant:ident, $rk_str:expr); )*
    }
) => {
    const STRICT_KEYWORD_START: ast::Name = first!($( ast::Name($sk_name), )*);
    const STRICT_KEYWORD_FINAL: ast::Name = last!($( ast::Name($sk_name), )*);
    const RESERVED_KEYWORD_START: ast::Name = first!($( ast::Name($rk_name), )*);
    const RESERVED_KEYWORD_FINAL: ast::Name = last!($( ast::Name($rk_name), )*);

    pub mod special_idents {
        use ast;
        $(
            #[allow(non_upper_case_globals)]
            pub const $si_static: ast::Ident = ast::Ident {
                name: ast::Name($si_name),
                ctxt: ast::EMPTY_CTXT,
            };
         )*
    }

    pub mod special_names {
        use ast;
        $(
            #[allow(non_upper_case_globals)]
            pub const $si_static: ast::Name = ast::Name($si_name);
        )*
    }

    /// All the valid words that have meaning in the Rust language.
    ///
    /// Rust keywords are either 'strict' or 'reserved'.  Strict keywords may not
    /// appear as identifiers at all. Reserved keywords are not used anywhere in
    /// the language and may not appear as identifiers.
    pub mod keywords {
        pub use self::Keyword::*;
        use ast;

        #[derive(Copy, Clone, PartialEq, Eq)]
        pub enum Keyword {
            $( $sk_variant, )*
            $( $rk_variant, )*
        }

        impl Keyword {
            pub fn to_name(&self) -> ast::Name {
                match *self {
                    $( $sk_variant => ast::Name($sk_name), )*
                    $( $rk_variant => ast::Name($rk_name), )*
                }
            }
        }
    }

    fn mk_fresh_ident_interner() -> IdentInterner {
        // The indices here must correspond to the numbers in
        // special_idents, in Keyword to_name(), and in static
        // constants below.
        let mut init_vec = Vec::new();
        $(init_vec.push($si_str);)*
        $(init_vec.push($sk_str);)*
        $(init_vec.push($rk_str);)*
        interner::StrInterner::prefill(&init_vec[..])
    }
}}

// If the special idents get renumbered, remember to modify these two as appropriate
pub const SELF_KEYWORD_NAME: ast::Name = ast::Name(SELF_KEYWORD_NAME_NUM);
const STATIC_KEYWORD_NAME: ast::Name = ast::Name(STATIC_KEYWORD_NAME_NUM);
const SUPER_KEYWORD_NAME: ast::Name = ast::Name(SUPER_KEYWORD_NAME_NUM);
const SELF_TYPE_KEYWORD_NAME: ast::Name = ast::Name(SELF_TYPE_KEYWORD_NAME_NUM);

pub const SELF_KEYWORD_NAME_NUM: u32 = 1;
const STATIC_KEYWORD_NAME_NUM: u32 = 2;
const SUPER_KEYWORD_NAME_NUM: u32 = 3;
const SELF_TYPE_KEYWORD_NAME_NUM: u32 = 10;

// NB: leaving holes in the ident table is bad! a different ident will get
// interned with the id from the hole, but it will be between the min and max
// of the reserved words, and thus tagged as "reserved".

declare_special_idents_and_keywords! {
    pub mod special_idents {
        // These ones are statics
        (0,                          invalid,                "");
        (super::SELF_KEYWORD_NAME_NUM,   self_,              "self");
        (super::STATIC_KEYWORD_NAME_NUM, statik,             "static");
        (super::SUPER_KEYWORD_NAME_NUM, super_,              "super");
        (4,                          static_lifetime,        "'static");

        // for matcher NTs
        (5,                          tt,                     "tt");
        (6,                          matchers,               "matchers");

        // outside of libsyntax
        (7,                          clownshoe_abi,          "__rust_abi");
        (8,                          opaque,                 "<opaque>");
        (9,                          unnamed_field,          "<unnamed_field>");
        (super::SELF_TYPE_KEYWORD_NAME_NUM, type_self,       "Self");
        (11,                         prelude_import,         "prelude_import");
    }

    pub mod keywords {
        // These ones are variants of the Keyword enum

        'strict:
        (12,                         As,         "as");
        (13,                         Break,      "break");
        (14,                         Crate,      "crate");
        (15,                         Else,       "else");
        (16,                         Enum,       "enum");
        (17,                         Extern,     "extern");
        (18,                         False,      "false");
        (19,                         Fn,         "fn");
        (20,                         For,        "for");
        (21,                         If,         "if");
        (22,                         Impl,       "impl");
        (23,                         In,         "in");
        (24,                         Let,        "let");
        (25,                         Loop,       "loop");
        (26,                         Match,      "match");
        (27,                         Mod,        "mod");
        (28,                         Move,       "move");
        (29,                         Mut,        "mut");
        (30,                         Pub,        "pub");
        (31,                         Ref,        "ref");
        (32,                         Return,     "return");
        // Static and Self are also special idents (prefill de-dupes)
        (super::STATIC_KEYWORD_NAME_NUM, Static, "static");
        (super::SELF_KEYWORD_NAME_NUM, SelfValue, "self");
        (super::SELF_TYPE_KEYWORD_NAME_NUM, SelfType, "Self");
        (33,                         Struct,     "struct");
        (super::SUPER_KEYWORD_NAME_NUM, Super,   "super");
        (34,                         True,       "true");
        (35,                         Trait,      "trait");
        (36,                         Type,       "type");
        (37,                         Unsafe,     "unsafe");
        (38,                         Import,     "import");
        (39,                         While,      "while");
        (40,                         Continue,   "continue");
        (41,                         Box,        "box");
        (42,                         Const,      "const");
        (43,                         Where,      "where");
        'reserved:
        (44,                         Virtual,    "virtual");
        (45,                         Proc,       "proc");
        (46,                         Alignof,    "alignof");
        (47,                         Become,     "become");
        (48,                         Offsetof,   "offsetof");
        (49,                         Priv,       "priv");
        (50,                         Pure,       "pure");
        (51,                         Sizeof,     "sizeof");
        (52,                         Typeof,     "typeof");
        (53,                         Unsized,    "unsized");
        (54,                         Yield,      "yield");
        (55,                         Do,         "do");
        (56,                         Abstract,   "abstract");
        (57,                         Final,      "final");
        (58,                         Override,   "override");
        (59,                         Macro,      "macro");
    }
}

// looks like we can get rid of this completely...
pub type IdentInterner = StrInterner;

// if an interner exists in TLS, return it. Otherwise, prepare a
// fresh one.
// FIXME(eddyb) #8726 This should probably use a thread-local reference.
pub fn get_ident_interner() -> Rc<IdentInterner> {
    thread_local!(static KEY: Rc<::parse::token::IdentInterner> = {
        Rc::new(mk_fresh_ident_interner())
    });
    KEY.with(|k| k.clone())
}

/// Reset the ident interner to its initial state.
pub fn reset_ident_interner() {
    let interner = get_ident_interner();
    interner.reset(mk_fresh_ident_interner());
}

/// Represents a string stored in the thread-local interner. Because the
/// interner lives for the life of the thread, this can be safely treated as an
/// immortal string, as long as it never crosses between threads.
///
/// FIXME(pcwalton): You must be careful about what you do in the destructors
/// of objects stored in TLS, because they may run after the interner is
/// destroyed. In particular, they must not access string contents. This can
/// be fixed in the future by just leaking all strings until thread death
/// somehow.
#[derive(Clone, PartialEq, Hash, PartialOrd, Eq, Ord)]
pub struct InternedString {
    string: RcStr,
}

impl InternedString {
    #[inline]
    pub fn new(string: &'static str) -> InternedString {
        InternedString {
            string: RcStr::new(string),
        }
    }

    #[inline]
    fn new_from_rc_str(string: RcStr) -> InternedString {
        InternedString {
            string: string,
        }
    }

    #[inline]
    pub fn new_from_name(name: ast::Name) -> InternedString {
        let interner = get_ident_interner();
        InternedString::new_from_rc_str(interner.get(name))
    }
}

impl Deref for InternedString {
    type Target = str;

    fn deref(&self) -> &str { &*self.string }
}

impl fmt::Debug for InternedString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.string, f)
    }
}

impl fmt::Display for InternedString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.string, f)
    }
}

impl<'a> PartialEq<&'a str> for InternedString {
    #[inline(always)]
    fn eq(&self, other: & &'a str) -> bool {
        PartialEq::eq(&self.string[..], *other)
    }
    #[inline(always)]
    fn ne(&self, other: & &'a str) -> bool {
        PartialEq::ne(&self.string[..], *other)
    }
}

impl<'a> PartialEq<InternedString> for &'a str {
    #[inline(always)]
    fn eq(&self, other: &InternedString) -> bool {
        PartialEq::eq(*self, &other.string[..])
    }
    #[inline(always)]
    fn ne(&self, other: &InternedString) -> bool {
        PartialEq::ne(*self, &other.string[..])
    }
}

impl Decodable for InternedString {
    fn decode<D: Decoder>(d: &mut D) -> Result<InternedString, D::Error> {
        Ok(intern(try!(d.read_str()).as_ref()).as_str())
    }
}

impl Encodable for InternedString {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        s.emit_str(&self.string)
    }
}

/// Interns and returns the string contents of an identifier, using the
/// thread-local interner.
#[inline]
pub fn intern_and_get_ident(s: &str) -> InternedString {
    intern(s).as_str()
}

/// Maps a string to its interned representation.
#[inline]
pub fn intern(s: &str) -> ast::Name {
    get_ident_interner().intern(s)
}

/// gensym's a new usize, using the current interner.
#[inline]
pub fn gensym(s: &str) -> ast::Name {
    get_ident_interner().gensym(s)
}

/// Maps a string to an identifier with an empty syntax context.
#[inline]
pub fn str_to_ident(s: &str) -> ast::Ident {
    ast::Ident::with_empty_ctxt(intern(s))
}

/// Maps a string to a gensym'ed identifier.
#[inline]
pub fn gensym_ident(s: &str) -> ast::Ident {
    ast::Ident::with_empty_ctxt(gensym(s))
}

