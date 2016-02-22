use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use rustc_serialize::{Encodable, Decodable, Encoder, Decoder};

use abi::Abi;
use codemap::{Span, Spanned};
use parse::token::InternedString;
use parse::token;
use print::pprust;
use ptr::P;


/// A name is a part of an identifier, representing a string or gensym. It's
/// the result of interning.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub u32);

/// A SyntaxContext represents a chain of macro-expandings
/// and renamings. Each macro expansion corresponds to
/// a fresh u32. This u32 is a reference to a table stored
/// in thread-local storage.
/// The special value EMPTY_CTXT is used to indicate an empty
/// syntax context.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, RustcEncodable, RustcDecodable)]
pub struct SyntaxContext(pub u32);

/// An identifier contains a Name (index into the interner
/// table) and a SyntaxContext to track renaming and
/// macro expansion per Flatt et al., "Macros That Work Together"
#[derive(Clone, Copy, Eq)]
pub struct Ident {
    pub name: Name,
    pub ctxt: SyntaxContext
}

impl Name {
    pub fn as_str(self) -> token::InternedString {
        token::InternedString::new_from_name(self)
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({})", self, self.0)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.as_str(), f)
    }
}

impl Encodable for Name {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        s.emit_str(&self.as_str())
    }
}

impl Decodable for Name {
    fn decode<D: Decoder>(d: &mut D) -> Result<Name, D::Error> {
        Ok(token::intern(&try!(d.read_str())[..]))
    }
}

pub const EMPTY_CTXT : SyntaxContext = SyntaxContext(0);

impl Ident {
    pub fn new(name: Name, ctxt: SyntaxContext) -> Ident {
        Ident {name: name, ctxt: ctxt}
    }
    pub fn with_empty_ctxt(name: Name) -> Ident {
        Ident {name: name, ctxt: EMPTY_CTXT}
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Ident) -> bool {
        if self.ctxt != other.ctxt {
            // There's no one true way to compare Idents. They can be compared
            // non-hygienically `id1.name == id2.name`, hygienically
            // `mtwt::resolve(id1) == mtwt::resolve(id2)`, or even member-wise
            // `(id1.name, id1.ctxt) == (id2.name, id2.ctxt)` depending on the situation.
            // Ideally, PartialEq should not be implemented for Ident at all, but that
            // would be too impractical, because many larger structures (Token, in particular)
            // including Idents as their parts derive PartialEq and use it for non-hygienic
            // comparisons. That's why PartialEq is implemented and defaults to non-hygienic
            // comparison. Hash is implemented too and is consistent with PartialEq, i.e. only
            // the name of Ident is hashed. Still try to avoid comparing idents in your code
            // (especially as keys in hash maps), use one of the three methods listed above
            // explicitly.
            //
            // If you see this panic, then some idents from different contexts were compared
            // non-hygienically. It's likely a bug. Use one of the three comparison methods
            // listed above explicitly.

            panic!("idents with different contexts are compared with operator `==`: \
                {:?}, {:?}.", self, other);
        }

        self.name == other.name
    }
}

impl Hash for Ident {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state)
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}#{}", self.name, self.ctxt.0)
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.name, f)
    }
}

impl Encodable for Ident {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        self.name.encode(s)
    }
}

impl Decodable for Ident {
    fn decode<D: Decoder>(d: &mut D) -> Result<Ident, D::Error> {
        Ok(Ident::with_empty_ctxt(try!(Name::decode(d))))
    }
}

/// A "Path" is essentially Rust's notion of a name; for instance:
/// std::cmp::PartialEq  .  It's represented as a sequence of identifiers,
/// along with a bunch of supporting information.
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Path {
    pub span: Span,
    /// A `::foo` path, is relative to the crate root rather than current
    /// module (like paths in an import).
    pub global: bool,
    /// The segments in the path: the things separated by `::`.
    pub segments: Vec<Ident>,
}

/*
impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "path({})", pprust::path_to_string(self))
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", pprust::path_to_string(self))
    }
}*/

/// A delimited sequence of token trees
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Delimited {
    /// The type of delimiter
    pub delim: token::DelimToken,
    /// The span covering the opening delimiter
    pub open_span: Span,
    /// The delimited sequence of token trees
    pub tts: Vec<TokenTree>,
    /// The span covering the closing delimiter
    pub close_span: Span,
}

/// A sequence of token trees
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SequenceRepetition {
    /// The sequence of token trees
    pub tts: Vec<TokenTree>,
    /// The optional separator
    pub separator: Option<token::Token>,
    /// Whether the sequence can be repeated zero (*), or one or more times (+)
    pub op: KleeneOp,
    /// The number of `MatchNt`s that appear in the sequence (and subsequences)
    pub num_captures: usize,
}

/// A Kleene-style [repetition operator](http://en.wikipedia.org/wiki/Kleene_star)
/// for token sequences.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy)]
pub enum KleeneOp {
    ZeroOrMore,
    OneOrMore,
}

/// When the main rust parser encounters a syntax-extension invocation, it
/// parses the arguments to the invocation as a token-tree. This is a very
/// loose structure, such that all sorts of different AST-fragments can
/// be passed to syntax extensions using a uniform type.
///
/// If the syntax extension is an MBE macro, it will attempt to match its
/// LHS token tree against the provided token tree, and if it finds a
/// match, will transcribe the RHS token tree, splicing in any captured
/// macro_parser::matched_nonterminals into the `SubstNt`s it finds.
///
/// The RHS of an MBE macro is the only place `SubstNt`s are substituted.
/// Nothing special happens to misnamed or misplaced `SubstNt`s.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TokenTree {
    /// A single token
    Token(Span, token::Token),
    /// A delimited sequence of token trees
    Delimited(Span, Rc<Delimited>),

    // This only makes sense in MBE macros.

    /// A kleene-style repetition sequence with a span
    // FIXME(eddyb) #12938 Use DST.
    Sequence(Span, Rc<SequenceRepetition>),
}

pub type CrateNum = u32;

pub type NodeId = u32;

/// Node id used to represent the root of the crate.
pub const CRATE_NODE_ID: NodeId = 0;

/// When parsing and doing expansions, we initially give all AST nodes this AST
/// node value. Then later, in the renumber pass, we renumber them to have
/// small, positive ids.
pub const DUMMY_NODE_ID: NodeId = !0;


#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub enum IntTy {
    Is,
    I8,
    I16,
    I32,
    I64,
}

impl fmt::Debug for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.ty_to_string())
    }
}

impl IntTy {
    pub fn ty_to_string(&self) -> &'static str {
        match *self {
            IntTy::Is => "isize",
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64"
        }
    }

    pub fn val_to_string(&self, val: i64) -> String {
        // cast to a u64 so we can correctly print INT64_MIN. All integral types
        // are parsed as u64, so we wouldn't want to print an extra negative
        // sign.
        format!("{}{}", val as u64, self.ty_to_string())
    }

    pub fn ty_max(&self) -> u64 {
        match *self {
            IntTy::I8 => 0x80,
            IntTy::I16 => 0x8000,
            IntTy::Is | IntTy::I32 => 0x80000000, // FIXME: actually ni about Is
            IntTy::I64 => 0x8000000000000000
        }
    }

    pub fn bit_width(&self) -> Option<usize> {
        Some(match *self {
            IntTy::Is => return None,
            IntTy::I8 => 8,
            IntTy::I16 => 16,
            IntTy::I32 => 32,
            IntTy::I64 => 64,
        })
    }
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub enum UintTy {
    Us,
    U8,
    U16,
    U32,
    U64,
}

impl UintTy {
    pub fn ty_to_string(&self) -> &'static str {
        match *self {
            UintTy::Us => "usize",
            UintTy::U8 => "u8",
            UintTy::U16 => "u16",
            UintTy::U32 => "u32",
            UintTy::U64 => "u64"
        }
    }

    pub fn val_to_string(&self, val: u64) -> String {
        format!("{}{}", val, self.ty_to_string())
    }

    pub fn ty_max(&self) -> u64 {
        match *self {
            UintTy::U8 => 0xff,
            UintTy::U16 => 0xffff,
            UintTy::Us | UintTy::U32 => 0xffffffff, // FIXME: actually ni about Us
            UintTy::U64 => 0xffffffffffffffff
        }
    }

    pub fn bit_width(&self) -> Option<usize> {
        Some(match *self {
            UintTy::Us => return None,
            UintTy::U8 => 8,
            UintTy::U16 => 16,
            UintTy::U32 => 32,
            UintTy::U64 => 64,
        })
    }
}

impl fmt::Debug for UintTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for UintTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.ty_to_string())
    }
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub enum FloatTy {
    F32,
    F64,
}

impl fmt::Debug for FloatTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for FloatTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.ty_to_string())
    }
}

impl FloatTy {
    pub fn ty_to_string(&self) -> &'static str {
        match *self {
            FloatTy::F32 => "f32",
            FloatTy::F64 => "f64",
        }
    }

    pub fn bit_width(&self) -> usize {
        match *self {
            FloatTy::F32 => 32,
            FloatTy::F64 => 64,
        }
    }
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Ty {
    pub id: NodeId,
    pub node: TyKind,
    pub span: Span,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct BareFnTy {
    pub abi: Abi,
    pub decl: P<FnDecl>
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
/// The different kinds of types recognized by the compiler
pub enum TyKind {
    Vec(P<Ty>),
    /// A fixed length array (`[T; n]`)
    FixedLengthVec(P<Ty>, P<Expr>),
    /// A raw pointer (`*const T` or `*mut T`)
    Ptr(P<Ty>),
    /// A reference (`&'a T` or `&'a mut T`)
    Rptr(P<Ty>),
    /// A bare function (e.g. `fn(usize) -> bool`)
    BareFn(P<BareFnTy>),
    /// A tuple (`(A, B, C, D,...)`)
    Tup(Vec<P<Ty>> ),
    /// A path (`module::module::...::Type`), optionally
    /// "qualified", e.g. `<Vec<T> as SomeTrait>::SomeType`.
    ///
    /// Type parameters are stored in the Path itself
    Path(Option<QSelf>, Path),
    /// No-op; kept solely so that we can pretty-print faithfully
    Paren(P<Ty>),
    /// TyKind::Infer means the type should be inferred instead of it having been
    /// specified. This can appear anywhere in a type.
    Infer
}

/// represents an argument in a function header
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Arg {
    pub ty: P<Ty>,
    pub id: NodeId,
}

/// Represents the header (not the body) of a function declaration
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct FnDecl {
    pub inputs: Vec<Arg>,
    pub output: FunctionRetTy,
    pub variadic: bool
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum FunctionRetTy {
    /// Functions with return type `!`that always
    /// raise an error or exit (i.e. never return to the caller)
    None(Span),
    /// Return type is not specified.
    ///
    /// Functions default to `()` and
    /// closures default to inference. Span points to where return
    /// type would be inserted.
    Default(Span),
    /// Everything else
    Ty(P<Ty>),
}

impl FunctionRetTy {
    pub fn span(&self) -> Span {
        match *self {
            FunctionRetTy::None(span) => span,
            FunctionRetTy::Default(span) => span,
            FunctionRetTy::Ty(ref ty) => ty.span,
        }
    }
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct QSelf {
    pub ty: P<Ty>,
    pub position: usize
}

/// An expression
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash,)]
pub struct Expr {
    pub id: NodeId,
    pub node: ExprKind,
    pub span: Span,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash,)]
pub enum ExprKind {
  /// An array (`[a, b, c, d]`)
  Vec(Vec<P<Expr>>),
  /// A function call
  ///
  /// The first field resolves to the function itself,
  /// and the second field is the list of arguments
  Call(P<Expr>, Vec<P<Expr>>),
  /// A tuple (`(a, b, c ,d)`)
  Tup(Vec<P<Expr>>),
  /// A binary operation (For example: `a + b`, `a * b`)
  Binary(BinOp, P<Expr>, P<Expr>),
  /// A unary operation (For example: `!x`, `*x`)
  Unary(UnOp, P<Expr>),
  /// A literal (For example: `1u8`, `"foo"`)
  Lit(P<Lit>),
  /// A cast (`foo as f64`)
  Cast(P<Expr>, P<Ty>),
  Type(P<Expr>, P<Ty>),
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug, Copy)]
pub enum BinOpKind {
    /// The `+` operator (addition)
    Add,
    /// The `-` operator (subtraction)
    Sub,
    /// The `*` operator (multiplication)
    Mul,
    /// The `/` operator (division)
    Div,
    /// The `%` operator (modulus)
    Rem,
    /// The `&&` operator (logical and)
    And,
    /// The `||` operator (logical or)
    Or,
    /// The `^` operator (bitwise xor)
    BitXor,
    /// The `&` operator (bitwise and)
    BitAnd,
    /// The `|` operator (bitwise or)
    BitOr,
    /// The `<<` operator (shift left)
    Shl,
    /// The `>>` operator (shift right)
    Shr,
    /// The `==` operator (equality)
    Eq,
    /// The `<` operator (less than)
    Lt,
    /// The `<=` operator (less than or equal to)
    Le,
    /// The `!=` operator (not equal to)
    Ne,
    /// The `>=` operator (greater than or equal to)
    Ge,
    /// The `>` operator (greater than)
    Gt,
}

impl BinOpKind {
    pub fn to_string(&self) -> &'static str {
        use self::BinOpKind::*;
        match *self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            Rem => "%",
            And => "&&",
            Or => "||",
            BitXor => "^",
            BitAnd => "&",
            BitOr => "|",
            Shl => "<<",
            Shr => ">>",
            Eq => "==",
            Lt => "<",
            Le => "<=",
            Ne => "!=",
            Ge => ">=",
            Gt => ">",
        }
    }
    pub fn lazy(&self) -> bool {
        match *self {
            BinOpKind::And | BinOpKind::Or => true,
            _ => false
        }
    }

    pub fn is_shift(&self) -> bool {
        match *self {
            BinOpKind::Shl | BinOpKind::Shr => true,
            _ => false
        }
    }
    pub fn is_comparison(&self) -> bool {
        use self::BinOpKind::*;
        match *self {
            Eq | Lt | Le | Ne | Gt | Ge =>
            true,
            And | Or | Add | Sub | Mul | Div | Rem |
            BitXor | BitAnd | BitOr | Shl | Shr =>
            false,
        }
    }
    /// Returns `true` if the binary operator takes its arguments by value
    pub fn is_by_value(&self) -> bool {
        !self.is_comparison()
    }
}

pub type BinOp = Spanned<BinOpKind>;

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug, Copy)]
pub enum UnOp {
    /// The `*` operator for dereferencing
    Deref,
    /// The `!` operator for logical inversion
    Not,
    /// The `-` operator for negation
    Neg,
}

impl UnOp {
    /// Returns `true` if the unary operator takes its argument by value
    pub fn is_by_value(u: UnOp) -> bool {
        match u {
            UnOp::Neg | UnOp::Not => true,
            _ => false,
        }
    }

    pub fn to_string(op: UnOp) -> &'static str {
        match op {
            UnOp::Deref => "*",
            UnOp::Not => "!",
            UnOp::Neg => "-",
        }
    }
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug, Copy)]
pub enum StrStyle {
    /// A regular string, like `"foo"`
    Cooked,
    /// A raw string, like `r##"foo"##`
    ///
    /// The uint is the number of `#` symbols used
    Raw(usize)
}

/// A literal
pub type Lit = Spanned<LitKind>;

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug, Copy)]
pub enum LitIntType {
    Signed(IntTy),
    Unsigned(UintTy),
    Unsuffixed,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug)]
pub enum LitKind {
    /// A string literal (`"foo"`)
    Str(InternedString, StrStyle),
    /// A byte string (`b"foo"`)
    ByteStr(Rc<Vec<u8>>),
    /// A byte char (`b'f'`)
    Byte(u8),
    /// A character literal (`'a'`)
    Char(char),
    /// An integer literal (`1u8`)
    Int(u64, LitIntType),
    /// A float literal (`1f64` or `1E10f64`)
    Float(InternedString, FloatTy),
    /// A float literal without a suffix (`1.0 or 1.0E10`)
    FloatUnsuffixed(InternedString),
    /// A boolean literal
    Bool(bool),
}

impl LitKind {
    /// Returns true if this literal is a string and false otherwise.
    pub fn is_str(&self) -> bool {
        match *self {
            LitKind::Str(..) => true,
            _ => false,
        }
    }
}