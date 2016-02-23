pub use self::StructFieldKind::*;

use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use rustc_serialize::{Encodable, Decodable, Encoder, Decoder};

use abi::Abi;
use attr::ThinAttributes;
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

pub type CrateNum = u32;

pub type NodeId = u32;

/// Node id used to represent the root of the crate.
pub const CRATE_NODE_ID: NodeId = 0;

/// When parsing and doing expansions, we initially give all AST nodes this AST
/// node value. Then later, in the renumber pass, we renumber them to have
/// small, positive ids.
pub const DUMMY_NODE_ID: NodeId = !0;

pub trait NodeIdAssigner {
    fn next_node_id(&self) -> NodeId;
    fn peek_node_id(&self) -> NodeId;
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct TyParam {
    pub ident: Ident,
    pub id: NodeId,
    pub default: Option<P<Ty>>,
    pub span: Span
}

/// Represents lifetimes and type parameters attached to a declaration
/// of a function, enum, trait, etc.
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Generics {
    pub ty_params: P<[TyParam]>,
    pub where_clause: WhereClause,
}

impl Generics {
    pub fn is_type_parameterized(&self) -> bool {
        !self.ty_params.is_empty()
    }
    pub fn is_parameterized(&self) -> bool {
        self.is_type_parameterized()
    }
}

impl Default for Generics {
    fn default() ->  Generics {
        Generics {
            ty_params: P::empty(),
            where_clause: WhereClause {
                id: DUMMY_NODE_ID,
                predicates: Vec::new(),
            }
        }
    }
}

/// A `where` clause in a definition
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct WhereClause {
    pub id: NodeId,
    pub predicates: Vec<WherePredicate>,
}

/// A single predicate in a `where` clause
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum WherePredicate {
    /// A type binding, e.g. `for<'c> Foo: Send+Clone+'c`
    BoundPredicate(WhereBoundPredicate),
}

/// A type bound, e.g. `for<'c> Foo: Send+Clone+'c`
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct WhereBoundPredicate {
    pub span: Span,
    /// The type being bounded
    pub bounded_ty: P<Ty>,
}

/// The set of MetaItems that define the compilation environment of the crate,
/// used to drive conditional compilation
pub type CrateConfig = Vec<P<MetaItem>> ;

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Crate {
    pub module: Mod,
    pub attrs: Vec<Attribute>,
    pub config: CrateConfig,
    pub span: Span,
}

pub type MetaItem = Spanned<MetaItemKind>;

#[derive(Clone, Eq, RustcEncodable, RustcDecodable, Hash, Debug)]
pub enum MetaItemKind {
    Word(InternedString),
    List(InternedString, Vec<P<MetaItem>>),
    NameValue(InternedString, Lit),
}

// can't be derived because the MetaItemKind::List requires an unordered comparison
impl PartialEq for MetaItemKind {
    fn eq(&self, other: &MetaItemKind) -> bool {
        use self::MetaItemKind::*;
        match *self {
            Word(ref ns) => match *other {
                Word(ref no) => (*ns) == (*no),
                _ => false
            },
            NameValue(ref ns, ref vs) => match *other {
                NameValue(ref no, ref vo) => {
                    (*ns) == (*no) && vs.node == vo.node
                }
                _ => false
            },
            List(ref ns, ref miss) => match *other {
                List(ref no, ref miso) => {
                    ns == no &&
                        miss.iter().all(|mi| miso.iter().any(|x| x.node == mi.node))
                }
                _ => false
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Block {
    /// Statements in a block
    pub stmts: Vec<Stmt>,
    /// An expression at the end of the block
    /// without a semicolon, if any
    pub expr: Option<P<Expr>>,
    pub id: NodeId,
    /// Distinguishes between `unsafe { ... }` and `{ ... }`
    pub rules: BlockCheckMode,
    pub span: Span,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Pat {
    pub id: NodeId,
    pub node: Pat_,
    pub span: Span,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum Pat_ {
  /// Represents a wildcard pattern (`_`)
  PatWild,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug, Copy)]
pub enum Mutability {
    Mutable,
    Immutable,
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

/// A statement
pub type Stmt = Spanned<StmtKind>;

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum StmtKind {
    /// Could be an item or a local (let) binding:
    Decl(P<Decl>, NodeId),

    /// Expr without trailing semi-colon (must have unit type):
    Expr(P<Expr>, NodeId),

    /// Expr with trailing semi-colon (may have any type):
    Semi(P<Expr>, NodeId),
}

// FIXME (pending discussion of #1697, #2178...): local should really be
// a refinement on pat.
/// Local represents a `let` statement, e.g., `let <pat>:<ty> = <expr>;`
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Local {
    pub pat: P<Pat>,
    pub ty: Option<P<Ty>>,
    /// Initializer expression to set the value, if any
    pub init: Option<P<Expr>>,
    pub id: NodeId,
    pub span: Span,
    pub attrs: ThinAttributes,
}

impl Local {
    pub fn attrs(&self) -> &[Attribute] {
        match self.attrs {
            Some(ref b) => b,
            None => &[],
        }
    }
}

pub type Decl = Spanned<DeclKind>;

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum DeclKind {
    /// A local (let) binding:
    Local(P<Local>),
    /// An item binding:
    Item(P<Item>),
}

impl Decl {
    pub fn attrs(&self) -> &[Attribute] {
        match self.node {
            DeclKind::Local(ref l) => l.attrs(),
            DeclKind::Item(ref i) => i.attrs(),
        }
    }
}

/// represents one arm of a 'match'
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash,)]
pub struct Arm {
    pub attrs: Vec<Attribute>,
    pub pats: Vec<P<Pat>>,
    pub guard: Option<P<Expr>>,
    pub body: P<Expr>,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash,)]
pub struct Field {
    pub ident: SpannedIdent,
    pub expr: P<Expr>,
    pub span: Span,
}

pub type SpannedIdent = Spanned<Ident>;

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub enum BlockCheckMode {
    Default,
    Unsafe(UnsafeSource),
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub enum UnsafeSource {
    CompilerGenerated,
    UserProvided,
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
  /// An `if` block, with an optional else block
  ///
  /// `if expr { block } else { expr }`
  If(P<Expr>, P<Block>, Option<P<Expr>>),
  /// A while loop, with an optional label
  ///
  /// `'label: while expr { block }`
  While(P<Expr>, P<Block>, Option<Ident>),
  /// A for loop, with an optional label
  ///
  /// `'label: for pat in expr { block }`
  ///
  /// This is desugared to a combination of `loop` and `match` expressions.
  ForLoop(P<Pat>, P<Expr>, P<Block>, Option<Ident>),
  /// Conditionless loop (can be exited with break, continue, or return)
  ///
  /// `'label: loop { block }`
  Loop(P<Block>, Option<Ident>),
  /// A `match` block.
  Match(P<Expr>, Vec<Arm>),
  /// A closure (for example, `move |a, b, c| {a + b + c}`)
  Closure(CaptureBy, P<FnDecl>, P<Block>),
  /// A block (`{ ... }`)
  Block(P<Block>),

  /// An assignment (`a = foo()`)
  Assign(P<Expr>, P<Expr>),
  /// An assignment with an operator
  ///
  /// For example, `a += 1`.
  AssignOp(BinOp, P<Expr>, P<Expr>),
  /// Access of a named struct field (`obj.foo`)
  Field(P<Expr>, SpannedIdent),
  /// Access of an unnamed field of a struct or tuple-struct
  ///
  /// For example, `foo.0`.
  TupField(P<Expr>, Spanned<usize>),
  /// An indexing operation (`foo[2]`)
  Index(P<Expr>, P<Expr>),
  /// A range (`1..2`, `1..`, or `..2`)
  Range(Option<P<Expr>>, Option<P<Expr>>),

  /// Variable reference, possibly containing `::` and/or type
  /// parameters, e.g. foo::bar::<baz>.
  ///
  /// Optionally "qualified",
  /// e.g. `<Vec<T> as SomeTrait>::SomeType`.
  Path(Option<QSelf>, Path),

  /// A referencing operation (`&a` or `&mut a`)
  AddrOf(Mutability, P<Expr>),
  /// A `break`, with an optional label to break
  Break(Option<SpannedIdent>),
  /// A `continue`, with an optional label
  Again(Option<SpannedIdent>),
  /// A `return`, with an optional value to be returned
  Ret(Option<P<Expr>>),

  /// A struct literal expression.
  ///
  /// For example, `Foo {x: 1, y: 2}`, or
  /// `Foo {x: 1, .. base}`, where `base` is the `Option<Expr>`.
  Struct(Path, Vec<Field>, Option<P<Expr>>),

  /// An array literal constructed from one repeated element.
  ///
  /// For example, `[1u8; 5]`. The first expression is the element
  /// to be repeated; the second is the number of times to repeat it.
  Repeat(P<Expr>, P<Expr>),

  /// No-op: used solely so we can pretty-print faithfully
  Paren(P<Expr>),
}

/// The explicit Self type in a "qualified path". The actual
/// path, including the trait and the associated item, is stored
/// separately. `position` represents the index of the associated
/// item qualified with this Self type.
///
/// ```ignore
/// <Vec<T> as a::b::Trait>::AssociatedItem
///  ^~~~~     ~~~~~~~~~~~~~~^
///  ty        position = 3
///
/// <Vec<T>>::AssociatedItem
///  ^~~~~    ^
///  ty       position = 0
/// ```
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct QSelf {
    pub ty: P<Ty>,
    pub position: usize
}

/// A capture clause
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub enum CaptureBy {
    Value,
    Ref,
}

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

impl Delimited {
    /// Returns the opening delimiter as a token.
    pub fn open_token(&self) -> token::Token {
        token::OpenDelim(self.delim)
    }

    /// Returns the closing delimiter as a token.
    pub fn close_token(&self) -> token::Token {
        token::CloseDelim(self.delim)
    }

    /// Returns the opening delimiter as a token tree.
    pub fn open_tt(&self) -> TokenTree {
        TokenTree::Token(self.open_span, self.open_token())
    }

    /// Returns the closing delimiter as a token tree.
    pub fn close_tt(&self) -> TokenTree {
        TokenTree::Token(self.close_span, self.close_token())
    }
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

#[derive(Copy, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash,)]
pub enum Unsafety {
    Unsafe,
    Normal,
}

#[derive(Copy, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash,)]
pub enum Constness {
    Const,
    NotConst,
}

impl fmt::Display for Unsafety {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(match *self {
            Unsafety::Normal => "normal",
            Unsafety::Unsafe => "unsafe",
        }, f)
    }
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
pub struct Mod {
    /// A span from the first token past `{` to the last token until `}`.
    /// For `mod foo;`, the inner span ranges from the first token
    /// to the last token in the external file.
    pub inner: Span,
    pub items: Vec<P<Item>>,
}

/// Meta-data associated with an item
pub type Attribute = Spanned<Attribute_>;

/// Distinguishes between Attributes that decorate items and Attributes that
/// are contained as statements within items. These two cases need to be
/// distinguished for pretty-printing.
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub enum AttrStyle {
    Outer,
    Inner,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub struct AttrId(pub usize);

/// Doc-comments are promoted to attributes that have is_sugared_doc = true
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Attribute_ {
    pub id: AttrId,
    pub style: AttrStyle,
    pub value: P<MetaItem>,
    pub is_sugared_doc: bool,
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug, Copy)]
pub enum Visibility {
    Public,
    Inherited,
}

impl Visibility {
    pub fn inherit_from(&self, parent_visibility: Visibility) -> Visibility {
        match *self {
            Visibility::Inherited => parent_visibility,
            Visibility::Public => *self
        }
    }
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct StructField_ {
    pub kind: StructFieldKind,
    pub id: NodeId,
    pub ty: P<Ty>,
    pub attrs: Vec<Attribute>,
}

impl StructField_ {
    pub fn ident(&self) -> Option<Ident> {
        match self.kind {
            NamedField(ref ident, _) => Some(ident.clone()),
            UnnamedField(_) => None
        }
    }
}

pub type StructField = Spanned<StructField_>;

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Copy)]
pub enum StructFieldKind {
    NamedField(Ident, Visibility),
    /// Element of a tuple-like struct
    UnnamedField(Visibility),
}

impl StructFieldKind {
    pub fn is_unnamed(&self) -> bool {
        match *self {
            UnnamedField(..) => true,
            NamedField(..) => false,
        }
    }

    pub fn visibility(&self) -> Visibility {
        match *self {
            NamedField(_, vis) | UnnamedField(vis) => vis
        }
    }
}

/// Fields and Ids of enum variants and structs
///
/// For enum variants: `NodeId` represents both an Id of the variant itself (relevant for all
/// variant kinds) and an Id of the variant's constructor (not relevant for `Struct`-variants).
/// One shared Id can be successfully used for these two purposes.
/// Id of the whole enum lives in `Item`.
///
/// For structs: `NodeId` represents an Id of the structure's constructor, so it is not actually
/// used for `Struct`-structs (but still presents). Structures don't have an analogue of "Id of
/// the variant itself" from enum variants.
/// Id of the whole struct lives in `Item`.
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum VariantData {
    Struct(Vec<StructField>, NodeId),
    Tuple(Vec<StructField>, NodeId),
    Unit(NodeId),
}

impl VariantData {
    pub fn fields(&self) -> &[StructField] {
        match *self {
            VariantData::Struct(ref fields, _) | VariantData::Tuple(ref fields, _) => fields,
            _ => &[],
        }
    }
    pub fn id(&self) -> NodeId {
        match *self {
            VariantData::Struct(_, id) | VariantData::Tuple(_, id) | VariantData::Unit(id) => id
        }
    }
    pub fn is_struct(&self) -> bool {
        if let VariantData::Struct(..) = *self { true } else { false }
    }
    pub fn is_tuple(&self) -> bool {
        if let VariantData::Tuple(..) = *self { true } else { false }
    }
    pub fn is_unit(&self) -> bool {
        if let VariantData::Unit(..) = *self { true } else { false }
    }
}

/*
  FIXME (#3300): Should allow items to be anonymous. Right now
  we just use dummy names for anon items.
 */
/// An item
///
/// The name might be a dummy name in case of anonymous items
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub struct Item {
    pub ident: Ident,
    pub attrs: Vec<Attribute>,
    pub id: NodeId,
    pub node: ItemKind,
    pub vis: Visibility,
    pub span: Span,
}

impl Item {
    pub fn attrs(&self) -> &[Attribute] {
        &self.attrs
    }
}

#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum ItemKind {
  /// A type alias, e.g. `type Foo = Bar<u8>`
  Ty(P<Ty>, Generics),
}