use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use parser::token;
use codemap::Span;

/// A name is a part of an identifier, representing a string or gensym. It's
/// the result of interning.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub u32);

/// A SyntaxContext represents a chain of macro-expandings
/// and renamings. Each macro expansion corresponds to
/// a fresh u32. This u32 is a reference to a table stored
// in thread-local storage.
// The special value EMPTY_CTXT is used to indicate an empty
// syntax context.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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