use codemap::Span;
use parser::parser;

/// The specific types of unsupported syntax
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum ObsoleteSyntax {
    ClosureKind,
    ExternCrateString,
}