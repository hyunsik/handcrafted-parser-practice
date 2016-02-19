use codemap::Span;
use parse::parser;

/// The specific types of unsupported syntax
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum ObsoleteSyntax {
    ClosureKind,
    ExternCrateString,
}