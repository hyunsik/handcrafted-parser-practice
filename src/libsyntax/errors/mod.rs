pub use errors::emitter::ColorConfig;

use self::Level::*;
use self::RenderSpan::*;

pub mod emitter;

use codemap::{self, CodeMap, MultiSpan};
use errors::emitter::{Emitter, EmitterWriter, Registry};

use std::cell::{RefCell, Cell};
use std::fmt;
use std::rc::Rc;
use term;

#[derive(Clone)]
pub enum RenderSpan {
    /// A FullSpan renders with both with an initial line for the
    /// message, prefixed by file:linenum, followed by a summary of
    /// the source code covered by the span.
    FullSpan(MultiSpan),

    /// Similar to a FullSpan, but the cited position is the end of
    /// the span, instead of the start. Used, at least, for telling
    /// compiletest/runtest to look at the last line of the span
    /// (since `end_highlight_lines` displays an arrow to the end
    /// of the span).
    EndSpan(MultiSpan),

    /// A suggestion renders with both with an initial line for the
    /// message, prefixed by file:linenum, followed by a summary
    /// of hypothetical source code, where each `String` is spliced
    /// into the lines in place of the code covered by each span.
    Suggestion(CodeSuggestion),

    /// A FileLine renders with just a line for the message prefixed
    /// by file:linenum.
    FileLine(MultiSpan),
}

#[derive(Clone)]
pub struct CodeSuggestion {
    msp: MultiSpan,
    substitutes: Vec<String>,
}

impl RenderSpan {
    fn span(&self) -> &MultiSpan {
        match *self {
            FullSpan(ref msp) |
            Suggestion(CodeSuggestion { ref msp, .. }) |
            EndSpan(ref msp) |
            FileLine(ref msp) =>
                msp
        }
    }
}


/// Used for emitting structured error messages and other diagnostic information.
#[must_use]
pub struct DiagnosticBuilder<'a> {
    emitter: &'a RefCell<Box<Emitter>>,
    level: Level,
    message: String,
    code: Option<String>,
    span: Option<MultiSpan>,
    children: Vec<SubDiagnostic>,
}

/// For example a note attached to an error.
struct SubDiagnostic {
    level: Level,
    message: String,
    span: Option<MultiSpan>,
    render_span: Option<RenderSpan>,
}

impl<'a> DiagnosticBuilder<'a> {
  pub fn span<S: Into<MultiSpan>>(&mut self, sp: S) -> &mut Self {
        self.span = Some(sp.into());
        self
    }

  /// Convenience function for internal use, clients should use one of the
    /// struct_* methods on Handler.
    fn new(emitter: &'a RefCell<Box<Emitter>>,
           level: Level,
           message: &str) -> DiagnosticBuilder<'a> {
        DiagnosticBuilder {
            emitter: emitter,
            level: level,
            message: message.to_owned(),
            code: None,
            span: None,
            children: vec![],
        }
    }

    /// Convenience function for internal use, clients should use one of the
    /// public methods above.
    fn sub(&mut self,
           level: Level,
           message: &str,
           span: Option<MultiSpan>,
           render_span: Option<RenderSpan>) {
        let sub = SubDiagnostic {
            level: level,
            message: message.to_owned(),
            span: span,
            render_span: render_span,
        };
        self.children.push(sub);
    }
}

/// A handler deals with errors; certain errors
/// (fatal, bug, unimpl) may cause immediate exit,
/// others log errors for later reporting.
pub struct Handler {
    err_count: Cell<usize>,
    emit: RefCell<Box<Emitter>>,
    pub can_emit_warnings: bool,
    treat_err_as_bug: bool,
    delayed_span_bug: RefCell<Option<(MultiSpan, String)>>,
}

impl Handler {
    pub fn with_tty_emitter(color_config: ColorConfig,
                            registry: Option<Registry>,
                            can_emit_warnings: bool,
                            treat_err_as_bug: bool,
                            cm: Rc<codemap::CodeMap>)
                            -> Handler {
        let emitter = Box::new(EmitterWriter::stderr(color_config, registry, cm));
        Handler::with_emitter(can_emit_warnings, treat_err_as_bug, emitter)
    }

    pub fn with_emitter(can_emit_warnings: bool,
                        treat_err_as_bug: bool,
                        e: Box<Emitter>) -> Handler {
        Handler {
            err_count: Cell::new(0),
            emit: RefCell::new(e),
            can_emit_warnings: can_emit_warnings,
            treat_err_as_bug: treat_err_as_bug,
            delayed_span_bug: RefCell::new(None),
        }
    }

    pub fn struct_span_fatal<'a, S: Into<MultiSpan>>(&'a self,
                                                     sp: S,
                                                     msg: &str)
                                                     -> DiagnosticBuilder<'a> {
        self.bump_err_count();
        let mut result = DiagnosticBuilder::new(&self.emit, Level::Fatal, msg);
        result.span(sp);
        result
    }

    pub fn bump_err_count(&self) {
        self.err_count.set(self.err_count.get() + 1);
    }

}

#[derive(Copy, PartialEq, Clone, Debug)]
pub enum Level {
    Bug,
    Fatal,
    // An error which while not immediately fatal, should stop the compiler
    // progressing beyond the current phase.
    PhaseFatal,
    Error,
    Warning,
    Note,
    Help,
    Cancelled,
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use std::fmt::Display;

        self.to_str().fmt(f)
    }
}

impl Level {
    fn color(self) -> term::color::Color {
        match self {
            Bug | Fatal | PhaseFatal | Error => term::color::BRIGHT_RED,
            Warning => term::color::BRIGHT_YELLOW,
            Note => term::color::BRIGHT_GREEN,
            Help => term::color::BRIGHT_CYAN,
            Cancelled => unreachable!(),
        }
    }

    fn to_str(self) -> &'static str {
        match self {
            Bug => "error: internal compiler error",
            Fatal | PhaseFatal | Error => "error",
            Warning => "warning",
            Note => "note",
            Help => "help",
            Cancelled => panic!("Shouldn't call on cancelled error"),
        }
    }
}