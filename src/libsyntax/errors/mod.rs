pub use errors::emitter::ColorConfig;

use self::Level::*;
use self::RenderSpan::*;

pub mod emitter;

use codemap::{self, CodeMap, MultiSpan};
use errors::emitter::{Emitter, EmitterWriter, Registry};

use std::cell::{RefCell, Cell};
use std::{error, fmt};
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

/// Used as a return value to signify a fatal error occurred. (It is also
/// used as the argument to panic at the moment, but that will eventually
/// not be true.)
#[derive(Copy, Clone, Debug)]
#[must_use]
pub struct FatalError;

impl fmt::Display for FatalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "parser fatal error")
    }
}

impl error::Error for FatalError {
    fn description(&self) -> &str {
        "The parser has encountered a fatal error"
    }
}

/// Signifies that the compiler died with an explicit call to `.bug`
/// or `.span_bug` rather than a failed assertion, etc.
#[derive(Copy, Clone, Debug)]
pub struct ExplicitBug;

impl fmt::Display for ExplicitBug {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "parser internal bug")
    }
}

impl error::Error for ExplicitBug {
    fn description(&self) -> &str {
        "The parser has encountered an internal bug"
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
  /// Emit the diagnostic.
    pub fn emit(&mut self) {
        if self.cancelled() {
            return;
        }

        self.emitter.borrow_mut().emit_struct(&self);
        self.cancel();

        // if self.is_fatal() {
        //     panic!(FatalError);
        // }
    }

    /// Cancel the diagnostic (a structured diagnostic must either be emitted or
    /// cancelled or it will panic when dropped).
    /// BEWARE: if this DiagnosticBuilder is an error, then creating it will
    /// bump the error count on the Handler and cancelling it won't undo that.
    /// If you want to decrement the error count you should use `Handler::cancel`.
    pub fn cancel(&mut self) {
        self.level = Level::Cancelled;
    }

    pub fn cancelled(&self) -> bool {
        self.level == Level::Cancelled
    }

    pub fn is_fatal(&self) -> bool {
        self.level == Level::Fatal
    }

    pub fn note(&mut self , msg: &str) -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Note, msg, None, None);
        self
    }

    pub fn span_note<S: Into<MultiSpan>>(&mut self,
                                         sp: S,
                                         msg: &str)
                                         -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Note, msg, Some(sp.into()), None);
        self
    }
    pub fn warn(&mut self, msg: &str) -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Warning, msg, None, None);
        self
    }
    pub fn span_warn<S: Into<MultiSpan>>(&mut self,
                                         sp: S,
                                         msg: &str)
                                         -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Warning, msg, Some(sp.into()), None);
        self
    }
    pub fn help(&mut self , msg: &str) -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Help, msg, None, None);
        self
    }
    pub fn span_help<S: Into<MultiSpan>>(&mut self,
                                         sp: S,
                                         msg: &str)
                                         -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Help, msg, Some(sp.into()), None);
        self
    }

    /// Prints out a message with a suggested edit of the code.
    ///
    /// See `diagnostic::RenderSpan::Suggestion` for more information.
    pub fn span_suggestion<S: Into<MultiSpan>>(&mut self,
                                               sp: S,
                                               msg: &str,
                                               suggestion: String)
                                               -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Help, msg, None, Some(Suggestion(CodeSuggestion {
            msp: sp.into(),
            substitutes: vec![suggestion],
        })));
        self
    }
    pub fn span_end_note<S: Into<MultiSpan>>(&mut self,
                                             sp: S,
                                             msg: &str)
                                             -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Note, msg, None, Some(EndSpan(sp.into())));
        self
    }
    pub fn fileline_warn<S: Into<MultiSpan>>(&mut self,
                                             sp: S,
                                             msg: &str)
                                             -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Warning, msg, None, Some(FileLine(sp.into())));
        self
    }
    pub fn fileline_note<S: Into<MultiSpan>>(&mut self,
                                             sp: S,
                                             msg: &str)
                                             -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Note, msg, None, Some(FileLine(sp.into())));
        self
    }
    pub fn fileline_help<S: Into<MultiSpan>>(&mut self,
                                             sp: S,
                                             msg: &str)
                                             -> &mut DiagnosticBuilder<'a> {
        self.sub(Level::Help, msg, None, Some(FileLine(sp.into())));
        self
    }

    pub fn span<S: Into<MultiSpan>>(&mut self, sp: S) -> &mut Self {
        self.span = Some(sp.into());
        self
    }

    pub fn code(&mut self, s: String) -> &mut Self {
        self.code = Some(s);
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

impl<'a> fmt::Debug for DiagnosticBuilder<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.message.fmt(f)
    }
}

/// Destructor bomb - a DiagnosticBuilder must be either emitted or cancelled or
/// we emit a bug.
impl<'a> Drop for DiagnosticBuilder<'a> {
    fn drop(&mut self) {
        if !self.cancelled() {
            self.emitter.borrow_mut().emit(None, "Error constructed but not emitted", None, Bug);
            panic!();
        }
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

    pub fn span_fatal<S: Into<MultiSpan>>(&self, sp: S, msg: &str) -> FatalError {
        if self.treat_err_as_bug {
            self.span_bug(sp, msg);
        }
        self.emit(Some(&sp.into()), msg, Fatal);
        self.bump_err_count();
        return FatalError;
    }

    pub fn span_err<S: Into<MultiSpan>>(&self, sp: S, msg: &str) {
        if self.treat_err_as_bug {
            self.span_bug(sp, msg);
        }
        self.emit(Some(&sp.into()), msg, Error);
        self.bump_err_count();
    }

    pub fn span_warn<S: Into<MultiSpan>>(&self, sp: S, msg: &str) {
        self.emit(Some(&sp.into()), msg, Warning);
    }

    pub fn span_bug<S: Into<MultiSpan>>(&self, sp: S, msg: &str) -> ! {
        self.emit(Some(&sp.into()), msg, Bug);
        panic!(ExplicitBug);
    }

    pub fn fatal(&self, msg: &str) -> FatalError {
        if self.treat_err_as_bug {
            self.bug(msg);
        }
        self.emit.borrow_mut().emit(None, msg, None, Fatal);
        self.bump_err_count();
        FatalError
    }
    pub fn err(&self, msg: &str) {
        if self.treat_err_as_bug {
            self.bug(msg);
        }
        self.emit.borrow_mut().emit(None, msg, None, Error);
        self.bump_err_count();
    }
    pub fn warn(&self, msg: &str) {
        self.emit.borrow_mut().emit(None, msg, None, Warning);
    }

    pub fn bug(&self, msg: &str) -> ! {
        self.emit.borrow_mut().emit(None, msg, None, Bug);
        panic!(ExplicitBug);
    }

    pub fn bump_err_count(&self) {
        self.err_count.set(self.err_count.get() + 1);
    }

    pub fn err_count(&self) -> usize {
        self.err_count.get()
    }

    pub fn has_errors(&self) -> bool {
        self.err_count.get() > 0
    }

    pub fn abort_if_errors(&self) {
        let s;
        match self.err_count.get() {
            0 => {
                let delayed_bug = self.delayed_span_bug.borrow();
                match *delayed_bug {
                    Some((ref span, ref errmsg)) => {
                        self.span_bug(span.clone(), errmsg);
                    },
                    _ => {}
                }

                return;
            }
            1 => s = "aborting due to previous error".to_string(),
            _  => {
                s = format!("aborting due to {} previous errors",
                            self.err_count.get());
            }
        }

        panic!(self.fatal(&s));
    }

    pub fn emit(&self,
                msp: Option<&MultiSpan>,
                msg: &str,
                lvl: Level) {
        if lvl == Warning && !self.can_emit_warnings { return }
        self.emit.borrow_mut().emit(msp, msg, None, lvl);
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