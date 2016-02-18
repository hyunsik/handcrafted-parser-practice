use self::Destination::*;

use codemap::{self, COMMAND_LINE_SP, DUMMY_SP, Pos, Span, MultiSpan};

use errors::{Level, RenderSpan, CodeSuggestion, DiagnosticBuilder, SubDiagnostic};
use errors::RenderSpan::*;
use errors::Level::*;

use std::{cmp, fmt};
use std::io::prelude::*;
use std::io;
use std::rc::Rc;
use term;

pub trait Emitter {
    fn emit(&mut self, span: Option<&MultiSpan>, msg: &str, code: Option<&str>, lvl: Level);
    fn custom_emit(&mut self, sp: &RenderSpan, msg: &str, lvl: Level);

    /// Emit a structured diagnostic.
    fn emit_struct(&mut self, db: &DiagnosticBuilder) {
        self.emit(db.span.as_ref(), &db.message, db.code.as_ref().map(|s| &**s), db.level);
        for child in &db.children {
            match child.render_span {
                Some(ref sp) => self.custom_emit(sp, &child.message, child.level),
                None => self.emit(child.span.as_ref(), &child.message, None, child.level),
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColorConfig {
    Auto,
    Always,
    Never,
}

impl ColorConfig {
    fn use_color(&self) -> bool {
        match *self {
            ColorConfig::Always => true,
            ColorConfig::Never  => false,
            ColorConfig::Auto   => stderr_isatty(),
        }
    }
}

pub struct Registry;

pub struct EmitterWriter {
    dst: Destination,
    registry: Option<Registry>,
    cm: Rc<codemap::CodeMap>,
}

impl Emitter for EmitterWriter {
    fn emit(&mut self,
            msp: Option<&MultiSpan>,
            msg: &str,
            code: Option<&str>,
            lvl: Level) {
        let error = match msp.map(|s|(s.to_span_bounds(), s)) {
            Some((COMMAND_LINE_SP, msp)) => {
                self.emit_(&FileLine(msp.clone()), msg, code, lvl)
            },
            None => print_diagnostic(&mut self.dst, "", lvl, msg, code),
            Some((_, msp)) => self.emit_(&FullSpan(msp.clone()), msg, code, lvl),
        };

        if let Err(e) = error {
            panic!("failed to print diagnostics: {:?}", e);
        }
    }

    fn custom_emit(&mut self,
                   rsp: &RenderSpan,
                   msg: &str,
                   lvl: Level) {
        if let Err(e) = self.emit_(rsp, msg, None, lvl) {
            panic!("failed to print diagnostics: {:?}", e);
        }
    }
}

/// Do not use this for messages that end in `\n` – use `println_maybe_styled` instead. See
/// `EmitterWriter::print_maybe_styled` for details.
macro_rules! print_maybe_styled {
    ($dst: expr, $style: expr, $($arg: tt)*) => {
        $dst.print_maybe_styled(format_args!($($arg)*), $style, false)
    }
}

macro_rules! println_maybe_styled {
    ($dst: expr, $style: expr, $($arg: tt)*) => {
        $dst.print_maybe_styled(format_args!($($arg)*), $style, true)
    }
}

impl EmitterWriter {
  pub fn stderr(color_config: ColorConfig,
                  registry: Option<Registry>,
                  code_map: Rc<codemap::CodeMap>)
                  -> EmitterWriter {
        if color_config.use_color() {
            let dst = Destination::from_stderr();
            EmitterWriter { dst: dst, registry: registry, cm: code_map }
        } else {
            EmitterWriter { dst: Raw(Box::new(io::stderr())), registry: registry, cm: code_map }
        }
    }

    pub fn new(dst: Box<Write + Send>,
               registry: Option<Registry>,
               code_map: Rc<codemap::CodeMap>)
               -> EmitterWriter {
        EmitterWriter { dst: Raw(dst), registry: registry, cm: code_map }
    }

    fn emit_(&mut self,
             rsp: &RenderSpan,
             msg: &str,
             code: Option<&str>,
             lvl: Level)
             -> io::Result<()> {
      // TODO
      Ok(())
    }
}

fn print_diagnostic(dst: &mut Destination,
                    topic: &str,
                    lvl: Level,
                    msg: &str,
                    code: Option<&str>)
                    -> io::Result<()> {
    if !topic.is_empty() {
        try!(write!(dst, "{} ", topic));
    }

    try!(print_maybe_styled!(dst, term::Attr::ForegroundColor(lvl.color()),
                             "{}: ", lvl.to_string()));
    try!(print_maybe_styled!(dst, term::Attr::Bold, "{}", msg));

    if let Some(code) = code {
        let style = term::Attr::ForegroundColor(term::color::BRIGHT_MAGENTA);
        try!(print_maybe_styled!(dst, style, " [{}]", code.clone()));
    }
    try!(write!(dst, "\n"));
    Ok(())
}

#[cfg(unix)]
fn stderr_isatty() -> bool {
    use libc;
    unsafe { libc::isatty(libc::STDERR_FILENO) != 0 }
}
#[cfg(windows)]
fn stderr_isatty() -> bool {
    type DWORD = u32;
    type BOOL = i32;
    type HANDLE = *mut u8;
    const STD_ERROR_HANDLE: DWORD = -12i32 as DWORD;
    extern "system" {
        fn GetStdHandle(which: DWORD) -> HANDLE;
        fn GetConsoleMode(hConsoleHandle: HANDLE,
                          lpMode: *mut DWORD) -> BOOL;
    }
    unsafe {
        let handle = GetStdHandle(STD_ERROR_HANDLE);
        let mut out = 0;
        GetConsoleMode(handle, &mut out) != 0
    }
}

enum Destination {
    Terminal(Box<term::StderrTerminal>),
    Raw(Box<Write + Send>),
}

impl Destination {
    fn from_stderr() -> Destination {
        match term::stderr() {
            Some(t) => Terminal(t),
            None    => Raw(Box::new(io::stderr())),
        }
    }

    fn print_maybe_styled(&mut self,
                          args: fmt::Arguments,
                          color: term::Attr,
                          print_newline_at_end: bool)
                          -> io::Result<()> {
        match *self {
            Terminal(ref mut t) => {
                try!(t.attr(color));
                // If `msg` ends in a newline, we need to reset the color before
                // the newline. We're making the assumption that we end up writing
                // to a `LineBufferedWriter`, which means that emitting the reset
                // after the newline ends up buffering the reset until we print
                // another line or exit. Buffering the reset is a problem if we're
                // sharing the terminal with any other programs (e.g. other rustc
                // instances via `make -jN`).
                //
                // Note that if `msg` contains any internal newlines, this will
                // result in the `LineBufferedWriter` flushing twice instead of
                // once, which still leaves the opportunity for interleaved output
                // to be miscolored. We assume this is rare enough that we don't
                // have to worry about it.
                try!(t.write_fmt(args));
                try!(t.reset());
                if print_newline_at_end {
                    t.write_all(b"\n")
                } else {
                    Ok(())
                }
            }
            Raw(ref mut w) => {
                try!(w.write_fmt(args));
                if print_newline_at_end {
                    w.write_all(b"\n")
                } else {
                    Ok(())
                }
            }
        }
    }
}

impl Write for Destination {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        match *self {
            Terminal(ref mut t) => t.write(bytes),
            Raw(ref mut w) => w.write(bytes),
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        match *self {
            Terminal(ref mut t) => t.flush(),
            Raw(ref mut w) => w.flush(),
        }
    }
}