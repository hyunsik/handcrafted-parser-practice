use std::cell::{Cell, RefCell};
use std::fs;
use std::io::{self,Read};
use std::ops::{Add, Sub};
use std::path::Path;
use std::rc::Rc;

pub trait Pos {
  fn from_usize(n: usize) -> Self;
  fn to_usize(&self) -> usize;
}

/// A byte offset. Keep this small (currently 32-bits), as AST contains
/// a lot of them.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Debug)]
pub struct BytePos(pub u32);

/// A character offset. Because of multibyte utf8 characters, a byte offset
/// is not equivalent to a character offset. The CodeMap will convert BytePos
/// values to CharPos values as necessary.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Debug)]
pub struct CharPos(pub usize);

impl Pos for BytePos {
    fn from_usize(n: usize) -> BytePos { BytePos(n as u32) }
    fn to_usize(&self) -> usize { let BytePos(n) = *self; n as usize }
}

impl Add for BytePos {
    type Output = BytePos;

    fn add(self, rhs: BytePos) -> BytePos {
        BytePos((self.to_usize() + rhs.to_usize()) as u32)
    }
}

impl Sub for BytePos {
    type Output = BytePos;

    fn sub(self, rhs: BytePos) -> BytePos {
        BytePos((self.to_usize() - rhs.to_usize()) as u32)
    }
}

impl Pos for CharPos {
    fn from_usize(n: usize) -> CharPos { CharPos(n) }
    fn to_usize(&self) -> usize { let CharPos(n) = *self; n }
}

impl Add for CharPos {
    type Output = CharPos;

    fn add(self, rhs: CharPos) -> CharPos {
        CharPos(self.to_usize() + rhs.to_usize())
    }
}

impl Sub for CharPos {
    type Output = CharPos;

    fn sub(self, rhs: CharPos) -> CharPos {
        CharPos(self.to_usize() - rhs.to_usize())
    }
}

/// Spans represent a region of code, used for error reporting. Positions in spans
/// are *absolute* positions from the beginning of the codemap, not positions
/// relative to FileMaps. Methods on the CodeMap can be used to relate spans back
/// to the original source.
/// You must be careful if the span crosses more than one file - you will not be
/// able to use many of the functions on spans in codemap and you cannot assume
/// that the length of the span = hi - lo; there may be space in the BytePos
/// range between files.
#[derive(Clone, Copy, Hash, Debug)]
pub struct Span {
  pub lo: BytePos,
  pub hi: BytePos
}

pub const DUMMY_SP: Span = Span { lo: BytePos(0), hi: BytePos(0) };

impl PartialEq for Span {
  fn eq(&self, other: &Span) -> bool {
    return (*self).lo == (*other).lo && (*self).hi == (*other).hi;
  }
  fn ne(&self, other: &Span) -> bool { !(*self).eq(other) }
}

impl Eq for Span {}

/* assuming that we're not in macro expansion */
pub fn mk_sp(lo: BytePos, hi: BytePos) -> Span {
  Span {lo: lo, hi: hi}
}

// _____________________________________________________________________________
// FileMap, MultiByteChar, FileName, FileLines
//

pub type FileName = String;

/// Identifies an offset of a multi-byte character in a FileMap
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct MultiByteChar {
    /// The absolute offset of the character in the CodeMap
    pub pos: BytePos,
    /// The number of bytes, >=2
    pub bytes: usize,
}

/// A single source in the CodeMap.
pub struct FileMap {
    /// The name of the file that the source came from, source that doesn't
    /// originate from files has names between angle brackets by convention,
    /// e.g. `<anon>`
    pub name: FileName,
    /// The complete source code
    pub src: Option<Rc<String>>,
    /// The start position of this source in the CodeMap
    pub start_pos: BytePos,
    /// The end position of this source in the CodeMap
    pub end_pos: BytePos,
    /// Locations of lines beginnings in the source code
    pub lines: RefCell<Vec<BytePos>>,
    /// Locations of multi-byte characters in the source code
    pub multibyte_chars: RefCell<Vec<MultiByteChar>>,
}

impl FileMap {
    /// EFFECT: register a start-of-line offset in the
    /// table of line-beginnings.
    /// UNCHECKED INVARIANT: these offsets must be added in the right
    /// order and must be in the right places; there is shared knowledge
    /// about what ends a line between this file and parse.rs
    /// WARNING: pos param here is the offset relative to start of CodeMap,
    /// and CodeMap will append a newline when adding a filemap without a newline at the end,
    /// so the safe way to call this is with value calculated as
    /// filemap.start_pos + newline_offset_relative_to_the_start_of_filemap.
    pub fn next_line(&self, pos: BytePos) {
        // the new charpos must be > the last one (or it's the first one).
        let mut lines = self.lines.borrow_mut();
        let line_len = lines.len();
        assert!(line_len == 0 || ((*lines)[line_len - 1] < pos));
        lines.push(pos);
    }

    /// get a line from the list of pre-computed line-beginnings.
    /// line-number here is 0-based.
    pub fn get_line(&self, line_number: usize) -> Option<&str> {
        match self.src {
            Some(ref src) => {
                let lines = self.lines.borrow();
                lines.get(line_number).map(|&line| {
                    let begin: BytePos = line - self.start_pos;
                    let begin = begin.to_usize();
                    // We can't use `lines.get(line_number+1)` because we might
                    // be parsing when we call this function and thus the current
                    // line is the last one we have line info for.
                    let slice = &src[begin..];
                    match slice.find('\n') {
                        Some(e) => &slice[..e],
                        None => slice
                    }
                })
            }
            None => None
        }
    }
}

pub struct CodeMap {
  pub files: RefCell<Vec<Rc<FileMap>>>,
  file_loader: Box<FileLoader>
}

impl CodeMap {
  pub fn new() -> CodeMap {
        CodeMap {
            files: RefCell::new(Vec::new()),
            file_loader: Box::new(RealFileLoader)
        }
    }

    pub fn with_file_loader(file_loader: Box<FileLoader>) -> CodeMap {
        CodeMap {
            files: RefCell::new(Vec::new()),
            file_loader: file_loader
        }
    }

    pub fn file_exists(&self, path: &Path) -> bool {
        self.file_loader.file_exists(path)
    }

    fn next_start_pos(&self) -> usize {
        let files = self.files.borrow();
        match files.last() {
            None => 0,
            // Add one so there is some space between files. This lets us distinguish
            // positions in the codemap, even in the presence of zero-length files.
            Some(last) => last.end_pos.to_usize() + 1,
        }
    }

    /// Creates a new filemap without setting its line information. If you don't
    /// intend to set the line information yourself, you should use new_filemap_and_lines.
    pub fn new_filemap(&self, filename: FileName, mut src: String) -> Rc<FileMap> {
        let start_pos = self.next_start_pos();
        let mut files = self.files.borrow_mut();

        // Remove utf-8 BOM if any.
        if src.starts_with("\u{feff}") {
            src.drain(..3);
        }

        let end_pos = start_pos + src.len();

        let filemap = Rc::new(FileMap {
            name: filename,
            src: Some(Rc::new(src)),
            start_pos: Pos::from_usize(start_pos),
            end_pos: Pos::from_usize(end_pos),
            lines: RefCell::new(Vec::new()),
            multibyte_chars: RefCell::new(Vec::new()),
        });

        files.push(filemap.clone());

        filemap
    }

    /// Creates a new filemap and sets its line information.
    pub fn new_filemap_and_lines(&self, filename: &str, src: &str) -> Rc<FileMap> {
        let fm = self.new_filemap(filename.to_string(), src.to_owned());
        let mut byte_pos: u32 = 0;
        for line in src.lines() {
            // register the start of this line
            fm.next_line(BytePos(byte_pos));

            // update byte_pos to include this line and the \n at the end
            byte_pos += line.len() as u32 + 1;
        }
        fm
    }
}

/// An abstraction over the fs operations used by the Parser.
pub trait FileLoader {
    /// Query the existence of a file.
    fn file_exists(&self, path: &Path) -> bool;

    /// Read the contents of an UTF-8 file into memory.
    fn read_file(&self, path: &Path) -> io::Result<String>;
}

/// A FileLoader that uses std::fs to load real files.
pub struct RealFileLoader;

impl FileLoader for RealFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        fs::metadata(path).is_ok()
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        let mut src = String::new();
        try!(try!(fs::File::open(path)).read_to_string(&mut src));
        Ok(src)
    }
}

// _____________________________________________________________________________
// Tests
//

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t1 () {
        let cm = CodeMap::new();
        let fm = cm.new_filemap("blork.rs".to_string(),
                                "first line.\nsecond line".to_string());
        fm.next_line(BytePos(0));
        // Test we can get lines with partial line info.
        assert_eq!(fm.get_line(0), Some("first line."));
        // TESTING BROKEN BEHAVIOR: line break declared before actual line break.
        fm.next_line(BytePos(10));
        assert_eq!(fm.get_line(1), Some("."));
        fm.next_line(BytePos(12));
        assert_eq!(fm.get_line(2), Some("second line"));
    }
}