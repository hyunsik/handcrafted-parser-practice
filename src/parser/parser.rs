use std::collections::HashSet;
use std::rc::Rc;

use parser::obsolete::ObsoleteSyntax;
use parser::ParseSess;
use parser::token::{self, keywords};
use parser::token::Token;
use parser::lexer::{Reader, TokenAndSpan};
use codemap::Span;

bitflags! {
    flags Restrictions: u8 {
        const RESTRICTION_STMT_EXPR         = 1 << 0,
        const RESTRICTION_NO_STRUCT_LITERAL = 1 << 1,
    }
}

pub struct Parser<'a> {
    pub sess: &'a ParseSess,
    /// the current token:
    pub token: token::Token,
    /// the span of the current token:
    pub span: Span,
    /// the span of the prior token:
    pub last_span: Span,

    /// the previous token or None (only stashed sometimes).
    pub last_token: Option<Box<token::Token>>,
    last_token_interpolated: bool,
    pub buffer: [TokenAndSpan; 4],
    pub buffer_start: isize,
    pub buffer_end: isize,
    pub tokens_consumed: usize,
    pub restrictions: Restrictions,
    pub quote_depth: usize, // not (yet) related to the quasiquoter
    pub reader: Box<Reader+'a>,
    pub interner: Rc<token::IdentInterner>,
    /// The set of seen errors about obsolete syntax. Used to suppress
    /// extra detail when the same error is seen twice
    pub obsolete_set: HashSet<ObsoleteSyntax>,
    /// Used to determine the path to externally loaded source files
    pub mod_path_stack: Vec<token::InternedString>,
    /// Stack of spans of open delimiters. Used for error message.
    pub open_braces: Vec<Span>,
    /// Flag if this parser "owns" the directory that it is currently parsing
    /// in. This will affect how nested files are looked up.
    pub owns_directory: bool,
    /// Name of the root module this parser originated from. If `None`, then the
    /// name is not known. This does not change while the parser is descending
    /// into modules, and sub-parsers have new values for this name.
    pub root_module_name: Option<String>,
    pub expected_tokens: Vec<TokenType>,
}

impl<'a> Parser<'a> {
    pub fn new(sess: &'a ParseSess,
               mut rdr: Box<Reader+'a>)
               -> Parser<'a>
    {
        let tok0 = rdr.real_token();
        let span = tok0.sp;
        let placeholder = TokenAndSpan {
            tok: Token::Underscore,
            sp: span,
        };

        Parser {
            reader: rdr,
            interner: token::get_ident_interner(),
            sess: sess,
            token: tok0.tok,
            span: span,
            last_span: span,
            last_token: None,
            last_token_interpolated: false,
            buffer: [
                placeholder.clone(),
                placeholder.clone(),
                placeholder.clone(),
                placeholder.clone(),
            ],
            buffer_start: 0,
            buffer_end: 0,
            tokens_consumed: 0,
            restrictions: Restrictions::empty(),
            quote_depth: 0,
            obsolete_set: HashSet::new(),
            mod_path_stack: Vec::new(),
            open_braces: Vec::new(),
            owns_directory: true,
            root_module_name: None,
            expected_tokens: Vec::new(),
        }
    }

    /*
    // parse a stream of tokens into a list of TokenTree's,
    // up to EOF.
    pub fn parse_all_token_trees(&mut self) -> Result<Vec<TokenTree>, String> {
        let mut tts = Vec::new();
        while self.token != Token::Eof {
            tts.push(try!(self.parse_token_tree()));
        }
        Ok(tts)
    }*/
}

#[derive(PartialEq, Eq, Clone)]
pub enum TokenType {
    Token(token::Token),
    Keyword(keywords::Keyword),
    Operator,
}