use parse::token;

/// SeqSep : a sequence separator (token)
/// and whether a trailing separator is allowed.
pub struct SeqSep {
    pub sep: Option<token::Token>,
    pub trailing_sep_allowed: bool,
}

pub fn seq_sep_trailing_allowed(t: token::Token) -> SeqSep {
    SeqSep {
        sep: Some(t),
        trailing_sep_allowed: true,
    }
}

pub fn seq_sep_none() -> SeqSep {
    SeqSep {
        sep: None,
        trailing_sep_allowed: false,
    }
}