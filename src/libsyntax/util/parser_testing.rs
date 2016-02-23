use ast;
use parse::{ParseSess,PResult,filemap_to_tts};
use parse::new_parser_from_source_str;
use parse::parser::Parser;
use parse::token;

/// Map a string to tts, using a made-up filename:
pub fn string_to_tts(source_str: String) -> Vec<ast::TokenTree> {
    let ps = ParseSess::new();
    filemap_to_tts(&ps, ps.codemap().new_filemap("bogofile".to_string(), source_str))
}

/// Map string to parser (via tts)
pub fn string_to_parser<'a>(ps: &'a ParseSess, source_str: String) -> Parser<'a> {
    new_parser_from_source_str(ps,
                               Vec::new(),
                               "bogofile".to_string(),
                               source_str)
}

/// Convert a vector of strings to a vector of ast::Ident's
pub fn strs_to_idents(ids: Vec<&str> ) -> Vec<ast::Ident> {
    ids.iter().map(|u| token::str_to_ident(*u)).collect()
}