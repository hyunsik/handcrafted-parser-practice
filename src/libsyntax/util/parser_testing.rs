use ast;
use parse::{ParseSess,PResult,filemap_to_tts};
use parse::parser::Parser;
use parse::token;

/// Map a string to tts, using a made-up filename:
pub fn string_to_tts(source_str: String) -> Vec<ast::TokenTree> {
    let ps = ParseSess::new();
    filemap_to_tts(&ps, ps.codemap().new_filemap("bogofile".to_string(), source_str))
}