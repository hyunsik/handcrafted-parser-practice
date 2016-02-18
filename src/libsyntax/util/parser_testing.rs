use ast;
use parser::{ParseSess};

/*
/// Map string to parser (via tts)
pub fn string_to_parser<'a>(ps: &'a ParseSess, source_str: String) -> Parser<'a> {
    new_parser_from_source_str(ps,
                               Vec::new(),
                               "bogofile".to_string(),
                               source_str)
}

fn with_error_checking_parse<'a, T, F>(s: String, ps: &'a ParseSess, f: F) -> T where
    F: FnOnce(&mut Parser<'a>) -> PResult<'a, T>,
{
    let mut p = string_to_parser(&ps, s);
    let x = panictry!(f(&mut p));
    p.abort_if_errors();
    x
}

/// Parse a string, return an expr
pub fn string_to_expr (source_str : String) -> P<ast::Expr> {
    let ps = ParseSess::new();
    with_error_checking_parse(source_str, &ps, |p| {
        p.parse_expr()
    })
}
*/