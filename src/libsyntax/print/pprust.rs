use std::io;
use std::iter;

use ast::{self, Expr};

use parse::token::{self, BinOpToken, Token, InternedString};

pub fn binop_to_string(op: BinOpToken) -> &'static str {
    match op {
        token::Plus     => "+",
        token::Minus    => "-",
        token::Star     => "*",
        token::Slash    => "/",
        token::Percent  => "%",
        token::Caret    => "^",
        token::And      => "&",
        token::Or       => "|",
        token::Shl      => "<<",
        token::Shr      => ">>",
    }
}

pub fn token_to_string(tok: &Token) -> String {
    match *tok {
        token::Eq                   => "=".to_string(),
        token::Lt                   => "<".to_string(),
        token::Le                   => "<=".to_string(),
        token::EqEq                 => "==".to_string(),
        token::Ne                   => "!=".to_string(),
        token::Ge                   => ">=".to_string(),
        token::Gt                   => ">".to_string(),
        token::Not                  => "!".to_string(),
        token::Tilde                => "~".to_string(),
        token::OrOr                 => "||".to_string(),
        token::AndAnd               => "&&".to_string(),
        token::BinOp(op)            => binop_to_string(op).to_string(),
        token::BinOpEq(op)          => format!("{}=", binop_to_string(op)),

        /* Structural symbols */
        token::At                   => "@".to_string(),
        token::Dot                  => ".".to_string(),
        token::DotDot               => "..".to_string(),
        token::DotDotDot            => "...".to_string(),
        token::Comma                => ",".to_string(),
        token::Semi                 => ";".to_string(),
        token::Colon                => ":".to_string(),
        token::ModSep               => "::".to_string(),
        token::RArrow               => "->".to_string(),
        token::LArrow               => "<-".to_string(),
        token::FatArrow             => "=>".to_string(),
        token::OpenDelim(token::Paren) => "(".to_string(),
        token::CloseDelim(token::Paren) => ")".to_string(),
        token::OpenDelim(token::Bracket) => "[".to_string(),
        token::CloseDelim(token::Bracket) => "]".to_string(),
        token::OpenDelim(token::Brace) => "{".to_string(),
        token::CloseDelim(token::Brace) => "}".to_string(),
        token::Pound                => "#".to_string(),
        token::Dollar               => "$".to_string(),
        token::Question             => "?".to_string(),

        /* Literals */
        token::Literal(lit, suf) => {
            let mut out = match lit {
                token::Byte(b)           => format!("b'{}'", b),
                token::Char(c)           => format!("'{}'", c),
                token::Float(c)          => c.to_string(),
                token::Integer(c)        => c.to_string(),
                token::Str_(s)           => format!("\"{}\"", s),
                token::StrRaw(s, n)      => format!("r{delim}\"{string}\"{delim}",
                                                    delim=repeat("#", n),
                                                    string=s),
                token::ByteStr(v)         => format!("b\"{}\"", v),
                token::ByteStrRaw(s, n)   => format!("br{delim}\"{string}\"{delim}",
                                                    delim=repeat("#", n),
                                                    string=s),
            };

            if let Some(s) = suf {
                out.push_str(&s.as_str())
            }

            out
        }

        /* Name components */
        token::Ident(s, _)          => s.to_string(),
        token::Lifetime(s)          => s.to_string(),
        token::Underscore           => "_".to_string(),

        /* Other */
        token::DocComment(s)        => s.to_string(),
        token::Eof                  => "<eof>".to_string(),
        token::Whitespace           => " ".to_string(),
        token::Comment              => "/* */".to_string(),
        token::Shebang(s)           => format!("/* shebang: {}*/", s),
    }
}

/*
pub fn ty_to_string(ty: &ast::Ty) -> String {
    to_string(|s| s.print_type(ty))
}

pub fn path_to_string(p: &ast::Path) -> String {
    to_string(|s| s.print_path(p, false, 0))
}
*/

fn repeat(s: &str, n: usize) -> String { iter::repeat(s).take(n).collect() }