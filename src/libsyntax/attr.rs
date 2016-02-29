use ast;
use ast::{AttrId, Attribute, Attribute_, MetaItem, MetaItemKind};
use codemap::{Span, Spanned, spanned, dummy_spanned};
use codemap::BytePos;
use parse::lexer::comments::{doc_comment_style, strip_doc_comment_decoration};
use parse::token::InternedString;
use ptr::P;

use std::cell::Cell;

thread_local! { static NEXT_ATTR_ID: Cell<usize> = Cell::new(0) }

pub fn mk_attr_id() -> AttrId {
    let id = NEXT_ATTR_ID.with(|slot| {
        let r = slot.get();
        slot.set(r + 1);
        r
    });
    AttrId(id)
}

pub fn mk_sugared_doc_attr(id: AttrId, text: InternedString, lo: BytePos,
                           hi: BytePos)
                           -> Attribute {
    let style = doc_comment_style(&text);
    let lit = spanned(lo, hi, ast::LitKind::Str(text, ast::StrStyle::Cooked));
    let attr = Attribute_ {
        id: id,
        style: style,
        value: P(spanned(lo, hi, MetaItemKind::NameValue(InternedString::new("doc"), lit))),
        is_sugared_doc: true
    };
    spanned(lo, hi, attr)
}


/// A list of attributes, behind a optional box as
/// a space optimization.
pub type ThinAttributes = Option<Box<Vec<Attribute>>>;

pub trait ThinAttributesExt {
    fn map_thin_attrs<F>(self, f: F) -> Self
        where F: FnOnce(Vec<Attribute>) -> Vec<Attribute>;
    fn prepend(mut self, attrs: Self) -> Self;
    fn append(mut self, attrs: Self) -> Self;
    fn update<F>(&mut self, f: F)
        where Self: Sized,
              F: FnOnce(Self) -> Self;
    fn as_attr_slice(&self) -> &[Attribute];
    fn into_attr_vec(self) -> Vec<Attribute>;
}

impl ThinAttributesExt for ThinAttributes {
    fn map_thin_attrs<F>(self, f: F) -> Self
        where F: FnOnce(Vec<Attribute>) -> Vec<Attribute>
    {
        f(self.map(|b| *b).unwrap_or(Vec::new())).into_thin_attrs()
    }

    fn prepend(self, attrs: ThinAttributes) -> Self {
        attrs.map_thin_attrs(|mut attrs| {
            attrs.extend(self.into_attr_vec());
            attrs
        })
    }

    fn append(self, attrs: ThinAttributes) -> Self {
        self.map_thin_attrs(|mut self_| {
            self_.extend(attrs.into_attr_vec());
            self_
        })
    }

    fn update<F>(&mut self, f: F)
        where Self: Sized,
              F: FnOnce(ThinAttributes) -> ThinAttributes
    {
        let self_ = f(self.take());
        *self = self_;
    }

    fn as_attr_slice(&self) -> &[Attribute] {
        match *self {
            Some(ref b) => b,
            None => &[],
        }
    }

    fn into_attr_vec(self) -> Vec<Attribute> {
        match self {
            Some(b) => *b,
            None => Vec::new(),
        }
    }
}


pub trait AttributesExt {
    fn into_thin_attrs(self) -> ThinAttributes;
}

impl AttributesExt for Vec<Attribute> {
    fn into_thin_attrs(self) -> ThinAttributes {
        if self.len() == 0 {
            None
        } else {
            Some(Box::new(self))
        }
    }
}