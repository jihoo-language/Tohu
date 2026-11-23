//! Lexer and parser for Tohu source text.

use crate::error::{Error, Span};
use crate::types::Ty;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Num(u64),
    Sym(&'static str),
    Eof,
}

#[derive(Clone, Debug)]
struct Token {
    tok: Tok,
    span: Span,
    start: usize,
    end: usize,
}

/// Primitive names that end in `+` or `*`. The lexer glues the suffix on only
/// for these, so `id+id` still reads as a sum of two identities.
const SUFFIXED: &[&str] = &[
    "swap+", "assocl+", "assocr+", "unite+", "uniti+", "assocl*", "assocr*", "unitel*", "unitil*",
    "uniter*", "unitir*", "swap*",
];

pub const KEYWORDS: &[&str] = &["type", "def", "run", "expect", "refute", "table", "homology"];

const SYMS: [&str; 17] = ["<->", "=>", "(", ")", "[", "]", ";", ",", ":", "=", "+", "*", "~", ".", "-", "\u{b7}", "|"];

fn lex(src: &str) -> Result<Vec<Token>, Error> {
    let bytes = src.as_bytes();
    let mut out = Vec::new();
    let (mut i, mut line, mut col) = (0usize, 1usize, 1usize);
    while i < bytes.len() {
        let c = src[i..].chars().next().unwrap();
        if c == '\n' {
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if c.is_whitespace() {
            i += c.len_utf8();
            col += 1;
            continue;
        }
        if src[i..].starts_with("//") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let span = Span { line, col };
        let start = i;
        if c.is_ascii_alphabetic() || c == '_' {
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'') {
                i += 1;
            }
            let mut word = src[start..i].to_string();
            if i < bytes.len() && (bytes[i] == b'+' || bytes[i] == b'*') {
                let glued = format!("{}{}", word, bytes[i] as char);
                if SUFFIXED.contains(&glued.as_str()) {
                    word = glued;
                    i += 1;
                }
            }
            col += i - start;
            out.push(Token { tok: Tok::Ident(word), span, start, end: i });
            continue;
        }
        if c.is_ascii_digit() {
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let n = src[start..i]
                .parse::<u64>()
                .map_err(|_| Error::at(span, "numeral is too large"))?;
            col += i - start;
            out.push(Token { tok: Tok::Num(n), span, start, end: i });
            continue;
        }
        match SYMS.iter().find(|s| src[i..].starts_with(**s)) {
            Some(s) => {
                i += s.len();
                col += s.chars().count();
                out.push(Token { tok: Tok::Sym(s), span, start, end: i });
            }
            None => return Err(Error::at(span, format!("unexpected character `{}`", c))),
        }
    }
    out.push(Token { tok: Tok::Eof, span: Span { line, col }, start: i, end: i });
    Ok(out)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Prim {
    SwapS,
    AssoclS,
    AssocrS,
    UniteS,
    UnitiS,
    SwapP,
    AssoclP,
    AssocrP,
    UnitelP,
    UnitilP,
    UniterP,
    UnitirP,
    Distl,
    Factorl,
    Annl,
    Annil,
    Annr,
    Annir,
    Cup,
    Cap,
}

impl Prim {
    pub fn from_name(s: &str) -> Option<Prim> {
        Some(match s {
            "swap+" => Prim::SwapS,
            "assocl+" => Prim::AssoclS,
            "assocr+" => Prim::AssocrS,
            "unite+" => Prim::UniteS,
            "uniti+" => Prim::UnitiS,
            "swap*" => Prim::SwapP,
            "assocl*" => Prim::AssoclP,
            "assocr*" => Prim::AssocrP,
            "unitel*" => Prim::UnitelP,
            "unitil*" => Prim::UnitilP,
            "uniter*" => Prim::UniterP,
            "unitir*" => Prim::UnitirP,
            "distl" => Prim::Distl,
            "factorl" => Prim::Factorl,
            "annl" => Prim::Annl,
            "annil" => Prim::Annil,
            "annr" => Prim::Annr,
            "annir" => Prim::Annir,
            "cup" => Prim::Cup,
            "cap" => Prim::Cap,
            _ => return None,
        })
    }

    /// Every primitive is a signed permutation, so its adjoint is its inverse.
    pub fn adjoint(self) -> Prim {
        use Prim::*;
        match self {
            SwapS => SwapS,
            SwapP => SwapP,
            AssoclS => AssocrS,
            AssocrS => AssoclS,
            UniteS => UnitiS,
            UnitiS => UniteS,
            AssoclP => AssocrP,
            AssocrP => AssoclP,
            UnitelP => UnitilP,
            UnitilP => UnitelP,
            UniterP => UnitirP,
            UnitirP => UniterP,
            Distl => Factorl,
            Factorl => Distl,
            Annl => Annil,
            Annil => Annl,
            Annr => Annir,
            Annir => Annr,
            Cup => Cap,
            Cap => Cup,
        }
    }
}

#[derive(Clone, Debug)]
pub enum TermKind {
    Id,
    Prim(Prim),
    /// `fold` (false) or `unfold` (true), with an optional recursive type.
    Fold(Option<Ty>, bool),
    Ref(String),
    Seq(Box<Term>, Box<Term>),
    Sum(Box<Term>, Box<Term>),
    Prod(Box<Term>, Box<Term>),
    Adj(Box<Term>),
    /// `loop[U] f`, with an optional feedback type.
    Loop(Option<Ty>, Box<Term>),
    Iter(Box<Term>),
}

#[derive(Clone, Debug)]
pub struct Term {
    pub id: usize,
    pub span: Span,
    pub kind: TermKind,
}

#[derive(Clone, Debug)]
pub enum Lit {
    Unit,
    Psi,
    Num(u64),
    List(Vec<Lit>),
    Inl(Box<Lit>),
    Inr(Box<Lit>),
    Pair(Box<Lit>, Box<Lit>),
    Fold(Box<Lit>),
}

/// An integer combination of values. The empty combination is `tohu`.
#[derive(Clone, Debug)]
pub struct Combo {
    pub span: Span,
    pub terms: Vec<(i128, Lit)>,
}

#[derive(Clone, Debug)]
pub enum Item {
    Def { name: String, span: Span, input: Ty, output: Ty, body: Term },
    Run { term: Term, text: String, input: Combo },
    Expect { term: Term, text: String, input: Combo, output: Combo },
    Refute { term: Term, text: String, input: Combo },
    Table { term: Term, text: String },
    Homology { span: Span, terms: Vec<(Term, String)> },
}

pub struct Program {
    pub items: Vec<Item>,
    /// Type aliases in declaration order, used to print types and values.
    pub aliases: Vec<(String, Ty)>,
}

struct Parser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    pos: usize,
    aliases: HashMap<String, Ty>,
    alias_order: Vec<(String, Ty)>,
    bound: Vec<String>,
    next_id: usize,
}

pub fn parse(src: &str) -> Result<Program, Error> {
    let mut p = Parser {
        src,
        toks: lex(src)?,
        pos: 0,
        aliases: HashMap::new(),
        alias_order: Vec::new(),
        bound: Vec::new(),
        next_id: 0,
    };
    let mut items = Vec::new();
    while p.peek() != &Tok::Eof {
        if let Some(item) = p.statement()? {
            items.push(item);
        }
    }
    Ok(Program { items, aliases: p.alias_order })
}

const RESERVED: &[&str] = &["id", "fold", "unfold", "loop", "iter", "mu", "inl", "inr", "psi", "Psi", "tohu"];

impl<'s> Parser<'s> {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn peek_at(&self, k: usize) -> &Tok {
        &self.toks[(self.pos + k).min(self.toks.len() - 1)].tok
    }
    fn span(&self) -> Span {
        self.toks[self.pos].span
    }
    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn is_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Tok::Sym(x) if *x == s)
    }
    fn is_word(&self, w: &str) -> bool {
        matches!(self.peek(), Tok::Ident(x) if x == w)
    }
    fn expect_sym(&mut self, s: &str) -> Result<(), Error> {
        if self.is_sym(s) {
            self.bump();
            Ok(())
        } else {
            Err(Error::at(self.span(), format!("expected `{}`, found {}", s, self.describe())))
        }
    }
    fn describe(&self) -> String {
        match self.peek() {
            Tok::Ident(w) => format!("`{}`", w),
            Tok::Num(n) => format!("`{}`", n),
            Tok::Sym(s) => format!("`{}`", s),
            Tok::Eof => "end of input".into(),
        }
    }
    fn ident(&mut self) -> Result<String, Error> {
        match self.peek().clone() {
            Tok::Ident(w) => {
                self.bump();
                Ok(w)
            }
            _ => Err(Error::at(self.span(), format!("expected a name, found {}", self.describe()))),
        }
    }
    fn fresh(&mut self) -> usize {
        self.next_id += 1;
        self.next_id
    }

    fn statement(&mut self) -> Result<Option<Item>, Error> {
        let span = self.span();
        let kw = self.ident()?;
        let item = match kw.as_str() {
            "type" => {
                let name = self.ident()?;
                if KEYWORDS.contains(&name.as_str()) || Prim::from_name(&name).is_some() || RESERVED.contains(&name.as_str()) {
                    return Err(Error::at(span, format!("`{}` cannot name a type", name)));
                }
                if self.aliases.contains_key(&name) {
                    return Err(Error::at(span, format!("type `{}` is already declared", name)));
                }
                self.expect_sym("=")?;
                let ty = self.ty()?;
                self.aliases.insert(name.clone(), ty.clone());
                self.alias_order.push((name, ty));
                None
            }
            "def" => {
                let name = self.ident()?;
                if KEYWORDS.contains(&name.as_str()) || Prim::from_name(&name).is_some() || RESERVED.contains(&name.as_str()) {
                    return Err(Error::at(span, format!("`{}` is reserved", name)));
                }
                self.expect_sym(":")?;
                let input = self.ty()?;
                self.expect_sym("<->")?;
                let output = self.ty()?;
                self.expect_sym("=")?;
                let body = self.term()?;
                Some(Item::Def { name, span, input, output, body })
            }
            "run" | "refute" => {
                let (term, text) = self.term_with_text()?;
                let input = self.combo()?;
                Some(if kw == "run" {
                    Item::Run { term, text, input }
                } else {
                    Item::Refute { term, text, input }
                })
            }
            "expect" => {
                let (term, text) = self.term_with_text()?;
                let input = self.combo()?;
                self.expect_sym("=>")?;
                let output = self.combo()?;
                Some(Item::Expect { term, text, input, output })
            }
            "table" => {
                let (term, text) = self.term_with_text()?;
                Some(Item::Table { term, text })
            }
            "homology" => {
                let mut terms = vec![self.term_with_text()?];
                while self.is_sym(",") {
                    self.bump();
                    terms.push(self.term_with_text()?);
                }
                Some(Item::Homology { span, terms })
            }
            _ => {
                return Err(Error::at(
                    span,
                    format!(
                        "expected `type`, `def`, `run`, `expect`, `refute`, `table` or `homology`, found `{}`",
                        kw
                    ),
                ))
            }
        };
        self.expect_sym(";")?;
        Ok(item)
    }

    // ---------- types ----------

    fn ty(&mut self) -> Result<Ty, Error> {
        if self.is_word("mu") {
            self.bump();
            let var = self.ident()?;
            self.expect_sym(".")?;
            self.bound.push(var);
            let body = self.ty();
            self.bound.pop();
            return Ok(Ty::Mu(Box::new(body?)));
        }
        let span = self.span();
        let lhs = self.ty_prod()?;
        if !self.is_sym("+") {
            return Ok(lhs);
        }
        self.bump();
        let rhs = if self.is_word("mu") { self.ty()? } else { self.ty_prod()? };
        if self.is_sym("+") {
            return Err(Error::at(
                span,
                "a chain of `+` has no association in Tohu; parenthesize it, because `A + (B + C)` and `(A + B) + C` are different types",
            ));
        }
        Ok(Ty::Sum(Box::new(lhs), Box::new(rhs)))
    }

    fn ty_prod(&mut self) -> Result<Ty, Error> {
        let span = self.span();
        let lhs = self.ty_atom()?;
        if !self.is_sym("*") {
            return Ok(lhs);
        }
        self.bump();
        let rhs = self.ty_atom()?;
        if self.is_sym("*") {
            return Err(Error::at(
                span,
                "a chain of `*` has no association in Tohu; parenthesize it, because `A * (B * C)` and `(A * B) * C` are different types",
            ));
        }
        Ok(Ty::Prod(Box::new(lhs), Box::new(rhs)))
    }

    fn ty_atom(&mut self) -> Result<Ty, Error> {
        let span = self.span();
        match self.peek().clone() {
            Tok::Num(0) => {
                self.bump();
                Ok(Ty::Zero)
            }
            Tok::Num(1) => {
                self.bump();
                Ok(Ty::One)
            }
            Tok::Num(n) => Err(Error::at(
                span,
                format!("`{}` is not a type; only `0`, `1` and `Psi` are atomic. Build {} from sums", n, n),
            )),
            Tok::Sym("-") => Err(Error::at(
                span,
                "`-1` is not a type. The type whose dimension is -1 is the fermion `Psi`",
            )),
            Tok::Sym("(") => {
                self.bump();
                let t = self.ty()?;
                self.expect_sym(")")?;
                Ok(t)
            }
            Tok::Ident(w) if w == "mu" => {
                Err(Error::at(span, "parenthesize a `mu` type that is not the last operand"))
            }
            Tok::Ident(w) => {
                self.bump();
                if let Some(k) = self.bound.iter().rev().position(|b| *b == w) {
                    return Ok(Ty::Rec(k));
                }
                if w == "Psi" {
                    return Ok(Ty::Psi);
                }
                self.aliases
                    .get(&w)
                    .cloned()
                    .ok_or_else(|| Error::at(span, format!("unknown type `{}`", w)))
            }
            _ => Err(Error::at(span, format!("expected a type, found {}", self.describe()))),
        }
    }

    // ---------- terms ----------

    fn term_with_text(&mut self) -> Result<(Term, String), Error> {
        let start = self.toks[self.pos].start;
        let term = self.term()?;
        let end = self.toks[self.pos - 1].end;
        Ok((term, self.src[start..end].to_string()))
    }

    /// Statement ends are also written `;`. A `;` that is followed by a
    /// keyword or by the end of the input closes the statement instead of
    /// composing.
    fn ends_statement(&self) -> bool {
        match self.peek_at(1) {
            Tok::Eof => true,
            Tok::Ident(w) => KEYWORDS.contains(&w.as_str()),
            _ => false,
        }
    }

    fn term(&mut self) -> Result<Term, Error> {
        let mut lhs = self.term_sum()?;
        while self.is_sym(";") && !self.ends_statement() {
            let span = self.span();
            self.bump();
            let rhs = self.term_sum()?;
            let id = self.fresh();
            lhs = Term { id, span, kind: TermKind::Seq(Box::new(lhs), Box::new(rhs)) };
        }
        Ok(lhs)
    }

    fn term_sum(&mut self) -> Result<Term, Error> {
        let lhs = self.term_prod()?;
        if !self.is_sym("+") {
            return Ok(lhs);
        }
        let span = self.span();
        self.bump();
        let rhs = self.term_prod()?;
        if self.is_sym("+") {
            return Err(Error::at(span, "a chain of `+` has no association in Tohu; parenthesize it"));
        }
        let id = self.fresh();
        Ok(Term { id, span, kind: TermKind::Sum(Box::new(lhs), Box::new(rhs)) })
    }

    fn term_prod(&mut self) -> Result<Term, Error> {
        let lhs = self.term_unary()?;
        if !self.is_sym("*") {
            return Ok(lhs);
        }
        let span = self.span();
        self.bump();
        let rhs = self.term_unary()?;
        if self.is_sym("*") {
            return Err(Error::at(span, "a chain of `*` has no association in Tohu; parenthesize it"));
        }
        let id = self.fresh();
        Ok(Term { id, span, kind: TermKind::Prod(Box::new(lhs), Box::new(rhs)) })
    }

    fn term_unary(&mut self) -> Result<Term, Error> {
        let span = self.span();
        let kind = if self.is_sym("~") {
            self.bump();
            TermKind::Adj(Box::new(self.term_unary()?))
        } else if self.is_sym("-") {
            return Err(Error::at(
                span,
                "Tohu has no minus sign. The only source of -1 is a fermion: `loop[Psi] id` is minus the identity",
            ));
        } else if self.is_word("loop") {
            self.bump();
            let ann = if self.is_sym("[") {
                self.bump();
                let t = self.ty()?;
                self.expect_sym("]")?;
                Some(t)
            } else {
                None
            };
            TermKind::Loop(ann, Box::new(self.term_unary()?))
        } else if self.is_word("iter") {
            self.bump();
            TermKind::Iter(Box::new(self.term_unary()?))
        } else {
            return self.term_atom();
        };
        let id = self.fresh();
        Ok(Term { id, span, kind })
    }

    fn term_atom(&mut self) -> Result<Term, Error> {
        let span = self.span();
        if self.is_sym("(") {
            self.bump();
            let t = self.term()?;
            self.expect_sym(")")?;
            return Ok(t);
        }
        let name = match self.peek().clone() {
            Tok::Ident(w) if !KEYWORDS.contains(&w.as_str()) => w,
            Tok::Num(n) => {
                return Err(Error::at(
                    span,
                    format!(
                        "`{}` is not a term. Tohu has no scalars; {} times the identity is a loop whose feedback has dimension {}",
                        n, n, n
                    ),
                ))
            }
            _ => return Err(Error::at(span, format!("expected a term, found {}", self.describe()))),
        };
        self.bump();
        let kind = match name.as_str() {
            "id" => TermKind::Id,
            "fold" | "unfold" => {
                let ann = if self.is_sym("[") {
                    self.bump();
                    let t = self.ty()?;
                    self.expect_sym("]")?;
                    Some(t)
                } else {
                    None
                };
                TermKind::Fold(ann, name == "unfold")
            }
            _ => match Prim::from_name(&name) {
                Some(p) => TermKind::Prim(p),
                None => TermKind::Ref(name),
            },
        };
        let id = self.fresh();
        Ok(Term { id, span, kind })
    }

    // ---------- value literals ----------

    /// `tohu`, or a signed sum of terms `[n·] value`.
    fn combo(&mut self) -> Result<Combo, Error> {
        let span = self.span();
        if self.is_word("tohu") {
            self.bump();
            return Ok(Combo { span, terms: Vec::new() });
        }
        let mut terms = Vec::new();
        let mut sign: i128 = 1;
        if self.is_sym("-") {
            self.bump();
            sign = -1;
        }
        loop {
            let mut coeff: i128 = 1;
            if let Tok::Num(n) = self.peek().clone() {
                if matches!(self.peek_at(1), Tok::Sym("\u{b7}") | Tok::Sym("*")) {
                    self.bump();
                    self.bump();
                    coeff = n as i128;
                }
            }
            terms.push((sign * coeff, self.lit()?));
            if self.is_sym("+") {
                sign = 1;
            } else if self.is_sym("-") {
                sign = -1;
            } else {
                break;
            }
            self.bump();
        }
        Ok(Combo { span, terms })
    }

    fn lit(&mut self) -> Result<Lit, Error> {
        let span = self.span();
        let node = match self.peek().clone() {
            Tok::Num(n) => {
                self.bump();
                Lit::Num(n)
            }
            Tok::Sym("(") => {
                self.bump();
                if self.is_sym(")") {
                    self.bump();
                    Lit::Unit
                } else {
                    let a = self.lit()?;
                    if self.is_sym(",") {
                        self.bump();
                        let b = self.lit()?;
                        if self.is_sym(",") {
                            return Err(Error::at(self.span(), "tuples have no association in Tohu; nest the pairs explicitly"));
                        }
                        self.expect_sym(")")?;
                        Lit::Pair(Box::new(a), Box::new(b))
                    } else if self.is_sym("+") || self.is_sym("-") {
                        return Err(Error::at(
                            self.span(),
                            "a combination cannot appear inside a value; values are basis vectors, and only a whole input or output is a combination",
                        ));
                    } else {
                        self.expect_sym(")")?;
                        a
                    }
                }
            }
            Tok::Sym("[") => {
                self.bump();
                let mut xs = Vec::new();
                if !self.is_sym("]") {
                    loop {
                        xs.push(self.lit()?);
                        if self.is_sym(",") {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                self.expect_sym("]")?;
                Lit::List(xs)
            }
            Tok::Ident(w) if w == "psi" => {
                self.bump();
                Lit::Psi
            }
            Tok::Ident(w) if w == "inl" || w == "inr" || w == "fold" => {
                self.bump();
                let x = Box::new(self.lit()?);
                match w.as_str() {
                    "inl" => Lit::Inl(x),
                    "inr" => Lit::Inr(x),
                    _ => Lit::Fold(x),
                }
            }
            _ => return Err(Error::at(span, format!("expected a value, found {}", self.describe()))),
        };
        Ok(node)
    }
}
