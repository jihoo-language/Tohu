//! Values, integer combinations of values, and the bidirectional linear
//! evaluator.
//!
//! A term denotes a ℤ-linear map between free abelian groups whose bases are
//! the values of its boundary types. Each value has a parity, the number of
//! `psi` it contains modulo two. Every primitive is a parity-preserving
//! signed permutation. Running a term backward applies its transpose.

use crate::error::{Error, Span};
use crate::syntax::{Combo, Lit, Prim, Term, TermKind};
use crate::types::{show_ty, LoopInfo, Ty};
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Value {
    Unit,
    Psi,
    Inl(Box<Value>),
    Inr(Box<Value>),
    Pair(Box<Value>, Box<Value>),
    Fold(Box<Value>),
}

impl Value {
    /// True for odd values: those with an odd number of `psi`.
    pub fn parity(&self) -> bool {
        let mut odd = false;
        let mut stack = vec![self];
        while let Some(v) = stack.pop() {
            match v {
                Value::Unit => {}
                Value::Psi => odd = !odd,
                Value::Inl(x) | Value::Inr(x) | Value::Fold(x) => stack.push(x),
                Value::Pair(x, y) => {
                    stack.push(x);
                    stack.push(y);
                }
            }
        }
        odd
    }
}

fn inl(v: Value) -> Value {
    Value::Inl(Box::new(v))
}
fn inr(v: Value) -> Value {
    Value::Inr(Box::new(v))
}
fn pair(a: Value, b: Value) -> Value {
    Value::Pair(Box::new(a), Box::new(b))
}

/// A finitely supported integer combination of values. Zero coefficients are
/// never stored, so the empty map is the zero vector.
pub type Vector = BTreeMap<Value, i128>;

pub const LOOP_LIMIT: usize = 1 << 16;
/// The largest support a vector may reach inside `iter`.
pub const SUPPORT_LIMIT: usize = 1 << 20;

/// The basis of a finite type, in a fixed order.
pub fn enumerate(t: &Ty) -> Option<Vec<Value>> {
    Some(match t {
        Ty::Zero => vec![],
        Ty::One => vec![Value::Unit],
        Ty::Psi => vec![Value::Psi],
        Ty::Sum(a, b) => {
            let mut v: Vec<Value> = enumerate(a)?.into_iter().map(inl).collect();
            v.extend(enumerate(b)?.into_iter().map(inr));
            if v.len() > LOOP_LIMIT {
                return None;
            }
            v
        }
        Ty::Prod(a, b) => {
            let (xs, ys) = (enumerate(a)?, enumerate(b)?);
            if xs.len().saturating_mul(ys.len()) > LOOP_LIMIT {
                return None;
            }
            let mut v = Vec::new();
            for x in &xs {
                for y in &ys {
                    v.push(pair(x.clone(), y.clone()));
                }
            }
            v
        }
        _ => return None,
    })
}

/// Shows a value at its type: numerals for `mu x. 1 + x`, brackets for lists.
pub fn show_value(v: &Value, t: &Ty) -> String {
    show_at(v, t).0
}

fn show_at(v: &Value, t: &Ty) -> (String, bool) {
    if t.is_nat_shaped() {
        let mut n = 0u64;
        let mut cur = v;
        while let Value::Fold(inner) = cur {
            match &**inner {
                Value::Inr(next) => {
                    n += 1;
                    cur = next;
                }
                _ => return (n.to_string(), true),
            }
        }
    }
    if let Some(elem) = t.list_element() {
        let mut items = Vec::new();
        let mut cur = v;
        while let Value::Fold(inner) = cur {
            match &**inner {
                Value::Inr(p) => match &**p {
                    Value::Pair(x, rest) => {
                        items.push(show_at(x, elem).0);
                        cur = rest;
                    }
                    _ => break,
                },
                _ => return (format!("[{}]", items.join(", ")), true),
            }
        }
    }
    match (v, t) {
        (Value::Unit, _) => ("()".into(), true),
        (Value::Psi, _) => ("psi".into(), true),
        (Value::Inl(x), Ty::Sum(a, _)) => (format!("inl {}", atom(show_at(x, a))), false),
        (Value::Inr(x), Ty::Sum(_, b)) => (format!("inr {}", atom(show_at(x, b))), false),
        (Value::Pair(x, y), Ty::Prod(a, b)) => (format!("({}, {})", show_at(x, a).0, show_at(y, b).0), true),
        (Value::Fold(x), Ty::Mu(_)) => (format!("fold {}", atom(show_at(x, &t.unroll().unwrap()))), false),
        _ => (format!("{:?}", v), true),
    }
}

fn atom((s, is_atom): (String, bool)) -> String {
    if is_atom {
        s
    } else {
        format!("({})", s)
    }
}

/// Shows a combination as `inl 4 - 2·inl 5 + inl 6`, or `tohu` when it is zero.
pub fn show_vector(v: &Vector, t: &Ty) -> String {
    if v.is_empty() {
        return "tohu".into();
    }
    let mut s = String::new();
    for (i, (x, c)) in v.iter().enumerate() {
        let body = show_value(x, t);
        let mag = c.unsigned_abs();
        let term = if mag == 1 { body } else { format!("{}\u{b7}{}", mag, body) };
        match (i, *c < 0) {
            (0, false) => s.push_str(&term),
            (0, true) => {
                s.push('-');
                s.push_str(&term);
            }
            (_, false) => {
                s.push_str(" + ");
                s.push_str(&term);
            }
            (_, true) => {
                s.push_str(" - ");
                s.push_str(&term);
            }
        }
    }
    s
}

pub fn combo_to_vector(c: &Combo, t: &Ty, aliases: &[(String, Ty)]) -> Result<Vector, Error> {
    let mut v = Vector::new();
    for (k, lit) in &c.terms {
        let x = convert(lit, t, aliases).map_err(|m| Error::at(c.span, m))?;
        add_to(&mut v, x, *k).map_err(|_| Error::at(c.span, "coefficient overflow"))?;
    }
    Ok(v)
}

fn convert(l: &Lit, t: &Ty, aliases: &[(String, Ty)]) -> Result<Value, String> {
    let bad = || format!("this value does not inhabit `{}`", show_ty(t, aliases));
    match (l, t) {
        (Lit::Unit, Ty::One) => Ok(Value::Unit),
        (Lit::Psi, Ty::Psi) => Ok(Value::Psi),
        (Lit::Num(n), _) if t.is_nat_shaped() => {
            let mut v = Value::Fold(Box::new(inl(Value::Unit)));
            for _ in 0..*n {
                v = Value::Fold(Box::new(inr(v)));
            }
            Ok(v)
        }
        (Lit::Num(_), _) => Err(format!("a numeral needs a type of the form `mu x. 1 + x`, not `{}`", show_ty(t, aliases))),
        (Lit::List(xs), _) => {
            let elem = t
                .list_element()
                .ok_or_else(|| format!("a list needs a type of the form `mu x. 1 + A * x`, not `{}`", show_ty(t, aliases)))?;
            let mut v = Value::Fold(Box::new(inl(Value::Unit)));
            for x in xs.iter().rev() {
                v = Value::Fold(Box::new(inr(pair(convert(x, elem, aliases)?, v))));
            }
            Ok(v)
        }
        (Lit::Inl(x), Ty::Sum(a, _)) => Ok(inl(convert(x, a, aliases)?)),
        (Lit::Inr(x), Ty::Sum(_, b)) => Ok(inr(convert(x, b, aliases)?)),
        (Lit::Pair(x, y), Ty::Prod(a, b)) => Ok(pair(convert(x, a, aliases)?, convert(y, b, aliases)?)),
        (Lit::Fold(x), Ty::Mu(_)) => Ok(Value::Fold(Box::new(convert(x, &t.unroll().unwrap(), aliases)?))),
        (Lit::Inl(_) | Lit::Inr(_), Ty::Mu(_)) => Err(format!("{}; a recursive value starts with `fold`", bad())),
        _ => Err(bad()),
    }
}

#[derive(Debug)]
pub enum Fail {
    Diverge(Span, usize),
    Explode(Span),
    Overflow(Span),
    Depth(Span),
}

impl Fail {
    pub fn message(&self) -> String {
        match self {
            Fail::Diverge(s, n) => format!(
                "divergence at {}: `iter` did not empty its feedback within the step limit; {} histories were still circulating",
                s, n
            ),
            Fail::Explode(s) => format!("explosion at {}: the histories circulating in `iter` exceeded {} basis vectors", s, SUPPORT_LIMIT),
            Fail::Overflow(s) => format!("overflow at {}: a coefficient left the 128-bit range", s),
            Fail::Depth(s) => format!("recursion at {} exceeded the depth limit", s),
        }
    }
}

pub struct Machine<'p> {
    pub defs: &'p HashMap<String, Term>,
    pub loops: &'p HashMap<usize, LoopInfo>,
    pub fuel: u64,
    pub depth: usize,
}

pub const FUEL: u64 = 2_000_000;
pub const DEPTH: usize = 100_000;

fn add_to(v: &mut Vector, x: Value, c: i128) -> Result<(), ()> {
    if c == 0 {
        return Ok(());
    }
    match v.get_mut(&x) {
        Some(old) => {
            let n = old.checked_add(c).ok_or(())?;
            if n == 0 {
                v.remove(&x);
            } else {
                *old = n;
            }
        }
        None => {
            v.insert(x, c);
        }
    }
    Ok(())
}

fn single(x: Value) -> Vector {
    let mut v = Vector::new();
    v.insert(x, 1);
    v
}

/// A primitive on a basis vector: the image and its sign.
fn prim(p: Prim, v: Value) -> (Value, i128) {
    use Prim::*;
    use Value::*;
    let r = match (p, v) {
        (SwapS, Inl(a)) => Inr(a),
        (SwapS, Inr(a)) => Inl(a),
        (SwapP, Pair(a, b)) => {
            // The Koszul sign: exchanging two odd values costs -1.
            let sign = if a.parity() && b.parity() { -1 } else { 1 };
            return (Pair(b, a), sign);
        }
        (AssoclS, Inl(a)) => inl(Inl(a)),
        (AssoclS, Inr(bc)) => match *bc {
            Inl(b) => inl(Inr(b)),
            Inr(c) => Inr(c),
            _ => unreachable!(),
        },
        (AssocrS, Inl(ab)) => match *ab {
            Inl(a) => Inl(a),
            Inr(b) => inr(Inl(b)),
            _ => unreachable!(),
        },
        (AssocrS, Inr(c)) => inr(Inr(c)),
        (UniteS, Inr(a)) => *a,
        (UnitiS, a) => inr(a),
        (AssoclP, Pair(a, bc)) => match *bc {
            Pair(b, c) => Pair(Box::new(Pair(a, b)), c),
            _ => unreachable!(),
        },
        (AssocrP, Pair(ab, c)) => match *ab {
            Pair(a, b) => Pair(a, Box::new(Pair(b, c))),
            _ => unreachable!(),
        },
        (UnitelP, Pair(_, a)) => *a,
        (UnitilP, a) => pair(Unit, a),
        (UniterP, Pair(a, _)) => *a,
        (UnitirP, a) => pair(a, Unit),
        (Distl, Pair(ab, c)) => match *ab {
            Inl(a) => inl(Pair(a, c)),
            Inr(b) => inr(Pair(b, c)),
            _ => unreachable!(),
        },
        (Factorl, Inl(ac)) => match *ac {
            Pair(a, c) => pair(Inl(a), *c),
            _ => unreachable!(),
        },
        (Factorl, Inr(bc)) => match *bc {
            Pair(b, c) => pair(Inr(b), *c),
            _ => unreachable!(),
        },
        (Cup, Unit) => pair(Psi, Psi),
        (Cap, Pair(_, _)) => Unit,
        (p, v) => unreachable!("ill-typed value {:?} for {:?}", v, p),
    };
    (r, 1)
}

impl<'p> Machine<'p> {
    /// Applies a term to a combination, by linearity.
    pub fn apply(&mut self, t: &Term, fwd: bool, v: &Vector) -> Result<Vector, Fail> {
        let mut out = Vector::new();
        for (x, c) in v {
            for (y, d) in self.eval(t, fwd, x.clone())? {
                let k = c.checked_mul(d).ok_or(Fail::Overflow(t.span))?;
                add_to(&mut out, y, k).map_err(|_| Fail::Overflow(t.span))?;
            }
        }
        Ok(out)
    }

    /// Applies a term to one basis vector.
    pub fn eval(&mut self, t: &Term, fwd: bool, v: Value) -> Result<Vector, Fail> {
        match &t.kind {
            TermKind::Id => Ok(single(v)),
            TermKind::Prim(p) => {
                let (x, s) = prim(if fwd { *p } else { p.adjoint() }, v);
                let mut out = Vector::new();
                out.insert(x, s);
                Ok(out)
            }
            TermKind::Fold(_, unfold) => Ok(single(if fwd != *unfold {
                Value::Fold(Box::new(v))
            } else {
                match v {
                    Value::Fold(x) => *x,
                    _ => unreachable!(),
                }
            })),
            TermKind::Ref(name) => {
                if self.depth >= DEPTH {
                    return Err(Fail::Depth(t.span));
                }
                self.depth += 1;
                let r = self.eval(&self.defs[name], fwd, v);
                self.depth -= 1;
                r
            }
            TermKind::Seq(f, g) => {
                let (first, second) = if fwd { (f, g) } else { (g, f) };
                let mid = self.eval(first, fwd, v)?;
                self.apply(second, fwd, &mid)
            }
            TermKind::Sum(f, g) => match v {
                Value::Inl(x) => Ok(self.eval(f, fwd, *x)?.into_iter().map(|(y, c)| (inl(y), c)).collect()),
                Value::Inr(x) => Ok(self.eval(g, fwd, *x)?.into_iter().map(|(y, c)| (inr(y), c)).collect()),
                _ => unreachable!(),
            },
            TermKind::Prod(f, g) => match v {
                Value::Pair(x, y) => {
                    // Both maps are even, so the Koszul rule adds no sign.
                    let xs = self.eval(f, fwd, *x)?;
                    let ys = self.eval(g, fwd, *y)?;
                    let mut out = Vector::new();
                    for (a, c) in &xs {
                        for (b, d) in &ys {
                            let k = c.checked_mul(*d).ok_or(Fail::Overflow(t.span))?;
                            out.insert(pair(a.clone(), b.clone()), k);
                        }
                    }
                    Ok(out)
                }
                _ => unreachable!(),
            },
            TermKind::Adj(f) => self.eval(f, !fwd, v),
            TermKind::Loop(_, f) => {
                // The supertrace over the feedback: every history that sends
                // back the value it received counts, an odd one with sign -1.
                let info = &self.loops[&t.id];
                let mut out = Vector::new();
                for (u, odd) in &info.basis {
                    for (k, c) in self.eval(f, fwd, pair(v.clone(), u.clone()))? {
                        if let Value::Pair(b, u2) = k {
                            if *u2 == *u {
                                let c = if *odd { -c } else { c };
                                add_to(&mut out, *b, c).map_err(|_| Fail::Overflow(t.span))?;
                            }
                        }
                    }
                }
                Ok(out)
            }
            TermKind::Iter(f) => {
                // The execution formula: feed the `U` part back until no
                // history is left circulating.
                let mut out = Vector::new();
                let mut state = self.eval(f, fwd, inl(v))?;
                loop {
                    let mut back = Vector::new();
                    for (k, c) in std::mem::take(&mut state) {
                        match k {
                            Value::Inl(b) => add_to(&mut out, *b, c).map_err(|_| Fail::Overflow(t.span))?,
                            u @ Value::Inr(_) => {
                                back.insert(u, c);
                            }
                            _ => unreachable!(),
                        }
                    }
                    if back.is_empty() {
                        return Ok(out);
                    }
                    if back.len() > SUPPORT_LIMIT {
                        return Err(Fail::Explode(t.span));
                    }
                    let cost = back.len() as u64;
                    if self.fuel < cost {
                        return Err(Fail::Diverge(t.span, back.len()));
                    }
                    self.fuel -= cost;
                    state = self.apply(f, fwd, &back)?;
                }
            }
        }
    }
}
