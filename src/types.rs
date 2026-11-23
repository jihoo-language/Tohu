//! Types, unification and type inference for point-free terms.

use crate::error::{Error, Span};
use crate::syntax::{Prim, Term, TermKind};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Zero,
    One,
    /// The fermion: one odd basis vector, `psi`.
    Psi,
    Sum(Box<Ty>, Box<Ty>),
    Prod(Box<Ty>, Box<Ty>),
    /// `mu x. body`, with the bound variable as de Bruijn index 0.
    Mu(Box<Ty>),
    Rec(usize),
    Meta(usize),
}

fn sum(a: Ty, b: Ty) -> Ty {
    Ty::Sum(Box::new(a), Box::new(b))
}
fn prod(a: Ty, b: Ty) -> Ty {
    Ty::Prod(Box::new(a), Box::new(b))
}

impl Ty {
    /// `body[mu x. body / x]` for a closed `mu` type.
    pub fn unroll(&self) -> Option<Ty> {
        match self {
            Ty::Mu(body) => Some(subst(body, 0, self)),
            _ => None,
        }
    }

    pub fn has_meta(&self) -> bool {
        match self {
            Ty::Meta(_) => true,
            Ty::Sum(a, b) | Ty::Prod(a, b) => a.has_meta() || b.has_meta(),
            Ty::Mu(b) => b.has_meta(),
            _ => false,
        }
    }

    pub fn has_mu(&self) -> bool {
        match self {
            Ty::Mu(_) => true,
            Ty::Sum(a, b) | Ty::Prod(a, b) => a.has_mu() || b.has_mu(),
            _ => false,
        }
    }

    fn mentions_rec(&self) -> bool {
        match self {
            Ty::Rec(_) => true,
            Ty::Sum(a, b) | Ty::Prod(a, b) => a.mentions_rec() || b.mentions_rec(),
            Ty::Mu(b) => b.mentions_rec(),
            _ => false,
        }
    }

    /// `mu x. 1 + x`
    pub fn is_nat_shaped(&self) -> bool {
        matches!(self, Ty::Mu(b) if **b == sum(Ty::One, Ty::Rec(0)))
    }

    /// `mu x. 1 + A * x` with `A` closed: returns `A`.
    pub fn list_element(&self) -> Option<&Ty> {
        if let Ty::Mu(b) = self {
            if let Ty::Sum(l, r) = &**b {
                if let (Ty::One, Ty::Prod(a, x)) = (&**l, &**r) {
                    if **x == Ty::Rec(0) && !a.mentions_rec() {
                        return Some(a);
                    }
                }
            }
        }
        None
    }
}

fn subst(t: &Ty, depth: usize, by: &Ty) -> Ty {
    match t {
        Ty::Rec(i) if *i == depth => by.clone(),
        Ty::Rec(i) if *i > depth => Ty::Rec(i - 1),
        Ty::Sum(a, b) => sum(subst(a, depth, by), subst(b, depth, by)),
        Ty::Prod(a, b) => prod(subst(a, depth, by), subst(b, depth, by)),
        Ty::Mu(b) => Ty::Mu(Box::new(subst(b, depth + 1, by))),
        other => other.clone(),
    }
}

/// Prints a type, using declared aliases where they match exactly.
pub fn show_ty(t: &Ty, aliases: &[(String, Ty)]) -> String {
    show_ty_at(t, aliases, 0, &mut Vec::new())
}

fn show_ty_at(t: &Ty, aliases: &[(String, Ty)], prec: u8, names: &mut Vec<String>) -> String {
    if !matches!(t, Ty::Zero | Ty::One | Ty::Psi | Ty::Rec(_) | Ty::Meta(_)) {
        if let Some((n, _)) = aliases.iter().find(|(_, a)| a == t) {
            return n.clone();
        }
    }
    let wrap = |s: String, p: u8| if prec > p { format!("({})", s) } else { s };
    match t {
        Ty::Zero => "0".into(),
        Ty::One => "1".into(),
        Ty::Psi => "Psi".into(),
        Ty::Meta(i) => format!("?{}", i),
        Ty::Rec(i) => names.get(names.len().wrapping_sub(1 + i)).cloned().unwrap_or_else(|| format!("#{}", i)),
        Ty::Sum(a, b) => {
            let s = format!("{} + {}", show_ty_at(a, aliases, 2, names), show_ty_at(b, aliases, 2, names));
            wrap(s, 1)
        }
        Ty::Prod(a, b) => {
            let s = format!("{} * {}", show_ty_at(a, aliases, 3, names), show_ty_at(b, aliases, 3, names));
            wrap(s, 2)
        }
        Ty::Mu(b) => {
            let v = ["x", "y", "z", "w"].get(names.len()).map(|s| s.to_string()).unwrap_or(format!("x{}", names.len()));
            names.push(v.clone());
            let s = format!("mu {}. {}", v, show_ty_at(b, aliases, 0, names));
            names.pop();
            wrap(s, 0)
        }
    }
}

/// The feedback and boundary types of a `loop`, fixed after checking.
#[derive(Clone, Debug)]
pub struct LoopInfo {
    pub feedback: Ty,
    /// The basis of the feedback type, each vector with its parity.
    pub basis: Vec<(crate::eval::Value, bool)>,
}

pub struct Checker<'a> {
    defs: &'a HashMap<String, (Ty, Ty)>,
    aliases: &'a [(String, Ty)],
    metas: Vec<Option<Ty>>,
    /// `(unrolled, recursive)` pairs from unannotated `fold`/`unfold`.
    deferred: Vec<(Ty, Ty, Span)>,
    loops: Vec<(usize, Ty, Span)>,
}

fn hint(name: &str) -> Option<&'static str> {
    Some(match name {
        "neg" | "negate" | "minus" | "sign" | "flip" => "Tohu has no minus sign. The only source of -1 is a fermion: `loop[Psi] id` is minus the identity, and `swap*` of two odd values is minus their exchange",
        "zero" | "void" | "kill" | "annihilate" => "the zero map is not primitive. It is a loop whose bootstrap cancels, such as `loop[1 + Psi] id`, or one with no consistent history",
        "scale" | "times" | "scalar" => "Tohu has no scalars. `n` times the identity is `loop[U] id` for a feedback `U` of dimension `n`",
        "plus" | "sum" | "superpose" | "fork" => "there is no primitive superposition. A sum of histories is a loop with two consistent ones",
        "distr" | "factorr" => "only the left factor of a product can be inspected: Tohu has `distl` and `factorl`. Exchange the factors with `swap*` first, and mind the signs",
        "dup" | "copy" | "clone" | "diag" | "delta" | "contract" => "nothing in Tohu can be copied. A linear map cannot copy a superposition, and Tohu has no other kind of map",
        "drop" | "discard" | "fst" | "snd" | "erase" | "weaken" | "forget" | "proj" | "counit" => "nothing in Tohu can be forgotten. A value can cancel against its negative, but it cannot be thrown away",
        "transpose" | "dagger" | "adjoint" | "inv" | "inverse" => "write `~f` for the adjoint of `f`",
        "lambda" | "fun" | "let" | "fix" | "rec" | "case" | "match" => "Tohu has no variables and no binders. Write the term as a composite of combinators",
        _ => return None,
    })
}

impl<'a> Checker<'a> {
    pub fn new(defs: &'a HashMap<String, (Ty, Ty)>, aliases: &'a [(String, Ty)]) -> Self {
        Checker { defs, aliases, metas: Vec::new(), deferred: Vec::new(), loops: Vec::new() }
    }

    fn fresh(&mut self) -> Ty {
        self.metas.push(None);
        Ty::Meta(self.metas.len() - 1)
    }

    fn resolve(&self, t: &Ty) -> Ty {
        let mut t = t.clone();
        while let Ty::Meta(i) = t {
            match &self.metas[i] {
                Some(u) => t = u.clone(),
                None => break,
            }
        }
        t
    }

    pub fn zonk(&self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Sum(a, b) => sum(self.zonk(&a), self.zonk(&b)),
            Ty::Prod(a, b) => prod(self.zonk(&a), self.zonk(&b)),
            Ty::Mu(b) => Ty::Mu(Box::new(self.zonk(&b))),
            other => other,
        }
    }

    pub fn show(&self, t: &Ty) -> String {
        show_ty(&self.zonk(t), self.aliases)
    }

    fn occurs(&self, m: usize, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Meta(j) => j == m,
            Ty::Sum(a, b) | Ty::Prod(a, b) => self.occurs(m, &a) || self.occurs(m, &b),
            Ty::Mu(b) => self.occurs(m, &b),
            _ => false,
        }
    }

    fn unify_inner(&mut self, a: &Ty, b: &Ty) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            (Ty::Meta(i), Ty::Meta(j)) if i == j => true,
            (Ty::Meta(i), t) | (t, Ty::Meta(i)) => {
                if self.occurs(*i, t) {
                    return false;
                }
                self.metas[*i] = Some(t.clone());
                true
            }
            (Ty::Sum(a1, a2), Ty::Sum(b1, b2)) | (Ty::Prod(a1, a2), Ty::Prod(b1, b2)) => {
                self.unify_inner(a1, b1) && self.unify_inner(a2, b2)
            }
            (Ty::Mu(x), Ty::Mu(y)) => self.unify_inner(x, y),
            _ => a == b,
        }
    }

    pub fn unify(&mut self, a: &Ty, b: &Ty, span: Span, what: &str) -> Result<(), Error> {
        let (sa, sb) = (self.show(a), self.show(b));
        if self.unify_inner(a, b) {
            Ok(())
        } else {
            Err(Error::at(span, format!("{}: `{}` does not match `{}`", what, sa, sb)))
        }
    }

    fn prim(&mut self, p: Prim) -> (Ty, Ty) {
        use Prim::*;
        let (a, b, c) = (self.fresh(), self.fresh(), self.fresh());
        let forward = |p: Prim| -> (Ty, Ty) {
            match p {
                SwapS => (sum(a.clone(), b.clone()), sum(b.clone(), a.clone())),
                SwapP => (prod(a.clone(), b.clone()), prod(b.clone(), a.clone())),
                AssoclS => (
                    sum(a.clone(), sum(b.clone(), c.clone())),
                    sum(sum(a.clone(), b.clone()), c.clone()),
                ),
                UniteS => (sum(Ty::Zero, a.clone()), a.clone()),
                AssoclP => (
                    prod(a.clone(), prod(b.clone(), c.clone())),
                    prod(prod(a.clone(), b.clone()), c.clone()),
                ),
                UnitelP => (prod(Ty::One, a.clone()), a.clone()),
                UniterP => (prod(a.clone(), Ty::One), a.clone()),
                Distl => (
                    prod(sum(a.clone(), b.clone()), c.clone()),
                    sum(prod(a.clone(), c.clone()), prod(b.clone(), c.clone())),
                ),
                Annl => (prod(Ty::Zero, a.clone()), Ty::Zero),
                Annr => (prod(a.clone(), Ty::Zero), Ty::Zero),
                Cup => (Ty::One, prod(Ty::Psi, Ty::Psi)),
                _ => unreachable!(),
            }
        };
        match p {
            SwapS | SwapP | AssoclS | UniteS | AssoclP | UnitelP | UniterP | Distl | Annl | Annr | Cup => forward(p),
            _ => {
                let (i, o) = forward(p.adjoint());
                (o, i)
            }
        }
    }

    pub fn infer(&mut self, t: &Term) -> Result<(Ty, Ty), Error> {
        match &t.kind {
            TermKind::Id => {
                let a = self.fresh();
                Ok((a.clone(), a))
            }
            TermKind::Prim(p) => Ok(self.prim(*p)),
            TermKind::Fold(ann, unfold) => {
                let (unrolled, rec) = match ann {
                    Some(ty) => match ty.unroll() {
                        Some(u) => (u, ty.clone()),
                        None => {
                            return Err(Error::at(
                                t.span,
                                format!("`{}` is not a recursive type", show_ty(ty, self.aliases)),
                            ))
                        }
                    },
                    None => {
                        let (u, m) = (self.fresh(), self.fresh());
                        self.deferred.push((u.clone(), m.clone(), t.span));
                        (u, m)
                    }
                };
                Ok(if *unfold { (rec, unrolled) } else { (unrolled, rec) })
            }
            TermKind::Ref(name) => match self.defs.get(name) {
                Some(sig) => Ok(sig.clone()),
                None => Err(Error::at(
                    t.span,
                    match hint(name) {
                        Some(h) => format!("`{}` does not exist: {}", name, h),
                        None => format!("unknown term `{}`", name),
                    },
                )),
            },
            TermKind::Seq(f, g) => {
                let (a, b) = self.infer(f)?;
                let (c, d) = self.infer(g)?;
                self.unify(&b, &c, t.span, "the two sides of `;` do not meet")?;
                Ok((a, d))
            }
            TermKind::Sum(f, g) | TermKind::Prod(f, g) => {
                let (a, b) = self.infer(f)?;
                let (c, d) = self.infer(g)?;
                Ok(if matches!(t.kind, TermKind::Sum(..)) { (sum(a, c), sum(b, d)) } else { (prod(a, c), prod(b, d)) })
            }
            TermKind::Adj(f) => {
                let (a, b) = self.infer(f)?;
                Ok((b, a))
            }
            TermKind::Loop(ann, f) => {
                let (i, o) = self.infer(f)?;
                let (a, b) = (self.fresh(), self.fresh());
                let u = match ann {
                    Some(t) => t.clone(),
                    None => self.fresh(),
                };
                self.unify(&i, &prod(a.clone(), u.clone()), t.span, "the body of `loop` must take a product `A * U`")?;
                self.unify(&o, &prod(b.clone(), u.clone()), t.span, "the body of `loop` must return its feedback `B * U` on the right")?;
                self.loops.push((t.id, u, t.span));
                Ok((a, b))
            }
            TermKind::Iter(f) => {
                let (i, o) = self.infer(f)?;
                let (a, b, u) = (self.fresh(), self.fresh(), self.fresh());
                self.unify(&i, &sum(a.clone(), u.clone()), t.span, "the body of `iter` must take a sum `A + U`")?;
                self.unify(&o, &sum(b.clone(), u), t.span, "the body of `iter` must return `B + U`")?;
                Ok((a, b))
            }
        }
    }

    /// Resolves deferred `fold`/`unfold` constraints and the feedback types of
    /// loops. Call after the boundary types are known.
    pub fn finish(&mut self, loops: &mut HashMap<usize, LoopInfo>) -> Result<(), Error> {
        loop {
            let mut progress = false;
            let pending = std::mem::take(&mut self.deferred);
            for (u, m, span) in pending {
                match self.zonk(&m) {
                    rec @ Ty::Mu(_) if !rec.has_meta() => {
                        let unrolled = rec.unroll().unwrap();
                        self.unify(&u, &unrolled, span, "`fold` and `unfold` relate a recursive type to its unrolling")?;
                        progress = true;
                    }
                    Ty::Meta(_) => self.deferred.push((u, m, span)),
                    other => {
                        return Err(Error::at(
                            span,
                            format!("`fold`/`unfold` needs a recursive type here, not `{}`", show_ty(&other, self.aliases)),
                        ))
                    }
                }
            }
            if self.deferred.is_empty() {
                break;
            }
            if !progress {
                let span = self.deferred[0].2;
                return Err(Error::at(span, "cannot tell which recursive type this `fold`/`unfold` is about; write `fold[T]`"));
            }
        }
        for (id, u, span) in std::mem::take(&mut self.loops) {
            let u = self.zonk(&u);
            if u.has_meta() {
                return Err(Error::at(
                    span,
                    "the feedback type of this loop is not determined, and its dimension is the answer; write `loop[U]`",
                ));
            }
            if u.has_mu() {
                return Err(Error::at(
                    span,
                    format!("a loop takes a trace, and a trace needs a finite type: `{}` is recursive", show_ty(&u, self.aliases)),
                ));
            }
            let basis = crate::eval::enumerate(&u).ok_or_else(|| {
                Error::at(span, format!("the feedback type `{}` has more than {} basis vectors", show_ty(&u, self.aliases), crate::eval::LOOP_LIMIT))
            })?;
            let basis = basis.into_iter().map(|v| {
                let p = v.parity();
                (v, p)
            }).collect();
            loops.insert(id, LoopInfo { feedback: u, basis });
        }
        Ok(())
    }
}
