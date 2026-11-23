//! Tohu: a point-free, super-linear language over the integers whose time
//! loops are supertraces and whose histories interfere.

pub mod error;
pub mod eval;
pub mod linalg;
pub mod syntax;
pub mod types;

use error::{Error, Span};
use eval::{combo_to_vector, enumerate, show_value, show_vector, Fail, Machine, Value, Vector, FUEL};
use linalg::{show_super, Matrix};
use std::collections::{BTreeMap, HashMap};
use syntax::{Item, Term};
use types::{show_ty, Checker, LoopInfo, Ty};

struct Session {
    defs: HashMap<String, Term>,
    sigs: HashMap<String, (Ty, Ty)>,
    loops: HashMap<usize, LoopInfo>,
    aliases: Vec<(String, Ty)>,
}

impl Session {
    /// Checks a statement's term and returns its closed boundary types.
    fn check(&mut self, term: &Term) -> Result<(Ty, Ty), Error> {
        let mut c = Checker::new(&self.sigs, &self.aliases);
        let (i, o) = c.infer(term)?;
        let (zi, zo) = (c.zonk(&i), c.zonk(&o));
        if zi.has_meta() || zo.has_meta() {
            return Err(Error::at(
                term.span,
                format!("the type `{} <-> {}` of this term is not determined; name it with `def`", c.show(&i), c.show(&o)),
            ));
        }
        c.finish(&mut self.loops)?;
        Ok((zi, zo))
    }

    fn machine(&self) -> Machine<'_> {
        Machine { defs: &self.defs, loops: &self.loops, fuel: FUEL, depth: 0 }
    }

    fn run(&self, term: &Term, input: &Vector) -> Result<Vector, Fail> {
        self.machine().apply(term, true, input)
    }

    fn ty(&self, t: &Ty) -> String {
        show_ty(t, &self.aliases)
    }

    /// The matrix of a term between finite types, columns indexed by the
    /// input basis and rows by the output basis.
    fn matrix(&self, term: &Term, i: &Ty, o: &Ty, what: &str) -> Result<(Vec<Value>, Vec<Value>, Matrix), Error> {
        let finite = |t: &Ty| {
            enumerate(t).ok_or_else(|| {
                Error::at(
                    term.span,
                    format!("{} needs finite types with at most {} basis vectors, and `{}` is not one", what, eval::LOOP_LIMIT, self.ty(t)),
                )
            })
        };
        let (cols, rows) = (finite(i)?, finite(o)?);
        let index: BTreeMap<&Value, usize> = rows.iter().enumerate().map(|(k, v)| (v, k)).collect();
        let mut m = Matrix::zero(rows.len(), cols.len());
        let mut machine = self.machine();
        for (j, x) in cols.iter().enumerate() {
            let image = machine.eval(term, true, x.clone()).map_err(|f| Error::at(term.span, f.message()))?;
            for (y, c) in image {
                m.data[index[&y]][j] = c;
            }
        }
        Ok((cols, rows, m))
    }

    fn homology(&mut self, span: Span, terms: &[(Term, String)]) -> Result<String, Error> {
        let overflow = || Error::at(span, "overflow while reducing the complex");
        let parities = |basis: &[Value]| -> (Vec<usize>, Vec<usize>) {
            let (mut e, mut o) = (Vec::new(), Vec::new());
            for (k, v) in basis.iter().enumerate() {
                if v.parity() { o.push(k) } else { e.push(k) }
            }
            (e, o)
        };
        let mut sigs = Vec::new();
        for (t, _) in terms {
            sigs.push(self.check(t)?);
        }
        // One term `d : C <-> C * Psi` is an odd differential on `C`.
        if let [(term, text)] = terms {
            if let (i, Ty::Prod(c, p)) = &sigs[0] {
                if **p == Ty::Psi && **c == *i {
                    let (basis, out, m) = self.matrix(term, i, &sigs[0].1, "homology")?;
                    let index: BTreeMap<&Value, usize> = basis.iter().enumerate().map(|(k, v)| (v, k)).collect();
                    let mut d = Matrix::zero(basis.len(), basis.len());
                    for (r, y) in out.iter().enumerate() {
                        if let Value::Pair(b, _) = y {
                            d.data[index[&**b]] = m.data[r].clone();
                        }
                    }
                    let dd = d.mul(&d).ok_or_else(overflow)?;
                    if !dd.is_zero() {
                        let j = (0..basis.len()).find(|&j| (0..basis.len()).any(|r| dd.data[r][j] != 0)).unwrap();
                        return Err(Error::at(
                            term.span,
                            format!(
                                "`{}` is not a differential: applying it twice to {} does not give tohu",
                                text,
                                show_value(&basis[j], i)
                            ),
                        ));
                    }
                    let (e, o) = parities(&basis);
                    let even = linalg::homology(e.len(), &d.select(&e, &o), &d.select(&o, &e)).ok_or_else(overflow)?;
                    let odd = linalg::homology(o.len(), &d.select(&o, &e), &d.select(&e, &o)).ok_or_else(overflow)?;
                    return Ok(format!("H = {}", show_super(&even, &odd)));
                }
            }
        }
        // Otherwise the terms form a sequence C0 -> C1 -> ... -> Ck.
        for k in 1..terms.len() {
            if sigs[k - 1].1 != sigs[k].0 {
                return Err(Error::at(
                    terms[k].0.span,
                    format!(
                        "this complex does not compose: `{}` ends in `{}` but `{}` starts from `{}`",
                        terms[k - 1].1,
                        self.ty(&sigs[k - 1].1),
                        terms[k].1,
                        self.ty(&sigs[k].0)
                    ),
                ));
            }
        }
        let mut objects = vec![sigs[0].0.clone()];
        objects.extend(sigs.iter().map(|(_, o)| o.clone()));
        let mut maps = Vec::new();
        let mut bases = Vec::new();
        for (k, (t, _)) in terms.iter().enumerate() {
            let (cols, rows, m) = self.matrix(t, &sigs[k].0, &sigs[k].1, "homology")?;
            if k == 0 {
                bases.push(cols);
            }
            bases.push(rows);
            maps.push(m);
        }
        for k in 1..maps.len() {
            let p = maps[k].mul(&maps[k - 1]).ok_or_else(overflow)?;
            if !p.is_zero() {
                let j = (0..p.cols).find(|&j| (0..p.rows).any(|r| p.data[r][j] != 0)).unwrap();
                return Err(Error::at(
                    terms[k].0.span,
                    format!(
                        "not a complex: `{}` after `{}` sends {} to something other than tohu",
                        terms[k].1,
                        terms[k - 1].1,
                        show_value(&bases[k - 1][j], &objects[k - 1])
                    ),
                ));
            }
        }
        let split: Vec<[Vec<usize>; 2]> = bases.iter().map(|b| {
            let (e, o) = parities(b);
            [e, o]
        }).collect();
        let mut groups = Vec::new();
        for k in 0..objects.len() {
            let mut parts = Vec::new();
            for p in 0..2 {
                let here = &split[k][p];
                let incoming = if k == 0 { Matrix::zero(here.len(), 0) } else { maps[k - 1].select(here, &split[k - 1][p]) };
                let outgoing = if k == maps.len() { Matrix::zero(0, here.len()) } else { maps[k].select(&split[k + 1][p], here) };
                parts.push(linalg::homology(here.len(), &incoming, &outgoing).ok_or_else(overflow)?);
            }
            groups.push(show_super(&parts[0], &parts[1]));
        }
        Ok(format!("H = [{}]", groups.join(", ")))
    }
}

pub fn run_source(src: &str, out: &mut dyn std::io::Write) -> Result<(), Error> {
    let program = syntax::parse(src)?;
    let mut s = Session { defs: HashMap::new(), sigs: HashMap::new(), loops: HashMap::new(), aliases: program.aliases };
    for item in &program.items {
        if let Item::Def { name, span, input, output, body } = item {
            if s.sigs.insert(name.clone(), (input.clone(), output.clone())).is_some() {
                return Err(Error::at(*span, format!("`{}` is defined twice", name)));
            }
            s.defs.insert(name.clone(), body.clone());
        }
    }
    for item in &program.items {
        if let Item::Def { name, span, input, output, body } = item {
            let mut c = Checker::new(&s.sigs, &s.aliases);
            let (i, o) = c.infer(body)?;
            c.unify(&i, input, *span, &format!("`{}` does not take its declared input", name))?;
            c.unify(&o, output, *span, &format!("`{}` does not return its declared output", name))?;
            c.finish(&mut s.loops)?;
        }
    }
    let emit = |out: &mut dyn std::io::Write, line: String| {
        writeln!(out, "{}", line).map_err(|e| Error { span: None, msg: e.to_string() })
    };
    for item in &program.items {
        match item {
            Item::Def { .. } => {}
            Item::Run { term, input, .. } => {
                let (i, o) = s.check(term)?;
                let v = combo_to_vector(input, &i, &s.aliases)?;
                let r = s.run(term, &v).map_err(|f| Error::at(term.span, f.message()))?;
                emit(out, show_vector(&r, &o))?;
            }
            Item::Expect { term, text, input, output } => {
                let (i, o) = s.check(term)?;
                let v = combo_to_vector(input, &i, &s.aliases)?;
                let w = combo_to_vector(output, &o, &s.aliases)?;
                let r = s.run(term, &v).map_err(|f| Error::at(term.span, f.message()))?;
                if r != w {
                    return Err(Error::at(
                        term.span,
                        format!(
                            "expectation failed: `{}` sends {} to {}, not {}",
                            text,
                            show_vector(&v, &i),
                            show_vector(&r, &o),
                            show_vector(&w, &o)
                        ),
                    ));
                }
            }
            Item::Refute { term, text, input } => {
                let (i, o) = s.check(term)?;
                let v = combo_to_vector(input, &i, &s.aliases)?;
                match s.run(term, &v) {
                    Ok(r) => {
                        return Err(Error::at(
                            term.span,
                            format!("refutation failed: `{}` sends {} to {}", text, show_vector(&v, &i), show_vector(&r, &o)),
                        ))
                    }
                    Err(f) => emit(out, format!("refuted: {}", f.message()))?,
                }
            }
            Item::Table { term, .. } => {
                let (i, o) = s.check(term)?;
                let (cols, _, _) = s.matrix(term, &i, &o, "a table")?;
                let mut machine = s.machine();
                for x in cols {
                    let image = machine.eval(term, true, x.clone()).map_err(|f| Error::at(term.span, f.message()))?;
                    emit(out, format!("{} |-> {}", show_value(&x, &i), show_vector(&image, &o)))?;
                }
            }
            Item::Homology { span, terms } => {
                let line = s.homology(*span, terms)?;
                emit(out, line)?;
            }
        }
    }
    Ok(())
}
