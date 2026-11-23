//! Integer matrices, the Smith normal form, and homology of complexes of
//! free abelian groups.

/// A dense integer matrix stored by rows.
#[derive(Clone, Debug)]
pub struct Matrix {
    pub rows: usize,
    pub cols: usize,
    pub data: Vec<Vec<i128>>,
}

impl Matrix {
    pub fn zero(rows: usize, cols: usize) -> Matrix {
        Matrix { rows, cols, data: vec![vec![0; cols]; rows] }
    }

    pub fn select(&self, rows: &[usize], cols: &[usize]) -> Matrix {
        Matrix {
            rows: rows.len(),
            cols: cols.len(),
            data: rows.iter().map(|&r| cols.iter().map(|&c| self.data[r][c]).collect()).collect(),
        }
    }

    /// `self * other`, or `None` on overflow.
    pub fn mul(&self, other: &Matrix) -> Option<Matrix> {
        let mut m = Matrix::zero(self.rows, other.cols);
        for i in 0..self.rows {
            for k in 0..self.cols {
                let a = self.data[i][k];
                if a == 0 {
                    continue;
                }
                for j in 0..other.cols {
                    let p = a.checked_mul(other.data[k][j])?;
                    m.data[i][j] = m.data[i][j].checked_add(p)?;
                }
            }
        }
        Some(m)
    }

    pub fn is_zero(&self) -> bool {
        self.data.iter().all(|r| r.iter().all(|&x| x == 0))
    }
}

/// The nonzero invariant factors `d1 | d2 | ...` of a matrix, or `None` on
/// overflow.
#[allow(clippy::needless_range_loop)]
pub fn invariant_factors(m: &Matrix) -> Option<Vec<i128>> {
    let mut a = m.data.clone();
    let (r, c) = (m.rows, m.cols);
    let mut out = Vec::new();
    let mut t = 0;
    while t < r.min(c) {
        // The smallest nonzero entry of the remaining block becomes the pivot.
        let mut best: Option<(usize, usize)> = None;
        for i in t..r {
            for j in t..c {
                if a[i][j] != 0 && best.is_none_or(|(bi, bj)| a[i][j].abs() < a[bi][bj].abs()) {
                    best = Some((i, j));
                }
            }
        }
        let Some((pi, pj)) = best else { break };
        a.swap(t, pi);
        for row in a.iter_mut() {
            row.swap(t, pj);
        }
        loop {
            let p = a[t][t];
            let mut clean = true;
            for i in t + 1..r {
                let q = a[i][t] / p;
                if q != 0 {
                    for j in t..c {
                        a[i][j] = a[i][j].checked_sub(q.checked_mul(a[t][j])?)?;
                    }
                }
                if a[i][t] != 0 {
                    clean = false;
                }
            }
            for j in t + 1..c {
                let q = a[t][j] / p;
                if q != 0 {
                    for i in t..r {
                        a[i][j] = a[i][j].checked_sub(q.checked_mul(a[i][t])?)?;
                    }
                }
                if a[t][j] != 0 {
                    clean = false;
                }
            }
            if !clean {
                // A remainder smaller than the pivot appeared; make it the pivot.
                let mut best = (t, t);
                for i in t + 1..r {
                    if a[i][t] != 0 && a[i][t].abs() < a[best.0][best.1].abs() {
                        best = (i, t);
                    }
                }
                for j in t + 1..c {
                    if a[t][j] != 0 && a[t][j].abs() < a[best.0][best.1].abs() {
                        best = (t, j);
                    }
                }
                a.swap(t, best.0);
                for row in a.iter_mut() {
                    row.swap(t, best.1);
                }
                continue;
            }
            // The pivot must divide the rest of the block.
            let mut bad = None;
            'find: for i in t + 1..r {
                for j in t + 1..c {
                    if a[i][j] % p != 0 {
                        bad = Some(i);
                        break 'find;
                    }
                }
            }
            match bad {
                Some(i) => {
                    for j in t..c {
                        a[t][j] = a[t][j].checked_add(a[i][j])?;
                    }
                }
                None => break,
            }
        }
        out.push(a[t][t].abs());
        t += 1;
    }
    Some(out)
}

/// A finitely generated abelian group `ℤ^rank ⊕ ⊕ ℤ/t`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    pub rank: usize,
    pub torsion: Vec<i128>,
}

impl Group {
    pub fn is_zero(&self) -> bool {
        self.rank == 0 && self.torsion.is_empty()
    }

    /// The summands, each written with the given prefix (`Π` for odd ones).
    pub fn summands(&self, prefix: &str) -> Vec<String> {
        let mut parts = Vec::new();
        match self.rank {
            0 => {}
            1 => parts.push(format!("{}Z", prefix)),
            n => parts.push(format!("{}Z^{}", prefix, n)),
        }
        let mut i = 0;
        while i < self.torsion.len() {
            let t = self.torsion[i];
            let mut k = 1;
            while i + k < self.torsion.len() && self.torsion[i + k] == t {
                k += 1;
            }
            if k == 1 {
                parts.push(format!("{}Z/{}", prefix, t));
            } else {
                parts.push(format!("{}(Z/{})^{}", prefix, t, k));
            }
            i += k;
        }
        parts
    }
}

/// Shows an even part and an odd part as one super group.
pub fn show_super(even: &Group, odd: &Group) -> String {
    let mut parts = even.summands("");
    parts.extend(odd.summands("\u{3a0}"));
    if parts.is_empty() {
        "0".into()
    } else {
        parts.join(" \u{2295} ")
    }
}

/// `ker g / im f` for `f : ℤ^a → ℤ^n` and `g : ℤ^n → ℤ^c` with `g f = 0`.
/// Since the quotient of the middle by the kernel of `g` is free, the
/// torsion is that of the cokernel of `f`.
pub fn homology(n: usize, f: &Matrix, g: &Matrix) -> Option<Group> {
    let df = invariant_factors(f)?;
    let dg = invariant_factors(g)?;
    Some(Group {
        rank: n - df.len() - dg.len(),
        torsion: df.into_iter().filter(|&d| d != 1).collect(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(rows: Vec<Vec<i128>>) -> Matrix {
        Matrix { rows: rows.len(), cols: rows.first().map_or(0, |r| r.len()), data: rows }
    }

    #[test]
    fn smith_of_small_matrices() {
        assert_eq!(invariant_factors(&m(vec![vec![2, 4], vec![6, 8]])), Some(vec![2, 4]));
        assert_eq!(invariant_factors(&m(vec![vec![4, 6]])), Some(vec![2]));
        assert_eq!(invariant_factors(&m(vec![vec![2, 0], vec![0, 3]])), Some(vec![1, 6]));
        assert_eq!(invariant_factors(&m(vec![vec![0, 0], vec![0, 0]])), Some(vec![]));
    }
}
