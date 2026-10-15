//! Row-sparse evaluation of the custom gates on the plain domain `H`.
//!
//! Almost every gate polynomial is a product with a fixed (selector) column
//! factor that vanishes on most rows, so `Σ_k y_k·poly_k(row i)` only needs
//! the polynomials whose gating factors are all nonzero on row `i`. The
//! coset quotient of a plain proof cannot use this; the fold evaluates on
//! `H` itself, where the fixed columns keep their assigned values.

use ff::WithSmallOrderMulGroup;
use rayon::{iter::ParallelIterator, slice::ParallelSlice};

use crate::{
    plonk::{
        ConstraintSystem, Expression,
        evaluation::{FlatGraphEvaluator, GraphEvaluator, get_rotation_idx},
    },
    poly::{EvaluationDomain, LagrangeCoeff, Polynomial},
    utils::arithmetic::parallelize,
};

/// Rows handled per task when building the activity table.
const TABLE_CHUNK: usize = 1024;

/// Fixed-column queries `(column, rotation)` whose vanishing makes `expr`
/// vanish: the leaves reachable through `Product`, `Negated` and `Scaled`.
fn gating_factors<F>(expr: &Expression<F>, out: &mut Vec<(usize, i32)>) {
    match expr {
        Expression::Fixed(q) => out.push((q.column_index, q.rotation.0)),
        Expression::Product(a, b) => {
            gating_factors(a, out);
            gating_factors(b, out);
        }
        Expression::Negated(a) | Expression::Scaled(a, _) => gating_factors(a, out),
        _ => (),
    }
}

/// One evaluator per gate polynomial, plus for each row the list of
/// polynomials that can be nonzero there (CSR: the polynomials of row `i`
/// are `polys[offsets[i]..offsets[i + 1]]`).
#[derive(Debug)]
pub(crate) struct SparseGates<F> {
    evaluators: Vec<FlatGraphEvaluator<F>>,
    /// Number of gating factors of each polynomial (for the census).
    factor_counts: Vec<usize>,
    offsets: Vec<u32>,
    polys: Vec<u32>,
}

impl<F: WithSmallOrderMulGroup<3>> SparseGates<F> {
    pub(crate) fn new(cs: &ConstraintSystem<F>, fixed: &[Polynomial<F, LagrangeCoeff>]) -> Self {
        let exprs: Vec<&Expression<F>> = cs.gates.iter().flat_map(|g| g.polynomials()).collect();
        let evaluators: Vec<_> = exprs
            .iter()
            .enumerate()
            .map(|(k, e)| GraphEvaluator::flat_single_gate(e, k))
            .collect();
        let factors: Vec<Vec<(usize, i32)>> = exprs
            .iter()
            .map(|e| {
                let mut f = Vec::new();
                gating_factors(e, &mut f);
                f
            })
            .collect();

        let n = fixed.first().map_or(0, |c| c.len());
        let active = |k: usize, i: usize| {
            factors[k].iter().all(|&(col, rot)| {
                let row = (i as isize + rot as isize).rem_euclid(n as isize) as usize;
                !bool::from(ff::Field::is_zero(&fixed[col][row]))
            })
        };
        let rows: Vec<usize> = (0..n).collect();
        let chunks: Vec<(Vec<u32>, Vec<u32>)> = rows
            .par_chunks(TABLE_CHUNK)
            .map(|rows| {
                let (mut counts, mut polys) = (Vec::new(), Vec::new());
                for &i in rows {
                    let before = polys.len();
                    polys.extend((0..exprs.len()).filter(|&k| active(k, i)).map(|k| k as u32));
                    counts.push((polys.len() - before) as u32);
                }
                (counts, polys)
            })
            .collect();

        let mut offsets = Vec::with_capacity(n + 1);
        let mut polys = Vec::new();
        offsets.push(0u32);
        for (c, p) in chunks {
            for count in c {
                offsets.push(offsets.last().unwrap() + count);
            }
            polys.extend(p);
        }
        let factor_counts = factors.iter().map(Vec::len).collect();
        SparseGates {
            evaluators,
            factor_counts,
            offsets,
            polys,
        }
    }

    fn active_on(&self, row: usize) -> &[u32] {
        &self.polys[self.offsets[row] as usize..self.offsets[row + 1] as usize]
    }

    /// `Σ_{k active on i} y[k]·poly_k` at every row `i` of `H`. `y` holds (at
    /// least) the gate challenges, first.
    pub(crate) fn evaluate(
        &self,
        domain: &EvaluationDomain<F>,
        advice: &[Polynomial<F, LagrangeCoeff>],
        instance: &[Polynomial<F, LagrangeCoeff>],
        fixed: &[Polynomial<F, LagrangeCoeff>],
        y: &[F],
    ) -> Polynomial<F, LagrangeCoeff> {
        let log_n = domain.k();
        let mut values = domain.empty_lagrange();
        parallelize(&mut values, |values, start| {
            let mut bufs: Vec<Vec<F>> = self
                .evaluators
                .iter()
                .map(|e| e.new_values_buffer(&F::ZERO, &[], &[], y))
                .collect();
            let mut rots = Vec::new();
            for (j, value) in values.iter_mut().enumerate() {
                let row = start + j;
                let mut acc = F::ZERO;
                for &k in self.active_on(row) {
                    let e = &self.evaluators[k as usize];
                    rots.clear();
                    rots.extend(e.rotations.iter().map(|&r| get_rotation_idx(row, r, 0, log_n)));
                    acc += e.evaluate(
                        &mut bufs[k as usize],
                        fixed,
                        advice,
                        instance,
                        &rots,
                        &F::ZERO,
                    );
                }
                *value = acc;
            }
        });
        values
    }

    /// Prints the activity of each gate polynomial and the overall density.
    pub(crate) fn print_census(&self, n: usize) {
        let mut per_poly = vec![0usize; self.evaluators.len()];
        for &k in &self.polys {
            per_poly[k as usize] += 1;
        }
        let empty = (0..n).filter(|&i| self.active_on(i).is_empty()).count();
        let total: usize = per_poly.iter().sum();
        eprintln!(
            "[sparse] {} gate polys, n={n}: density={:.2}%, rows with no active poly={:.2}%",
            per_poly.len(),
            100.0 * total as f64 / (per_poly.len() * n).max(1) as f64,
            100.0 * empty as f64 / n as f64
        );
        for (k, c) in per_poly.iter().enumerate() {
            eprintln!(
                "[sparse]   poly {k}: {} gating factors, active {c} rows ({:.2}%)",
                self.factor_counts[k],
                100.0 * *c as f64 / n as f64
            );
        }
    }
}
