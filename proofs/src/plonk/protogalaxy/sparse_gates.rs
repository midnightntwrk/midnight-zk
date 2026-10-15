//! Row-sparse evaluation of the custom gates on the plain domain `H`.
//!
//! Almost every gate polynomial is a product with a fixed (selector) column
//! factor that vanishes on most rows, so `Σ_k y_k·poly_k(row i)` only needs
//! the polynomials whose gating factors are all nonzero on row `i`. The
//! coset quotient of a plain proof cannot use this; the fold evaluates on
//! `H` itself, where the fixed columns keep their assigned values.
//!
//! [`SparseGates`] is built lazily and cached in the [`Evaluator`] of the
//! proving key it was built from.
//!
//! [`Evaluator`]: crate::plonk::evaluation::Evaluator

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
#[derive(Clone, Debug)]
pub(crate) struct SparseGates<F> {
    evaluators: Vec<FlatGraphEvaluator<F>>,
    offsets: Vec<usize>,
    polys: Vec<u32>,
}

impl<F: WithSmallOrderMulGroup<3>> SparseGates<F> {
    /// The tables of the gates of `cs` over `domain`, for the fixed columns
    /// `fixed`.
    pub(crate) fn new(
        cs: &ConstraintSystem<F>,
        domain: &EvaluationDomain<F>,
        fixed: &[Polynomial<F, LagrangeCoeff>],
    ) -> Self {
        let exprs: Vec<&Expression<F>> = cs.gates.iter().flat_map(|g| g.polynomials()).collect();
        let evaluators: Vec<_> =
            exprs.iter().map(|e| GraphEvaluator::flat_single_gate(e)).collect();
        let factors: Vec<Vec<(usize, i32)>> = exprs
            .iter()
            .map(|e| {
                let mut f = Vec::new();
                gating_factors(e, &mut f);
                f
            })
            .collect();

        let n = domain.n as usize;
        assert!(
            fixed.iter().all(|c| c.len() == n),
            "fixed column of unexpected length"
        );
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
        offsets.push(0);
        for (c, p) in chunks {
            for count in c {
                offsets.push(offsets.last().unwrap() + count as usize);
            }
            polys.extend(p);
        }
        SparseGates {
            evaluators,
            offsets,
            polys,
        }
    }

    /// Indices of the gate polynomials that can be nonzero on `row`.
    fn active_on(&self, row: usize) -> &[u32] {
        &self.polys[self.offsets[row]..self.offsets[row + 1]]
    }

    /// `Σ_{k active on i} y[k]·poly_k` at every row `i` of `H`. `y` holds (at
    /// least) the gate challenges, first. `domain` and `fixed` are those of
    /// [`SparseGates::new`].
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
            let mut bufs: Vec<Vec<F>> = (self.evaluators.iter().enumerate())
                .map(|(k, e)| e.new_values_buffer(&F::ZERO, &[], &[], &y[k..k + 1]))
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
}
