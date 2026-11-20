// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Polynomial evaluations and the KZG multi-open, in parallel tasks of
//! bounded size. Field arithmetic is exact, so regrouping sums and products
//! gives the stock values (the stock evaluation's grouping already follows
//! the thread count).

use ff::Field;
use rayon::{
    iter::{
        IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
    },
    slice::ParallelSliceMut,
};

use super::DIVISION_MIN_LEN;
use crate::{
    poly::{Coeff, Polynomial},
    utils::arithmetic::eval_polynomial_seq,
};

/// Coefficients per evaluation task.
const EVAL_CHUNK: usize = 1 << 13;

/// Independent Horner chains per evaluation task.
const CHAINS: usize = 8;

/// Coefficients per task of an inner product of polynomials.
const SUM_CHUNK: usize = 1 << 12;

/// Rows per block of a division.
const DIV_BLOCK: usize = 1 << 13;

/// Calls that divided in parallel blocks, so the golden-digest test at
/// division size can check it reached them.
#[cfg(test)]
pub(crate) mod reached {
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub(crate) static DIVIDE_BY_ROOTS: AtomicUsize = AtomicUsize::new(0);
    pub(crate) static KATE_DIVISION: AtomicUsize = AtomicUsize::new(0);

    pub(super) fn hit(counter: &AtomicUsize) {
        counter.fetch_add(1, Ordering::Relaxed);
    }

    /// The counts of `divide_by_roots` and `kate_division`, in that order.
    pub(crate) fn counts() -> [usize; 2] {
        [&DIVIDE_BY_ROOTS, &KATE_DIVISION].map(|c| c.load(Ordering::Relaxed))
    }
}

/// [`crate::utils::arithmetic::eval_polynomial`] of each `(polynomial,
/// point)` of `jobs`, with all chunks of all jobs spread over the pool.
pub(crate) fn eval_many<F: Field>(jobs: &[(&[F], F)]) -> Vec<F> {
    let tasks: Vec<(usize, usize)> = (jobs.iter().enumerate())
        .flat_map(|(j, (poly, _))| (0..poly.len().div_ceil(EVAL_CHUNK)).map(move |c| (j, c)))
        .collect();
    let parts: Vec<F> = tasks
        .par_iter()
        .map(|&(j, c)| {
            let (poly, x) = jobs[j];
            let start = c * EVAL_CHUNK;
            let end = (start + EVAL_CHUNK).min(poly.len());
            horner_interleaved(&poly[start..end], x) * x.pow_vartime([start as u64])
        })
        .collect();
    let mut evals = vec![F::ZERO; jobs.len()];
    for (&(j, _), part) in tasks.iter().zip(parts) {
        evals[j] += part;
    }
    evals
}

/// `eval_polynomial_seq(poly, x)` as [`CHAINS`] interleaved Horner chains
/// over consecutive parts of `poly`, joined by Horner in `x^part`.
/// Independent chains keep the multiplier busy instead of waiting on each
/// product.
fn horner_interleaved<F: Field>(poly: &[F], x: F) -> F {
    let part = poly.len() / CHAINS;
    if part == 0 {
        return eval_polynomial_seq(poly, x);
    }
    let mut acc = [F::ZERO; CHAINS];
    acc[CHAINS - 1] = eval_polynomial_seq(&poly[CHAINS * part..], x);
    for i in (0..part).rev() {
        for (k, acc) in acc.iter_mut().enumerate() {
            *acc = *acc * x + poly[k * part + i];
        }
    }
    let x_part = x.pow_vartime([part as u64]);
    acc.iter().rev().fold(F::ZERO, |sum, acc| sum * x_part + acc)
}

/// The stock `poly_inner_product` helper of the KZG multi-open, cut into
/// tasks of [`SUM_CHUNK`] coefficients.
pub(crate) fn poly_inner_product<F: Field>(
    polys: &[&Polynomial<F, Coeff>],
    scalars: impl IntoIterator<Item = F>,
) -> Polynomial<F, Coeff> {
    let scalars: Vec<F> = scalars.into_iter().take(polys.len()).collect();
    let max_len = polys.iter().map(|p| p.len()).max().unwrap_or(0);
    let mut values: Vec<F> = (0..max_len).into_par_iter().map(|_| F::ZERO).collect();
    values.par_chunks_mut(SUM_CHUNK).enumerate().for_each(|(c, chunk)| {
        let start = c * SUM_CHUNK;
        for (poly, scalar) in polys.iter().zip(scalars.iter()) {
            let pv: &[F] = poly;
            let end = (start + chunk.len()).min(pv.len());
            if start < pv.len() {
                for (out, coeff) in chunk[..end - start].iter_mut().zip(&pv[start..end]) {
                    *out += *coeff * scalar;
                }
            }
        }
    });
    Polynomial {
        values,
        _marker: std::marker::PhantomData,
    }
}

/// `crate::utils::arithmetic::divide_by_roots` in parallel blocks.
///
/// With `d` roots and `v_j` the coefficients of the vanishing product, the
/// stock loop is the recurrence `q_k = a_{k+d} - Σ_{j<d} v_j · q_{k+d-j}`,
/// from the top down, with lags `d - j`. Each block is solved with a zero
/// history; the true rows add the true history through the solutions `h_s`
/// of the homogeneous recurrence with a unit history at lag `s`. A short
/// scan over the blocks gives each block's history.
pub(crate) fn divide_by_roots<F: Field>(poly: &[F], roots: &[F]) -> Vec<F> {
    let mut vanishing = vec![F::ONE];
    for root in roots {
        let mut next = vec![F::ZERO; vanishing.len() + 1];
        for (i, coeff) in vanishing.iter().enumerate() {
            next[i + 1] += coeff;
            next[i] -= *coeff * root;
        }
        vanishing = next;
    }
    let degree = roots.len();
    // (lag, coefficient) with lag = degree - j in 1..=degree.
    let terms: Vec<(usize, F)> = (vanishing[..degree].iter().enumerate())
        .filter(|(_, coeff)| !bool::from(coeff.is_zero()))
        .map(|(j, coeff)| (degree - j, *coeff))
        .collect();
    let m = poly.len().saturating_sub(degree);
    // The history a block needs: its rows read up to `lags` rows above it.
    let lags = terms.iter().map(|(lag, _)| *lag).max().unwrap_or(0);

    // A history longer than a block would reach past the block above.
    if lags > DIV_BLOCK {
        return crate::utils::arithmetic::divide_by_roots_seq(poly, roots);
    }
    #[cfg(test)]
    reached::hit(&reached::DIVIDE_BY_ROOTS);

    // The input of row `p` (from the top): `a_{k+d}` with `k = m - 1 - p`.
    let input = |p: usize| poly[m - 1 - p + degree];
    // Block `b` from the top is the `b`-th chunk from the end; its row `t`
    // is the element `len - 1 - t`.
    let mut q: Vec<F> = (0..m).into_par_iter().map(|_| F::ZERO).collect();

    // Solves the block starting at row `first` with a zero history.
    let solve = |first: usize, block: &mut [F]| {
        let len = block.len();
        for t in 0..len {
            let mut value = input(first + t);
            for (lag, coeff) in &terms {
                if *lag <= t {
                    value -= *coeff * block[len - 1 - (t - lag)];
                }
            }
            block[len - 1 - t] = value;
        }
    };
    let homogeneous = || -> Vec<Vec<F>> {
        // `h[s - 1][t]`: the row `t` of a block whose only nonzero history
        // is a one at lag `s` (the row `s` above its first row).
        (1..=lags)
            .into_par_iter()
            .map(|s| {
                let mut h = vec![F::ZERO; DIV_BLOCK.min(m)];
                for t in 0..h.len() {
                    let mut value = F::ZERO;
                    for (lag, coeff) in &terms {
                        if *lag <= t {
                            value -= *coeff * h[t - lag];
                        } else if *lag - t == s {
                            value -= *coeff;
                        }
                    }
                    h[t] = value;
                }
                h
            })
            .collect()
    };
    let (_, h) = rayon::join(
        || {
            q.par_rchunks_mut(DIV_BLOCK)
                .enumerate()
                .for_each(|(b, block)| solve(b * DIV_BLOCK, block))
        },
        homogeneous,
    );

    // `histories[b][s - 1]`: the true value `s` rows above block `b`.
    let blocks = m.div_ceil(DIV_BLOCK);
    let mut histories: Vec<Vec<F>> = Vec::with_capacity(blocks);
    histories.push(vec![F::ZERO; lags]);
    for b in 1..blocks {
        let hist_above = &histories[b - 1];
        let next: Vec<F> = (1..=lags)
            .map(|s| {
                // the true value of the row `DIV_BLOCK - s` of the block above
                let t = DIV_BLOCK - s;
                let mut value = q[m - 1 - ((b - 1) * DIV_BLOCK + t)];
                for (r, hr) in hist_above.iter().enumerate() {
                    value += *hr * h[r][t];
                }
                value
            })
            .collect();
        histories.push(next);
    }

    q.par_rchunks_mut(DIV_BLOCK)
        .zip(histories.par_iter())
        .skip(1)
        .for_each(|(block, hist)| {
            let len = block.len();
            for (r, hr) in hist.iter().enumerate() {
                if bool::from(hr.is_zero()) {
                    continue;
                }
                for (t, hv) in h[r][..len].iter().enumerate() {
                    block[len - 1 - t] += *hr * hv;
                }
            }
        });

    q
}

/// `crate::utils::arithmetic::kate_division` of `a - c` by `X - b`, for any
/// constant `c`: the quotient does not depend on the constant coefficient,
/// so `a` is divided without the copy `a - c`.
///
/// # Panics
///
/// If `a` is empty, as `kate_division`.
pub(crate) fn kate_division<F: Field>(a: &[F], b: F) -> Vec<F> {
    assert!(!a.is_empty(), "kate_division of an empty polynomial");
    if a.len() < DIVISION_MIN_LEN {
        return crate::utils::arithmetic::kate_division(a, b);
    }
    #[cfg(test)]
    reached::hit(&reached::KATE_DIVISION);
    divide_by_roots(a, &[b])
}

#[cfg(test)]
mod tests {
    use ff::{Field, PrimeField, WithSmallOrderMulGroup};
    use midnight_curves::Fq;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    use super::*;
    use crate::{
        par::testing::{assert_on_pools, poly, random_values, stock_poly_inner_product},
        utils::arithmetic::{divide_by_roots_seq, eval_polynomial, kate_division as stock_kate},
    };

    #[test]
    fn eval_many_matches_eval_polynomial() {
        let mut rng = ChaCha20Rng::seed_from_u64(0x3a);
        // every remainder of the interleaved chains, and across a task boundary
        let polys: Vec<Vec<Fq>> = (0..2 * CHAINS)
            .chain([EVAL_CHUNK + 1])
            .map(|n| random_values(&mut rng, n))
            .collect();
        let points = [Fq::ZERO, Fq::random(&mut rng)];
        let jobs: Vec<(&[Fq], Fq)> =
            polys.iter().flat_map(|p| points.map(|x| (p.as_slice(), x))).collect();
        let stock: Vec<Fq> = jobs.iter().map(|(p, x)| eval_polynomial(p, *x)).collect();
        assert_on_pools(&stock, || eval_many(&jobs));
        assert!(eval_many::<Fq>(&[]).is_empty());
    }

    /// More scalars than polynomials, of different lengths.
    #[test]
    fn poly_inner_product_matches_stock() {
        let mut rng = ChaCha20Rng::seed_from_u64(0x3b);
        for lens in [
            vec![],
            vec![3, 1],
            vec![SUM_CHUNK + 3, 7, 2 * SUM_CHUNK, 0, 40_000],
        ] {
            let polys: Vec<Polynomial<Fq, Coeff>> =
                lens.iter().map(|&n| poly(random_values(&mut rng, n))).collect();
            let refs: Vec<_> = polys.iter().collect();
            let scalars: Vec<Fq> = crate::utils::arithmetic::powers(Fq::random(&mut rng))
                .take(lens.len() + 2)
                .collect();
            let stock = stock_poly_inner_product(&refs, scalars.clone());
            assert_on_pools(&stock, || poly_inner_product(&refs, scalars.clone()).values);
        }
    }

    /// Also through the dispatching crate function.
    #[test]
    fn divide_by_roots_matches_stock() {
        let mut rng = ChaCha20Rng::seed_from_u64(0x3c);
        let x = Fq::random(&mut rng);
        let root_sets = [
            vec![],
            vec![x],
            vec![Fq::ZERO],
            vec![x, x],
            random_values(&mut rng, 4),
            // X^3 - x^3: zero terms are skipped
            vec![x, Fq::ZETA * x, Fq::ZETA.square() * x],
        ];
        let lens = [
            0,
            3,
            5,
            DIV_BLOCK + 2,
            3 * DIV_BLOCK + 17,
            DIVISION_MIN_LEN - 1,
            DIVISION_MIN_LEN,
        ];
        for roots in &root_sets {
            for n in lens {
                let a = random_values(&mut rng, n);
                let stock = divide_by_roots_seq(&a, roots);
                assert_on_pools(&stock, || divide_by_roots(&a, roots));
                assert_eq!(crate::utils::arithmetic::divide_by_roots(&a, roots), stock);
            }
        }
    }

    /// Lags past a block fall back to the stock division: the product
    /// `(X^DIV_BLOCK - x^DIV_BLOCK) (X - y)` has its lowest term at lag
    /// `DIV_BLOCK + 1`.
    #[test]
    fn divide_by_roots_more_roots_than_a_block() {
        let mut rng = ChaCha20Rng::seed_from_u64(0x3f);
        let omega = Fq::ROOT_OF_UNITY.pow_vartime([1u64 << (Fq::S - DIV_BLOCK.ilog2())]);
        let mut roots: Vec<Fq> =
            std::iter::successors(Some(Fq::random(&mut rng)), |r| Some(*r * omega))
                .take(DIV_BLOCK)
                .collect();
        roots.push(Fq::random(&mut rng));
        let a = random_values(&mut rng, DIVISION_MIN_LEN + 3);
        let stock = divide_by_roots_seq(&a, &roots);
        assert_on_pools(&stock, || divide_by_roots(&a, &roots));
        assert_eq!(crate::utils::arithmetic::divide_by_roots(&a, &roots), stock);
    }

    /// Against the stock quotient of the dividend minus a constant, as the
    /// stock multi-open calls it.
    #[test]
    fn kate_division_matches_stock() {
        let mut rng = ChaCha20Rng::seed_from_u64(0x3d);
        for n in [1, 2, DIVISION_MIN_LEN - 1, DIVISION_MIN_LEN] {
            let a = random_values(&mut rng, n);
            for b in [Fq::ZERO, Fq::random(&mut rng)] {
                let mut shifted = a.clone();
                shifted[0] -= Fq::random(&mut rng);
                assert_on_pools(&stock_kate(&shifted, b), || kate_division(&a, b));
            }
        }
    }
}
