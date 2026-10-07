//! Helpers of the fflonk scheme: the combination `g` of a chunk and the roots
//! it is opened at.

use std::{
    collections::{HashMap, hash_map::Entry},
    hash::Hash,
    iter,
    marker::PhantomData,
};

use ff::{PrimeField, WithSmallOrderMulGroup};
use rayon::prelude::*;

use crate::{
    poly::{Polynomial, PolynomialBasis, PolynomialRepresentation},
    utils::arithmetic::powers,
};

/// `g(X) = Σ_i X^i f_i(X^t)`, for `polys` the polynomials `f_0, ..., f_{k-1}`
/// and `t` the next power of two of `k`, in the basis of the polynomials.
///
/// In coefficient form, the coefficients of `g` interleave those of the `f_i`,
/// with the slots of the `t - k` dummy polynomials padding the `k` given ones
/// to `t` left zero.
///
/// In Lagrange form, the `f_i` are evaluations over the domain of size `n` and
/// `g` is given by its evaluations over the domain of size `t·n`. For `ω` the
/// generator of the latter, every row `j` and every `m` in `[0, t)`:
///
///   `g(ω^(j + n·m)) = Σ_i (ω^n)^(m·i) · ω^(j·i) f_i(j)`
///
/// so the `t` evaluations of row `j` are the size-`t` DFT of `ω^(j·i) f_i(j)`,
/// and a row where every `f_i` vanishes gives `t` zeros.
///
/// # Panics
///
/// Panics if the polynomials are in neither coefficient nor Lagrange form, if
/// they are in Lagrange form and have different lengths, or if the field has
/// no roots of unity of order `n · t`, for `n` the length of the polynomials.
pub(super) fn compute_g<F, B>(polys: &[&Polynomial<F, B>]) -> Polynomial<F, B>
where
    F: WithSmallOrderMulGroup<3>,
    B: PolynomialRepresentation,
{
    let t = polys.len().next_power_of_two();
    let n = polys.iter().map(|poly| poly.len()).max().unwrap_or(0);
    let log_order = n.next_power_of_two().ilog2() + t.ilog2();
    assert!(
        log_order <= F::S,
        "the field has no roots of unity of order 2^{log_order} for fflonk"
    );
    if t == 1 {
        return polys[0].clone();
    }
    let values = match B::BASIS {
        PolynomialBasis::Coeff => {
            let mut values = vec![F::ZERO; t * n];
            for (i, poly) in polys.iter().enumerate() {
                for (j, coeff) in poly.values.iter().enumerate() {
                    values[t * j + i] = *coeff;
                }
            }
            values
        }
        PolynomialBasis::Lagrange => {
            assert!(polys.iter().all(|poly| poly.len() == n));
            let omega = F::ROOT_OF_UNITY.pow_vartime([1u64 << (F::S - log_order)]);
            let omega_t: Vec<F> = powers(omega.pow_vartime([n as u64])).take(t).collect();

            // The evaluations row by row: `rows[j·t + m] = g(ω^(j + n·m))`, computed
            // in blocks of rows, along which `ω^j` advances by one factor `ω` per row.
            const BLOCK: usize = 256;
            let mut rows = vec![F::ZERO; t * n];
            rows.par_chunks_mut(t * BLOCK).enumerate().for_each(|(b, block)| {
                let mut omega_j = omega.pow_vartime([(b * BLOCK) as u64]);
                let mut twisted = vec![F::ZERO; polys.len()];
                for (r, row) in block.chunks_mut(t).enumerate() {
                    let j = b * BLOCK + r;
                    if polys.iter().any(|poly| !bool::from(poly[j].is_zero())) {
                        for ((a, w), poly) in twisted.iter_mut().zip(powers(omega_j)).zip(polys) {
                            *a = w * poly[j];
                        }
                        for (m, out) in row.iter_mut().enumerate() {
                            *out = (twisted.iter().enumerate())
                                .map(|(i, a)| omega_t[(m * i) % t] * a)
                                .sum();
                        }
                    }
                    omega_j *= omega;
                }
            });
            let mut values = vec![F::ZERO; t * n];
            values
                .par_iter_mut()
                .enumerate()
                .for_each(|(k, v)| *v = rows[(k % n) * t + k / n]);
            values
        }
        basis => panic!("fflonk cannot combine polynomials in the {basis:?} basis"),
    };
    Polynomial {
        values,
        _marker: PhantomData,
    }
}

/// The `t`-th roots of `x`, for a power of two `t`.
///
/// Returns `None` if `x` is not a `t`-th power. Since the field has roots of
/// unity of order `t`, if `x` has a `t`-th root then it has all `t` of them.
///
/// # Panics
///
/// Panics if `t` is not a power of two, or if `F` has no roots of unity of
/// order `t`.
pub(super) fn roots<F: PrimeField>(x: F, t: usize) -> Option<Vec<F>> {
    assert!(
        t.is_power_of_two(),
        "fflonk roots of order {t}, not a power of two"
    );
    let log_t = t.trailing_zeros();
    assert!(
        log_t <= F::S,
        "the field has no roots of unity of order {t}"
    );
    let mut root = x;
    for _ in 0..log_t {
        root = Option::from(root.sqrt())?;
    }
    let omega = F::ROOT_OF_UNITY.pow_vartime([1u64 << (F::S - log_t)]);
    Some(iter::successors(Some(root), |r| Some(*r * omega)).take(t).collect())
}

/// [`roots`] of `x`, computed once per `x` and `t` and kept in `cache`.
pub(super) fn cached_roots<F: PrimeField + Hash>(
    cache: &mut HashMap<(F, usize), Vec<F>>,
    x: F,
    t: usize,
) -> Option<&[F]> {
    Some(match cache.entry((x, t)) {
        Entry::Occupied(entry) => entry.into_mut(),
        Entry::Vacant(entry) => entry.insert(roots(x, t)?),
    })
}
