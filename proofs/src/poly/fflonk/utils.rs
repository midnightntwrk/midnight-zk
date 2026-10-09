//! Helpers of the fflonk scheme: the combination `g` of a chunk and the roots
//! it is opened at.

use std::{
    collections::{HashMap, hash_map::Entry},
    hash::Hash,
    iter,
    marker::PhantomData,
};

use ff::PrimeField;

use crate::poly::{Coeff, Polynomial};

/// `g(X) = Σ_i X^i f_i(X^t)`, for `polys` the polynomials `f_0, ..., f_{k-1}`
/// in coefficient form and `t` the next power of two of `k`: the coefficients
/// of `g` interleave those of the `f_i`, with the slots of the `t - k` dummy
/// polynomials padding the `k` given ones to `t` left zero.
pub(super) fn compute_g<F: PrimeField>(polys: &[&Polynomial<F, Coeff>]) -> Polynomial<F, Coeff> {
    let t = polys.len().next_power_of_two();
    let n = polys.iter().map(|poly| poly.len()).max().unwrap_or(0);
    let mut values = vec![F::ZERO; t * n];
    for (i, poly) in polys.iter().enumerate() {
        for (j, coeff) in poly.values.iter().enumerate() {
            values[t * j + i] = *coeff;
        }
    }
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
