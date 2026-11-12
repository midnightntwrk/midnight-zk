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

use std::{
    cmp::min,
    collections::{HashMap, hash_map::Entry},
    ops::Range,
};

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::fflonk::roots,
};
use num_bigint::BigUint;
use num_traits::One;

use crate::{
    CircuitField,
    field::AssignedNative,
    instructions::{
        ArithInstructions, AssignmentInstructions, FieldInstructions, NativeInstructions,
    },
};

/// An assigned scalar known to be bounded in the range [0, bound].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignedBoundedScalar<F: CircuitField> {
    pub(crate) scalar: AssignedNative<F>,
    pub(crate) bound: BigUint,
}

impl<F: CircuitField> AssignedBoundedScalar<F> {
    /// Creates a new `AssignedBoundedScalar` from an assigned scalar and an
    /// inclusive bound on its value. The bound will default to maximum possible
    /// value of a field element when not provided.
    pub(crate) fn new(scalar: &AssignedNative<F>, bound_opt: Option<BigUint>) -> Self {
        Self {
            scalar: scalar.clone(),
            bound: bound_opt.unwrap_or(F::modulus() - BigUint::one()),
        }
    }

    /// An `AssignedBoundedScalar` with a fixed value of 1.
    pub(crate) fn one(
        layouter: &mut impl Layouter<F>,
        scalar_chip: &impl AssignmentInstructions<F, AssignedNative<F>>,
    ) -> Result<AssignedBoundedScalar<F>, Error> {
        let one = scalar_chip.assign_fixed(layouter, F::ONE)?;
        Ok(AssignedBoundedScalar {
            scalar: one,
            bound: BigUint::one(),
        })
    }
}

/// Assigns a slice of scalars, producing a vector of assigned bounded scalars
/// with worst-case bound.
pub(crate) fn assign_bounded_scalars<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl AssignmentInstructions<F, AssignedNative<F>>,
    values: &[Value<F>],
) -> Result<Vec<AssignedBoundedScalar<F>>, Error> {
    Ok(scalar_chip
        .assign_many(layouter, values)?
        .iter()
        .map(|s| AssignedBoundedScalar::new(s, None))
        .collect())
}

/// Adds the given assigned bounded scalars, updating the bound.
pub(crate) fn add_bounded_scalars<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    x1: &AssignedBoundedScalar<F>,
    x2: &AssignedBoundedScalar<F>,
) -> Result<AssignedBoundedScalar<F>, Error> {
    Ok(AssignedBoundedScalar {
        scalar: scalar_chip.add(layouter, &x1.scalar, &x2.scalar)?,
        bound: min(
            x1.bound.clone() + x2.bound.clone(),
            F::modulus() - BigUint::one(),
        ),
    })
}

/// Multiplies the given assigned bounded scalars, updating the bound.
pub fn mul_bounded_scalars<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    x1: &AssignedBoundedScalar<F>,
    x2: &AssignedBoundedScalar<F>,
) -> Result<AssignedBoundedScalar<F>, Error> {
    Ok(AssignedBoundedScalar {
        scalar: scalar_chip.mul(layouter, &x1.scalar, &x2.scalar, None)?,
        bound: min(
            x1.bound.clone() * x2.bound.clone(),
            F::modulus() - BigUint::one(),
        ),
    })
}

/// Truncates a field element by removing its most-significative half, as the
/// off-circuit verifier does with its challenges.
pub(crate) fn truncate_off_circuit<F: CircuitField>(scalar: F) -> F {
    let nb_bytes = F::NUM_BITS.div_ceil(8).div_ceil(2) as usize;
    let bytes = scalar.to_bytes_le();
    let mut buffer = vec![0u8; F::NUM_BITS.div_ceil(8) as usize];
    buffer[..nb_bytes].copy_from_slice(&bytes[..nb_bytes]);
    F::from_bytes_le(&buffer).unwrap()
}

/// In-circuit analog of [truncate].
pub(crate) fn truncate<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl NativeInstructions<F>,
    x: &AssignedNative<F>,
) -> Result<AssignedBoundedScalar<F>, Error> {
    // TODO: This could be optimized by splitting in bigger chunks, but it is
    // a bit tricky to maintain consistency with upstream.
    // Also, enforcing canonicity when dividing into bigger chunks is a challenge.
    //
    // TODO: We are dividing into chunks when truncating and then again for the
    // msm. This computation is not being reused. It is hard to combine
    // elegantly though.
    let bits = scalar_chip.assigned_to_le_bits(layouter, x, None, true)?;
    let nb_half_bits = 8 * (F::NUM_BITS.div_ceil(8).div_ceil(2) as usize);
    let scalar = scalar_chip.assigned_from_le_bits(layouter, &bits[..nb_half_bits])?;
    let bound = (BigUint::one() << nb_half_bits) - BigUint::one();
    Ok(AssignedBoundedScalar::new(&scalar, Some(bound)))
}

/// Evaluates the i-th Lagrange polynomial (with respect to the `n`-th root of
/// unity `ω`) at the given point `x`, for all the given `i_indices`. That is,
/// for every `i ∈ i_indices`, computes `L_i(x)` where `L_i(X)` is the
/// degree-`n` polynomial such that `L_i(ωⁱ) = 1` and `L_i(ωʲ) = 0` for all
/// `j ∈ {1, ..., n} \ {i}`.
///
/// The values `w_inv`, `n_inv` and `xn` are taken as arguments (instead of
/// being derived here) so that they can be computed once and shared by all
/// calls over the same domain and evaluation point. It is the caller's
/// responsibility to guarantee that `w_inv = ω⁻¹`, `n_inv = n⁻¹` and `xn = xⁿ`.
///
/// It is also the caller's responsibility to guarantee that `|i| < n` for every
/// `i ∈ i_indices`.
///
/// # Unsatisfiable Circuit
///
/// If x^n = 1.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_lagrange_polynomials<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl FieldInstructions<F, AssignedNative<F>>,
    w: &AssignedNative<F>,
    w_inv: &AssignedNative<F>,
    n_inv: &AssignedNative<F>,
    x: &AssignedNative<F>,
    xn: &AssignedNative<F>,
    i_indices: Range<i32>,
) -> Result<Vec<AssignedNative<F>>, Error> {
    // For every i, L_i(X) := (ωⁱ / n) · (Xⁿ - 1) / (X - ωⁱ).
    let xn_minus_one = scalar_chip.add_constant(layouter, xn, -F::ONE)?;

    i_indices
        .map(|i| {
            let wi = if i >= 0 {
                scalar_chip.pow(layouter, w, i as u64)?
            } else {
                scalar_chip.pow(layouter, w_inv, (-i) as u64)?
            };
            let x_minus_wi = scalar_chip.sub(layouter, x, &wi)?;
            let quotient = scalar_chip.div(layouter, &xn_minus_one, &x_minus_wi)?;
            let wi_over_n = scalar_chip.mul(layouter, &wi, n_inv, None)?;
            scalar_chip.mul(layouter, &quotient, &wi_over_n, None)
        })
        .collect()
}

/// Given n evaluation points {x_i}_i, n evaluations {y_i}_i and a value `q`,
/// returns `(q - f(x)) / Π_i (x - x_i)`.
///
/// Here f is the polynomial of smallest degree such that f(x_i) = y_i for all
/// i in \[n\].
pub fn evaluate_interpolation_quotient<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    points: &[AssignedNative<F>],
    evals: &[AssignedNative<F>],
    x: &AssignedNative<F>,
    q: &AssignedNative<F>,
) -> Result<AssignedNative<F>, Error> {
    assert_eq!(points.len(), evals.len());

    // Assert that the points are pair-wise different.
    for i in 0..points.len() {
        for j in (i + 1)..points.len() {
            scalar_chip.assert_not_equal(layouter, &points[i], &points[j])?;
        }
    }

    let x_minus_xs = points
        .iter()
        .map(|xi| scalar_chip.sub(layouter, x, xi))
        .collect::<Result<Vec<_>, Error>>()?;

    if points.len() == 1 {
        let num = scalar_chip.sub(layouter, q, &evals[0])?;
        return scalar_chip.div(layouter, &num, &x_minus_xs[0]);
    }

    // In factored form, f(x) is
    // `Π_j (x - x_j) · Σ_i y_i / ((x - x_i) Π_{j≠i} (x_i - x_j))`,
    // and the quotient is `q / Π_j (x - x_j)` minus the sum.
    let mut terms = vec![];
    for (i, (xi, yi)) in points.iter().zip(evals).enumerate() {
        let mut den = x_minus_xs[i].clone();
        for (_, xj) in points.iter().enumerate().filter(|(j, _)| *j != i) {
            // den * (xi - xj) computed as den * xi - den * xj
            den = scalar_chip.add_and_double_mul(
                layouter,
                (F::ZERO, &den),
                (F::ZERO, xi),
                (F::ZERO, xj),
                F::ZERO,
                (F::ONE, -F::ONE),
            )?;
        }
        terms.push((-F::ONE, scalar_chip.div(layouter, yi, &den)?));
    }
    let vanishing = prod::<F>(layouter, scalar_chip, &x_minus_xs)?;
    terms.push((F::ONE, scalar_chip.div(layouter, q, &vanishing)?));
    scalar_chip.linear_combination(layouter, &terms, F::ZERO)
}

/// A point `x` and all its `t`-th roots `p`, each with an evaluation:
/// `(x, [(p, eval)])`.
pub(crate) type Coset<F> = (
    AssignedNative<F>,
    Vec<(AssignedNative<F>, AssignedNative<F>)>,
);

/// Given cosets of points with their evaluations and a value `q`, returns
/// `(q - f(z)) / Z(z)`, for `f` the polynomial interpolating the cosets and
/// `Z(X) = Π_j (X^t - x_j)` their vanishing polynomial.
///
/// The `x_j` of the cosets must be distinct and non-zero, otherwise the circuit
/// is unsatisfiable. The Lagrange basis at `p` in coset `j` is
/// `Z(z) p / ((z - p) t x_j Π_{k≠j} (x_j - x_k))`.
///
/// # Panics
///
/// If `cosets` is empty.
pub(crate) fn evaluate_interpolation_quotient_on_cosets<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    t: usize,
    cosets: &[Coset<F>],
    z: &AssignedNative<F>,
    q: &AssignedNative<F>,
) -> Result<AssignedNative<F>, Error> {
    let z_pow_t = scalar_chip.pow(layouter, z, t as u64)?;
    let vanishing_factors = (cosets.iter())
        .map(|(x, _)| scalar_chip.sub(layouter, &z_pow_t, x))
        .collect::<Result<Vec<_>, Error>>()?;
    let vanishing = prod(layouter, scalar_chip, &vanishing_factors)?;

    // f(z) is `Z(z) · Σ_j Σ_p eval_p p / ((z - p) t x_j Π_{k≠j} (x_j - x_k))`,
    // and the quotient is `q / Z(z)` minus the sum.
    let mut terms = Vec::with_capacity(cosets.len() + 1);
    for (j, (xj, coset)) in cosets.iter().enumerate() {
        // Σ_p eval_p p / (z - p)
        let coset_terms = (coset.iter())
            .map(|(p, eval)| {
                let num = scalar_chip.mul(layouter, eval, p, None)?;
                let den = scalar_chip.sub(layouter, z, p)?;
                scalar_chip.div(layouter, &num, &den)
            })
            .collect::<Result<Vec<_>, Error>>()?;
        let coset_sum = sum(layouter, scalar_chip, &coset_terms)?;

        // t x_j Π_{k≠j} (x_j - x_k)
        let mut den = scalar_chip.mul_by_constant(layouter, xj, F::from(t as u64))?;
        for (_, (xk, _)) in cosets.iter().enumerate().filter(|(k, _)| *k != j) {
            let diff = scalar_chip.sub(layouter, xj, xk)?;
            den = scalar_chip.mul(layouter, &den, &diff, None)?;
        }
        terms.push((-F::ONE, scalar_chip.div(layouter, &coset_sum, &den)?));
    }
    terms.push((F::ONE, scalar_chip.div(layouter, q, &vanishing)?));
    scalar_chip.linear_combination(layouter, &terms, F::ZERO)
}

/// Computes the addition of all the given scalars.
pub(crate) fn sum<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    terms: &[AssignedNative<F>],
) -> Result<AssignedNative<F>, Error> {
    let terms = terms.iter().map(|t| (F::ONE, t.clone())).collect::<Vec<_>>();
    scalar_chip.linear_combination(layouter, &terms, F::ZERO)
}

/// Computes the product of all the given scalars.
pub(crate) fn prod<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    terms: &[AssignedNative<F>],
) -> Result<AssignedNative<F>, Error> {
    let mut res = terms[0].clone();
    for term in terms.iter().skip(1) {
        res = scalar_chip.mul(layouter, &res, term, None)?;
    }
    Ok(res)
}

/// Computes the inner product between terms1 and terms2, zero if they are
/// empty.
///
/// # Panics
///
/// If `|terms1| != |terms2|`.
pub(crate) fn inner_product<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    terms1: &[AssignedNative<F>],
    terms2: &[AssignedNative<F>],
) -> Result<AssignedNative<F>, Error> {
    assert_eq!(terms1.len(), terms2.len());

    let mut iter = terms1.iter().zip(terms2.iter());
    let Some((x0, y0)) = iter.next() else {
        return scalar_chip.assign_fixed(layouter, F::ZERO);
    };
    let init = scalar_chip.mul(layouter, x0, y0, None)?;
    iter.try_fold(init, |acc, (xi, yi)| {
        mul_add(layouter, scalar_chip, xi, yi, &acc)
    })
}

/// Computes `2^k` in-circuit, where `k` is an assigned value known to lie in
/// the range `[0, F::S]` (`F::S` is the field's 2-adicity).
pub(crate) fn pow_of_two<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl FieldInstructions<F, AssignedNative<F>>,
    k: &AssignedNative<F>,
) -> Result<AssignedNative<F>, Error> {
    let mut acc: AssignedNative<F> = scalar_chip.assign_fixed(layouter, F::ONE)?;
    let mut result = acc.clone();

    for i in 1..=F::S as usize {
        acc = scalar_chip.add(layouter, &acc, &acc)?;
        let is_k = scalar_chip.is_equal_to_fixed(layouter, k, F::from(i as u64))?;
        result = scalar_chip.select(layouter, &is_k, &acc, &result)?;
    }

    Ok(result)
}

/// Squares `x` `k` times in-circuit, i.e. computes `x^(2^k)`, where `k` is an
/// assigned value known to lie in the range `[0, F::S]` (the field's
/// 2-adicity).
pub(crate) fn square_k_times<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl FieldInstructions<F, AssignedNative<F>>,
    x: &AssignedNative<F>,
    k: &AssignedNative<F>,
) -> Result<AssignedNative<F>, Error> {
    let mut acc = x.clone();
    let mut result = acc.clone();

    for i in 1..=F::S as usize {
        acc = scalar_chip.mul(layouter, &acc, &acc, None)?;
        let is_k = scalar_chip.is_equal_to_fixed(layouter, k, F::from(i as u64))?;
        result = scalar_chip.select(layouter, &is_k, &acc, &result)?;
    }

    Ok(result)
}

/// Computes n powers of the given scalar x, starting from the 0-th power: 1.
pub(crate) fn powers<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    x: &AssignedNative<F>,
    n: usize,
) -> Result<Vec<AssignedNative<F>>, Error> {
    let one = scalar_chip.assign_fixed(layouter, F::ONE)?;
    let mut powers = vec![one];

    let mut acc = x.clone();
    for i in 1..n {
        powers.push(acc.clone());
        if i < n - 1 {
            acc = scalar_chip.mul(layouter, &acc, x, None)?;
        }
    }

    Ok(powers)
}

/// Computes n powers of the given scalar x, starting from the 0-th power: 1.
/// The powers are then truncated by removing their most-significative half.
pub(crate) fn truncated_powers<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl NativeInstructions<F>,
    x: &AssignedNative<F>,
    n: usize,
) -> Result<Vec<AssignedBoundedScalar<F>>, Error> {
    powers::<F>(layouter, scalar_chip, x, n)?
        .iter()
        .enumerate()
        .map(|(i, p)| {
            // The first power is known to be 1.
            if i == 0 {
                scalar_chip.assert_equal_to_fixed(layouter, p, F::ONE)?;
                return Ok(AssignedBoundedScalar::new(p, Some(BigUint::one())));
            }
            truncate::<F>(layouter, scalar_chip, p)
        })
        .collect()
}

/// The "try" analog of `reduce` (just like `try_fold` and `fold`). This has
/// hard-coded the plonk::Error type.
///
/// # Error
///
/// Returns a `Synthesis` error if the iterator is empty.
pub(crate) fn try_reduce<T, F>(iter: impl IntoIterator<Item = T>, f: F) -> Result<T, Error>
where
    F: FnMut(T, T) -> Result<T, Error>,
{
    let mut iterator = iter.into_iter();
    let first = iterator.next().ok_or(Error::Synthesis(
        "try_reduced: iterator must not be empty".into(),
    ))?;
    iterator.try_fold(first, f)
}

/// Computes `x * y + z`.
pub(crate) fn mul_add<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    x: &AssignedNative<F>,
    y: &AssignedNative<F>,
    z: &AssignedNative<F>,
) -> Result<AssignedNative<F>, Error> {
    scalar_chip.add_and_mul(
        layouter,
        (F::ZERO, x),
        (F::ZERO, y),
        (F::ONE, z),
        F::ZERO,
        F::ONE,
    )
}

/// The `t`-th roots of the points computed so far, keyed by the cell of the
/// point and `t`.
///
/// Two chunks opened at the same point must share the very same root cells:
/// the inner multi-open groups the queries by point cell, so distinct cells for
/// equal roots would split a point set that the off-circuit verifier keeps
/// whole.
pub(crate) type RootsCache<F> = HashMap<(AssignedNative<F>, usize), Vec<AssignedNative<F>>>;

/// The roots `[z, z ω_t, ..., z ω_t^{t-1}]` of `x`, for a witness `z`
/// constrained by `z^t = x`, in the order of [`roots`], computed once per `x`
/// and `t` and kept in `cache`.
pub(crate) fn cached_roots<'c, F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    cache: &'c mut RootsCache<F>,
    x: &AssignedNative<F>,
    t: usize,
) -> Result<&'c [AssignedNative<F>], Error> {
    let entry = match cache.entry((x.clone(), t)) {
        Entry::Occupied(entry) => return Ok(entry.into_mut()),
        Entry::Vacant(entry) => entry,
    };

    let z = if t == 1 {
        x.clone()
    } else {
        // A point with no `t`-th root gets 0, which fails `z^t = x`.
        let z = x.value().map(|x| roots(*x, t).map_or(F::ZERO, |roots| roots[0]));
        let z = scalar_chip.assign(layouter, z)?;
        let z_pow_t = scalar_chip.pow(layouter, &z, t as u64)?;
        scalar_chip.assert_equal(layouter, &z_pow_t, x)?;
        z
    };

    let omega_t = root_of_unity::<F>(t);
    let mut roots = vec![z.clone()];
    let mut omega_pow = omega_t;
    for _ in 1..t {
        roots.push(scalar_chip.mul_by_constant(layouter, &z, omega_pow)?);
        omega_pow *= omega_t;
    }

    Ok(entry.insert(roots))
}

/// The primitive `t`-th root of unity of [`cached_roots`].
fn root_of_unity<F: CircuitField>(t: usize) -> F {
    F::ROOT_OF_UNITY.pow_vartime([1u64 << (F::S - t.trailing_zeros())])
}

/// The powers `[z, z^2, ...]` computed so far, keyed by the cell of `z`.
pub(crate) type PowersCache<F> = HashMap<AssignedNative<F>, Vec<AssignedNative<F>>>;

/// `Σ_i r^i coeffs[i]` for every root `r = z ω_t^j` (`j < t`) of
/// [`cached_roots`], computed as `Σ_i ω_t^{ij} (z^i coeffs[i])`: one product
/// per coefficient and one linear combination per root. The powers of `z` are
/// kept in `z_powers`.
pub(crate) fn eval_polynomial_on_roots<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    z_powers: &mut PowersCache<F>,
    coeffs: &[&AssignedNative<F>],
    z: &AssignedNative<F>,
    t: usize,
) -> Result<Vec<AssignedNative<F>>, Error> {
    if coeffs.len() == 1 {
        return Ok(vec![coeffs[0].clone(); t]);
    }
    let z_powers = z_powers.entry(z.clone()).or_insert_with(|| vec![z.clone()]);
    while z_powers.len() < coeffs.len() - 1 {
        let next = scalar_chip.mul(layouter, z_powers.last().unwrap(), z, None)?;
        z_powers.push(next);
    }
    let terms = std::iter::once(Ok(coeffs[0].clone()))
        .chain(
            (coeffs[1..].iter().zip(z_powers.iter()))
                .map(|(c, z_i)| scalar_chip.mul(layouter, c, z_i, None)),
        )
        .collect::<Result<Vec<_>, Error>>()?;
    let omega_t = root_of_unity::<F>(t);
    (0..t as u64)
        .map(|j| {
            let omega_j = omega_t.pow_vartime([j]);
            let lc = (terms.iter().enumerate())
                .map(|(i, a)| (omega_j.pow_vartime([i as u64]), a.clone()))
                .collect::<Vec<_>>();
            scalar_chip.linear_combination(layouter, &lc, F::ZERO)
        })
        .collect()
}
