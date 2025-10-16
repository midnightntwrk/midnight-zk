// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

use std::{cmp::min, ops::Range};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::BigUint;
use num_traits::One;

#[cfg(not(feature = "truncated-challenges"))]
use crate::instructions::FieldInstructions;
#[cfg(feature = "truncated-challenges")]
use crate::instructions::NativeInstructions;
use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    utils::util::modulus,
};

/// An assigned scalar known to be bounded in the range [0, bound].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignedBoundedScalar<F: PrimeField> {
    pub(crate) scalar: AssignedNative<F>,
    pub(crate) bound: BigUint,
}

impl<F: PrimeField> AssignedBoundedScalar<F> {
    /// Creates a new `AssignedBoundedScalar` from an assigned scalar and an
    /// inclusive bound on its value. The bound will default to maximum possible
    /// value of a field element when not provided.
    pub(crate) fn new(scalar: &AssignedNative<F>, bound_opt: Option<BigUint>) -> Self {
        Self {
            scalar: scalar.clone(),
            bound: bound_opt.unwrap_or(modulus::<F>() - BigUint::one()),
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
pub(crate) fn assign_bounded_scalars<F: PrimeField>(
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
pub(crate) fn add_bounded_scalars<F: PrimeField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    x1: &AssignedBoundedScalar<F>,
    x2: &AssignedBoundedScalar<F>,
) -> Result<AssignedBoundedScalar<F>, Error> {
    Ok(AssignedBoundedScalar {
        scalar: scalar_chip.add(layouter, &x1.scalar, &x2.scalar)?,
        bound: min(
            x1.bound.clone() + x2.bound.clone(),
            modulus::<F>() - BigUint::one(),
        ),
    })
}

/// Multiplies the given assigned bounded scalars, updating the bound.
pub fn mul_bounded_scalars<F: PrimeField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    x1: &AssignedBoundedScalar<F>,
    x2: &AssignedBoundedScalar<F>,
) -> Result<AssignedBoundedScalar<F>, Error> {
    Ok(AssignedBoundedScalar {
        scalar: scalar_chip.mul(layouter, &x1.scalar, &x2.scalar, None)?,
        bound: min(
            x1.bound.clone() * x2.bound.clone(),
            modulus::<F>() - BigUint::one(),
        ),
    })
}

/// Truncates a field element by removing its most-significative half.
/// This function is supposed to perform the exact same truncation that
/// halo2 does when `feature = "truncated-challenges"` is enabled.
#[cfg(feature = "truncated-challenges")]
pub(crate) fn truncate_off_circuit<F: PrimeField>(scalar: F) -> F {
    let nb_bytes = F::NUM_BITS.div_ceil(8).div_ceil(2) as usize;
    let bytes = scalar.to_repr().as_ref()[..nb_bytes].to_vec();
    let bi = BigUint::from_bytes_le(&bytes);
    F::from_str_vartime(&BigUint::to_string(&bi)).unwrap()
}

/// In-circuit analog of [truncate].
#[cfg(feature = "truncated-challenges")]
pub(crate) fn truncate<F: PrimeField>(
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

/// Evaluates the i-th Lagrange polynomial (with respect to n-root of unity w)
/// at the given point x, for all the given i. That is, for every i, computes
/// Li(x) where Li(X) is the degree-n polynomial such that Li(w^i) = 1 and
/// Li(w^j) = 0 for all j in {1, ..., n} \ {i}.
///
/// # Unsatisfiable Circuit
///
/// If x^n = 1.
pub fn evaluate_lagrange_polynomials<F: PrimeField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    n: u64,
    w: F,
    i_indices: Range<i32>,
    x: &AssignedNative<F>,
) -> Result<Vec<AssignedNative<F>>, Error> {
    // For every i, Li(X) := (w^i / n) * (X^n - 1) / (X - w^i).

    let n_inv = F::from(n).invert().unwrap();
    let xn = scalar_chip.pow(layouter, x, n)?;
    let xn_minus_one = scalar_chip.add_constant(layouter, &xn, -F::ONE)?;

    i_indices
        .map(|i| {
            assert!(-(n as i32) <= i);
            let i = if i < 0 { n as i32 + i } else { i };
            let wi = w.pow([i as u64, 0, 0, 0]);
            let x_minus_wi = scalar_chip.add_constant(layouter, x, -wi)?;
            let quotient = scalar_chip.div(layouter, &xn_minus_one, &x_minus_wi)?;
            scalar_chip.mul_by_constant(layouter, &quotient, wi * n_inv)
        })
        .collect()
}

/// Given n evaluation points {x_i}_i and n evaluations {y_i}_i, returns the
/// evaluation at x of the minimal polynomial that interpolates them.
///
/// That is, let f be the polynomial of smallest degree such that f(x_i) = y_i
/// for all i in \[n\]. This function returns f(x).
pub fn evaluate_interpolated_polynomial<F: PrimeField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    points: &[AssignedNative<F>],
    evals: &[AssignedNative<F>],
    x: &AssignedNative<F>,
) -> Result<AssignedNative<F>, Error> {
    assert_eq!(points.len(), evals.len());

    // Assert that the points are pair-wise different.
    for i in 0..points.len() {
        for j in (i + 1)..points.len() {
            scalar_chip.assert_not_equal(layouter, &points[i], &points[j])?;
        }
    }

    if points.len() == 1 {
        return Ok(evals[0].clone());
    }

    // Compute the Lagrange bases L_j evaluated at x.
    let mut lj_s = vec![];
    let x_minus_xs = points
        .iter()
        .map(|xi| scalar_chip.sub(layouter, x, xi))
        .collect::<Result<Vec<_>, Error>>()?;
    for (j, xj) in points.iter().enumerate() {
        let mut num_terms = vec![];
        let mut den_terms = vec![];
        for (i, xi) in points.iter().enumerate() {
            if i != j {
                num_terms.push(x_minus_xs[i].clone());
                den_terms.push(scalar_chip.sub(layouter, xj, xi)?);
            }
        }
        let num = prod::<F>(layouter, scalar_chip, &num_terms)?;
        let den = prod::<F>(layouter, scalar_chip, &den_terms)?;
        lj_s.push(scalar_chip.div(layouter, &num, &den)?);
    }

    inner_product(layouter, scalar_chip, &lj_s, evals)
}

/// Computes the addition of all the given scalars.
pub(crate) fn sum<F: PrimeField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    terms: &[AssignedNative<F>],
) -> Result<AssignedNative<F>, Error> {
    let terms = terms.iter().map(|t| (F::ONE, t.clone())).collect::<Vec<_>>();
    scalar_chip.linear_combination(layouter, &terms, F::ZERO)
}

/// Computes the product of all the given scalars.
pub(crate) fn prod<F: PrimeField>(
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

/// Computes the inner product between terms1 and terms2.
///
/// # Panics
///
/// If `terms1` is empty or `|terms1| != |terms2|`.
pub(crate) fn inner_product<F: PrimeField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    terms1: &[AssignedNative<F>],
    terms2: &[AssignedNative<F>],
) -> Result<AssignedNative<F>, Error> {
    assert_eq!(terms1.len(), terms2.len());

    let mut iter = terms1.iter().zip(terms2.iter());
    let (x0, y0) = iter.next().expect("inner_product received an empty input");
    let init = scalar_chip.mul(layouter, x0, y0, None)?;
    iter.try_fold(init, |acc, (xi, yi)| {
        mul_add(layouter, scalar_chip, xi, yi, &acc)
    })
}

/// Computes n powers of the given scalar x, starting from the 0-th power: 1.
pub(crate) fn powers<F: PrimeField>(
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
pub(crate) fn truncated_powers<F: PrimeField>(
    layouter: &mut impl Layouter<F>,
    #[cfg(feature = "truncated-challenges")] scalar_chip: &impl NativeInstructions<F>,
    #[cfg(not(feature = "truncated-challenges"))] scalar_chip: &impl FieldInstructions<
        F,
        AssignedNative<F>,
    >,
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
            #[cfg(feature = "truncated-challenges")]
            return truncate::<F>(layouter, scalar_chip, p);
            #[cfg(not(feature = "truncated-challenges"))]
            return Ok(AssignedBoundedScalar::new(p, None));
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
pub(crate) fn mul_add<F: PrimeField>(
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

/// The minimum number of digits necessary to represent the given integer.
/// Examples:
///  * `num_digits(0) = 1`
///  * `num_digits(1) = 1`
///  * `num_digits(9) = 1`
///  * `num_digits(10) = 2`
///  * `num_digits(99) = 2`
///  * `num_digits(100) = 3`
pub(crate) fn num_digits(mut n: usize) -> usize {
    let mut digits = 1;
    while n >= 10 {
        n /= 10;
        digits += 1;
    }
    digits
}
