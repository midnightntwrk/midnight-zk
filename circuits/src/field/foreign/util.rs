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

// Util functions of the foreign arithmetic module

use std::ops::{Mul, Rem};

use ff::PrimeField;
use midnight_proofs::{
    circuit::Value,
    plonk::{Advice, Column, Expression, VirtualCells},
    poly::Rotation,
};
use num_bigint::{BigInt as BI, BigUint, ToBigInt};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use crate::utils::util::{bigint_to_fe, modulus};

/// Like .rem, but gives positive answers only.
pub fn urem(value: &BI, modulus: &BI) -> BI {
    let mut output = value.rem(modulus);
    if output.is_negative() {
        output += modulus;
    }
    output
}

/// Computes the logarithm in base 2 of the given value, rounded up.
pub fn ceil_log2(value: &BI) -> u32 {
    BI::bits(&(value - BI::one())) as u32
}

/// Computes the smallest n such that 2^n is >= the given value.
pub fn next_power_of_two(value: &BI) -> BI {
    BI::pow(&BI::from(2), ceil_log2(value))
}

/// Breaks the given `value` into `nb_limbs` limbs representing the value in the
/// given `base` (in little-endian).
/// Panics if the given value is negative or if the conversion is not possible.
pub fn bi_to_limbs(nb_limbs: u32, base: &BI, value: &BI) -> Vec<BI> {
    if value.is_negative() {
        panic!("bi_to_limbs: value must be greater than or equal to zero");
    }

    let mut output = vec![];
    let mut q = (*value).clone();
    let mut r;
    while output.len() < nb_limbs as usize {
        (q, r) = q.div_rem(base);
        output.push(r.clone());
    }
    if !BI::is_zero(&q) {
        panic!(
            "bi_to_limbs: {} cannot be expressed in base {} with {} limbs",
            value, base, nb_limbs
        )
    };
    output
}

/// Returns the (positive) BigInt represented by the given `limbs`, parsing them
/// in the given `base`, in little-endian.
pub fn bi_from_limbs(base: &BI, limbs: &[BI]) -> BI {
    limbs
        .iter()
        .rev()
        .fold(BI::zero(), |acc, limb| acc * base + limb)
}

/// Breaks the given `value` into `nb_limbs` limbs representing the value in the
/// given `base` (in little-endian).
/// Panics if the conversion is not possible.
pub fn big_to_limbs(nb_limbs: u32, base: &BigUint, value: &BigUint) -> Vec<BigUint> {
    let mut output = vec![];
    let mut q = (*value).clone();
    let mut r;
    while output.len() < nb_limbs as usize {
        (q, r) = q.div_rem(base);
        output.push(r.clone());
    }
    if !BigUint::is_zero(&q) {
        panic!(
            "big_to_limbs: {} cannot be expressed in base {} with {} limbs",
            value, base, nb_limbs
        )
    };
    output
}

/// Returns the BigUint represented by the given `limbs`, parsing them
/// in the given `base`, in little-endian.
pub fn big_from_limbs(base: &BigUint, limbs: &[BigUint]) -> BigUint {
    limbs
        .iter()
        .rev()
        .fold(BigUint::zero(), |acc, limb| acc * base + limb)
}

/// Sum the given `coeffs` pair-wise multiplied by the given `values`.
pub fn sum_bigints(coeffs: &[BI], values: &[BI]) -> BI {
    debug_assert!(coeffs.len() == values.len());
    values
        .iter()
        .zip(coeffs.iter())
        .map(|(v, b)| b * v)
        .sum::<BI>()
}

/// Same as [sum_bigints], but adds `Expressions<F>`.
pub fn sum_exprs<F: PrimeField>(coeffs: &[BI], exprs: &[Expression<F>]) -> Expression<F> {
    debug_assert!(coeffs.len() == exprs.len());
    exprs
        .iter()
        .zip(coeffs.iter())
        .map(|(v, b)| Expression::Constant(bigint_to_fe::<F>(b)) * v.clone())
        .fold(Expression::Constant(F::ZERO), |acc, e| acc + e)
}

/// On input `v`, `w`, returns `z : Vec<T>` with `z_i = v_i * w_i` for all `i`.
pub fn pair_wise_prod<T: Mul<Output = T> + Clone>(v: &[T], w: &[T]) -> Vec<T> {
    v.iter()
        .flat_map(|vi| {
            w.iter()
                .map(|wj| vi.clone() * wj.clone())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}

/// Fetches a the expressions contained in a vector of columns at the given
/// rotation with respect to the current offset.
pub fn get_advice_vec<F: PrimeField>(
    meta: &mut VirtualCells<'_, F>,
    columns: &[Column<Advice>],
    rotation: Rotation,
) -> Vec<Expression<F>> {
    columns
        .iter()
        .map(|&col| meta.query_advice(col, rotation))
        .collect::<Vec<_>>()
}

/// Checks that the FieldEmulationParams are sound for implementing an emulated
/// gate expressed as `expr_bounds` and `expr_mj_bounds`.
/// Returns (k_min, u_max), {(lj_min, vj_max)}_j, which are parameters involved
/// in the identities enforced by the emulated arithmetic custom gate. We refer
/// to the implementation of this function for explanations on what such values
/// represent.
pub fn get_identity_auxiliary_bounds<F, K>(
    equation_name: &str,
    moduli: &[BI],
    expr_bounds: (BI, BI),
    expr_mj_bounds: &[(BI, BI)],
) -> ((BI, BI), Vec<(BI, BI)>)
where
    F: PrimeField,
    K: PrimeField,
{
    let m = &modulus::<K>().to_bigint().unwrap();
    let native_modulus = &modulus::<F>().to_bigint().unwrap();
    // We enforce expr = 0 (mod m) with the equation expr = k * m
    //
    // expr_bounds := (expr_min, expr_max) contain lower and upper bounds
    // respectively on the value that expr can take. We can use them to bound the
    // value of k.
    let k_min = expr_bounds.0.div_ceil(m);
    let k_max = expr_bounds.1.div_floor(m);

    // By defining u := k - k_min, we can express the above equation as:
    //  expr = (u + k_min) * m
    //
    // The advantage of this is that now u is restricted in the range [0, u_max),
    // (for any u_max > k_max - k_min), a constraint that can be enforced through
    // range-checks.
    let u_max = next_power_of_two(&(&k_max - &k_min + BI::one()));

    // Now, assuming u is restricted in [0, u_max), we will bound the amount:
    //  expr - (u + k_min) * m
    //
    //  lower_bound:  expr_bounds.0 - (u_max + k_min) * m
    //  upper_bound:  expr_bounds.1 - k_min * m

    // If we define M := {native_modulus, moduli}, and lcm(M) > |lower_bound|,
    // lcm(M) > upper_bound, then a solution modulo lcm(M) implies a solution over
    // the integers.
    let lower_bound = expr_bounds.0 - (&u_max + &k_min) * m;
    let upper_bound = expr_bounds.1 - &k_min * m;

    // We take moduli until the lcm threshold is is exceeded
    let mut necessary_moduli = vec![];
    let mut lcm = native_modulus.clone();
    for mj in moduli.iter() {
        if lcm > -&lower_bound && lcm > upper_bound {
            break;
        }
        lcm = lcm.lcm(mj);
        necessary_moduli.push(mj.clone());
    }
    if lcm <= -lower_bound || lcm <= upper_bound {
        panic!("lcm-threshold not reached, consider using extra auxiliari moduli")
    }

    // In order to enforce the above equation modulo lcm(M), we need to enforce
    // the following equation for every mj in M:
    //  expr_mj - u * (m % mj) - (k_min * m) % mj = lj * mj ,
    //
    // with the exception of the native modulus, p, for which we can directly check:
    //  expr - (u + k_min) * m =_p 0 .
    //
    // Here, expr_mj is an expression equivalent to expr (mod mj), obtained by
    // possibly having reduced the coefficients of expr modulo mj.
    // The slice expr_mj_bounds contain lower and upper bound pairs on the values of
    // expr_mj, for every mj.
    //
    // We can bound the value of every auxiliary variable lj as:
    //  lj_min := (expr_mj_min - u_max * (m % mj) - (k_min * m) % mj ) / mj
    //  lj_max := (expr_mj_max - (k_min * m) % mj ) / mj
    //
    // Note that k_min is negative, so we must consider it when computing lj_max.
    // On the other hand, we do not have to consider it when computing lj_min, but
    // we choose to do it because it leads to a better ("less negative") bound.
    let v_bounds: Vec<_> = necessary_moduli
        .iter()
        .zip(expr_mj_bounds.iter())
        .map(|(mj, (expr_mj_min, expr_mj_max))| {
            let k_min_m_mod_mj = urem(&(&k_min * m), mj);
            let lj_min = (expr_mj_min - &u_max * urem(m, mj) - &k_min_m_mod_mj).div_ceil(mj);
            let lj_max = (expr_mj_max - &k_min_m_mod_mj).div_floor(mj);

            // As before, by defining vj := lj - lj_min, we can express the equation as:
            //  expr_mj - u * (m % mj) - (k_min * m) % mj = (vj + lj_min) * mj
            //
            // Now, vj can be restricted in the range [0, vj_max),
            // (for any vj_max > lj_max - lj_min).
            let vj_max = next_power_of_two(&(&lj_max - &lj_min + BI::one()));

            // Now, assuming vj is restricted in [0, vj_max), we will bound the amount:
            //  expr_mj - u * (m % mj) - (k_min * m) % mj - (vj + lj_min) * mj

            let lower_bound =
                expr_mj_min - &u_max * urem(m, mj) - &k_min_m_mod_mj - (&vj_max + &lj_min) * mj;

            let upper_bound = expr_mj_max - &k_min_m_mod_mj - &lj_min * mj;

            // Assert that there will be no wrap-around when checking the equality mod mj.
            if *native_modulus <= -lower_bound || *native_modulus <= upper_bound {
                panic!(
                    "Equation {} modulo {} may wrap-around the native modulus",
                    equation_name, mj
                )
            }
            (lj_min, vj_max)
        })
        .collect();
    ((k_min, u_max), v_bounds)
}

pub fn compute_u(m: &BI, expr: &BI, u_bounds: (&BI, &BI), _assertions: Value<bool>) -> BI {
    // expr = (u + k_min) * m
    let (k_min, _u_max) = u_bounds;
    let (u_plus_k_min, _r) = expr.div_rem(m);
    // The following sanity-check is disabled for tests so that we can have negative
    // tests that do not get interrupted here.
    #[cfg(not(test))]
    _assertions.map(|b| {
        if b {
            let u = u_plus_k_min.clone() - k_min;
            debug_assert!(BI::is_zero(&_r));
            debug_assert!(!BI::is_negative(&u));
            debug_assert!(&u < _u_max);
        }
    });
    u_plus_k_min - k_min
}

pub fn compute_vj(
    m: &BI,
    mj: &BI,
    expr_mj: &BI,
    u: &BI,
    k_min: &BI,
    vj_bounds: (&BI, &BI),
    _assertions: Value<bool>,
) -> BI {
    // expr_mj - u * (m % mj) - (k_min * m) % mj = (vj + lj_min) * mj
    let (lj_min, _vj_max) = vj_bounds;
    let (vj_plus_lj_min, _r) = (expr_mj - u * urem(m, mj) - urem(&(k_min * m), mj)).div_rem(mj);
    #[cfg(not(test))]
    _assertions.map(|b| {
        if b {
            let vj = &vj_plus_lj_min - lj_min;
            debug_assert!(BI::is_zero(&_r));
            debug_assert!(!BI::is_negative(&vj));
            debug_assert!(&vj < _vj_max);
        }
    });
    &vj_plus_lj_min - lj_min
}
