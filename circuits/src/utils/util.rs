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

// TODO: We should add docs to all of this utilities.
#![allow(missing_docs)]

use ff::PrimeField;
use num_bigint::{BigInt as BI, BigUint, Sign};
use num_integer::Integer;
use num_traits::{Num, One, Signed, Zero};
#[cfg(any(test, feature = "testing"))]
use {
    midnight_proofs::circuit::Layouter,
    midnight_proofs::plonk::{Column, ConstraintSystem, Instance},
};

pub fn modulus<F: PrimeField>() -> BigUint {
    BigUint::from_str_radix(&F::MODULUS[2..], 16).unwrap()
}

/// Returns a quadratic non-residue of the given field.
pub fn qnr<F: PrimeField>() -> F {
    debug_assert!(bool::from(F::MULTIPLICATIVE_GENERATOR.sqrt().is_none()));
    F::MULTIPLICATIVE_GENERATOR
}

pub fn big_to_fe<F: PrimeField>(e: BigUint) -> F {
    let modulus = modulus::<F>();
    let e = e % modulus;
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

pub fn fe_to_big<F: PrimeField>(fe: F) -> BigUint {
    BigUint::from_bytes_le(fe.to_repr().as_ref())
}

pub fn bigint_to_fe<F: PrimeField>(value: &BI) -> F {
    let f = F::from_str_vartime(&BI::to_string(&value.abs())).unwrap();
    if value.is_negative() {
        F::neg(f)
    } else {
        f
    }
}

pub fn fe_to_bigint<F: PrimeField>(value: &F) -> BI {
    BI::from_bytes_le(Sign::Plus, F::to_repr(value).as_ref())
}

/// Decompose the given field element into little-endian bits.
///
/// - If `nb_bits = None`, the output will have as many bits as necessary to
///   represent the given element, but no more.
/// - If `nb_bits` is provided, the output will have the specified length,
///   possibly with trailing zeros.
///
/// # Panics
///
/// If `nb_bits` is given but this value is smaller than the minimum number of
/// bits necessary to represent the given element.
pub fn fe_to_le_bits<F: PrimeField>(value: &F, nb_bits: Option<usize>) -> Vec<bool> {
    let big = fe_to_big(*value);
    let mut bits: Vec<bool> = (0..big.bits()).map(|i| big.bit(i)).collect();
    if let Some(n) = nb_bits {
        assert!(n >= bits.len());
        bits.resize(n, false);
    }
    bits
}

/// The field element represented by an L-bit little-endian bitstring.
///
/// # Panics
///
/// Panics if the bitstring is longer than `F::NUM_BITS`.
pub fn le_bits_to_field_elem<F: PrimeField>(bits: &[bool]) -> F {
    assert!(
        bits.len() as u32 <= F::NUM_BITS,
        "{} > {}",
        bits.len(),
        F::NUM_BITS
    );

    let mut repr = F::from(0).to_repr();
    let view = repr.as_mut();

    let bytes = bits.chunks(8).map(|bits| {
        bits.iter()
            .enumerate()
            .fold(0u8, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
    });
    for (byte, repr) in bytes.zip(view.iter_mut()) {
        *repr = byte
    }

    F::from_repr(repr).unwrap()
}

/// Given a slice of vectors, returns the concatenation of all of them in order.
#[inline]
pub fn concat<T: Clone>(chunks: &[Vec<T>]) -> Vec<T> {
    chunks.iter().flatten().cloned().collect()
}

/// Off-circuit GLV scalar decomposition.
/// Given a scalar `x`, and the cubic-root `zeta`, returns `(s1, x1), (s2, x2)`
/// with x = ±x1 + zeta * (±x2), where the sign in front of `x1`
/// (resp. `x2`) depends on `s1` (resp. `s2`) as `+ if s1 else -`.
///
/// The resulting `x1` and `x2` are half-size, i.e. they can be expressed
/// with at most `ceil(F::NUM_BITS / 2)` bits.
pub fn glv_scalar_decomposition<F: PrimeField>(x: &F, zeta: &F) -> ((bool, F), (bool, F)) {
    // We follow Algorithm 3.74 from "Guide to Elliptic Curve Cryptography",
    // Hankerson, Menezes, Vanstone, 2004.

    let n: BI = modulus::<F>().into();
    let lambda = fe_to_bigint(zeta);
    let k = fe_to_bigint(x);

    // xgcd:
    //  Input: Positive integers a, b with a >= b.
    // Output: Three sequences r, s, t such that for every i,
    //         si * a + ti * b = ri
    //         and (r0, s0, t0) = (a, 1, 0)
    //         and (r1, s1, t1) = (b, 0, 1)
    let xgcd = |a: &BI, b: &BI| -> (Vec<BI>, Vec<BI>, Vec<BI>) {
        let mut rs = vec![a.clone(), b.clone()];
        let mut ss = vec![BI::one(), BI::zero()];
        let mut ts = vec![BI::zero(), BI::one()];

        loop {
            if rs[rs.len() - 1].is_zero() {
                break;
            }

            let q = rs[rs.len() - 2].clone() / rs[rs.len() - 1].clone();
            let r = rs[rs.len() - 2].clone() % rs[rs.len() - 1].clone();
            let s = ss[rs.len() - 2].clone() - q.clone() * ss[rs.len() - 1].clone();
            let t = ts[rs.len() - 2].clone() - q.clone() * ts[rs.len() - 1].clone();

            rs.push(r);
            ss.push(s);
            ts.push(t);
        }

        (rs, ss, ts)
    };

    let (rs, _ss, ts) = xgcd(&n, &lambda);

    // Let l be the greatest index such that rs[l] >= sqrt(n).
    let l = rs.iter().position(|r: &BI| r.pow(2) < n).unwrap() - 1;

    let cond = rs[l].pow(2) + ts[l].pow(2) <= rs[l + 2].pow(2) + ts[l + 2].pow(2);
    let ll = if cond { l } else { l + 2 };

    let a1 = rs[l + 1].clone();
    let b1 = -ts[l + 1].clone();
    let a2 = rs[ll].clone();
    let b2 = -ts[ll].clone();

    let div_with_rounding = |a: &BI, b: &BI| -> BI {
        let (q, r) = a.div_rem(b);
        q + BI::from(if r.clone() + r > b.clone() { 1 } else { 0 })
    };

    let c1 = div_with_rounding(&(b2.clone() * k.clone()), &n);
    let c2 = div_with_rounding(&(-b1.clone() * k.clone()), &n);

    let k1 = k - c1.clone() * a1 - c2.clone() * a2;
    let k2 = -c1 * b1 - c2 * b2;

    let s1 = k1.is_positive();
    let s2 = k2.is_positive();
    let x1 = if s1 { k1 } else { -k1 };
    let x2 = if s2 { k2 } else { -k2 };

    // Throw an error if the x1 or x2 do not fit in the desired number of bits.
    // This should never happen. Anyway, if this could happen, that would be a
    // completeness issue (not soundness).
    let max_length = F::NUM_BITS.div_ceil(2) as u64;
    if x1.bits() > max_length || x2.bits() > max_length {
        panic!(
            "Oops, an error occurred in GLV decomposition. \
             Please, open an issue to report this problem: \
             https://github.com/midnightntwrk/midnight-circuits/issues"
        )
    };

    ((s1, bigint_to_fe(&x1)), (s2, bigint_to_fe(&x2)))
}

/// A temporary trait (until David's work on Composable Chips is finished) to
/// create chips from scratch.
#[cfg(any(test, feature = "testing"))]
pub trait FromScratch<F: PrimeField> {
    type Config: Clone + std::fmt::Debug;

    fn new_from_scratch(config: &Self::Config) -> Self;

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config;

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config);
}
