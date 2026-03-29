// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use ff::PrimeField;
use midnight_proofs::plonk::Expression;

/// Mask for selecting even bits in u64 (little-endian representation).
pub const MASK_EVN_64: u64 = 0x5555_5555_5555_5555; // 010101...01 (even positions in u64)

/// Mask for selecting odd bits in u64 (little-endian representation).
pub const MASK_ODD_64: u64 = 0xAAAA_AAAA_AAAA_AAAA; // 101010...10 (odd positions in u64)

/// Returns the even and odd bits of little-endian binary representation of u64.
pub fn get_even_and_odd_bits(value: u64) -> (u32, u32) {
    (compact_even(value), compact_even(value >> 1))
}

/// Compacts the even bits of the u64 into the least-significant u32 half.
fn compact_even(mut x: u64) -> u32 {
    x &= MASK_EVN_64;
    x = (x | (x >> 1)) & 0x3333_3333_3333_3333;
    x = (x | (x >> 2)) & 0x0f0f_0f0f_0f0f_0f0f;
    x = (x | (x >> 4)) & 0x00ff_00ff_00ff_00ff;
    x = (x | (x >> 8)) & 0x0000_ffff_0000_ffff;
    x = (x | (x >> 16)) & 0x0000_0000_ffff_ffff;
    x as u32
}

/// Asserts x is in correct spreaded form, i.e. its little-endian binary
/// representation has zeros in odd positions.
pub fn assert_in_valid_spreaded_form(x: u64) {
    assert_eq!(MASK_ODD_64 & x, 0, "Input must be in valid spreaded form")
}

/// Spreads the input value, which is by definition inserting a zero between all
/// its bits: [bn, ..., b1, b0] ->  [0, bn,..., 0, b1, 0, b0].
pub fn spread(x: u32) -> u64 {
    (0..32).fold(0u64, |acc, i| acc | (((x as u64 >> i) & 1) << (2 * i)))
}

/// Negates the even bits of u64 (in little-endian representation).
///
/// # Panics
///
/// If the input is not in clean spreaded form.
pub fn negate_spreaded(x: u64) -> u64 {
    assert_in_valid_spreaded_form(x);
    x ^ MASK_EVN_64
}

/// Breaks the 32-bit value into big-endian limbs following the required limb lengths.
///
/// This function is generic over the length type to support both `u8` and `usize`.
/// It also supports zero-length segments.
///
/// # Panics
///
/// If sum(limb_lengths) != 32.
pub fn u32_to_be_limbs<const N: usize>(value: u32, limb_lengths: [usize; N]) -> [u32; N] {
    let mut sum = 0;
    for &len in &limb_lengths {
        sum += len;
    }
    assert_eq!(sum, 32, "Sum of limb lengths must be 32 (got {})", sum);

    let mut result = [0u32; N];
    let mut shift = 32;

    for (i, &len) in limb_lengths.iter().enumerate() {
        if len != 0 {
            shift -= len as u32;
            result[i] = (value >> shift) & (((1u64 << len) - 1) as u32);
        } else {
            result[i] = 0;
        }
    }

    result
}

/// Generates the plain-spreaded lookup table for the given bit lengths.
pub fn gen_spread_table<F: PrimeField>(
    lengths: impl IntoIterator<Item = u32>,
) -> impl Iterator<Item = (F, F, F)> {
    lengths.into_iter().flat_map(|len| {
        let tag = F::from(len as u64);
        (0..(1 << len)).map(move |i| (tag, F::from(i as u64), F::from(spread(i as u32))))
    })
}

/// Returns sum_i 2^(exponents[i]) * terms[i].
pub fn expr_pow2_ip<F: PrimeField, const N: usize>(
    exponents: [u8; N],
    terms: [&Expression<F>; N],
) -> Expression<F> {
    let mut expr = Expression::Constant(F::ZERO);
    for (pow, term) in exponents.into_iter().zip(terms.into_iter()) {
        expr = expr + Expression::Constant(F::from(1 << pow)) * term.clone();
    }
    expr
}

/// Returns sum_i 4^(exponents[i]) * terms[i].
pub fn expr_pow4_ip<F: PrimeField, const N: usize>(
    exponents: [u8; N],
    terms: [&Expression<F>; N],
) -> Expression<F> {
    expr_pow2_ip(exponents.map(|l| 2 * l), terms)
}

#[cfg(test)]
mod tests {
    use super::*;

    type F = midnight_curves::Fq;

    #[test]
    fn test_compact_even() {
        assert_eq!(compact_even(0x5555_5555_5555_5555), 0xffff_ffff);
        assert_eq!(compact_even(0x0000_0000_0000_0001), 1);
        assert_eq!(compact_even(0x0000_0000_0000_0004), 2);
        assert_eq!(compact_even(0), 0);
    }

    #[test]
    fn test_get_even_and_odd_bits() {
        assert_eq!(
            get_even_and_odd_bits(0x5555_5555_5555_5555),
            (0xffff_ffff, 0)
        );
        assert_eq!(
            get_even_and_odd_bits(0xAAAA_AAAA_AAAA_AAAA),
            (0, 0xffff_ffff)
        );
        assert_eq!(get_even_and_odd_bits(0), (0, 0));
        assert_eq!(get_even_and_odd_bits(0x3), (1, 1));
    }

    #[test]
    fn test_spread() {
        assert_eq!(spread(0xffff_ffff), 0x5555_5555_5555_5555);
        assert_eq!(spread(0), 0);
        assert_eq!(spread(1), 1);
        assert_eq!(spread(2), 4);
        assert_eq!(spread(3), 5);
    }

    #[test]
    fn test_negate_spreaded() {
        assert_eq!(negate_spreaded(0), MASK_EVN_64);
        assert_eq!(negate_spreaded(MASK_EVN_64), 0);
        assert_eq!(negate_spreaded(1), MASK_EVN_64 ^ 1);
    }

    #[test]
    #[should_panic(expected = "Input must be in valid spreaded form")]
    fn test_negate_spreaded_panic() {
        negate_spreaded(2); // bit 1 is set, which is an odd position
    }

    #[test]
    fn test_u32_to_be_limbs() {
        let value = 0x12345678u32;
        assert_eq!(
            u32_to_be_limbs(value, [8, 8, 8, 8]),
            [0x12, 0x34, 0x56, 0x78]
        );
        assert_eq!(
            u32_to_be_limbs(value, [4, 4, 4, 4, 4, 4, 4, 4]),
            [0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8]
        );
        assert_eq!(
            u32_to_be_limbs(value, [0, 16, 0, 16, 0]),
            [0, 0x1234, 0, 0x5678, 0]
        );
        assert_eq!(u32_to_be_limbs(0, [10, 10, 12]), [0, 0, 0]);
        assert_eq!(u32_to_be_limbs(0xffff_ffff, [32]), [0xffff_ffff]);
    }

    #[test]
    #[should_panic]
    fn test_u32_to_be_limbs_panic_sum() {
        u32_to_be_limbs(0, [10, 10, 10]); // sum is 30 != 32
    }

    #[test]
    fn test_expr_pow2_ip() {
        let c1 = Expression::<F>::Constant(F::from(10));
        let c2 = Expression::<F>::Constant(F::from(20));
        let expr = expr_pow2_ip([0, 1], [&c1, &c2]);
        // expect symbolic: 10 + 2 * 20
        let expected = Expression::Constant(F::from(10))
            + Expression::Constant(F::from(2)) * Expression::Constant(F::from(20));
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_expr_pow4_ip() {
        let c1 = Expression::<F>::Constant(F::from(10));
        let c2 = Expression::<F>::Constant(F::from(20));
        let expr = expr_pow4_ip([0, 1], [&c1, &c2]);
        // expect symbolic: 10 + 4 * 20
        let expected = Expression::Constant(F::from(10))
            + Expression::Constant(F::from(4)) * Expression::Constant(F::from(20));
        assert_eq!(expr, expected);
    }
}
