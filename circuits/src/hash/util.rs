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

use ff::PrimeField;
use midnight_proofs::plonk::Expression;

/// Mask for selecting even bits in u64 (little-endian representation).
pub const MASK_EVN_64: u64 = 0x5555_5555_5555_5555; // 010101...01 (even positions in u64)

/// Mask for selecting odd bits in u64 (little-endian representation).
pub const MASK_ODD_64: u64 = 0xAAAA_AAAA_AAAA_AAAA; // 101010...10 (odd positions in u64)

/// Returns the even and odd bits of little-endian binary representation of
/// u64.
pub fn get_even_and_odd_bits(value: u64) -> (u32, u32) {
    (compact_even(value), compact_even(value >> 1))
}

/// Compacts the even bits of the u64 into the least-significant u32 half.
fn compact_even(mut x: u64) -> u32 {
    x &= 0x5555_5555_5555_5555;
    x = (x | (x >> 1)) & 0x3333_3333_3333_3333;
    x = (x | (x >> 2)) & 0x0f0f_0f0f_0f0f_0f0f;
    x = (x | (x >> 4)) & 0x00ff_00ff_00ff_00ff;
    x = (x | (x >> 8)) & 0x0000_ffff_0000_ffff;
    x = (x | (x >> 16)) & 0x0000_0000_ffff_ffff;
    x as u32
}

/// Asserts x is in correct spreaded form, i.e. its little-endian binary
/// representation has zeros in odd positions.
///
/// # Panics
///
/// If the input is not in clean spreaded form.
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

/// Breaks the 32-bit value into big-endian limbs following the required limb
/// lengths.
///
/// # Panics
///
/// If sum(limb_lengths) != 32.
pub fn u32_in_be_limbs<const N: usize>(value: u32, limb_lengths: [u8; N]) -> [u32; N] {
    assert_eq!(limb_lengths.iter().map(|&l| l as usize).sum::<usize>(), 32);

    let mut result = [0u32; N];
    let mut shift = 32;

    for (i, &len) in limb_lengths.iter().enumerate() {
        if len != 0 {
            shift -= len as u32;
            result[i] = (value >> shift) & ((1 << len) - 1);
        } else {
            result[i] = 0;
        }
    }

    result
}

/// Returns sum_i 2^(exponents\[i\]) * terms\[i\].
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

/// Returns sum_i 4^(exponents\[i\]) * terms\[i\].
pub fn expr_pow4_ip<F: PrimeField, const N: usize>(
    exponents: [u8; N],
    terms: [&Expression<F>; N],
) -> Expression<F> {
    expr_pow2_ip(exponents.map(|l| 2 * l), terms)
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    #[test]
    fn test_get_even_and_odd_bits() {
        [
            (0, 0, 0),
            (1, 1, 0),
            (2, 0, 1),
            (1 << 3, 0, 2),
            (u64::MAX, 0xFFFF_FFFF, 0xFFFF_FFFF),
            (MASK_EVN_64, 0xFFFF_FFFF, 0),
            (MASK_ODD_64, 0, 0xFFFF_FFFF),
            (0b110101101u64, 19, 14),
        ]
        .into_iter()
        .for_each(|(n, expected_even, expected_odd)| {
            let (even, odd) = get_even_and_odd_bits(n);
            assert_eq!(even, expected_even);
            assert_eq!(odd, expected_odd);
        });
    }

    #[test]
    fn test_spread() {
        [(0, 0), (1, 1), (0b10, 0b0100), (0b11, 0b0101)]
            .into_iter()
            .for_each(|(plain, spreaded)| assert_eq!(spread(plain), spreaded));
    }

    #[test]
    fn test_negate_spreaded() {
        // Positive tests
        assert_eq!(negate_spreaded(MASK_EVN_64), 0);
        assert_eq!(negate_spreaded(1), MASK_EVN_64 - 1);
        // Negative tests
        assert_ne!(negate_spreaded(0), 0);
    }

    #[test]
    fn test_u32_in_be_limbs() {
        [
            (0x12345678u32, [8, 8, 8, 8], [0x12, 0x34, 0x56, 0x78]),
            (0x12345678u32, [4, 8, 12, 8], [0x1, 0x23, 0x456, 0x78]),
            (0x12345678u32, [0, 8, 16, 8], [0, 0x12, 0x3456, 0x78]), // test zero length
        ]
        .into_iter()
        .for_each(|(value, limb_lengths, expected)| {
            assert_eq!(u32_in_be_limbs(value, limb_lengths), expected)
        });

        // Test with 32 limbs of 1 bit each
        let mut rng = rand::thread_rng();
        let value: u32 = rng.gen();
        let limb_lengths = [1u8; 32];
        let result = u32_in_be_limbs(value, limb_lengths);
        let expected: [u32; 32] = core::array::from_fn(|i| (value >> (31 - i)) & 1);
        assert_eq!(result, expected);
    }
}
