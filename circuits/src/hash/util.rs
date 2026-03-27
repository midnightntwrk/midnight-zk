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
pub fn u32_to_be_limbs<const N: usize, T: Into<usize> + Copy>(value: u32, limb_lengths: [T; N]) -> [u32; N] {
    let limb_lengths_usize = limb_lengths.map(|l| l.into());
    assert_eq!(limb_lengths_usize.iter().sum::<usize>(), 32);

    let mut result = [0u32; N];
    let mut shift = 32;

    for (i, &len) in limb_lengths_usize.iter().enumerate() {
        if len != 0 {
            shift -= len as u32;
            result[i] = (value >> shift) & ((1 << len) - 1);
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

    #[test]
    fn test_u32_to_be_limbs() {
        let value = 0x12345678u32;
        // Test with usize
        assert_eq!(u32_to_be_limbs(value, [8usize, 8, 8, 8]), [0x12, 0x34, 0x56, 0x78]);
        // Test with u8
        assert_eq!(u32_to_be_limbs(value, [8u8, 8, 8, 8]), [0x12, 0x34, 0x56, 0x78]);
    }
}
