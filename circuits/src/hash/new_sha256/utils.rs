use ff::PrimeField;

use crate::utils::util::fe_to_u32;

pub(super) const MASK_EVN_64: u64 = 0x5555_5555_5555_5555; // 010101...01 (even positions in u64)
pub(super) const MASK_ODD_64: u64 = 0xAAAA_AAAA_AAAA_AAAA; // 101010...10 (odd positions in u64)

const LOOKUP_LENGTHS: [u32; 9] = [2, 5, 6, 7, 8, 9, 10, 11, 12]; // supported lookup bit lengths
const MAX_LOOKUP_LENGTH: usize = 12; // maximum bit length of plain values in lookup table

/// Returns the even and odd bits of little-endian binary representation of u64.
pub fn get_even_and_odd_bits(value: u64) -> (u32, u32) {
    let mut even = 0u64;
    let mut odd = 0u64;
    let mut bit_pos = 0usize;

    for i in 0..32 {
        let even_bit = (value >> (2 * i)) & 1;
        let odd_bit = (value >> (2 * i + 1)) & 1;
        even |= even_bit << bit_pos;
        odd |= odd_bit << bit_pos;
        bit_pos += 1;
    }

    (even as u32, odd as u32)
}

/// Asserts x is in correct spreaded form, i.e. its little-endian binary
/// representation has zeros in odd positions.
fn in_valid_spreaded_form(x: u64) -> bool {
    MASK_ODD_64 & x == 0
}

/// Spreads the input value, which is by definition interleaving the (big
/// endian) bit-array of input with zeros in the even indices:         
/// [b_n, ..., b_1, b_0] ->  [0, b_n,..., 0, b_1, 0, b_0].
pub fn spread(x: u32) -> u64 {
    let mut le_bits = [false; 64];
    for i in 0..32 {
        le_bits[2 * i] = ((x >> i) & 1) == 1;
    }

    let ret = le_bits.iter().enumerate().fold(
        0u64,
        |acc, (i, &bit)| {
            if bit {
                acc | (1 << i)
            } else {
                acc
            }
        },
    );
    ret
}

/// Negates the even bits of u64 (in little-endian representation).
///
/// # Panics
///
/// If the input is not in clean spreaded form.
pub fn negate_spreaded(x: u64) -> u64 {
    assert!(
        in_valid_spreaded_form(x),
        "Input must be in valid spreaded form"
    );
    x ^ MASK_EVN_64
}

/// Breaks the value into big-endian limbs following the required limb lengths.
///
/// # Panics
///
/// If sum(limb_lengths) != 32.
/// If any given limb length equals to 0.
pub fn u32_in_be_limbs<const N: usize>(value: u32, limb_lengths: [usize; N]) -> [u32; N] {
    assert_eq!(limb_lengths.iter().sum::<usize>(), 32);

    let mut result = Vec::new();
    let mut remaining = value;
    for limb_len in limb_lengths.iter().rev() {
        assert!(*limb_len != 0);
        let limb = remaining & ((1 << limb_len) - 1);
        result.push(limb);
        remaining >>= limb_len;
    }
    result.reverse();
    result.try_into().unwrap()
}

pub fn u32_to_fe<F: PrimeField>(value: u32) -> F {
    F::from(value.into())
}

pub fn u64_to_fe<F: PrimeField>(value: u64) -> F {
    F::from(value)
}

/// Generates the spreaded lookup table lazily as it is only used in keygen.
pub fn gen_spread_table<F: PrimeField>() -> impl Iterator<Item = (F, F, F)> {
    // Compute all pairs of (plain, spreaded) for the plain values in the range [0,
    // 2^MAX_LOOKUP_LENGTH).
    let plain_spreaded_max_len =
        (1..=(1 << MAX_LOOKUP_LENGTH)).scan((F::ZERO, F::ZERO), |(plain, spreaded), i| {
            let res = (*plain, *spreaded);
            // Compute (plain, spreaded) for the next row.
            *plain += F::ONE;
            if i & 1 == 1 {
                // The spreaded form of an odd number can be easily computed by adding 1 to the
                // spreaded form of the previous even number.
                *spreaded += F::ONE;
            } else {
                // Recompute the spreaded form for an even number.
                let spreaded_u64 = spread(fe_to_u32(*plain));
                *spreaded = u64_to_fe(spreaded_u64);
            }

            Some(res)
        });

    // Generate the sub-table consisting of (tag, plain, spreaded) for the plain
    // values in the range [0, 2^tag).
    let table_of_tag = |tag| {
        plain_spreaded_max_len
            .clone()
            .take(1 << tag as usize)
            .map(move |(plain, spreaded)| (u32_to_fe(tag), plain, spreaded))
    };

    // Generate the full table by concatenating sub-tables for each length in
    // LOOKUP_LENGTHS.
    LOOKUP_LENGTHS
        .map(|limb_length| table_of_tag(limb_length))
        .into_iter()
        .flatten()
}

/// Computes off-circuit spreaded Σ₀(A) with A in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub fn spreaded_Sigma_0(spreaded_limbs: [u64; 4]) -> u64 {
    assert!(spreaded_limbs.into_iter().all(in_valid_spreaded_form));

    let [sA_10, sA_09, sA_11, sA_02] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    (pow4(30) * sA_02 + pow4(20) * sA_10 + pow4(11) * sA_09 + sA_11)
        + (pow4(21) * sA_11 + pow4(19) * sA_02 + pow4(09) * sA_10 + sA_09)
        + (pow4(23) * sA_09 + pow4(12) * sA_11 + pow4(10) * sA_02 + sA_10)
}

/// Computes off-circuit spreaded Maj(A, B, C) with A, B, C in spreaded forms.
///
/// # Panics
///
/// If A, B, C are not in clean spreaded form.
pub fn spreaded_maj(spreaded_forms: [u64; 3]) -> u64 {
    assert!(spreaded_forms.into_iter().all(in_valid_spreaded_form));

    let [sA, sB, sC] = spreaded_forms;

    // As each of sA, sB, sC is in valid spreaded form, their sum
    // is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    sA + sB + sC
}

/// Computes off-circuit spreaded Σ₁(E) with E in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub fn spreaded_Sigma_1(spreaded_limbs: [u64; 5]) -> u64 {
    assert!(spreaded_limbs.into_iter().all(in_valid_spreaded_form));

    let [sE_07, sE_12, sE_02, sE_05, sE_06] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    (pow4(26) * sE_06 + pow4(19) * sE_07 + pow4(7) * sE_12 + pow4(5) * sE_02 + sE_05)
        + (pow4(27) * sE_05 + pow4(21) * sE_06 + pow4(14) * sE_07 + pow4(2) * sE_12 + sE_02)
        + (pow4(20) * sE_12 + pow4(18) * sE_02 + pow4(13) * sE_05 + pow4(7) * sE_06 + sE_07)
}

fn pow4(n: u32) -> u64 {
    1 << (2 * n)
}

#[cfg(test)]
mod tests {
    use std::u64;

    use rand::{seq::SliceRandom, Rng};

    use super::*;

    type F = midnight_curves::Fq;

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
    fn test_in_valid_spreaded_form() {
        // Positive tests
        assert!([MASK_EVN_64, 0b101010101, 0, 1]
            .into_iter()
            .all(in_valid_spreaded_form));

        // Negative tests
        assert!(![MASK_ODD_64, u64::MAX, 2]
            .into_iter()
            .any(in_valid_spreaded_form));
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
        ]
        .into_iter()
        .for_each(|(value, limb_lengths, expected)| {
            assert_eq!(u32_in_be_limbs(value, limb_lengths), expected)
        });

        // Test with 32 limbs of 1 bit each
        let mut rng = rand::thread_rng();
        let value: u32 = rng.gen();
        let limb_lengths = [1; 32];
        let result = u32_in_be_limbs(value, limb_lengths);
        let expected: [u32; 32] = core::array::from_fn(|i| ((value >> (31 - i)) & 1));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_gen_spread_table() {
        let table: Vec<_> = gen_spread_table::<F>().collect();
        let mut rng = rand::thread_rng();
        let to_fe = |(tag, plain, spreaded)| {
            (
                u32_to_fe::<F>(tag),
                u32_to_fe::<F>(plain),
                u64_to_fe::<F>(spreaded),
            )
        };

        for _ in 0..10 {
            // Positive test: check that the table contains a valid triple of (tag, plain,
            // spreaded) for a random tag in [`LOOKUP_LENGTHS`].
            let tag = *LOOKUP_LENGTHS.choose(&mut rng).unwrap();
            let plain = rng.gen_range(0..(1 << tag));
            let spreaded = spread(plain);
            let triple = to_fe((tag, plain, spreaded));
            assert!(table.contains(&triple));

            // Negative test: check that the table does not contain a random triple of
            // (tag, plain, spreaded).
            let random_triple = to_fe((rng.gen(), rng.gen(), rng.gen()));
            assert!(!table.contains(&random_triple));
        }

        // Negative test: check that the table does not contain a triple with a tag not
        // in [`LOOKUP_LENGTHS`].
        let tag = 16; // Not in LOOKUP_LENGTHS
        let plain = rng.gen_range(0..(1 << tag));
        let spreaded = spread(plain);
        let triple = to_fe((tag, plain, spreaded));
        assert!(!table.contains(&triple));
    }

    #[test]
    fn test_spreaded_Sigma_0() {
        // Assert Σ₀(A) equals the even bits of the output of [`spreaded_Sigma_0`].
        fn assert_even_of_spreaded_Sigma_0(val: u32) {
            // Compute Σ₀(A) with the built-in methods.
            let rot_by_2 = val.rotate_right(2);
            let rot_by_13 = val.rotate_right(13);
            let rot_by_22 = val.rotate_right(22);
            let ret = rot_by_2 ^ rot_by_13 ^ rot_by_22;

            // Compute Σ₀(A) by the even bits of the value returned by [`spreaded_Sigma_0`].
            let plain_limbs: [u32; 4] = u32_in_be_limbs(val, [10, 9, 11, 2]);
            let spreaded_limbs: [u64; 4] = plain_limbs.map(spread);
            let (even, _) = get_even_and_odd_bits(spreaded_Sigma_0(spreaded_limbs));

            assert_eq!(ret, even);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            assert_even_of_spreaded_Sigma_0(rng.gen());
        }
    }

    #[test]
    fn test_spreaded_maj() {
        // Assert Maj(A, B, C) equals the odd bits of the output of [`spreaded_maj`].
        fn assert_odd_of_spreaded_maj(vals: [u32; 3]) {
            // Compute Maj(A, B, C) with the built-in methods.
            let [a, b, c] = vals;
            let ret = (a & b) ^ (a & c) ^ (b & c);

            // Compute Maj(A, B, C) by the odd bits of the value returned by
            // [`spreaded_maj`].
            let spreaded_forms: [u64; 3] = vals.map(spread);
            let (_even, odd) = get_even_and_odd_bits(spreaded_maj(spreaded_forms));

            assert_eq!(ret, odd);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let vals: [u32; 3] = [rng.gen(), rng.gen(), rng.gen()];
            assert_odd_of_spreaded_maj(vals);
        }
    }

    #[test]
    fn test_spreaded_Sigma_1() {
        // Assert Σ₁(E) equals the even bits of the output of [`spreaded_Sigma_1`].
        fn assert_even_of_spreaded_Sigma_1(val: u32) {
            // Compute Σ₁(E) with the built-in methods.
            let rot_by_6 = val.rotate_right(6);
            let rot_by_11 = val.rotate_right(11);
            let rot_by_25 = val.rotate_right(25);
            let ret = rot_by_6 ^ rot_by_11 ^ rot_by_25;

            // Compute Σ₁(E) by the even bits of the value returned by [`spreaded_Sigma_1`].
            let plain_limbs: [u32; 5] = u32_in_be_limbs(val, [7, 12, 2, 5, 6]);
            let spreaded_limbs: [u64; 5] = plain_limbs.map(spread);
            let (even, _) = get_even_and_odd_bits(spreaded_Sigma_1(spreaded_limbs));

            assert_eq!(ret, even);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            assert_even_of_spreaded_Sigma_1(rng.gen());
        }
    }
}
