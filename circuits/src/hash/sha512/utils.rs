use ff::PrimeField;
use midnight_proofs::plonk::Expression;

use crate::utils::util::u128_to_fe;

pub(super) const MASK_EVN_128: u128 = 0x5555_5555_5555_5555_5555_5555_5555_5555; // 010101...01 (even positions in u128)
pub(super) const MASK_ODD_128: u128 = 0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA; // 101010...10 (odd positions in u128)

const LOOKUP_LENGTHS: [u32; 10] = [1, 2, 3, 4, 5, 6, 10, 11, 12, 13]; // supported lookup bit lengths

/// Returns the even and odd bits of little-endian binary representation of
/// u128.
pub fn get_even_and_odd_bits(value: u128) -> (u64, u64) {
    (compact_even(value), compact_even(value >> 1))
}

/// Compacts the even bits of the u128 into the least-significant u64 half.
fn compact_even(mut x: u128) -> u64 {
    x &= 0x5555_5555_5555_5555_5555_5555_5555_5555;
    x = (x | (x >> 1)) & 0x3333_3333_3333_3333_3333_3333_3333_3333;
    x = (x | (x >> 2)) & 0x0f0f_0f0f_0f0f_0f0f_0f0f_0f0f_0f0f_0f0f;
    x = (x | (x >> 4)) & 0x00ff_00ff_00ff_00ff_00ff_00ff_00ff_00ff;
    x = (x | (x >> 8)) & 0x0000_ffff_0000_ffff_0000_ffff_0000_ffff;
    x = (x | (x >> 16)) & 0x0000_0000_ffff_ffff_0000_0000_ffff_ffff;
    x = (x | (x >> 32)) & 0x0000_0000_0000_0000_ffff_ffff_ffff_ffff;
    x as u64
}

/// Asserts x is in correct spreaded form, i.e. its little-endian binary
/// representation has zeros in odd positions.
fn assert_in_valid_spreaded_form(x: u128) {
    assert_eq!(MASK_ODD_128 & x, 0, "Input must be in valid spreaded form")
}

/// Spreads the input value, which is by definition inserting a zero between all
/// its bits: [bn, ..., b1, b0] ->  [0, bn,..., 0, b1, 0, b0].
pub fn spread(x: u64) -> u128 {
    (0..64).fold(0u128, |acc, i| acc | (((x as u128 >> i) & 1) << (2 * i)))
}

/// Negates the even bits of u128 (in little-endian representation).
///
/// # Panics
///
/// If the input is not in clean spreaded form.
pub fn negate_spreaded(x: u128) -> u128 {
    assert_in_valid_spreaded_form(x);
    x ^ MASK_EVN_128
}

/// Breaks the value into big-endian limbs following the required limb lengths.
///
/// # Panics
///
/// If sum(limb_lengths) != 64.
/// If any given limb length equals 0.
pub fn u64_in_be_limbs<const N: usize>(value: u64, limb_lengths: [usize; N]) -> [u64; N] {
    assert_eq!(limb_lengths.iter().sum::<usize>(), 64);

    let mut result = [0u64; N];
    let mut shift = 64;

    for (i, &len) in limb_lengths.iter().enumerate() {
        assert!(len != 0);
        shift -= len;
        result[i] = (value >> shift) & ((1 << len) - 1);
    }

    result
}

/// Generates the plain-spreaded lookup table.
pub fn gen_spread_table<F: PrimeField>() -> impl Iterator<Item = (F, F, F)> {
    std::iter::once((F::ZERO, F::ZERO, F::ZERO)) // base case (disabled lookup)
        .chain(LOOKUP_LENGTHS.into_iter().flat_map(|len| {
            let tag = F::from(len as u64);
            (0..(1 << len)).map(move |i| (tag, F::from(i as u64), u128_to_fe(spread(i as u64))))
        }))
}

/// Computes off-circuit spreaded Maj(A, B, C) with A, B, C in spreaded forms.
///
/// # Panics
///
/// If A, B, C are not in clean spreaded form.
pub fn spreaded_maj(spreaded_forms: [u128; 3]) -> u128 {
    (spreaded_forms.into_iter()).for_each(assert_in_valid_spreaded_form);

    let [sA, sB, sC] = spreaded_forms;

    // As each of sA, sB, sC is in valid spreaded form, their sum
    // is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u128.
    sA + sB + sC
}

/// Computes off-circuit spreaded Σ₀(A) with A in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub fn spreaded_Sigma_0(spreaded_limbs: [u128; 7]) -> u128 {
    (spreaded_limbs.into_iter()).for_each(assert_in_valid_spreaded_form);

    let [sA_13a, sA_12, sA_05, sA_06, sA_13b, sA_13c, sA_02] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u128.
    pow4_ip(
        [51, 38, 36, 23, 11, 6, 0],
        [sA_13b, sA_13c, sA_02, sA_13a, sA_12, sA_05, sA_06],
    ) + pow4_ip(
        [58, 45, 32, 30, 17, 5, 0],
        [sA_06, sA_13b, sA_13c, sA_02, sA_13a, sA_12, sA_05],
    ) + pow4_ip(
        [59, 53, 40, 27, 25, 12, 0],
        [sA_05, sA_06, sA_13b, sA_13c, sA_02, sA_13a, sA_12],
    )
}

/// Computes off-circuit spreaded Σ₁(E) with E in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub fn spreaded_Sigma_1(spreaded_limbs: [u128; 7]) -> u128 {
    (spreaded_limbs.into_iter()).for_each(assert_in_valid_spreaded_form);

    let [sE_13a, sE_10a, sE_13b, sE_10b, sE_04, sE_13c, sE_01] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u128.
    pow4_ip(
        [51, 50, 37, 27, 14, 4, 0],
        [sE_13c, sE_01, sE_13a, sE_10a, sE_13b, sE_10b, sE_04],
    ) + pow4_ip(
        [60, 47, 46, 33, 23, 10, 0],
        [sE_04, sE_13c, sE_01, sE_13a, sE_10a, sE_13b, sE_10b],
    ) + pow4_ip(
        [51, 41, 37, 24, 23, 10, 0],
        [sE_13b, sE_10b, sE_04, sE_13c, sE_01, sE_13a, sE_10a],
    )
}

/// Computes off-circuit spreaded σ₀(W) with W in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub fn spreaded_sigma_0(spreaded_limbs: [u128; 10]) -> u128 {
    (spreaded_limbs.into_iter()).for_each(assert_in_valid_spreaded_form);

    let [sW_03a, sW_13a, sW_13b, sW_13c, sW_03b, sW_11, sW_01a, sW_01b, sW_05, sW_01c] =
        spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u128.
    pow4_ip(
        [54, 41, 28, 15, 12, 1, 0],
        [sW_03a, sW_13a, sW_13b, sW_13c, sW_03b, sW_11, sW_01a],
    ) + pow4_ip(
        [63, 60, 47, 34, 21, 18, 7, 6, 5, 0],
        [
            sW_01c, sW_03a, sW_13a, sW_13b, sW_13c, sW_03b, sW_11, sW_01a, sW_01b, sW_05,
        ],
    ) + pow4_ip(
        [63, 62, 57, 56, 53, 40, 27, 14, 11, 0],
        [
            sW_01a, sW_01b, sW_05, sW_01c, sW_03a, sW_13a, sW_13b, sW_13c, sW_03b, sW_11,
        ],
    )
}

/// Computes off-circuit spreaded σ₁(W) with W in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub fn spreaded_sigma_1(spreaded_limbs: [u128; 10]) -> u128 {
    (spreaded_limbs.into_iter()).for_each(assert_in_valid_spreaded_form);

    let [sW_03a, sW_13a, sW_13b, sW_13c, sW_03b, sW_11, sW_01a, sW_01b, sW_05, sW_01c] =
        spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u128.
    pow4_ip(
        [55, 42, 29, 16, 13, 2, 1, 0],
        [
            sW_03a, sW_13a, sW_13b, sW_13c, sW_03b, sW_11, sW_01a, sW_01b,
        ],
    ) + pow4_ip(
        [53, 52, 51, 46, 45, 42, 29, 16, 3, 0],
        [
            sW_11, sW_01a, sW_01b, sW_05, sW_01c, sW_03a, sW_13a, sW_13b, sW_13c, sW_03b,
        ],
    ) + pow4_ip(
        [51, 38, 25, 22, 11, 10, 9, 4, 3, 0],
        [
            sW_13a, sW_13b, sW_13c, sW_03b, sW_11, sW_01a, sW_01b, sW_05, sW_01c, sW_03a,
        ],
    )
}

/// Returns sum_i 4^(exponents\[i\]) * terms\[i\] for u128.
fn pow4_ip<const N: usize>(exponents: [u8; N], terms: [u128; N]) -> u128 {
    (exponents.iter().zip(terms.iter())).map(|(e, t)| (1 << (2 * e)) * t).sum()
}

/// Returns sum_i 2^(exponents\[i\]) * terms\[i\].
pub(crate) fn expr_pow2_ip<F: PrimeField, const N: usize>(
    exponents: [u8; N],
    terms: [&Expression<F>; N],
) -> Expression<F> {
    let mut expr = Expression::Constant(F::ZERO);
    for (pow, term) in exponents.into_iter().zip(terms.into_iter()) {
        expr = expr + Expression::Constant(u128_to_fe(1 << pow)) * term.clone();
    }
    expr
}

/// Returns sum_i 4^(exponents\[i\]) * terms\[i\].
pub(crate) fn expr_pow4_ip<F: PrimeField, const N: usize>(
    exponents: [u8; N],
    terms: [&Expression<F>; N],
) -> Expression<F> {
    expr_pow2_ip(exponents.map(|l| 2 * l), terms)
}

#[cfg(test)]
mod tests {

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
            (u128::MAX, 0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF),
            (MASK_EVN_128, 0xFFFF_FFFF_FFFF_FFFF, 0),
            (MASK_ODD_128, 0, 0xFFFF_FFFF_FFFF_FFFF),
            (0b110101101u128, 19, 14),
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
        assert_eq!(negate_spreaded(MASK_EVN_128), 0);
        assert_eq!(negate_spreaded(1), MASK_EVN_128 - 1);
        // Negative tests
        assert_ne!(negate_spreaded(0), 0);
    }

    #[test]
    fn test_u64_in_be_limbs() {
        [
            (
                0x123456789ABCDEF0u64,
                [8, 8, 8, 8, 8, 8, 8, 8],
                [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0],
            ),
            (
                0x123456789ABCDEF0u64,
                [4, 8, 12, 8, 4, 8, 12, 8],
                [0x1, 0x23, 0x456, 0x78, 0x9, 0xAB, 0xCDE, 0xF0],
            ),
        ]
        .into_iter()
        .for_each(|(value, limb_lengths, expected)| {
            assert_eq!(u64_in_be_limbs(value, limb_lengths), expected)
        });

        // Test with 64 limbs of 1 bit each
        let mut rng = rand::thread_rng();
        let value: u64 = rng.gen();
        let limb_lengths = [1; 64];
        let result = u64_in_be_limbs(value, limb_lengths);
        let expected: [u64; 64] = core::array::from_fn(|i| ((value >> (63 - i)) & 1));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_gen_spread_table() {
        let table: Vec<_> = gen_spread_table::<F>().collect();
        let mut rng = rand::thread_rng();
        let to_fe = |(tag, plain, spreaded)| {
            (
                F::from(tag as u64),
                F::from(plain as u64),
                u128_to_fe(spreaded),
            )
        };

        assert!(table.contains(&to_fe((0, 0, 0))));
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
        let tag = 14; // Not in LOOKUP_LENGTHS
        let plain = rng.gen_range(0..(1 << tag));
        let spreaded = spread(plain);
        let triple = to_fe((tag, plain, spreaded));
        assert!(!table.contains(&triple));
    }

    #[test]
    fn test_spreaded_maj() {
        // Assert Maj(A, B, C) equals the odd bits of the output of [`spreaded_maj`].
        fn assert_odd_of_spreaded_maj(vals: [u64; 3]) {
            // Compute Maj(A, B, C) with the built-in methods.
            let [a, b, c] = vals;
            let ret = (a & b) ^ (a & c) ^ (b & c);

            // Compute Maj(A, B, C) by the odd bits of the value returned by
            // [`spreaded_maj`].
            let spreaded_forms: [u128; 3] = vals.map(spread);
            let (_even, odd) = get_even_and_odd_bits(spreaded_maj(spreaded_forms));

            assert_eq!(ret, odd);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let vals: [u64; 3] = [rng.gen(), rng.gen(), rng.gen()];
            assert_odd_of_spreaded_maj(vals);
        }
    }

    #[test]
    fn test_spreaded_Sigma_0() {
        // Assert Σ₀(A) equals the even bits of the output of [`spreaded_Sigma_0`].
        fn assert_even_of_spreaded_Sigma_0(val: u64) {
            // Compute Σ₀(A) with the built-in methods.
            let rot_by_28 = val.rotate_right(28);
            let rot_by_34 = val.rotate_right(34);
            let rot_by_39 = val.rotate_right(39);
            let ret = rot_by_28 ^ rot_by_34 ^ rot_by_39;

            // Compute Σ₀(A) by the even bits of the value returned by [`spreaded_Sigma_0`].
            let plain_limbs: [u64; 7] = u64_in_be_limbs(val, [13, 12, 5, 6, 13, 13, 2]);
            let spreaded_limbs: [u128; 7] = plain_limbs.map(spread);
            let (even, _) = get_even_and_odd_bits(spreaded_Sigma_0(spreaded_limbs));

            assert_eq!(ret, even);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            assert_even_of_spreaded_Sigma_0(rng.gen());
        }
    }

    #[test]
    fn test_spreaded_Sigma_1() {
        // Assert Σ₁(E) equals the even bits of the output of [`spreaded_Sigma_1`].
        fn assert_even_of_spreaded_Sigma_1(val: u64) {
            // Compute Σ₁(E) with the built-in methods.
            let rot_by_14 = val.rotate_right(14);
            let rot_by_18 = val.rotate_right(18);
            let rot_by_41 = val.rotate_right(41);
            let ret = rot_by_14 ^ rot_by_18 ^ rot_by_41;

            // Compute Σ₁(E) by the even bits of the value returned by [`spreaded_Sigma_1`].
            let plain_limbs: [u64; 7] = u64_in_be_limbs(val, [13, 10, 13, 10, 4, 13, 1]);
            let spreaded_limbs: [u128; 7] = plain_limbs.map(spread);
            let (even, _) = get_even_and_odd_bits(spreaded_Sigma_1(spreaded_limbs));

            assert_eq!(ret, even);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            assert_even_of_spreaded_Sigma_1(rng.gen());
        }
    }

    #[test]
    fn test_spreaded_sigma_0() {
        // Assert σ₀(W) equals the even bits of the output of [`spreaded_sigma_0`].
        fn assert_even_of_spreaded_sigma_0(val: u64) {
            // Compute σ₀(W) with the built-in methods.
            let shifted_by_7 = val >> 7;
            let rot_by_1 = val.rotate_right(1);
            let rot_by_8 = val.rotate_right(8);
            let ret = shifted_by_7 ^ rot_by_1 ^ rot_by_8;

            // Compute σ₀(W) by the even bits of the value returned by [`spreaded_sigma_0`].
            let plain_limbs: [u64; 10] = u64_in_be_limbs(val, [3, 13, 13, 13, 3, 11, 1, 1, 5, 1]);
            let spreaded_limbs: [u128; 10] = plain_limbs.map(spread);
            let (even, _) = get_even_and_odd_bits(spreaded_sigma_0(spreaded_limbs));

            assert_eq!(ret, even);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            assert_even_of_spreaded_sigma_0(rng.gen());
        }
    }

    #[test]
    fn test_spreaded_sigma_1() {
        // Assert σ₁(W) equals the even bits of the output of [`spreaded_sigma_1`].
        fn assert_even_of_spreaded_sigma_1(val: u64) {
            // Compute σ₁(W) with the built-in methods.
            let shifted_by_6 = val >> 6;
            let rot_by_19 = val.rotate_right(19);
            let rot_by_61 = val.rotate_right(61);
            let ret = shifted_by_6 ^ rot_by_19 ^ rot_by_61;

            // Compute σ₁(W) by the even bits of the value returned by [`spreaded_sigma_1`].
            let plain_limbs: [u64; 10] = u64_in_be_limbs(val, [3, 13, 13, 13, 3, 11, 1, 1, 5, 1]);
            let spreaded_limbs: [u128; 10] = plain_limbs.map(spread);
            let (even, _) = get_even_and_odd_bits(spreaded_sigma_1(spreaded_limbs));

            assert_eq!(ret, even);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            assert_even_of_spreaded_sigma_1(rng.gen());
        }
    }
}
