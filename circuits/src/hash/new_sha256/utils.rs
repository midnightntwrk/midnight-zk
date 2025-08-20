use ff::PrimeField;

pub(super) const MASK_EVN_64: u64 = 0x5555_5555_5555_5555; // 010101...01 (even positions in u64)
pub(super) const MASK_ODD_64: u64 = 0xAAAA_AAAA_AAAA_AAAA; // 101010...10 (odd positions in u64)

const LOOKUP_LENGTHS: [u32; 10] = [2, 3, 4, 5, 6, 7, 9, 10, 11, 12]; // supported lookup bit lengths

/// Returns the even and odd bits of little-endian binary representation of u64.
pub fn get_even_and_odd_bits(value: u64) -> (u32, u32) {
    let mut even = 0u64;
    let mut odd = 0u64;

    for i in 0..32 {
        let even_bit = (value >> (2 * i)) & 1;
        let odd_bit = (value >> (2 * i + 1)) & 1;
        even |= even_bit << i;
        odd |= odd_bit << i;
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

/// Generates the plain-spreaded lookup table.
pub fn gen_spread_table<F: PrimeField>() -> Vec<(F, F, F)> {
    let mut table = vec![(F::ZERO, F::ZERO, F::ZERO)]; // base case (disabled lookup)
    for len in LOOKUP_LENGTHS.into_iter() {
        let tag = F::from(len as u64);
        for i in 0..(1 << len) {
            table.push((tag, F::from(i as u64), F::from(spread(i as u32))))
        }
    }
    table
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
        + (pow4(21) * sA_11 + pow4(19) * sA_02 + pow4(9) * sA_10 + sA_09)
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

/// Computes off-circuit spreaded σ₀(W) with W in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub fn spreaded_sigma_0(spreaded_limbs: [u64; 8]) -> u64 {
    assert!(spreaded_limbs.into_iter().all(in_valid_spreaded_form));

    let [sW_12, sW_1a, sW_1b, sW_1c, sW_07, sW_3a, sW_04, sW_3b] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    (pow4(17) * sW_12
        + pow4(16) * sW_1a
        + pow4(15) * sW_1b
        + pow4(14) * sW_1c
        + pow4(7) * sW_07
        + pow4(4) * sW_3a
        + sW_04)
        + (pow4(28) * sW_04
            + pow4(25) * sW_3b
            + pow4(13) * sW_12
            + pow4(12) * sW_1a
            + pow4(11) * sW_1b
            + pow4(10) * sW_1c
            + pow4(3) * sW_07
            + sW_3a)
        + (pow4(31) * sW_1c
            + pow4(24) * sW_07
            + pow4(21) * sW_3a
            + pow4(17) * sW_04
            + pow4(14) * sW_3b
            + pow4(2) * sW_12
            + pow4(1) * sW_1a
            + sW_1b)
}

/// Computes off-circuit spreaded σ₁(W) with W in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub fn spreaded_sigma_1(spreaded_limbs: [u64; 8]) -> u64 {
    assert!(spreaded_limbs.into_iter().all(in_valid_spreaded_form));

    let [sW_12, sW_1a, sW_1b, sW_1c, sW_07, sW_3a, sW_04, sW_3b] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    (pow4(10) * sW_12 + pow4(9) * sW_1a + pow4(8) * sW_1b + pow4(7) * sW_1c + sW_07)
        + (pow4(25) * sW_07
            + pow4(22) * sW_3a
            + pow4(18) * sW_04
            + pow4(15) * sW_3b
            + pow4(3) * sW_12
            + pow4(2) * sW_1a
            + pow4(1) * sW_1b
            + sW_1c)
        + (pow4(31) * sW_1b
            + pow4(30) * sW_1c
            + pow4(23) * sW_07
            + pow4(20) * sW_3a
            + pow4(16) * sW_04
            + pow4(13) * sW_3b
            + pow4(1) * sW_12
            + sW_1a)
}

fn pow4(n: u32) -> u64 {
    1 << (2 * n)
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
        let table: Vec<_> = gen_spread_table::<F>();
        let mut rng = rand::thread_rng();
        let to_fe = |(tag, plain, spreaded)| {
            (
                u32_to_fe::<F>(tag),
                u32_to_fe::<F>(plain),
                u64_to_fe::<F>(spreaded),
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

    #[test]
    fn test_spreaded_sigma_0() {
        // Assert σ₀(W) equals the even bits of the output of [`spreaded_sigma_0`].
        fn assert_even_of_spreaded_sigma_0(val: u32) {
            // Compute σ₀(W) with the built-in methods.
            let shifted_by_3 = val >> 3;
            let rot_by_7 = val.rotate_right(7);
            let rot_by_18 = val.rotate_right(18);
            let ret = shifted_by_3 ^ rot_by_7 ^ rot_by_18;

            // Compute σ₀(W) by the even bits of the value returned by [`spreaded_sigma_0`].
            let plain_limbs: [u32; 8] = u32_in_be_limbs(val, [12, 1, 1, 1, 7, 3, 4, 3]);
            let spreaded_limbs: [u64; 8] = plain_limbs.map(spread);
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
        fn assert_even_of_spreaded_sigma_1(val: u32) {
            // Compute σ₁(W) with the built-in methods.
            let shifted_by_10 = val >> 10;
            let rot_by_17 = val.rotate_right(17);
            let rot_by_19 = val.rotate_right(19);
            let ret = shifted_by_10 ^ rot_by_17 ^ rot_by_19;

            // Compute σ₁(W) by the even bits of the value returned by [`spreaded_sigma_1`].
            let plain_limbs: [u32; 8] = u32_in_be_limbs(val, [12, 1, 1, 1, 7, 3, 4, 3]);
            let spreaded_limbs: [u64; 8] = plain_limbs.map(spread);
            let (even, _) = get_even_and_odd_bits(spreaded_sigma_1(spreaded_limbs));

            assert_eq!(ret, even);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            assert_even_of_spreaded_sigma_1(rng.gen());
        }
    }
}
