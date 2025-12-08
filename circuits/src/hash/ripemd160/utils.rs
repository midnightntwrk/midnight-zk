use ff::PrimeField;

use crate::hash::sha256::utils::assert_in_valid_spreaded_form;
pub use crate::hash::sha256::utils::{get_even_and_odd_bits, spread};

const WORD: usize = 32;
const MAX_LIMB: usize = 11;
const LAST_LIMB: usize = WORD % MAX_LIMB; // 10
pub(super) const NUM_LIMBS: usize = (WORD - 1) / MAX_LIMB + 2; // 4

/// Decomposes a 32-bit word into limbs so that the first k limbs
/// represent the `rot` bits that will be left-rotated, and returns
/// the lengths of each limb along with k.
///
/// # Panics
///
/// If `rot` is not in the range (0, 16).
pub(super) fn limb_lengths(rot: usize) -> ([usize; NUM_LIMBS], usize) {
    // Given the word size |W| = [`WORD`] and the maximum lookup bit
    // size: [`MAX_LIMB`], the following two equalities hold:
    //
    // [`WORD`] = n * [`MAX_LIMB`] + [`LAST_LIMB`]
    // rot      = k * [`MAX_LIMB`] + a
    //
    // As 0 < rot < 16 in our use case, we have that rot < n * [`MAX_LIMB`].
    // Therefore, by splitting the (k+1)-th limb into two parts of sizes
    // a and b = [`MAX_LIMB`] - a, we can represent the rot bits in the first
    // k+1 limbs:
    // w   = | F0 | F1 | .. |    Fk   | .. | Fn | L |
    //     = |<--      rot    -->| S2 | .. | Fn | L |
    assert!(rot > 0 && rot < 16);
    let mut lengths = [MAX_LIMB; NUM_LIMBS];
    lengths[NUM_LIMBS - 1] = LAST_LIMB;
    let a = rot % MAX_LIMB;
    let b = MAX_LIMB - a;
    // When a == 0, the limb Fk will be split into | 0 | MAX_LIMB |,
    // thus the value of k should always be incremented by 1.
    let k = rot / MAX_LIMB + 1;
    lengths[k - 1] = a;
    lengths[k] = b;
    (lengths, k)
}

/// Computes the coefficients for each limb based on their lengths for a 32-bit
/// word in big-endian order.
///
/// # Panics
///
/// If the sum of limb lengths does not equal [`WORD`].
pub(super) fn limb_coeffs(limb_lengths: &[usize; NUM_LIMBS]) -> [u32; NUM_LIMBS] {
    assert!(limb_lengths.iter().sum::<usize>() == WORD);
    let mut coeffs = [0u32; NUM_LIMBS];
    let mut acc = 1u32;
    for (i, size) in limb_lengths.iter().rev().enumerate() {
        coeffs[i] = acc;
        acc = acc.wrapping_shl(*size as u32);
    }
    coeffs.reverse();
    coeffs
}

/// Decomposes a 32-bit word into its limb values based on the provided limb
/// lengths in big-endian order.
///
/// # Panics
///
/// If the sum of limb lengths does not equal [`WORD`].
pub(super) fn limb_values(value: u32, limb_lengths: &[usize; NUM_LIMBS]) -> [u32; NUM_LIMBS] {
    assert_eq!(limb_lengths.iter().sum::<usize>(), WORD);

    let mut result = [0u32; NUM_LIMBS];
    let mut shift = WORD;

    for (i, &len) in limb_lengths.iter().enumerate() {
        if len == 0 {
            result[i] = 0;
        } else {
            shift -= len;
            result[i] = (value >> shift) & ((1 << len) - 1);
        }
    }
    result
}

/// Computes off-circuit spreaded of the type one bitwise operation: A ⊕ B ⊕ C
/// with A, B, C in spreaded forms.
///
/// # Panics
///
/// If A, B, C are not in clean spreaded form.
pub fn spreaded_type_one(spreaded_forms: [u64; 3]) -> u64 {
    spreaded_forms.into_iter().for_each(assert_in_valid_spreaded_form);

    let [sA, sB, sC] = spreaded_forms;

    // As each of sA, sB, sC is in valid spreaded form, their sum
    // is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    sA + sB + sC
}

/// Generates the plain-spreaded lookup table. The limb lengths to be looked up
/// cover the range [0, 11] for the rotation offsets used in RIPEMD-160.
pub(super) fn gen_spread_table<F: PrimeField>() -> impl Iterator<Item = (F, F, F)> {
    (0..=11).flat_map(|len| {
        let tag = F::from(len as u64);
        (0..(1 << len)).map(move |i| (tag, F::from(i as u64), F::from(spread(i as u32))))
    })
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    type F = midnight_curves::Fq;

    #[test]
    fn test_limb_lengths() {
        // For every rotation offset, the sum of limb lengths should equal [`WORD`],
        // and the sum of the first k lengths should equal the rotation offset.
        for rot in 1..16 {
            let (lengths, k) = limb_lengths(rot);
            let sum: usize = lengths.iter().sum();
            assert_eq!(
                sum, WORD,
                "Sum of lengths does not equal WORD={} for rot={}",
                WORD, rot
            );
            let expected_rot = lengths.iter().take(k).sum::<usize>();
            assert_eq!(
                expected_rot, rot,
                "Sum of the first k = {} lengths does not equal rot={}",
                k, rot
            );
        }
    }

    #[test]
    fn test_decomposition_and_coeffs() {
        // For every rotation offset, decompose a random value into limbs and
        // reconstruct it using the derived coefficients and limb values.
        for rot in 1..16 {
            let (lengths, _) = limb_lengths(rot);
            let coeffs = limb_coeffs(&lengths);
            let mut rng = rand::thread_rng();
            let val: u32 = rng.gen();
            let limbs = limb_values(val, &lengths);
            let expected_val =
                limbs.iter().zip(coeffs.iter()).fold(0u32, |acc, (&limb, &coeff)| {
                    acc.wrapping_add(limb.wrapping_mul(coeff))
                });
            assert_eq!(val, expected_val, "Failed reconstruction for rot={}", rot);
        }
    }

    #[test]
    fn test_left_rotations() {
        // For every rotation offset, verify that rotating the value left by that offset
        // matches the reconstruction from derived limbs and coefficients.
        for rot in 1..16 {
            let (mut lengths, k) = limb_lengths(rot);
            let mut rng = rand::thread_rng();
            let val: u32 = rng.gen();
            let mut limbs = limb_values(val, &lengths);
            // Rotate the lengths and compute coefficients accordingly
            lengths.rotate_left(k);
            let coeffs = limb_coeffs(&lengths);
            // Rotate the limbs
            limbs.rotate_left(k);
            // Reconstruct the rotated value from rotated limbs and coefficients
            let expected_rot_val =
                limbs.iter().zip(coeffs.iter()).fold(0u32, |acc, (&limb, &coeff)| {
                    acc.wrapping_add(limb.wrapping_mul(coeff))
                });
            let rot_val = val.rotate_left(rot as u32);
            assert_eq!(
                rot_val, expected_rot_val,
                "Failed rotation reconstruction for rot={}",
                rot
            );
        }
    }

    #[test]
    fn test_spreaded_type_one() {
        // Assert A ⊕ B ⊕ C equals the even bits of the output of [`spreaded_type_one`].
        fn assert_even_of_spreaded_type_one(vals: [u32; 3]) {
            // Compute A ⊕ B ⊕ C with the built-in methods.
            let [a, b, c] = vals;
            let ret = a ^ b ^ c;

            // Compute A ⊕ B ⊕ C by the even bits of the value returned by
            // [`spreaded_type_one`].
            let spreaded_forms: [u64; 3] = vals.map(spread);
            let (even, _odd) = get_even_and_odd_bits(spreaded_type_one(spreaded_forms));

            assert_eq!(ret, even as u32);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let vals: [u32; 3] = [rng.gen(), rng.gen(), rng.gen()];
            assert_even_of_spreaded_type_one(vals);
        }
    }

    #[test]
    fn test_type_two() {
        // Assert (A ∧ B) ∨ (¬A ∧ C) equals (A ∧ B) ⊕ (¬A ∧ C)
        fn assert_type_two(vals: [u32; 3]) {
            let [a, b, c] = vals;
            // Compute (A ∧ B) ∨ (¬A ∧ C) with the built-in methods.
            let ret = (a & b) | ((!a) & c);
            // Compute (A ∧ B) ⊕ (¬A ∧ C) with the built-in methods.
            let expected_ret = (a & b) ^ ((!a) & c);
            assert_eq!(ret, expected_ret);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let vals: [u32; 3] = [rng.gen(), rng.gen(), rng.gen()];
            assert_type_two(vals);
        }
    }

    #[test]
    fn test_type_three() {
        // Assert (A ∨ ¬B) ⊕ C equals (A ⊕ ¬B ⊕ C) ⊕ (A ∧ ¬B)
        fn assert_type_three(vals: [u32; 3]) {
            let [a, b, c] = vals;
            // Compute (A ∨ ¬B) ⊕ C with the built-in methods.
            let ret = (a | (!b)) ^ c;
            // Compute (A ⊕ ¬B ⊕ C) ⊕ (A ∧ ¬B) with the built-in methods.
            let expected_ret = (a ^ (!b) ^ c) ^ (a & (!b));
            assert_eq!(ret, expected_ret);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let vals: [u32; 3] = [rng.gen(), rng.gen(), rng.gen()];
            assert_type_three(vals);
        }
    }

    #[test]
    fn test_gen_spread_table() {
        let table: Vec<_> = gen_spread_table::<F>().collect();
        let mut rng = rand::thread_rng();
        let to_fe = |(tag, plain, spreaded)| {
            (
                F::from(tag as u64),
                F::from(plain as u64),
                F::from(spreaded),
            )
        };

        assert!(table.contains(&to_fe((0, 0, 0))));
        for _ in 0..10 {
            // Positive test: check that the table contains a valid triple of (tag, plain,
            // spreaded) for a random tag in [0, 11].
            let tag = rng.gen_range(0..=11);
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
        let tag = 12; // Not in LOOKUP_LENGTHS
        let plain = rng.gen_range(0..(1 << tag));
        let spreaded = spread(plain);
        let triple = to_fe((tag, plain, spreaded));
        assert!(!table.contains(&triple));
    }
}
