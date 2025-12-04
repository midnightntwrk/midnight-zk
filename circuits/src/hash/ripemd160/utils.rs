const WORD: usize = 32;
const MAX_LIMB: usize = 11;
const LAST_LIMB: usize = WORD % MAX_LIMB; // 10
const NUM_LIMBS: usize = (WORD - 1) / MAX_LIMB + 2; // 4

/// Decomposes a 32-bit word into limbs so that the first k limbs
/// represent the `rot` bits that will be left-rotated, and returns
/// the lengths of each limb along with k.
pub(super) fn limb_lengths(rot: usize) -> ([usize; NUM_LIMBS], usize) {
    // Given the word size |W| = [`WORD`] and the maximum lookup bit
    // size: [`MAX_LIMB`], the following two equalities hold:
    //
    // [`WORD`] = n * [`MAX_LIMB`] + [`LAST_LIMB`]
    // rot      = k * [`MAX_LIMB`] + a
    //
    // As 0 < rot < 22 in our use case, we have that rot < n * [`MAX_LIMB`].
    // Therefore, by splitting the (k+1)-th limb into two parts of sizes
    // a and b = [`MAX_LIMB`] - a, we can represent the rot bits in the first
    // k+1 limbs:
    // w   = | F0 | F1 | .. |    Fk   | .. | Fn | L |
    //     = |<--      rot    -->| S2 | .. | Fn | L |
    assert!(rot > 0 && rot < WORD - LAST_LIMB);
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

#[cfg(test)]
mod tests {
    use rand::Rng;
    use super::*;

    #[test]
    fn test_limb_lengths() {
        // For every rotation offset, the sum of limb lengths should equal WORD,
        // and the sum of the first k lengths should equal the rotation offset.
        for rot in 1..22 {
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
        for rot in 1..22 {
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
        for rot in 1..22 {
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
}
