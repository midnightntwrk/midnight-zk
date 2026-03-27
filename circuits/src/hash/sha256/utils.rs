use ff::PrimeField;

pub(crate) use crate::hash::util::{
    assert_in_valid_spreaded_form, expr_pow2_ip, expr_pow4_ip, gen_spread_table as gen_table,
    get_even_and_odd_bits, negate_spreaded, spread, u32_to_be_limbs, MASK_EVN_64,
};

const LOOKUP_LENGTHS: [u32; 10] = [2, 3, 4, 5, 6, 7, 9, 10, 11, 12]; // supported lookup bit lengths

/// Breaks the 32-bit value into big-endian limbs following the required limb
/// lengths.
///
/// # Panics
///
/// If sum(limb_lengths) != 32.
/// If any given limb length equals 0.
pub(crate) fn u32_in_be_limbs<const N: usize>(value: u32, limb_lengths: [usize; N]) -> [u32; N] {
    for &len in &limb_lengths {
        assert!(len != 0);
    }
    u32_to_be_limbs(value, limb_lengths)
}

/// Generates the plain-spreaded lookup table.
pub(super) fn gen_spread_table<F: PrimeField>() -> impl Iterator<Item = (F, F, F)> {
    std::iter::once((F::ZERO, F::ZERO, F::ZERO)) // base case (disabled lookup)
        .chain(gen_table(LOOKUP_LENGTHS))
}

/// Computes off-circuit spreaded Maj(A, B, C) with A, B, C in spreaded forms.
///
/// # Panics
///
/// If A, B, C are not in clean spreaded form.
pub(super) fn spreaded_maj(spreaded_forms: [u64; 3]) -> u64 {
    spreaded_forms.into_iter().for_each(assert_in_valid_spreaded_form);

    let [sA, sB, sC] = spreaded_forms;

    // As each of sA, sB, sC is in valid spreaded form, their sum
    // is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    sA + sB + sC
}

/// Computes off-circuit spreaded Σ₀(A) with A in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub(super) fn spreaded_Sigma_0(spreaded_limbs: [u64; 4]) -> u64 {
    spreaded_limbs.into_iter().for_each(assert_in_valid_spreaded_form);

    let [sA_10, sA_09, sA_11, sA_02] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    pow4_ip([30, 20, 11, 0], [sA_02, sA_10, sA_09, sA_11])
        + pow4_ip([21, 19, 9, 0], [sA_11, sA_02, sA_10, sA_09])
        + pow4_ip([23, 12, 10, 0], [sA_09, sA_11, sA_02, sA_10])
}

/// Computes off-circuit spreaded Σ₁(E) with E in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub(super) fn spreaded_Sigma_1(spreaded_limbs: [u64; 5]) -> u64 {
    spreaded_limbs.into_iter().for_each(assert_in_valid_spreaded_form);

    let [sE_07, sE_12, sE_02, sE_05, sE_06] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    pow4_ip([26, 19, 7, 5, 0], [sE_06, sE_07, sE_12, sE_02, sE_05])
        + pow4_ip([27, 21, 14, 2, 0], [sE_05, sE_06, sE_07, sE_12, sE_02])
        + pow4_ip([20, 18, 13, 7, 0], [sE_12, sE_02, sE_05, sE_06, sE_07])
}

/// Computes off-circuit spreaded σ₀(W) with W in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub(super) fn spreaded_sigma_0(spreaded_limbs: [u64; 8]) -> u64 {
    spreaded_limbs.into_iter().for_each(assert_in_valid_spreaded_form);

    let [sW_12, sW_1a, sW_1b, sW_1c, sW_07, sW_3a, sW_04, sW_3b] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    pow4_ip(
        [17, 16, 15, 14, 7, 4, 0],
        [sW_12, sW_1a, sW_1b, sW_1c, sW_07, sW_3a, sW_04],
    ) + pow4_ip(
        [28, 25, 13, 12, 11, 10, 3, 0],
        [sW_04, sW_3b, sW_12, sW_1a, sW_1b, sW_1c, sW_07, sW_3a],
    ) + pow4_ip(
        [31, 24, 21, 17, 14, 2, 1, 0],
        [sW_1c, sW_07, sW_3a, sW_04, sW_3b, sW_12, sW_1a, sW_1b],
    )
}

/// Computes off-circuit spreaded σ₁(W) with W in (big endian) spreaded limbs.
///
/// # Panics
///
/// If the limbs are not in clean spreaded form.
pub(super) fn spreaded_sigma_1(spreaded_limbs: [u64; 8]) -> u64 {
    spreaded_limbs.into_iter().for_each(assert_in_valid_spreaded_form);

    let [sW_12, sW_1a, sW_1b, sW_1c, sW_07, sW_3a, sW_04, sW_3b] = spreaded_limbs;

    // As each limb is in valid spreaded form, the sum of three rotations composed
    // by the limbs is at most: 3 * 0b0101..01 = 0b1111..11.
    // Hence, the sum will never overflow u64.
    pow4_ip([10, 9, 8, 7, 0], [sW_12, sW_1a, sW_1b, sW_1c, sW_07])
        + pow4_ip(
            [25, 22, 18, 15, 3, 2, 1, 0],
            [sW_07, sW_3a, sW_04, sW_3b, sW_12, sW_1a, sW_1b, sW_1c],
        )
        + pow4_ip(
            [31, 30, 23, 20, 16, 13, 1, 0],
            [sW_1b, sW_1c, sW_07, sW_3a, sW_04, sW_3b, sW_12, sW_1a],
        )
}

/// Returns sum_i 4^(exponents\[i\]) * terms\[i\].
fn pow4_ip<const N: usize>(exponents: [u8; N], terms: [u64; N]) -> u64 {
    exponents.iter().zip(terms.iter()).map(|(e, t)| (1 << (2 * e)) * t).sum()
}

#[cfg(test)]
mod tests {
    use rand::{seq::SliceRandom, Rng};
    use super::*;
    type F = midnight_curves::Fq;

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
            let tag = *LOOKUP_LENGTHS.choose(&mut rng).unwrap();
            let plain = rng.gen_range(0..(1 << tag));
            let spreaded = spread(plain);
            let triple = to_fe((tag, plain, spreaded));
            assert!(table.contains(&triple));
        }
    }
}
