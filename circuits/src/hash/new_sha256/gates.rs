use ff::PrimeField;
use midnight_proofs::plonk::{Constraints, Expression};

/// Σ₀(A) gate.
pub fn Sigma_0_gate<F: PrimeField>(
    selector: Expression<F>,
    [sprdd_10, sprdd_09, sprdd_11, sprdd_02]: [Expression<F>; 4],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // 4^30 * ~limb_02 + 4^20 * ~limb_10 + 4^11 * ~limb_09  + ~limb_11
    let sprdd_1st_rot = linear_combination_pow4(
        [30, 20, 11, 0],
        [
            &sprdd_02.clone(),
            &sprdd_10.clone(),
            &sprdd_09.clone(),
            &sprdd_11.clone(),
        ],
    );

    // 4^21 * ~limb_11 + 4^19 * ~limb_02 + 4^9 * ~limb_10 + ~limb_09
    let sprdd_2nd_rot = linear_combination_pow4(
        [21, 19, 9, 0],
        [
            &sprdd_11.clone(),
            &sprdd_02.clone(),
            &sprdd_10.clone(),
            &sprdd_09.clone(),
        ],
    );

    // 4^23 * ~limb_09 + 4^12 * ~limb_11 + 4^10 * ~limb_02 + ~limb_10
    let sprdd_3rd_rot = linear_combination_pow4(
        [23, 12, 10, 0],
        [&sprdd_09, &sprdd_11, &sprdd_02, &sprdd_10],
    );

    // 4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8
    let sprdd_evn =
        linear_combination_pow4([20, 8, 0], [&sprdd_evn_12a, &sprdd_evn_12b, &sprdd_evn_8]);

    // 4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8
    let sprdd_odd =
        linear_combination_pow4([20, 8, 0], [&sprdd_odd_12a, &sprdd_odd_12b, &sprdd_odd_8]);

    let sprdd_Sigma_0_check = (sprdd_1st_rot + sprdd_2nd_rot + sprdd_3rd_rot)
        - (sprdd_evn + Expression::Constant(F::from(2)) * sprdd_odd);

    Constraints::with_selector(
        selector,
        [("Sigma_0 check", sprdd_Sigma_0_check)].into_iter(),
    )
}

/// Major(A, B, C) gate.
pub fn maj_gate<F: PrimeField>(
    selector: Expression<F>,
    [sprdd_a, sprdd_b, sprdd_c]: [Expression<F>; 3],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // 4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8
    let sprdd_evn =
        linear_combination_pow4([20, 8, 0], [&sprdd_evn_12a, &sprdd_evn_12b, &sprdd_evn_8]);

    // 4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8
    let sprdd_odd =
        linear_combination_pow4([20, 8, 0], [&sprdd_odd_12a, &sprdd_odd_12b, &sprdd_odd_8]);

    // (~A + ~B + ~C) - (~Even + 2 * ~Odd)
    let sprdd_maj_check =
        (sprdd_a + sprdd_b + sprdd_c) - (sprdd_evn + Expression::Constant(F::from(2)) * sprdd_odd);

    Constraints::with_selector(
        selector,
        [("Spreaded Major check", sprdd_maj_check)].into_iter(),
    )
}

/// Decompose 12-12-8 gate.
pub fn decompose_12_12_8_gate<F: PrimeField>(
    selector: Expression<F>,
    [limb_12a, limb_12b, limb_8]: [Expression<F>; 3],
    output: Expression<F>,
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // (2^20 * Limb.12a + 2^8 * Limb.12b + Limb.8) - output
    let decomposition_check =
        linear_combination_pow2([20, 8, 0], [&limb_12a, &limb_12b, &limb_8]) - output;

    Constraints::with_selector(
        selector,
        [("12-12-8 decomposition check", decomposition_check)].into_iter(),
    )
}

/// Decompose in 10-9-11-2 gate.
pub fn decompose_10_9_11_2_gate<F: PrimeField>(
    selector: Expression<F>,
    [limb_10, limb_09, limb_11, limb_02]: [Expression<F>; 4],
    [sprdd_limb_10, sprdd_limb_09, sprdd_limb_11, sprdd_limb_02]: [Expression<F>; 4],
    (plain, sprdd): (Expression<F>, Expression<F>),
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // 2^22 * limb_10 + 2^13 * limb_09 + 2^2 * limb_11 + limb_02 - plain
    let plain_id =
        linear_combination_pow2([22, 13, 2, 0], [&limb_10, &limb_09, &limb_11, &limb_02]) - plain;

    // 4^22 * ~limb_10 + 4^13 * ~limb_09 + 4^2 * ~limb_11 + ~limb_02 - sprdd
    let sprdd_id = linear_combination_pow4(
        [22, 13, 2, 0],
        [
            &sprdd_limb_10,
            &sprdd_limb_09,
            &sprdd_limb_11,
            &sprdd_limb_02,
        ],
    ) - sprdd;

    Constraints::with_selector(
        selector,
        [
            ("10_9_11_2 decomposition plain check", plain_id),
            ("10_9_11_2 decomposition sprdd check", sprdd_id),
        ]
        .into_iter(),
    )
}

/// Decompose in 7-12-2-5-6 gate.
pub fn decompose_7_12_2_5_6_gate<F: PrimeField>(
    selector: Expression<F>,
    [limb_07, limb_12, limb_02, limb_05, limb_06]: [Expression<F>; 5],
    [sprdd_limb_07, sprdd_limb_12, sprdd_limb_02, sprdd_limb_05, sprdd_limb_06]: [Expression<F>; 5],
    (plain, sprdd): (Expression<F>, Expression<F>),
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // (2^25 * limb_07 + 2^13 * limb_12 + 2^11 * limb_02 + 2^6 * limb_05 + limb_06)
    // - plain
    let plain_id = linear_combination_pow2(
        [25, 13, 11, 6, 0],
        [&limb_07, &limb_12, &limb_02, &limb_05, &limb_06],
    ) - plain;
    // (4^25 * ~limb_07 + 4^13 * ~limb_12 + 4^11 * ~limb_02 + 4^6 * ~limb_05 +
    // ~limb_06) - sprdd
    let sprdd_id = linear_combination_pow4(
        [25, 13, 11, 6, 0],
        [
            &sprdd_limb_07,
            &sprdd_limb_12,
            &sprdd_limb_02,
            &sprdd_limb_05,
            &sprdd_limb_06,
        ],
    ) - sprdd;

    Constraints::with_selector(
        selector,
        [
            ("7_12_2_5_6 decomposition plain check", plain_id),
            ("7_12_2_5_6 decomposition sprdd check", sprdd_id),
        ]
        .into_iter(),
    )
}

/// Computes a linear combination of terms with coefficients of powers of two.
fn linear_combination_pow2<F: PrimeField, const N: usize>(
    pow_of_coeffs: [u8; N],
    terms: [&Expression<F>; N],
) -> Expression<F> {
    let mut expr = Expression::Constant(F::ZERO);
    for (pow, term) in pow_of_coeffs.into_iter().zip(terms.into_iter()) {
        expr = expr + Expression::Constant(F::from(1 << pow)) * term.clone();
    }
    expr
}

/// Computes a linear combination of terms with coefficients of powers of four.
fn linear_combination_pow4<F: PrimeField, const N: usize>(
    pow_of_coeffs: [u8; N],
    terms: [&Expression<F>; N],
) -> Expression<F> {
    linear_combination_pow2(pow_of_coeffs.map(|l| 2 * l), terms)
}
