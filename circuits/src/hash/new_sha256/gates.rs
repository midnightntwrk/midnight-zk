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
    // 4^30 * ~L02 + 4^20 * ~L10 + 4^11 * ~L09  + ~L11
    let sprdd_1st_rot = linear_combination_pow4(
        [30, 20, 11, 0],
        [
            &sprdd_02.clone(),
            &sprdd_10.clone(),
            &sprdd_09.clone(),
            &sprdd_11.clone(),
        ],
    );

    // 4^21 * ~L11 + 4^19 * ~L02 + 4^9 * ~L10 + ~L09
    let sprdd_2nd_rot = linear_combination_pow4(
        [21, 19, 9, 0],
        [
            &sprdd_11.clone(),
            &sprdd_02.clone(),
            &sprdd_10.clone(),
            &sprdd_09.clone(),
        ],
    );

    // 4^23 * ~L09 + 4^12 * ~L11 + 4^10 * ~L02 + ~L10
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

    // (~A + ~B + ~C) - (~Evn + 2 * ~Odd)
    let sprdd_maj_check =
        (sprdd_a + sprdd_b + sprdd_c) - (sprdd_evn + Expression::Constant(F::from(2)) * sprdd_odd);

    Constraints::with_selector(
        selector,
        [("Spreaded Major check", sprdd_maj_check)].into_iter(),
    )
}

/// Σ₁(E) gate.
pub fn Sigma_1_gate<F: PrimeField>(
    selector: Expression<F>,
    [sprdd_07, sprdd_12, sprdd_02, sprdd_05, sprdd_06]: [Expression<F>; 5],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // 4^26 * ~L06 + 4^19 * ~L07 + 4^7 * ~L12 + 4^5 * ~L02 + ~L05
    let sprdd_1st_rot = linear_combination_pow4(
        [26, 19, 7, 5, 0],
        [&sprdd_06, &sprdd_07, &sprdd_12, &sprdd_02, &sprdd_05],
    );

    // 4^27 * ~L05 + 4^21 * ~L06 + 4^14 * ~L07 + 4^2 * ~L12 + ~L02
    let sprdd_2nd_rot = linear_combination_pow4(
        [27, 21, 14, 2, 0],
        [&sprdd_05, &sprdd_06, &sprdd_07, &sprdd_12, &sprdd_02],
    );

    // 4^20 * ~L12 + 4^18 * ~L02 + 4^13 * ~L05 + 4^7 * ~L06 + ~L07
    let sprdd_3rd_rot = linear_combination_pow4(
        [20, 18, 13, 7, 0],
        [&sprdd_12, &sprdd_02, &sprdd_05, &sprdd_06, &sprdd_07],
    );

    // 4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8
    let sprdd_evn =
        linear_combination_pow4([20, 8, 0], [&sprdd_evn_12a, &sprdd_evn_12b, &sprdd_evn_8]);

    // 4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8
    let sprdd_odd =
        linear_combination_pow4([20, 8, 0], [&sprdd_odd_12a, &sprdd_odd_12b, &sprdd_odd_8]);

    let sprdd_Sigma_1_check = (sprdd_1st_rot + sprdd_2nd_rot + sprdd_3rd_rot)
        - (sprdd_evn + Expression::Constant(F::from(2)) * sprdd_odd);

    Constraints::with_selector(
        selector,
        [("Sigma_1 check", sprdd_Sigma_1_check)].into_iter(),
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
    // 2^22 * L10 + 2^13 * L09 + 2^2 * L11 + L02 - plain
    let plain_id =
        linear_combination_pow2([22, 13, 2, 0], [&limb_10, &limb_09, &limb_11, &limb_02]) - plain;

    // 4^22 * ~L10 + 4^13 * ~L09 + 4^2 * ~L11 + ~L02 - sprdd
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
    // (2^25 * L07 + 2^13 * L12 + 2^11 * L02 + 2^6 * L05 + L06) - plain
    let plain_id = linear_combination_pow2(
        [25, 13, 11, 6, 0],
        [&limb_07, &limb_12, &limb_02, &limb_05, &limb_06],
    ) - plain;
    // (4^25 * ~L07 + 4^13 * ~L12 + 4^11 * ~L02 + 4^6 * ~L05 + ~L06) - sprdd
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

/// Addition modulo 2^32. The carry and result must be range-checked elsewhere.
/// At least one summand is required.
pub fn add_mod_2_32_gate<F: PrimeField>(
    selector: Expression<F>,
    summands: &[Expression<F>],
    carry: Expression<F>,
    result: Expression<F>,
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    assert!(!summands.is_empty(), "At least one summand is required");
    let lhs = (summands.iter().cloned()).reduce(|acc, x| acc + x).unwrap();
    let rhs = result + carry * Expression::Constant(F::from(1u64 << 32));

    Constraints::with_selector(selector, [("add_mod_2_32 check", lhs - rhs)].into_iter())
}

/// Helper gate, used to compute Ch(E, F, G).
pub fn ch_helper_gate<F: PrimeField>(
    selector: Expression<F>,
    [sprdd_x, sprdd_y]: [Expression<F>; 2],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
    [summand_1, summand_2, sum]: [Expression<F>; 3],
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

    // (~X + ~Y) - (~Evn + 2 * ~Odd)
    let sprdd_add_check =
        (sprdd_x + sprdd_y) - (sprdd_evn + Expression::Constant(F::from(2)) * sprdd_odd);

    // (summand_1 + summand_2) - sum
    let add_check = (summand_1 + summand_2) - sum;

    Constraints::with_selector(
        selector,
        [
            ("Spreaded addition check", sprdd_add_check),
            ("Addition check", add_check),
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
