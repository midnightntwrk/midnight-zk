use ff::PrimeField;
use midnight_proofs::plonk::Expression;

/// Σ₀(A) gate.
pub fn Sigma_0_gate<F: PrimeField>(
    [sprdd_10, sprdd_09, sprdd_11, sprdd_02]: [Expression<F>; 4],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
) -> Vec<(&'static str, Expression<F>)> {
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

    vec![("Sigma_0 check", sprdd_Sigma_0_check)]
}

/// Σ₁(E) gate.
pub fn Sigma_1_gate<F: PrimeField>(
    [sprdd_07, sprdd_12, sprdd_02, sprdd_05, sprdd_06]: [Expression<F>; 5],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
) -> Vec<(&'static str, Expression<F>)> {
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

    vec![("Sigma_1 check", sprdd_Sigma_1_check)]
}

/// Major(A, B, C) gate.
pub fn maj_gate<F: PrimeField>(
    [sprdd_a, sprdd_b, sprdd_c]: [Expression<F>; 3],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
) -> Vec<(&'static str, Expression<F>)> {
    // 4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8
    let sprdd_evn =
        linear_combination_pow4([20, 8, 0], [&sprdd_evn_12a, &sprdd_evn_12b, &sprdd_evn_8]);

    // 4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8
    let sprdd_odd =
        linear_combination_pow4([20, 8, 0], [&sprdd_odd_12a, &sprdd_odd_12b, &sprdd_odd_8]);

    // (~A + ~B + ~C) - (~Evn + 2 * ~Odd)
    let sprdd_maj_check =
        (sprdd_a + sprdd_b + sprdd_c) - (sprdd_evn + Expression::Constant(F::from(2)) * sprdd_odd);

    vec![("Spreaded Maj check", sprdd_maj_check)]
}

/// Half Ch(E, F, G) gate.
pub fn half_ch_gate<F: PrimeField>(
    [sprdd_x, sprdd_y]: [Expression<F>; 2],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
    [summand_1, summand_2, sum]: [Expression<F>; 3],
) -> Vec<(&'static str, Expression<F>)> {
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

    vec![
        ("Spreaded half Ch check", sprdd_add_check),
        ("Half Ch check (2-term add)", add_check),
    ]
}

/// Decompose 12-12-8 gate.
pub fn decompose_12_12_8_gate<F: PrimeField>(
    [limb_12a, limb_12b, limb_8]: [Expression<F>; 3],
    output: Expression<F>,
) -> Vec<(&'static str, Expression<F>)> {
    // (2^20 * Limb.12a + 2^8 * Limb.12b + Limb.8) - output
    let decomposition_check =
        linear_combination_pow2([20, 8, 0], [&limb_12a, &limb_12b, &limb_8]) - output;

    vec![("12-12-8 decomposition check", decomposition_check)]
}

/// Decompose in 10-9-11-2 gate.
pub fn decompose_10_9_11_2_gate<F: PrimeField>(
    [limb_10, limb_09, limb_11, limb_02]: [Expression<F>; 4],
    [sprdd_limb_10, sprdd_limb_09, sprdd_limb_11, sprdd_limb_02]: [Expression<F>; 4],
    (plain, sprdd): (Expression<F>, Expression<F>),
) -> Vec<(&'static str, Expression<F>)> {
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

    vec![
        ("10_9_11_2 decomposition plain check", plain_id),
        ("10_9_11_2 decomposition sprdd check", sprdd_id),
    ]
}

/// Decompose in 7-12-2-5-6 gate.
pub fn decompose_7_12_2_5_6_gate<F: PrimeField>(
    [limb_07, limb_12, limb_02, limb_05, limb_06]: [Expression<F>; 5],
    [sprdd_limb_07, sprdd_limb_12, sprdd_limb_02, sprdd_limb_05, sprdd_limb_06]: [Expression<F>; 5],
    (plain, sprdd): (Expression<F>, Expression<F>),
) -> Vec<(&'static str, Expression<F>)> {
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

    vec![
        ("7_12_2_5_6 decomposition plain check", plain_id),
        ("7_12_2_5_6 decomposition sprdd check", sprdd_id),
    ]
}

/// Addition modulo 2^32. The carry and result must be range-checked elsewhere.
/// At least one summand is required.
pub fn add_mod_2_32_gate<F: PrimeField>(
    summands: &[Expression<F>],
    carry: Expression<F>,
    result: Expression<F>,
) -> Vec<(&'static str, Expression<F>)> {
    assert!(!summands.is_empty(), "At least one summand is required");
    let lhs = (summands.iter().cloned()).reduce(|acc, x| acc + x).unwrap();
    let rhs = result + carry * Expression::Constant(F::from(1u64 << 32));

    vec![("add_mod_2_32 check", lhs - rhs)]
}

/// Decompose in 12-1-1-1-7-3-4-3 gate.
pub fn decompose_12_1_1_1_7_3_4_3_gate<F: PrimeField>(
    [w_12, w_1a, w_1b, w_1c, w_07, w_3a, w_04, w_3b]: [Expression<F>; 8],
    plain: Expression<F>,
) -> Vec<(&'static str, Expression<F>)> {
    // (2^20 * W.12 + 2^19 * W.1a + 2^18 * W.1b + 2^17 * W.1c + 2^10 * W.07 + 2^7 *
    // W.3a + 2^3 * W.04 + W.3b) - plain
    let plain_id = linear_combination_pow2(
        [20, 19, 18, 17, 10, 7, 3, 0],
        [&w_12, &w_1a, &w_1b, &w_1c, &w_07, &w_3a, &w_04, &w_3b],
    ) - plain;

    // 1-bit check for W.1a, W.1b and W.1c
    let w_1a_check = w_1a.clone() * (w_1a - Expression::Constant(F::ONE));
    let w_1b_check = w_1b.clone() * (w_1b - Expression::Constant(F::ONE));
    let w_1c_check = w_1c.clone() * (w_1c - Expression::Constant(F::ONE));

    vec![
        ("12_1_1_1_7_3_4_3 decomposition plain check", plain_id),
        ("W.1a 1-bit check", w_1a_check),
        ("W.1b 1-bit check", w_1b_check),
        ("W.1c 1-bit check", w_1c_check),
    ]
}

/// σ₀(W) gate.
pub fn sigma_0_gate<F: PrimeField>(
    [sprdd_w_12, sprdd_w_1a, sprdd_w_1b, sprdd_w_1c, sprdd_w_07, sprdd_w_3a, sprdd_w_04, sprdd_w_3b]: [Expression<F>;
        8],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
) -> Vec<(&'static str, Expression<F>)> {
    // 4^17 * ~W.12 + 4^16 * ~W.1a + 4^15 * ~W.1b + 4^14 * ~W.1c + 4^7 * ~W.07 + 4^4
    // * ~W.3a + ~W.04
    let sprdd_1st_shift = linear_combination_pow4(
        [17, 16, 15, 14, 7, 4, 0],
        [
            &sprdd_w_12,
            &sprdd_w_1a,
            &sprdd_w_1b,
            &sprdd_w_1c,
            &sprdd_w_07,
            &sprdd_w_3a,
            &sprdd_w_04,
        ],
    );

    // 4^28 * ~W.04 + 4^25 * ~W.3b + 4^13 * ~W.12 + 4^12 * ~W.1a + 4^11 * ~W.1b +
    // 4^10 * ~W.1c + 4^3 * ~W.07 + ~W.3a
    let sprdd_2nd_rot = linear_combination_pow4(
        [28, 25, 13, 12, 11, 10, 3, 0],
        [
            &sprdd_w_04,
            &sprdd_w_3b,
            &sprdd_w_12,
            &sprdd_w_1a,
            &sprdd_w_1b,
            &sprdd_w_1c,
            &sprdd_w_07,
            &sprdd_w_3a,
        ],
    );

    // 4^31 * ~W.1c + 4^24 * ~W.07 + 4^21 * ~W.3a + 4^17 * ~W.04 + 4^14 * ~W.3b +
    // 4^2 * ~W.12 + 4^1 * ~W.1a + ~W.1b
    let sprdd_3rd_rot = linear_combination_pow4(
        [31, 24, 21, 17, 14, 2, 1, 0],
        [
            &sprdd_w_1c,
            &sprdd_w_07,
            &sprdd_w_3a,
            &sprdd_w_04,
            &sprdd_w_3b,
            &sprdd_w_12,
            &sprdd_w_1a,
            &sprdd_w_1b,
        ],
    );

    // 4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8
    let sprdd_evn =
        linear_combination_pow4([20, 8, 0], [&sprdd_evn_12a, &sprdd_evn_12b, &sprdd_evn_8]);

    // 4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8
    let sprdd_odd =
        linear_combination_pow4([20, 8, 0], [&sprdd_odd_12a, &sprdd_odd_12b, &sprdd_odd_8]);

    let sprdd_sigma_0_check = (sprdd_1st_shift + sprdd_2nd_rot + sprdd_3rd_rot)
        - (sprdd_evn + Expression::Constant(F::from(2)) * sprdd_odd);

    vec![("Spreaded σ₀(W) check", sprdd_sigma_0_check)]
}

/// σ₁(W) gate.
pub fn sigma_1_gate<F: PrimeField>(
    [sprdd_w_12, sprdd_w_1a, sprdd_w_1b, sprdd_w_1c, sprdd_w_07, sprdd_w_3a, sprdd_w_04, sprdd_w_3b]: [Expression<F>;
        8],
    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8]: [Expression<F>; 3],
    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8]: [Expression<F>; 3],
) -> Vec<(&'static str, Expression<F>)> {
    // 4^10 * ~W.12 + 4^9 * ~W.1a + 4^8 * ~W.1b + 4^7 * ~W.1c + ~W.07
    let sprdd_1st_shift = linear_combination_pow4(
        [10, 9, 8, 7, 0],
        [
            &sprdd_w_12,
            &sprdd_w_1a,
            &sprdd_w_1b,
            &sprdd_w_1c,
            &sprdd_w_07,
        ],
    );

    // 4^25 * ~W.07 + 4^22 * ~W.3a + 4^18 * ~W.04 + 4^15 * ~W.3b + 4^3 * ~W.12 + 4^2
    // * ~W.1a + 4^1 * ~W.1b + ~W.1c
    let sprdd_2nd_rot = linear_combination_pow4(
        [25, 22, 18, 15, 3, 2, 1, 0],
        [
            &sprdd_w_07,
            &sprdd_w_3a,
            &sprdd_w_04,
            &sprdd_w_3b,
            &sprdd_w_12,
            &sprdd_w_1a,
            &sprdd_w_1b,
            &sprdd_w_1c,
        ],
    );

    // 4^31 * ~W.1b + 4^30 * ~W.1c + 4^23 * ~W.07 + 4^20 * ~W.3a + 4^16 * ~W.04 +
    // 4^13 * ~W.3b + 4^1 * ~W.12 + ~W.1a
    let sprdd_3rd_rot = linear_combination_pow4(
        [31, 30, 23, 20, 16, 13, 1, 0],
        [
            &sprdd_w_1b,
            &sprdd_w_1c,
            &sprdd_w_07,
            &sprdd_w_3a,
            &sprdd_w_04,
            &sprdd_w_3b,
            &sprdd_w_12,
            &sprdd_w_1a,
        ],
    );

    // 4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8
    let sprdd_evn =
        linear_combination_pow4([20, 8, 0], [&sprdd_evn_12a, &sprdd_evn_12b, &sprdd_evn_8]);

    // 4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8
    let sprdd_odd =
        linear_combination_pow4([20, 8, 0], [&sprdd_odd_12a, &sprdd_odd_12b, &sprdd_odd_8]);

    let sprdd_sigma_1_check = (sprdd_1st_shift + sprdd_2nd_rot + sprdd_3rd_rot)
        - (sprdd_evn + Expression::Constant(F::from(2)) * sprdd_odd);

    vec![("Spreaded σ₁(W) check", sprdd_sigma_1_check)]
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
