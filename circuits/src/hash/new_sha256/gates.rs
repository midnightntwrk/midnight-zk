use ff::PrimeField;
use midnight_proofs::plonk::{Constraints, Expression};
/// A in 10-9-11-2 decomposition gate.
pub fn a_in_10_9_11_2_gate<F: PrimeField>(
    s_a_in_10_9_11_2: Expression<F>,
    [limb_10, limb_9, limb_11, limb_1a, limb_1b]: [Expression<F>; 5],
    [spreaded_limb_10, spreaded_limb_9, spreaded_limb_11, spreaded_limb_2]: [Expression<F>; 4],
    a: Expression<F>,
    spreaded_a: Expression<F>,
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // (2^22 * A.10 + 2^13 * A.9 + 2^2 * A.11 + 2 * A.1a + A.1b) - A
    let a_decomposition_check = linear_combination_pow2(
        [22, 13, 2, 1, 0],
        [&limb_10, &limb_9, &limb_11, &limb_1a, &limb_1b],
    ) + (Expression::Constant(-F::ONE) * a);

    // (4^22 * ~A.10 + 4^13 * ~A.9 + 4^2 * ~A.11 + ~A.2) - ~A
    let a_spreaded_check = linear_combination_pow4(
        [22, 13, 2, 0],
        [
            &spreaded_limb_10,
            &spreaded_limb_9,
            &spreaded_limb_11,
            &spreaded_limb_2,
        ],
    ) + (Expression::Constant(-F::ONE) * spreaded_a);

    // 1-bit rangecheck
    let limb_1a_check = limb_1a.clone() * (limb_1a.clone() - Expression::Constant(F::from(1)));
    let limb_1b_check = limb_1b.clone() * (limb_1b.clone() - Expression::Constant(F::from(1)));

    // (4 * A.1a + A.1b) - ~A.2
    let limb_2_spreaded_check = linear_combination_pow4([1, 0], [&limb_1a, &limb_1b])
        + (Expression::Constant(-F::ONE) * spreaded_limb_2);

    Constraints::with_selector(
        s_a_in_10_9_11_2,
        [
            ("A decomposition check", a_decomposition_check),
            ("A spreaded check", a_spreaded_check),
            ("Limb 1a check", limb_1a_check),
            ("Limb 1b check", limb_1b_check),
            ("Limb 2 spreaded check", limb_2_spreaded_check),
        ]
        .into_iter(),
    )
}

/// Σ₀(A) gate.
pub fn Sigma_0_gate<F: PrimeField>(
    q_Sigma_0: Expression<F>,
    [spreaded_a_10, spreaded_a_9, spreaded_a_11, spreaded_a_2]: [Expression<F>; 4],
    [spreaded_evn_12a, spreaded_evn_12b, spreaded_evn_8]: [Expression<F>; 3],
    [spreaded_odd_12a, spreaded_odd_12b, spreaded_odd_8]: [Expression<F>; 3],
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // 4^30 *  ~A.2  +  4^20 * ~A.10  +  4^11 *  ~A.9  +  ~A.11
    let spreaded_1st_rot = linear_combination_pow4(
        [30, 20, 11, 0],
        [
            &spreaded_a_2.clone(),
            &spreaded_a_10.clone(),
            &spreaded_a_9.clone(),
            &spreaded_a_11.clone(),
        ],
    );
    // 4^21 * ~A.11  +  4^19 *  ~A.2  +  4^9 * ~A.10  +  ~A.9
    let spreaded_2nd_rot = linear_combination_pow4(
        [21, 19, 9, 0],
        [
            &spreaded_a_11.clone(),
            &spreaded_a_2.clone(),
            &spreaded_a_10.clone(),
            &spreaded_a_9.clone(),
        ],
    );
    // 4^23 *  ~A.9  +  4^12 * ~A.11  +  4^10 *  ~A.2  +  ~A.10
    let spreaded_3rd_rot = linear_combination_pow4(
        [23, 12, 10, 0],
        [&spreaded_a_9, &spreaded_a_11, &spreaded_a_2, &spreaded_a_10],
    );
    // 4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8
    let spreaded_evn = linear_combination_pow4(
        [20, 8, 0],
        [&spreaded_evn_12a, &spreaded_evn_12b, &spreaded_evn_8],
    );
    // 4^20 *  ~Odd.12a + 4^8 *  ~Odd.12b +  ~Odd.8
    let spreaded_odd = linear_combination_pow4(
        [20, 8, 0],
        [&spreaded_odd_12a, &spreaded_odd_12b, &spreaded_odd_8],
    );

    let spreaded_Sigma_0_check = (spreaded_1st_rot + spreaded_2nd_rot + spreaded_3rd_rot)
        + Expression::Constant(-F::ONE)
            * (spreaded_evn + Expression::Constant(F::from(2)) * spreaded_odd);

    Constraints::with_selector(
        q_Sigma_0,
        [("Spreaded Sigma_0 check", spreaded_Sigma_0_check)].into_iter(),
    )
}

/// Decompose 12-12-8 gate.
pub fn decompose_12_12_8_gate<F: PrimeField>(
    q_12_12_8: Expression<F>,
    [limb_12a, limb_12b, limb_8]: [Expression<F>; 3],
    output: Expression<F>,
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // (2^20 * Limb.12a + 2^8 * Limb.12b + Limb.8) - output
    let decomposition_check = linear_combination_pow2([20, 8, 0], [&limb_12a, &limb_12b, &limb_8])
        + (Expression::Constant(-F::ONE) * output);

    Constraints::with_selector(
        q_12_12_8,
        [("12-12-8 decomposition check", decomposition_check)].into_iter(),
    )
}

/// Major(A, B, C) gate.
pub fn maj_gate<F: PrimeField>(
    q_maj: Expression<F>,
    [spreaded_a, spreaded_b, spreaded_c]: [Expression<F>; 3],
    [spreaded_evn_12a, spreaded_evn_12b, spreaded_evn_8]: [Expression<F>; 3],
    [spreaded_odd_12a, spreaded_odd_12b, spreaded_odd_8]: [Expression<F>; 3],
) -> Constraints<
    F,
    (&'static str, Expression<F>),
    impl Iterator<Item = (&'static str, Expression<F>)>,
> {
    // 4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8
    let spreaded_evn = linear_combination_pow4(
        [20, 8, 0],
        [&spreaded_evn_12a, &spreaded_evn_12b, &spreaded_evn_8],
    );
    // 4^20 *  ~Odd.12a + 4^8 *  ~Odd.12b +  ~Odd.8
    let spreaded_odd = linear_combination_pow4(
        [20, 8, 0],
        [&spreaded_odd_12a, &spreaded_odd_12b, &spreaded_odd_8],
    );
    // (~A + ~B + ~C) - (~Even + 2 * ~Odd)
    let spreaded_maj_check = (spreaded_a + spreaded_b + spreaded_c)
        + Expression::Constant(-F::ONE)
            * (spreaded_evn + Expression::Constant(F::from(2)) * spreaded_odd);

    Constraints::with_selector(
        q_maj,
        [("Spreaded Major check", spreaded_maj_check)].into_iter(),
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
