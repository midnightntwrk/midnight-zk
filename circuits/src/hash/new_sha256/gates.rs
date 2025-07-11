use ff::PrimeField;
use midnight_proofs::plonk::{Constraints, Expression};

/// Σ₀(A) gate.
pub fn Sigma_0<F: PrimeField>(
    s_Sigma_0: Expression<F>,
    [spreaded_a_10, spreaded_a_9, spreaded_a_11, spreaded_a_2]: [Expression<F>; 4],
    [spreaded_even_12a, spreaded_even_12b, spreaded_even_8]: [Expression<F>; 3],
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
    // 4^20 * ~Even.12a + 4^8 * ~Even.12b + ~Even.8
    let spreaded_even = linear_combination_pow4(
        [20, 8, 0],
        [&spreaded_even_12a, &spreaded_even_12b, &spreaded_even_8],
    );
    // 4^20 *  ~Odd.12a + 4^8 *  ~Odd.12b +  ~Odd.8
    let spreaded_odd = linear_combination_pow4(
        [20, 8, 0],
        [&spreaded_odd_12a, &spreaded_odd_12b, &spreaded_odd_8],
    );

    let spreaded_Sigma_0_check = (spreaded_1st_rot + spreaded_2nd_rot + spreaded_3rd_rot)
        + Expression::Constant(-F::ONE)
            * (spreaded_even + Expression::Constant(F::from(2)) * spreaded_odd);

    Constraints::with_selector(
        s_Sigma_0,
        [("Spreaded Sigma_0 check", spreaded_Sigma_0_check)].into_iter(),
    )
}

/// Decompose 12-12-8 gate.
pub fn decompose_12_12_8<F: PrimeField>(
    s_12_12_8: Expression<F>,
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
        s_12_12_8,
        [("12-12-8 decomposition check", decomposition_check)].into_iter(),
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
