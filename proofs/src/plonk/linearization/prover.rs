use std::iter::successors;

use ff::PrimeField;

use crate::{
    plonk::ProvingKey,
    poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial},
};

/// Construct the linearization polynomial:
///
///  S_0(X) * id_0(x) + y * S_1(X) * id_1(x) + ... + y^m * S_m(X) * id_m(x)
///      - (h_0(X) + x^{n-1} * h_1(X) + ... + x^{l*(n-1)} * h_l(X)) * (x^n-1),
///
/// where:
/// * y is the batching challenge,
/// * x is the evaluation challenge,
/// * id_j(x) is a (partially or fully) evaluated identity at x,
/// * S_j(X) is, either,
///      - (i)  the poly of a fixed column corresponding to a simple,
///        multiplicative selector, or,
///      - (ii) 1 (in case the corresponding identity id_j has been fully
///        evaluated and, thus, the resulting scalar is part of the constant
///        term of the linearization poly),
/// * h_k(X) are the limbs of the quotient polynomial.
///
/// # Returns
///
/// The linearization polynomial as [Polynomial].
pub(crate) fn compute_linearization_poly<F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    expressions: Vec<(Option<usize>, F)>,
    pk: &ProvingKey<F, CS>,
    y: F,
    xn: F,
    splitting_factor: F,
    quotient_limbs: Vec<Polynomial<F, Coeff>>,
) -> Polynomial<F, Coeff> {
    let mut y_pow = F::ONE;
    let lin_poly = expressions.iter().rev().fold(
        Polynomial::init(pk.vk.get_domain().n as usize),
        |mut acc, (col_idx, eval)| match col_idx {
            Some(col_idx) => {
                let acc = acc + &pk.fixed_polys[*col_idx] * (y_pow * eval);
                y_pow *= y;
                acc
            }
            None => {
                acc.values[0] += y_pow * eval;
                y_pow *= y;
                acc
            }
        },
    );

    let splitting_powers = successors(Some(xn - F::ONE), |&prev| Some(prev * splitting_factor));

    quotient_limbs
        .iter()
        .zip(splitting_powers)
        .map(|(l, p)| l * p)
        .fold(lin_poly, |acc, next| acc - &next)
}
