use std::iter::successors;

use ff::PrimeField;

use crate::{
    plonk::ProvingKey,
    poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial},
};

/// Construct the linearization polynomial:
///
///  S_1(X)*id_1(x) + y*S_2(X)*id_2(x) + ... + y^{k-1}*S_k(X)*id_k(x)
///      - (h_0(X) + x^n*h_1(X) + ... + x^{l*n}*h_l(X)) * (x^n-1),
///
/// where:
/// * y is the batching challenge, for batching independent identities,
/// * x is the evaluation challenge,
/// * S_i(X) is a gate selector poly (possibly 1, if no gate selector exists)
/// * id_i(X) is the partially evaluated individual identity,
/// * h_j(X) are the limbs of the quotient polynomial.
pub(crate) fn compute_linearization_poly<'a, F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    expressions: impl Iterator<Item = (Option<usize>, F)> + 'a,
    pk: &ProvingKey<F, CS>,
    y: F,
    xn: F,
    quotient_limbs: Vec<Polynomial<F, Coeff>>,
) -> Polynomial<F, Coeff> {
    let mut y_pow = F::ONE;
    let lin_poly = expressions.collect::<Vec<(Option<usize>, F)>>().iter().rev().fold(
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

    let xn_powers = successors(Some(xn - F::ONE), |&prev| Some(prev * xn));
    quotient_limbs
        .iter()
        .zip(xn_powers)
        .map(|(l, p)| l * p)
        .fold(lin_poly, |acc, next| acc - &next)
}
