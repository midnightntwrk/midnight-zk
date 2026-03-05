use std::iter::successors;

use ff::PrimeField;

use crate::{
    plonk::ProvingKey,
    poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial},
};

/// Construct the linearization polynomial:
///
///  `S_0(T) * id_0(x) + y * S_1(T) * id_1(x) + ... + y^m * S_m(T) * id_m(x)
///      - (h_0(T) + x^{n-1} * h_1(T) + ... + x^{l*(n-1)} * h_l(T)) * (x^n-1),`
///
/// where:
/// * `y` is the batching challenge,
/// * `x` is the evaluation challenge,
/// * `id_j(x)` is a (partially or fully) evaluated identity at `x`,
/// * `S_j(T)` is, either,
///      - (i)  the polynomial of a fixed column corresponding to a simple,
///        multiplicative selector, or,
///      - (ii) 1 (in case the corresponding identity `id_j` has been fully
///        evaluated and, thus, the resulting scalar `id_j(x)` is part of the
///        constant term of the linearization polynomial),
/// * `h_k(T)` are the limbs of the quotient polynomial.
///
/// # Arguments
///
/// * `expressions` - the output of
///   [crate::plonk::partially_evaluate_identities]
/// * `splitting_factor` - the evaluated splitting factor `x^{n-1}` from
///   decomposing the quotient polynomial `h(T)` into limbs
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
                let acc = acc + pk.fixed_polys[*col_idx].clone() * (y_pow * eval);
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
        .map(|(l, p)| l.clone() * p)
        .fold(lin_poly, |acc, next| acc - &next)
}
