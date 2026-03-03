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
///        evaluated and, thus, the resulting scalar `id_j(x)` contributes to
///        the affine term `C` of the linearization polynomial),
/// * `h_k(T)` are the limbs of the quotient polynomial.
///
/// The linearization polynomial is split into its homogeneous and affine parts:
/// `L(X) = L'(X) + C`. Both parts are returned separately.
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
/// A tuple `(L'(X), C)`, where `L'(X)` is a [Polynomial] and `C` is a constant.
/// The verifier uses `-C` as the expected evaluation of `L'(X)` at `x`.
pub(crate) fn compute_linearization_poly<F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    expressions: Vec<(Option<usize>, F)>,
    pk: &ProvingKey<F, CS>,
    y: F,
    xn: F,
    splitting_factor: F,
    quotient_limbs: Vec<Polynomial<F, Coeff>>,
) -> (Polynomial<F, Coeff>, F) {
    let mut y_pow = F::ONE;
    let mut lin_poly_affine_term = F::ZERO;
    let lin_poly = expressions.iter().rev().fold(
        Polynomial::init(pk.vk.get_domain().n as usize),
        |acc, (col_idx, eval)| match col_idx {
            Some(col_idx) => {
                let acc = acc + pk.fixed_polys[*col_idx].clone() * (y_pow * eval);
                y_pow *= y;
                acc
            }
            None => {
                // The constant term is excluded from L'(X). It is moved to the
                // eval side of the VerifierQuery (as -C) by the verifier.
                lin_poly_affine_term += y_pow * eval;
                y_pow *= y;
                acc
            }
        },
    );

    let splitting_powers = successors(Some(xn - F::ONE), |&prev| Some(prev * splitting_factor));

    // When the `single-h-commitment` feature is enabled `quotient_limbs` contains a
    // single element: the full quotient polynomial H(X). In that case this
    // loop executes once and produces `lin_poly - (x^n - 1) * H(X)`, which
    // evaluates to zero at `x` iff the circuit is satisfied (same as the
    // multi-limb case). The resulting polynomial has degree deg(H), so
    // the caller must supply params with a sufficiently large SRS.
    //
    let lin_poly = quotient_limbs
        .iter()
        .zip(splitting_powers)
        .map(|(l, p)| l.clone() * p)
        .fold(lin_poly, |acc, next| acc.padded_sub(&next));

    (lin_poly, lin_poly_affine_term)
}
