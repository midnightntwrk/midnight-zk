use std::collections::BTreeMap;

use ff::PrimeField;

use crate::{plonk::VerifyingKey, poly::commitment::PolynomialCommitmentScheme};

/// Construct the commitment to the linearization polynomial and its expected
/// evaluation at `x`.
///
/// The commitment is:
///
///  `S_0 * id_0(x) + y * S_1 * id_1(x) + ... + y^m * S_m * id_m(x)
///        - (h_0 + x^{n-1} * h_1 + ... + x^{l*(n-1)} * h_l) * (x^n-1),`
///
/// where:
/// * `y` is the batching challenge,
/// * `x` is the evaluation challenge,
/// * `id_j(x)` is a (partially or fully) evaluated identity at `x`,
/// * `S_j` is either the commitment to a simple selector column or the
///   commitment to `P(X) = 1` (for fully evaluated identities),
/// * `h_k` are commitments to the limbs of the quotient polynomial.
///
/// # Returns
///
/// `(commitment, expected_eval)` where the commitment to the linearization
/// polynomial is expected to open to `expected_eval` at `x`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_linearization_commitment<
    F: PrimeField + ff::WithSmallOrderMulGroup<3> + ff::FromUniformBytes<64> + std::cmp::Ord,
    CS: PolynomialCommitmentScheme<F>,
>(
    expressions: Vec<(Option<usize>, F)>,
    vk: &VerifyingKey<F, CS>,
    y: &F,
    xn: &F,
    splitting_factor: &F,
    quotient_limb_commitments: &[CS::Commitment],
) -> (CS::Commitment, F) {
    let mut terms: Vec<(F, CS::Commitment)> = Vec::new();

    let mut splitting_pow = F::ONE - *xn;
    for com in quotient_limb_commitments {
        terms.push((splitting_pow, com.clone()));
        splitting_pow *= splitting_factor;
    }

    // Group multiples of the same fixed column in the MSM
    let mut grouped_points: BTreeMap<Option<usize>, F> = BTreeMap::new();
    let mut y_pow = F::ONE;
    expressions.iter().rev().for_each(|(col_idx, eval)| {
        *grouped_points.entry(*col_idx).or_insert(F::ZERO) += y_pow * eval;
        y_pow *= y;
    });

    let mut expected_eval = F::ZERO;
    grouped_points.into_iter().for_each(|(col_idx, eval)| match col_idx {
        Some(col_idx) => terms.push((eval, vk.fixed_commitments[col_idx].clone())),
        None => expected_eval -= eval,
    });

    let commitment = terms
        .into_iter()
        .map(|(scalar, com)| com * scalar)
        .reduce(|acc, term| acc + term)
        .unwrap_or_default();

    (commitment, expected_eval)
}
