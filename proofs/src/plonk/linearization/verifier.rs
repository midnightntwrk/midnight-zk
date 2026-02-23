use std::collections::BTreeMap;

use ff::PrimeField;

use crate::{
    plonk::VerifyingKey,
    poly::{commitment::PolynomialCommitmentScheme, CommitmentLabel, VerifierQuery},
};

/// Construct the commitment to the linearization polynomial
/// (which will be checked that it opens to 0 at x in the multi-open argument):
///
///  S_0 * id_0(x) + y * S_1 * id_1(x) + ... + y^m * S_m * id_m(x)
///        - (h_0 + x^{n-1} * h_1 + ... + x^{l*(n-1)} * h_l) * (x^n-1),
///
/// where:
/// * y is the batching challenge,
/// * x is the evaluation challenge,
/// * id_j(x) is a (partially or fully) evaluated identity at x,
/// * S_j is, either,
///      - (i)  the commitment to a fixed column corresponding to a simple,
///        multiplicative selector, or,
///      - (ii) the commitment to the constant polynomial `P(X) = 1` (in case
///        the corresponding identity id_j has been fully evaluated and, thus,
///        the resulting scalar is part of the constant term of the
///        linearization polynomial)
/// * h_k are commitments to the limbs of the quotient polynomial.
///
/// # Returns
///
/// A [VerifierQuery], that checks if the commitment to the linearization
/// polynomial opens to 0 at the evaluation challenge x. The commitment itself
/// is represented as an MSM in form of a vector of points and a vector of
/// scalars.
#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_linearization_commitment<
    'com,
    F: PrimeField + ff::WithSmallOrderMulGroup<3> + ff::FromUniformBytes<64> + std::cmp::Ord,
    CS: PolynomialCommitmentScheme<F>,
>(
    expressions: Vec<(Option<usize>, F)>,
    vk: &'com VerifyingKey<F, CS>,
    x: F,
    y: &F,
    xn: &F,
    splitting_factor: &F,
    quotient_limb_commitments: &'com [CS::Commitment],
    const_1_com: &'com CS::Commitment,
) -> VerifierQuery<'com, F, CS> {
    let lin_com_len = vk.cs.selector_flags().len() + quotient_limb_commitments.len() + 1;
    let mut identities_points = Vec::with_capacity(lin_com_len);
    let mut identities_scalars = Vec::with_capacity(lin_com_len);
    let mut identities_labels = Vec::with_capacity(lin_com_len);

    identities_points.extend(quotient_limb_commitments);

    let mut splitting_pow = F::ONE - *xn;
    for _ in 0..quotient_limb_commitments.len() {
        identities_scalars.push(splitting_pow);
        identities_labels.push(CommitmentLabel::NoLabel);
        splitting_pow *= splitting_factor;
    }

    // Group multiples of the same point in the MSM
    let mut grouped_points: BTreeMap<Option<usize>, F> = BTreeMap::new();
    let mut y_pow = F::ONE;
    expressions.iter().rev().for_each(|(col_idx, eval)| {
        *grouped_points.entry(*col_idx).or_insert(F::ZERO) += y_pow * eval;
        y_pow *= y;
    });

    grouped_points.into_iter().for_each(|(col_idx, eval)| {
        match col_idx {
            Some(col_idx) => {
                identities_points.push(&vk.fixed_commitments[col_idx]);
                identities_labels.push(CommitmentLabel::Fixed(col_idx));
            }
            // Fully evaluated identities go to the constant term
            None => {
                identities_points.push(const_1_com);
                identities_labels.push(CommitmentLabel::NoLabel);
            }
        }
        identities_scalars.push(eval);
    });

    VerifierQuery::new_linear(
        x,
        CommitmentLabel::Custom("linearization_poly".into()),
        identities_points,
        identities_scalars,
        identities_labels,
        F::ZERO,
    )
}
