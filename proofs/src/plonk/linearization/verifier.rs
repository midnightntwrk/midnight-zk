use std::collections::BTreeMap;

use ff::PrimeField;

use crate::{plonk::VerifyingKey, poly::commitment::PolynomialCommitmentScheme};

/// Construct the commitment to the linearization polynomial
/// (which will be checked that it opens to 0 at x in the multi-open argument):
///
///  S_0*id_0(x) + y*S_1*id_1(x) + y^2*S_2*id_2(x) + ... + y^m*S_m*id_m(x)
///        - (h_0 + x^n*h_1 + x^{2n}*h_2 + ... + x^{l*n}*h_l) * (x^n-1),
///
/// where:
/// * y is the batching challenge, for batching independent identities,
/// * x is the evaluation challenge,
/// * id_j(x) is the result of (partially or fully) evaluating the identity id_j
///   at x (i.e., a scalar),
/// * S_j is, either,
///      - (i)  the commitment to a fixed column corresponding to a simple
///        selector, or,
///      - (ii) the zero commitment (because the corresponding identity id_i has
///        been fully evaluated and thus the resulting scalar is part of the
///        constant term of the linearization poly)
/// * h_k are commitments to the limbs of the quotient polynomial.
#[allow(clippy::type_complexity)]
pub(crate) fn compute_linearization_commitment<
    'com,
    F: PrimeField + ff::WithSmallOrderMulGroup<3> + ff::FromUniformBytes<64> + std::cmp::Ord,
    CS: PolynomialCommitmentScheme<F>,
>(
    expressions: impl Iterator<Item = (Option<usize>, F)> + 'com,
    vk: &'com VerifyingKey<F, CS>,
    y: &F,
    xn: &F,
    quotient_limb_commitments: &'com [CS::Commitment],
    g1: &'com CS::Commitment,
) -> ((Vec<&'com CS::Commitment>, Vec<F>), Vec<Option<usize>>) {
    let mut indices = vec![];

    let mut identities_points = Vec::new();
    let mut identities_scalars = Vec::new();

    identities_points.extend(quotient_limb_commitments);

    let mut xn_pow = F::ONE - *xn;
    for _ in 0..quotient_limb_commitments.len() {
        indices.push(None);
        identities_scalars.push(xn_pow);
        xn_pow *= xn;
    }

    let mut grouped_points: BTreeMap<Option<usize>, F> = BTreeMap::new();
    let mut y_pow = F::ONE;
    expressions
        .collect::<Vec<(Option<usize>, F)>>()
        .iter()
        .rev()
        .for_each(|(col_idx, eval)| {
            *grouped_points.entry(*col_idx).or_insert(F::ZERO) += y_pow * eval;
            y_pow *= y;
        });

    grouped_points.into_iter().for_each(|(col_idx, eval)| {
        match col_idx {
            Some(col_idx) => {
                indices.push(Some(col_idx));
                identities_points.push(&vk.fixed_commitments[col_idx])
            }
            // Fully evaluated identities go to the constant term
            None => {
                indices.push(None);
                identities_points.push(g1)
            }
        }
        identities_scalars.push(eval);
    });
    ((identities_points, identities_scalars), indices)
}
