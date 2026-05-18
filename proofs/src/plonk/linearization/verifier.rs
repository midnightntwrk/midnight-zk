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
    let mut commitment = CS::Commitment::default();
    let mut expected_eval = F::ZERO;

    let mut splitting_pow = F::ONE - *xn;
    for com in quotient_limb_commitments {
        commitment = commitment + com.clone() * splitting_pow;
        splitting_pow *= splitting_factor;
    }

    // Group multiples of the same fixed column to reduce the number of scalar multiplications
    let mut grouped_points: BTreeMap<Option<usize>, F> = BTreeMap::new();
    let mut y_pow = F::ONE;
    for (col_idx, eval) in expressions.iter().rev() {
        *grouped_points.entry(*col_idx).or_insert(F::ZERO) += y_pow * eval;
        y_pow *= y;
    }

    for (col_idx, eval) in grouped_points {
        match col_idx {
            Some(idx) => commitment = commitment + vk.fixed_commitments[idx].clone() * eval,
            None => expected_eval -= eval,
        }
    }

    (commitment, expected_eval)
}
