//! Decider verifier (see `decider_prover.rs` for the statement and the
//! transcript). Beyond a plonk verifier it computes `W(x) = Σᵢ powᵢ(β⃗)·Lᵢ(x)`
//! natively in `O(n)` field operations (barycentric form, one batch
//! inversion) and opens `S` at `x` and `ωx`; no extra MSM beyond the PCS.

use std::{collections::BTreeMap, hash::Hash, iter};

use ff::{BatchInvert, FromUniformBytes, WithSmallOrderMulGroup};

use super::{decider_prover::grand_sum_label, instance::Accumulator, poly::pow_vector};
use crate::{
    plonk::{
        Error, VerifyingKey, argument, evaluate_identities,
        verifier::{instance_evals, scaled_quotient_commitment},
    },
    poly::{
        EvaluationDomain, PolynomialLabel, Rotation, VerifierQuery,
        commitment::PolynomialCommitmentScheme,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::compute_inner_product,
};

/// `Lᵢ(x) = ωⁱ·(xⁿ − 1)/(n·(x − ωⁱ))` for every `i ∈ [0, n)`, `x ∉ H`.
fn lagrange_evals<F: WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    x: F,
    xn: F,
) -> Vec<F> {
    let n = domain.n as usize;
    let omegas: Vec<F> = iter::successors(Some(F::ONE), |w| Some(*w * domain.get_omega()))
        .take(n)
        .collect();
    let mut denominators: Vec<F> = omegas.iter().map(|w| x - w).collect();
    denominators.batch_invert();
    let common = (xn - F::ONE) * F::from(n as u64).invert().unwrap();
    omegas.iter().zip(denominators).map(|(w, d)| *w * d * common).collect()
}

/// Verifies a decider proof for the accumulator `acc` (as computed by the
/// folding verifier) up to the PCS check: finalise the returned guard.
pub fn verify_relaxed_trace<F, CS, T>(
    vk: &VerifyingKey<F, CS>,
    acc: &Accumulator<F, CS>,
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Hash
        + Ord,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    let cs = vk.cs();
    let domain = vk.get_domain();
    let n = domain.n as usize;

    let vk_absorbed = vk.absorb_into(transcript)?;
    let phase0_committed = argument::verifier::Committed::from_key(&vk_absorbed);
    acc.absorb(transcript)?;

    let s_commitment = CS::read_commitment(transcript, &[grand_sum_label()])?;
    let zeta: F = transcript.squeeze_challenge();

    // `cs.degree()` limbs: one more than a plonk proof (the vk's domain was
    // built for `cs.degree()`, the decider's for `cs.degree() + 1`).
    let quotient_limb_coms = (0..cs.degree())
        .map(|i| CS::read_commitment(transcript, &[PolynomialLabel::QuotientPiece(i)]))
        .collect::<Result<Vec<_>, _>>()?;

    let x: F = CS::squeeze_evaluation_point(transcript);
    let splitting_factor = x.pow_vartime([vk.n() - 1]);
    let xn = splitting_factor * x;

    let instances: Vec<&[F]> = acc.instance.instances.iter().map(Vec::as_slice).collect();
    let instance_evals = instance_evals(vk, 0, &instances, x, xn, transcript)?;

    let x_rotations: BTreeMap<Rotation, F> = argument::rotations(cs)
        .into_iter()
        .map(|rotation| (rotation, domain.rotate_omega(x, rotation)))
        .collect();
    let phase1_committed = argument::verifier::Committed::new(
        vk.phase1_labels(),
        acc.instance.phase1_commitment.clone(),
    );
    let phase2_committed = argument::verifier::Committed::new(
        vk.phase2_labels(),
        acc.instance.phase2_commitment.clone(),
    );
    let phase0_evaluated = phase0_committed.evaluate(cs, &x_rotations, transcript)?;
    let phase1_evaluated = phase1_committed.evaluate(cs, &x_rotations, transcript)?;
    let phase2_evaluated = phase2_committed.evaluate(cs, &x_rotations, transcript)?;
    let x_next = domain.rotate_omega(x, Rotation::next());
    let s_eval: F = transcript.read()?;
    let s_next_eval: F = transcript.read()?;

    // f(x) with the folded challenges.
    let challenges = &acc.instance.challenges;
    let f_eval = evaluate_identities(
        vk,
        &instance_evals,
        &phase0_evaluated.evals_map,
        &phase1_evaluated.evals_map,
        &phase2_evaluated.evals_map,
        x,
        xn,
        challenges.beta,
        challenges.gamma,
        &challenges.theta,
        &challenges.trash_powers,
        &challenges.y,
    );

    let lagrange = lagrange_evals(domain, x, xn);
    let w_eval = compute_inner_product(&pow_vector(&acc.betas), &lagrange);
    let numerator = lagrange[0] * s_eval
        + zeta * (s_next_eval - s_eval - w_eval * f_eval + acc.error * lagrange[n - 1]);

    let quotient_commitment =
        scaled_quotient_commitment::<F, CS>(&quotient_limb_coms, splitting_factor, xn);

    let queries =
        iter::empty()
            .chain(phase1_evaluated.queries())
            .chain(phase2_evaluated.queries())
            .chain(phase0_evaluated.queries())
            .chain(iter::once(VerifierQuery::new(
                x,
                &quotient_commitment,
                PolynomialLabel::Quotient,
                -numerator,
            )))
            .chain([(x, s_eval), (x_next, s_next_eval)].map(|(point, eval)| {
                VerifierQuery::new(point, &s_commitment, grand_sum_label(), eval)
            }))
            .collect::<Vec<_>>();

    CS::multi_prepare(&queries, domain.k(), transcript).map_err(|_| Error::Opening)
}
