//! Folding verifier: reads a fresh instance, and folds `k` of them into the
//! running accumulator.

use std::{hash::Hash, iter::once};

use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};

use super::{
    degree::folding_degree,
    instance::{Accumulator, Challenges, FoldingInstance},
    poly::{lagrange_basis, squares, vanishing},
};
use crate::{
    plonk::{Error, VerifyingKey, parse_trace},
    poly::commitment::PolynomialCommitmentScheme,
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// Reads the commit phases of a fresh instance (the partial proof written by
/// [`commit_instance`](super::commit_instance)) for the public inputs
/// `instances`.
///
/// Committed instance columns are not supported: with the
/// `committed-instances` feature, none is committed (all of `instances` are
/// public inputs).
pub fn read_instance<F, CS, T>(
    vk: &VerifyingKey<F, CS>,
    instances: &[&[F]],
    transcript: &mut T,
) -> Result<FoldingInstance<F, CS>, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Ord,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    let trace = parse_trace(
        vk,
        #[cfg(feature = "committed-instances")]
        &[],
        instances,
        transcript,
    )?;
    Ok(FoldingInstance {
        phase1_commitment: trace.phase1_committed.commitment().clone(),
        phase2_commitment: trace.phase2_committed.commitment().clone(),
        instances: instances.iter().map(|i| i.to_vec()).collect(),
        challenges: Challenges {
            theta: trace.theta,
            beta: trace.beta,
            gamma: trace.gamma,
            trash: trace.trash_challenges,
            y: trace.y,
        },
    })
}

impl<F, CS> Accumulator<F, CS>
where
    F: WithSmallOrderMulGroup<3> + Hash + Ord + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
{
    /// The first accumulator: `fresh` itself, `e = 0` and `β⃗ = squares(β)`
    /// for a `β` squeezed after absorbing `fresh` (see "Folding" in the
    /// module documentation).
    pub fn init<T>(
        vk: &VerifyingKey<F, CS>,
        fresh: FoldingInstance<F, CS>,
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        T: Transcript,
        F: Hashable<T::Hash> + Sampleable<T::Hash>,
        CS::Commitment: Hashable<T::Hash>,
    {
        fresh.absorb_commitments_and_instances(transcript)?;
        let betas = squares(transcript.squeeze_challenge(), vk.domain.k() as usize);
        Ok(Accumulator {
            instance: fresh,
            betas,
            error: F::ZERO,
        })
    }

    /// Folds the `k = fresh.len() ≥ 1` fresh instances into `self`, reading
    /// the proof from a fresh `transcript` (steps 1-7 of "Folding" in the
    /// module documentation).
    pub fn fold<T>(
        &self,
        vk: &VerifyingKey<F, CS>,
        fresh: &[FoldingInstance<F, CS>],
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        T: Transcript,
        F: Hashable<T::Hash> + Sampleable<T::Hash>,
        CS::Commitment: Hashable<T::Hash>,
    {
        if fresh.is_empty() {
            return Err(Error::InvalidInstances);
        }
        let t = vk.domain.k() as usize;
        let k = fresh.len();
        let d = folding_degree(&vk.cs);

        self.absorb(transcript)?;
        for instance in fresh {
            instance.absorb_commitments_and_instances(transcript)?;
        }
        let deltas = squares(transcript.squeeze_challenge(), t);
        let mut f_coeffs = vec![self.error];
        for _ in 0..t {
            f_coeffs.push(transcript.read()?);
        }
        let alpha = transcript.squeeze_challenge();
        let k_coeffs = (0..d * k - k).map(|_| transcript.read()).collect::<Result<Vec<F>, _>>()?;
        let gamma = transcript.squeeze_challenge();

        next_accumulator(self, fresh, &deltas, &f_coeffs, alpha, &k_coeffs, gamma)
    }
}

/// Step 7 of the fold, shared by prover and verifier: the accumulator
/// `(Σⱼ Lⱼ(γ)·ωⱼ, β⃗ + α·δ⃗, F(α)·L₀(γ) + Z(γ)·K(γ))`, with `ω₀ = acc.instance`
/// and `ω₁, …, ω_k = fresh`. `f_coeffs` are the coefficients of `F` (constant
/// term `e` first) and `k_coeffs` those of `K`.
pub(crate) fn next_accumulator<F, CS>(
    acc: &Accumulator<F, CS>,
    fresh: &[FoldingInstance<F, CS>],
    deltas: &[F],
    f_coeffs: &[F],
    alpha: F,
    k_coeffs: &[F],
    gamma: F,
) -> Result<Accumulator<F, CS>, Error>
where
    F: PrimeField,
    CS: PolynomialCommitmentScheme<F>,
{
    let k = fresh.len();
    let weights = lagrange_basis(k, gamma);
    let instances: Vec<_> = once(&acc.instance).chain(fresh).collect();
    Ok(Accumulator {
        instance: FoldingInstance::linear_combination(&instances, &weights)?,
        betas: acc.betas.iter().zip(deltas).map(|(b, d)| *b + alpha * d).collect(),
        error: eval_polynomial(f_coeffs, alpha) * weights[0]
            + vanishing(k, gamma) * eval_polynomial(k_coeffs, gamma),
    })
}
