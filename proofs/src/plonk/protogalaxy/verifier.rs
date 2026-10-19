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
    utils::arithmetic::{eval_polynomial, truncate},
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
    /// the proof from a fresh `transcript` (steps 1-8 of "Folding" in the
    /// module documentation). Step 1 absorbs `acc_hash` instead of the
    /// accumulator if it is `Some`.
    ///
    /// # Warning
    ///
    /// With `acc_hash = Some(h)` the round binds only `h`, not the
    /// accumulator: `h` must be a collision-resistant hash of the ENTIRE
    /// accumulator, computed and bound by the caller (e.g. an IVC that also
    /// exposes it as a public input). Anything else lets a prover choose the
    /// accumulator after seeing `γ`.
    pub fn fold<T>(
        &self,
        vk: &VerifyingKey<F, CS>,
        fresh: &[FoldingInstance<F, CS>],
        acc_hash: Option<F>,
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

        self.absorb_or_hash(acc_hash, transcript)?;
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
        let gamma = truncate(transcript.squeeze_challenge());

        let next = next_accumulator(self, fresh, &deltas, &f_coeffs, alpha, &k_coeffs, gamma)?;
        for expected in fold_products(self, fresh, gamma) {
            let labels = CS::commitment_labels(&expected);
            if CS::read_commitment(transcript, &labels)? != expected {
                return Err(Error::InvalidInstances);
            }
        }
        Ok(next)
    }
}

/// Step 8 of the fold, shared by prover and verifier: the products
/// `Pⱼ = Lⱼ(γ)·(Cⱼ − C₀)` for `j = 1, …, k`, `P₁` of phase 1, `P₁` of phase 2,
/// `P₂` of phase 1, …, with `C₀` the commitment of `acc` and `Cⱼ` that of
/// `fresh[j - 1]`.
pub(crate) fn fold_products<F, CS>(
    acc: &Accumulator<F, CS>,
    fresh: &[FoldingInstance<F, CS>],
    gamma: F,
) -> Vec<CS::Commitment>
where
    F: PrimeField,
    CS: PolynomialCommitmentScheme<F>,
{
    let weights = lagrange_basis(fresh.len(), gamma);
    fresh
        .iter()
        .zip(&weights[1..])
        .flat_map(|(instance, w)| {
            let phase1 = (&instance.phase1_commitment, &acc.instance.phase1_commitment);
            let phase2 = (&instance.phase2_commitment, &acc.instance.phase2_commitment);
            [phase1, phase2].map(|(c, c0)| CS::combine_commitments(&[(*w, c), (-*w, c0)]))
        })
        .collect()
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
