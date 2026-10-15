//! Folding verifier: reads a fresh instance and folds it into the running
//! accumulator. Also hosts the transcript steps and the folding of the
//! public data shared with the prover, so both sides compute the same
//! accumulator by construction.

use std::hash::Hash;

use ff::{FromUniformBytes, WithSmallOrderMulGroup};

use super::{
    degree::folding_degree,
    instance::{Accumulator, Challenges, FoldingInstance},
    poly::{next_error, squares},
};
use crate::{
    plonk::{Error, VerifyingKey, parse_trace},
    poly::commitment::PolynomialCommitmentScheme,
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// `δ⃗ = (δ, δ², δ⁴, …)` for a fresh `δ` squeezed from the transcript.
pub(crate) fn squeeze_deltas<F, T>(transcript: &mut T, log_n: usize) -> Vec<F>
where
    F: ff::Field + Sampleable<T::Hash>,
    T: Transcript,
{
    squares(transcript.squeeze_challenge(), log_n)
}

/// The folding challenge `γ` (truncated under `truncated-challenges`: it
/// scales the commitments, one in-circuit scalar multiplication each).
pub(crate) fn squeeze_fold_challenge<F, T>(transcript: &mut T) -> F
where
    F: ff::PrimeField + Sampleable<T::Hash>,
    T: Transcript,
{
    let gamma: F = transcript.squeeze_challenge();
    #[cfg(feature = "truncated-challenges")]
    let gamma = crate::utils::arithmetic::truncate(gamma);
    gamma
}

/// The products `γ·(fresh − acc)` of the phase-1 and phase-2 commitments,
/// which the prover writes after `γ` and the in-circuit verifier checks with
/// one MSM instead of computing `[γ](fresh − acc)` per point (folded
/// commitment: `acc + product`). The in-circuit check then squeezes its
/// batching challenges `ρ`, which have no native counterpart: they come last
/// in the folding transcript.
pub(crate) fn fold_products<F, CS>(
    acc: &Accumulator<F, CS>,
    fresh: &FoldingInstance<F, CS>,
    gamma: F,
) -> [CS::Commitment; 2]
where
    F: ff::PrimeField,
    CS: PolynomialCommitmentScheme<F>,
{
    let (a, f) = (&acc.instance, fresh);
    [
        CS::fold_products(&a.phase1_commitment, &f.phase1_commitment, gamma),
        CS::fold_products(&a.phase2_commitment, &f.phase2_commitment, gamma),
    ]
}

/// `β⃗ + α·δ⃗`.
pub(crate) fn shift_betas<F: ff::Field>(betas: &[F], alpha: F, deltas: &[F]) -> Vec<F> {
    betas.iter().zip(deltas).map(|(b, d)| *b + alpha * d).collect()
}

/// The accumulator after one folding round: `β⃗* = β⃗ + α·δ⃗`,
/// `e' = F(α)·L₀(γ) + Z(γ)·K(γ)` and the instance `acc + γ·(fresh − acc)`.
/// `f_coeffs` are the perturbator's coefficients with `f_coeffs[0] = e`.
pub(crate) fn fold_public<F, CS>(
    acc: &Accumulator<F, CS>,
    fresh: &FoldingInstance<F, CS>,
    deltas: &[F],
    f_coeffs: &[F],
    alpha: F,
    k_coeffs: &[F],
    gamma: F,
) -> Result<Accumulator<F, CS>, Error>
where
    F: ff::PrimeField,
    CS: PolynomialCommitmentScheme<F>,
{
    Ok(Accumulator {
        instance: acc.instance.fold(fresh, gamma)?,
        betas: shift_betas(&acc.betas, alpha, deltas),
        error: next_error(eval_polynomial(f_coeffs, alpha), k_coeffs, gamma),
    })
}

/// Reads the commit phases of a fresh instance (the partial proof of one
/// step) for the public inputs `instances`.
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
        phase1_commitment: trace.phase1_commitment().clone(),
        phase2_commitment: trace.phase2_commitment().clone(),
        instances: instances.iter().map(|i| i.to_vec()).collect(),
        challenges: Challenges {
            theta: trace.theta,
            beta: trace.beta,
            gamma: trace.gamma,
            trash_powers: trace.trash_powers,
            y: trace.y,
        },
    })
}

impl<F, CS> Accumulator<F, CS>
where
    F: WithSmallOrderMulGroup<3> + Hash + Ord + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
{
    /// The first accumulator: the first fresh instance itself, `e = 0`, and
    /// `β⃗ = (β, β², β⁴, …)` for a `β` squeezed after absorbing the instance
    /// (commitments, public inputs) into the fresh `transcript`. Sound because
    /// `Σᵢ βⁱ·fᵢ = 0` for a random `β` implies `fᵢ = 0` on every row except
    /// with probability `(n − 1)/|F|`.
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
        let betas = squeeze_deltas(transcript, vk.domain.k() as usize);
        Ok(Accumulator {
            instance: fresh,
            betas,
            error: F::ZERO,
        })
    }

    /// Folds `fresh` into the accumulator, reading the folding messages (the
    /// perturbator `F` without its constant term, then `K`) from a fresh
    /// folding `transcript`. See the module documentation for the order.
    /// `acc_hash` is the accumulator's hash if the caller binds it (the
    /// in-circuit verifier absorbs only that); `None` absorbs the whole
    /// accumulator.
    pub fn fold<T>(
        &self,
        vk: &VerifyingKey<F, CS>,
        fresh: &FoldingInstance<F, CS>,
        acc_hash: Option<F>,
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        T: Transcript,
        F: Hashable<T::Hash> + Sampleable<T::Hash>,
        CS::Commitment: Hashable<T::Hash>,
    {
        let log_n = vk.domain.k() as usize;
        let d = folding_degree(&vk.cs);

        self.absorb_bound(acc_hash, transcript)?;
        fresh.absorb_commitments_and_instances(transcript)?;

        let deltas = squeeze_deltas(transcript, log_n);
        let mut f_coeffs = vec![self.error];
        for _ in 0..log_n {
            f_coeffs.push(transcript.read()?);
        }

        let alpha: F = transcript.squeeze_challenge();
        let k_coeffs = (0..d - 1).map(|_| transcript.read()).collect::<Result<Vec<F>, _>>()?;

        let gamma = squeeze_fold_challenge(transcript);
        // The prover's products must be the exact ones (else the in-circuit
        // check fails).
        for expected in fold_products(self, fresh, gamma) {
            let labels = CS::commitment_labels(&expected);
            if CS::read_commitment(transcript, &labels)? != expected {
                return Err(Error::InvalidInstances);
            }
        }
        fold_public(self, fresh, &deltas, &f_coeffs, alpha, &k_coeffs, gamma)
    }
}
