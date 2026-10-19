//! Folding prover: commits a fresh instance (the commit phases of a plonk
//! proof, no quotient, no opening) and holds the running accumulator.

use std::{hash::Hash, iter::once};

use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};

use super::{
    degree::folding_degree,
    instance::{Accumulator, Challenges, FoldingInstance},
    poly::{
        inner_product, interpolate, lagrange_basis, perturbator, pow_vector, squares, vanishing,
    },
    trace::{evaluate_rows, linear_combination},
    verifier::next_accumulator,
};
use crate::{
    plonk::{Circuit, Error, ProvingKey, prover::commit_phases, traces::ProverTrace},
    poly::{LagrangeCoeff, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// A fresh instance, prover side: the Lagrange-form trace after the commit
/// phases and its public data.
#[derive(Debug)]
pub struct ProverInstance<'a, F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) trace: ProverTrace<'a, F, LagrangeCoeff>,
    pub(crate) public: FoldingInstance<F, CS>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProverInstance<'_, F, CS> {
    /// What the folding verifier reads for this instance.
    pub fn public(&self) -> &FoldingInstance<F, CS> {
        &self.public
    }
}

/// Synthesises `circuit` and runs the commit phases (phase-1 and phase-2
/// commitments and their challenges) into `transcript`, which then holds
/// the partial proof of this instance. No quotient, no opening.
///
/// Committed instance columns are not supported: with the
/// `committed-instances` feature, none is committed (all of `instances` are
/// public inputs).
pub fn commit_instance<'a, F, CS, T, C>(
    params: &CS::Parameters,
    pk: &'a ProvingKey<F, CS>,
    circuit: &C,
    instances: &[&[F]],
    transcript: &mut T,
    rng: impl RngCore + CryptoRng,
) -> Result<ProverInstance<'a, F, CS>, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
    C: Circuit<F>,
{
    let (trace, [phase1_commitment, phase2_commitment]) = commit_phases(
        params,
        pk,
        circuit,
        #[cfg(feature = "committed-instances")]
        0,
        instances,
        transcript,
        rng,
    )?;
    let public = FoldingInstance {
        phase1_commitment,
        phase2_commitment,
        instances: instances.iter().map(|i| i.to_vec()).collect(),
        challenges: Challenges {
            theta: trace.theta.clone(),
            beta: trace.beta,
            gamma: trace.gamma,
            trash: trace.trash_challenges.clone(),
            y: trace.y.clone(),
        },
    };
    Ok(ProverInstance { trace, public })
}

/// The running accumulator, prover side: the folded trace (Lagrange form)
/// and the public accumulator. The trace's challenges and public inputs are
/// those of `public` (both are folded with the same weights).
#[derive(Debug)]
pub struct ProverAccumulator<'a, F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) public: Accumulator<F, CS>,
    pub(crate) trace: ProverTrace<'a, F, LagrangeCoeff>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProverAccumulator<'_, F, CS> {
    /// The public accumulator (what the folding verifier computes).
    pub fn accumulator(&self) -> &Accumulator<F, CS> {
        &self.public
    }
}

impl<'a, F, CS> ProverAccumulator<'a, F, CS>
where
    F: WithSmallOrderMulGroup<3> + Hash + Ord + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
{
    /// Prover side of [`Accumulator::init`]: the first accumulator is `fresh`.
    pub fn init<T>(
        pk: &ProvingKey<F, CS>,
        fresh: ProverInstance<'a, F, CS>,
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        T: Transcript,
        F: Hashable<T::Hash> + Sampleable<T::Hash>,
        CS::Commitment: Hashable<T::Hash>,
    {
        Ok(ProverAccumulator {
            public: Accumulator::init(&pk.vk, fresh.public, transcript)?,
            trace: fresh.trace,
        })
    }

    /// Prover side of [`Accumulator::fold`]: folds the `k = fresh.len() ≥ 1`
    /// fresh instances into `self`, writing the proof to a fresh `transcript`
    /// (steps 1-7 of "Folding" in the module documentation).
    pub fn fold<T>(
        self,
        pk: &ProvingKey<F, CS>,
        fresh: Vec<ProverInstance<'a, F, CS>>,
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
        let t = pk.vk.domain.k() as usize;
        let k = fresh.len();
        let d = folding_degree(&pk.vk.cs);
        let (fresh_traces, fresh_public): (Vec<_>, Vec<_>) =
            fresh.into_iter().map(|i| (i.trace, i.public)).unzip();
        let traces: Vec<_> = once(&self.trace).chain(&fresh_traces).collect();

        // 1. Absorb the accumulator, then the fresh instances.
        self.public.absorb(transcript)?;
        for instance in &fresh_public {
            instance.absorb_commitments_and_instances(transcript)?;
        }

        // 2. Squeeze δ.
        let deltas = squares(transcript.squeeze_challenge(), t);

        // 3. Write F₁, …, F_t (F₀ = e is known to the verifier).
        let f = evaluate_rows(pk, &self.trace);
        let f_coeffs = perturbator(&f, &self.public.betas, &deltas);
        for coeff in &f_coeffs[1..] {
            transcript.write(coeff)?;
        }

        // 4. Squeeze α; the rows are weighted by pow(β⃗ + α·δ⃗).
        let alpha: F = transcript.squeeze_challenge();
        let betas = self.public.betas.iter().zip(&deltas).map(|(b, delta)| *b + alpha * delta);
        let pows = pow_vector(&betas.collect::<Vec<_>>());

        // 5. Write K, interpolated from (G − F(α)·L₀)/Z on k+1, …, d·k.
        let g = |x: F| {
            let folded = linear_combination(&traces, &lagrange_basis(k, x));
            inner_product(&pows, &evaluate_rows(pk, &folded))
        };
        let f_alpha = eval_polynomial(&f_coeffs, alpha);
        let points: Vec<F> = (k + 1..=d * k).map(|x| F::from(x as u64)).collect();
        let k_evals: Vec<F> = (points.iter())
            .map(|x| {
                let z_inv = vanishing(k, *x).invert().expect("x is outside the domain");
                (g(*x) - f_alpha * lagrange_basis(k, *x)[0]) * z_inv
            })
            .collect();
        let k_coeffs = interpolate(&points, &k_evals);
        for coeff in &k_coeffs {
            transcript.write(coeff)?;
        }

        // 6. Squeeze γ.
        let gamma = transcript.squeeze_challenge();

        // 7. The new accumulator and its folded trace.
        let public = next_accumulator(
            &self.public,
            &fresh_public,
            &deltas,
            &f_coeffs,
            alpha,
            &k_coeffs,
            gamma,
        )?;
        let trace = linear_combination(&traces, &lagrange_basis(k, gamma));
        Ok(ProverAccumulator { public, trace })
    }
}
