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
    verifier::{fold_products, next_accumulator},
};
use crate::{
    plonk::{Circuit, Error, ProvingKey, prover::commit_phases, traces::ProverTrace},
    poly::{LagrangeCoeff, Polynomial, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::{eval_polynomial, parallelize, truncate},
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

/// The running accumulator, prover side: the folded trace (Lagrange form),
/// the public accumulator and the value of the identity on every row of the
/// trace. The trace's challenges and public inputs are those of `public` (both
/// are folded with the same weights). Memory: the trace plus one field element
/// per row (`rows`), which saves evaluating the identity on the accumulator at
/// each fold.
#[derive(Debug)]
pub struct ProverAccumulator<'a, F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) public: Accumulator<F, CS>,
    pub(crate) trace: ProverTrace<'a, F, LagrangeCoeff>,
    /// `fᵢ` of every row of `trace`, as [`evaluate_rows`] computes them;
    /// carried across folds so that the next one does not evaluate them
    /// again.
    pub(crate) rows: Polynomial<F, LagrangeCoeff>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProverAccumulator<'_, F, CS> {
    /// The public accumulator (what the folding verifier computes).
    pub fn accumulator(&self) -> &Accumulator<F, CS> {
        &self.public
    }

    /// Whether the relaxed relation `Σᵢ powᵢ(β⃗)·fᵢ(ω) = e` holds for the
    /// prover's folded trace. A check in the clear, for tests and examples; a
    /// verifier needs the decider proof instead.
    pub fn is_satisfied(&self, pk: &ProvingKey<F, CS>) -> bool {
        let rows = evaluate_rows(pk, &self.trace);
        inner_product(&pow_vector(&self.public.betas), &rows) == self.public.error()
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
            rows: evaluate_rows(pk, &fresh.trace),
            trace: fresh.trace,
        })
    }

    /// Prover side of [`Accumulator::fold`]: folds the `k = fresh.len() ≥ 1`
    /// fresh instances into `self`, writing the proof to a fresh `transcript`
    /// (steps 1-8 of "Folding" in the module documentation).
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
        let f = &self.rows;
        let f_coeffs = perturbator(f, &self.public.betas, &deltas);
        for coeff in &f_coeffs[1..] {
            transcript.write(coeff)?;
        }

        // 4. Squeeze α; the rows are weighted by pow(β⃗ + α·δ⃗).
        let alpha: F = transcript.squeeze_challenge();
        let betas = self.public.betas.iter().zip(&deltas).map(|(b, delta)| *b + alpha * delta);
        let pows = pow_vector(&betas.collect::<Vec<_>>());

        // 5. Write K, interpolated from (G − F(α)·L₀)/Z on k+1, …, d·k. The rows
        // at these points are kept to interpolate the new accumulator's rows.
        let f_alpha = eval_polynomial(&f_coeffs, alpha);
        let points: Vec<F> = (k + 1..=d * k).map(|x| F::from(x as u64)).collect();
        let point_rows: Vec<Polynomial<F, LagrangeCoeff>> = (points.iter())
            .map(|x| evaluate_rows(pk, &linear_combination(&traces, &lagrange_basis(k, *x))))
            .collect();
        let k_evals: Vec<F> = (points.iter().zip(&point_rows))
            .map(|(x, rows)| {
                let z_inv = vanishing(k, *x).invert().expect("x is outside the domain");
                (inner_product(&pows, rows) - f_alpha * lagrange_basis(k, *x)[0]) * z_inv
            })
            .collect();
        let k_coeffs = interpolate(&points, &k_evals);
        for coeff in &k_coeffs {
            transcript.write(coeff)?;
        }

        // 6. Squeeze γ.
        let gamma = truncate(transcript.squeeze_challenge());

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
        let rows = interpolate_rows(f, k, &point_rows, gamma);
        if cfg!(debug_assertions)
            && fresh_traces
                .iter()
                .all(|t| evaluate_rows(pk, t).iter().all(|f| bool::from(f.is_zero())))
        {
            assert_eq!(
                rows.values,
                evaluate_rows(pk, &trace).values,
                "interpolated rows"
            );
        }

        // 8. Write the products of the commitment fold.
        for product in fold_products(&self.public, &fresh_public, gamma) {
            CS::write_commitment(transcript, &product)?;
        }
        Ok(ProverAccumulator {
            public,
            trace,
            rows,
        })
    }
}

/// `pᵢ(γ)` for every row `i`, where `pᵢ(x)` is the identity on the row `i` of
/// `linear_combination(traces, lagrange_basis(k, x))`, a polynomial of degree
/// at most `d·k` in `x`. It is determined by its values on the nodes
/// `0..=d·k`: `acc_rows[i]` at node 0, `0` at nodes `1..=k` and
/// `rows_from_k_plus_1[x − k − 1][i]` at nodes `x = k+1..=d·k`. The Lagrange
/// basis on the nodes at γ is computed once and shared by all rows.
///
/// Nodes `1..=k` are the fresh traces, which satisfy the identity if honest,
/// and then contribute nothing. A dishonest fresh instance makes the returned
/// rows wrong; the decider, which re-evaluates the trace, catches it.
fn interpolate_rows<F: WithSmallOrderMulGroup<3>>(
    acc_rows: &Polynomial<F, LagrangeCoeff>,
    k: usize,
    rows_from_k_plus_1: &[Polynomial<F, LagrangeCoeff>],
    gamma: F,
) -> Polynomial<F, LagrangeCoeff> {
    let nodes: Vec<F> = (0..(k + rows_from_k_plus_1.len() + 1) as u64).map(F::from).collect();
    let basis: Vec<F> = (0..nodes.len())
        .map(|j| {
            let (num, den) = (nodes.iter().enumerate())
                .filter(|(m, _)| *m != j)
                .fold((F::ONE, F::ONE), |(num, den), (_, xm)| {
                    (num * (gamma - xm), den * (nodes[j] - xm))
                });
            num * den.invert().expect("nodes are distinct")
        })
        .collect();

    let mut values = acc_rows.clone();
    parallelize(&mut values.values, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            *value = *value * basis[0]
                + (rows_from_k_plus_1.iter().zip(&basis[k + 1..]))
                    .map(|(r, l)| r[start + i] * l)
                    .sum::<F>();
        }
    });
    values
}
