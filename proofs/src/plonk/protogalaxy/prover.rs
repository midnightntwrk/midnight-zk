//! Folding prover: commits a fresh instance (no proof) and folds it into the
//! running accumulator, writing the folding messages `F` and `K`.

use std::hash::Hash;

use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};

use super::{
    degree::folding_degree,
    instance::{Accumulator, Challenges, FoldingInstance},
    poly::{inner_product, interpolate, l0, perturbator, pow_vector, vanishing},
    sparse_gates::SparseGates,
    trace::{evaluate_rows, fold_trace},
    verifier::{fold_public, shift_betas, squeeze_deltas, squeeze_fold_challenge},
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
    let committed = commit_phases(
        params,
        pk,
        circuit,
        #[cfg(feature = "committed-instances")]
        0,
        instances,
        transcript,
        rng,
    )?;
    let trace = committed.trace;
    let public = FoldingInstance {
        phase1_commitment: committed.phase1_commitment,
        phase2_commitment: committed.phase2_commitment,
        instances: instances.iter().map(|i| i.to_vec()).collect(),
        challenges: Challenges {
            theta: trace.theta.clone(),
            beta: trace.beta,
            gamma: trace.gamma,
            trash_challenge: trace.trash_challenge,
            y: trace.y.clone(),
        },
    };
    Ok(ProverInstance { trace, public })
}

/// The running accumulator, prover side: the folded trace (Lagrange form)
/// and the public accumulator. The trace's challenges and public inputs are
/// those of `public` (both are folded with the same `γ`).
#[derive(Debug)]
pub struct ProverAccumulator<'a, F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) trace: ProverTrace<'a, F, LagrangeCoeff>,
    pub(crate) public: Accumulator<F, CS>,
    /// Row-sparse custom-gate evaluator of `pk`, built once.
    pub(crate) sparse: SparseGates<F>,
}

impl<'a, F, CS> ProverAccumulator<'a, F, CS>
where
    F: WithSmallOrderMulGroup<3> + Hash + Ord + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
{
    /// The public accumulator (what the folding verifier computes).
    pub fn accumulator(&self) -> &Accumulator<F, CS> {
        &self.public
    }

    /// Prover side of [`Accumulator::init`].
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
        let sparse = SparseGates::new(&pk.vk.cs, &pk.fixed_values);
        sparse.print_census(pk.vk.domain.n as usize);
        Ok(ProverAccumulator {
            public: Accumulator::init(&pk.vk, fresh.public, transcript)?,
            trace: fresh.trace,
            sparse,
        })
    }

    /// Prover side of [`Accumulator::fold`]: writes the perturbator `F(X)`
    /// (without its constant term `e`) and `K(X)`, then folds with `γ`.
    pub fn fold<T>(
        self,
        pk: &ProvingKey<F, CS>,
        fresh: ProverInstance<'a, F, CS>,
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        T: Transcript,
        F: Hashable<T::Hash> + Sampleable<T::Hash>,
        CS::Commitment: Hashable<T::Hash>,
    {
        let t_fold = std::time::Instant::now();
        let ms = |t: std::time::Instant| t.elapsed().as_secs_f64() * 1e3;
        let log_n = pk.vk.domain.k() as usize;
        let d = folding_degree(&pk.vk.cs);
        super::degree::debug_print_identity_degrees(&pk.vk.cs);

        self.public.absorb(transcript)?;
        fresh.public.absorb_commitments_and_instances(transcript)?;

        // F(X) = Σᵢ powᵢ(β⃗ + X·δ⃗)·fᵢ(acc), with F(0) = e.
        let t = std::time::Instant::now();
        let f_acc = evaluate_rows(pk, &self.trace, &self.sparse);
        let t_feval = ms(t);
        let deltas = squeeze_deltas(transcript, log_n);
        let t = std::time::Instant::now();
        let f_coeffs = perturbator(&f_acc, &self.public.betas, &deltas);
        let t_pert = ms(t);
        debug_assert_eq!(f_coeffs[0], self.public.error, "F(0) = e");
        for coeff in &f_coeffs[1..] {
            transcript.write(coeff)?;
        }

        let alpha: F = transcript.squeeze_challenge();
        let f_alpha = eval_polynomial(&f_coeffs, alpha);
        let t = std::time::Instant::now();
        let pows = pow_vector(&shift_betas(&self.public.betas, alpha, &deltas));
        let t_pow = ms(t);
        let pt_times = std::cell::RefCell::new(Vec::<(f64, f64)>::new());

        // G(x) = Σᵢ powᵢ(β⃗*)·fᵢ(acc + x·(fresh − acc)).
        let g = |x: F| {
            let t = std::time::Instant::now();
            let ft = fold_trace(&self.trace, &fresh.trace, x);
            let a = ms(t);
            let t = std::time::Instant::now();
            let rows = evaluate_rows(pk, &ft, &self.sparse);
            let b = ms(t);
            pt_times.borrow_mut().push((a, b));
            inner_product(&pows, &rows)
        };

        // K = (G − F(α)·L₀)/Z has degree d − 2: interpolate it on 2..=d. With
        // G(0) = F(α) and G(1) = 0 (honest fresh instance), these are the
        // d + 1 points that determine G.
        let points: Vec<F> = (2..=d as u64).map(F::from).collect();
        let k_evals: Vec<F> = (points.iter())
            .map(|x| (g(*x) - f_alpha * l0(*x)) * vanishing(*x).invert().unwrap())
            .collect();
        let t = std::time::Instant::now();
        let k_coeffs = interpolate(&points, &k_evals);
        let t_interp = ms(t);
        if cfg!(debug_assertions) {
            check_degree(d, &g, f_alpha, &f_acc, &pows);
        }
        for coeff in &k_coeffs {
            transcript.write(coeff)?;
        }

        let gamma = squeeze_fold_challenge(transcript);
        let t = std::time::Instant::now();
        let public = fold_public(
            &self.public,
            &fresh.public,
            &deltas,
            &f_coeffs,
            alpha,
            &k_coeffs,
            gamma,
        )?;
        let t_fpub = ms(t);
        let t = std::time::Instant::now();
        let trace = fold_trace(&self.trace, &fresh.trace, gamma);
        let t_final = ms(t);
        {
            let v = pt_times.borrow();
            let sf: f64 = v.iter().map(|p| p.0).sum();
            let se: f64 = v.iter().map(|p| p.1).sum();
            eprintln!("[fold] d={d} points={}", points.len());
            eprintln!("[fold] F_eval={t_feval:.2} perturbator={t_pert:.2} pow_vector={t_pow:.2}");
            for (x, (a, b)) in points.iter().zip(v.iter()) {
                eprintln!("[fold]   point {x:?}: fold_trace={a:.2} evaluate_rows={b:.2}");
            }
            eprintln!("[fold] sum_fold_trace={sf:.2} sum_evaluate_rows={se:.2}");
            eprintln!(
                "[fold] interpolate={t_interp:.2} fold_public={t_fpub:.2} final_fold_trace={t_final:.2} TOTAL={:.2}",
                ms(t_fold)
            );
        }
        Ok(ProverAccumulator {
            trace,
            public,
            sparse: self.sparse,
        })
    }
}

/// Checks that `d` bounds the degree of `G`: the interpolant of `G` on
/// `0..=d+1` has a zero coefficient of degree `d + 1`. Also checks
/// `G(0) = F(α)`. Costs `d + 1` extra evaluations; debug builds only.
fn check_degree<F: WithSmallOrderMulGroup<3>>(
    d: usize,
    g: impl Fn(F) -> F,
    f_alpha: F,
    f_acc: &[F],
    pows: &[F],
) {
    let g0 = inner_product(pows, f_acc);
    assert_eq!(g0, f_alpha, "G(0) = F(α)");
    let points: Vec<F> = (0..=d as u64 + 1).map(F::from).collect();
    let evals: Vec<F> = std::iter::once(g0).chain(points[1..].iter().map(|x| g(*x))).collect();
    let coeffs = interpolate(&points, &evals);
    assert_eq!(coeffs[d + 1], F::ZERO, "deg G > d_total = {d}");
}
