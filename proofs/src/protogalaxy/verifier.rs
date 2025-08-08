//! TODO

use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    plonk::{
        parse_trace,
        traces::{FoldingProverTrace, VerifierFoldingTrace},
        Error, Evaluator, VerifyingKey,
    },
    poly::{commitment::PolynomialCommitmentScheme, EvaluationDomain, LagrangeCoeff, Polynomial},
    protogalaxy::utils::{linear_combination, pow_vec},
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// This verifier can perform a 2**K - 1 to one folding
#[derive(Debug)]
pub struct ProtogalaxyVerifier<
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    const K: usize,
> {
    verifier_folding_trace: VerifierFoldingTrace<F, CS>,
    error_term: F,
    beta_powers: [F; K],
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const K: usize>
    ProtogalaxyVerifier<F, CS, K>
{
    /// Initialise the Protogalaxy verifier given an initial instance
    // TODO: We can probably start with no instance at all.
    pub fn init<T>(
        vk: &VerifyingKey<F, CS>,
        // Unlike the prover, the verifier gets their instances in two arguments:
        // committed and normal (non-committed). Note that the total number of
        // instance columns is expected to be the sum of committed instances and
        // normal instances for every proof. (Committed instances go first, that is,
        // the first instance columns are devoted to committed instances.)
        #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
        instances: &[&[&[F]]],
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        T: Transcript,
        CS: PolynomialCommitmentScheme<F>,
        CS::Commitment: Hashable<T::Hash>,
        F: WithSmallOrderMulGroup<3>
            + Sampleable<T::Hash>
            + Hashable<T::Hash>
            + Ord
            + FromUniformBytes<64>,
    {
        let folded_trace = parse_trace(
            vk,
            #[cfg(feature = "committed-instances")]
            committed_instances,
            instances,
            transcript,
        )?
        .into_folding_trace(vk.fixed_commitments());

        Ok(Self {
            verifier_folding_trace: folded_trace,
            error_term: F::ZERO,
            beta_powers: [F::ONE; K],
        })
    }

    /// Fold the given traces. Concretely, the verifier receives [Transcript]s
    /// from [K] proofs, parses them to extract the [VerifierTrace], and
    /// folds them following the protogalaxy protocol.
    /// TODO: We assume that nr of proofs is a power of 2.
    /// TODO: PCS not verified
    pub fn fold<T>(
        mut self,
        vk: &VerifyingKey<F, CS>,
        #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
        instances: &[&[&[F]]],
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        T: Transcript,
        CS: PolynomialCommitmentScheme<F>,
        CS::Commitment: Hashable<T::Hash>,
        F: WithSmallOrderMulGroup<3>
            + Sampleable<T::Hash>
            + Hashable<T::Hash>
            + Ord
            + FromUniformBytes<64>,
    {
        // We must increase the degree, since we need to count y as a variable.
        // TODO: We'll use independent challenges, instead of powers of y.
        let dk_domain = EvaluationDomain::new(
            vk.cs().degree() as u32 + 3,
            (instances.len() + 1).trailing_zeros(),
        );

        // TODO: Is this sufficient to check H-consistency? I'm not 'checking' anything,
        // but I'm computing the challenges myself - I believe that is enough.
        let traces = instances
            .iter()
            .map(|instance| {
                let trace = parse_trace(
                    vk,
                    #[cfg(feature = "committed-instances")]
                    committed_instances,
                    &[instance],
                    transcript,
                )?;

                Ok(trace.into_folding_trace(vk.fixed_commitments()))
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let mut delta = transcript.squeeze_challenge();
        let delta_powers: [F; K] = std::array::from_fn(|_| {
            let res = delta;
            delta = delta * delta;
            res
        });

        // let _committed_f: CS::Commitment = transcript.read()?;
        let alpha: F = transcript.squeeze_challenge();
        let eval_commited_f: F = transcript.read()?;

        let f_at_alpha = self.error_term + eval_commited_f;

        self.beta_powers = self
            .beta_powers
            .iter()
            .zip(delta_powers.iter())
            .map(|(beta, delta)| *beta + alpha * delta)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let _poly_k: CS::Commitment = transcript.read()?;
        let gamma: F = transcript.squeeze_challenge();
        let k_at_gamma: F = transcript.read()?;
        let z_in_gamma = gamma.pow_vartime([dk_domain.n]) - F::ONE;

        let mut l0 = dk_domain.empty_lagrange();
        l0[0] = F::ONE;
        let l0_coeff = dk_domain.lagrange_to_coeff(l0);
        let l0_at_gamma = eval_polynomial(&l0_coeff, gamma);

        self.error_term = f_at_alpha * l0_at_gamma + z_in_gamma * k_at_gamma;
        let traces = std::iter::once(&self.verifier_folding_trace)
            .chain(traces.iter())
            .collect::<Vec<_>>();

        assert!(traces.len().is_power_of_two());
        self.verifier_folding_trace = fold_traces(&dk_domain, &traces, &gamma);

        // TODO: need to verify the polynomial commitment openings
        Ok(self)
    }

    /// This function verifies that a folde trace satisfies the relaxed
    /// relation.
    // TODO: need to verify that the commitment is correct as well.
    #[allow(clippy::too_many_arguments)]
    pub fn is_sat(
        &self,
        params: &CS::Parameters,
        vk: &VerifyingKey<F, CS>,
        evaluator: &Evaluator<F>,
        folded_witness: FoldingProverTrace<F>,
        l0: &Polynomial<F, LagrangeCoeff>,
        l_last: &Polynomial<F, LagrangeCoeff>,
        l_active_row: &Polynomial<F, LagrangeCoeff>,
        permutation_pk_cosets: &[Polynomial<F, LagrangeCoeff>],
    ) -> Result<(), Error> {
        // First we check that the committed folded witness corresponds to the folded
        // instance
        let committed_folded_witness = folded_witness.commit(params);

        assert_eq!(committed_folded_witness, self.verifier_folding_trace);

        // Next, we evaluate the f_i function over the folded trace, to see it
        // corresponds with the computed error.
        let FoldingProverTrace {
            fixed_polys,
            advice_polys,
            instance_values,
            lookups,
            permutations: permutation,
            trashcans,
            challenges,
            beta,
            gamma,
            theta,
            y,
            trash_challenge,
            ..
        } = folded_witness;

        let witness_poly = evaluator.evaluate_h::<LagrangeCoeff>(
            vk.get_domain(),
            vk.cs(),
            &advice_polys.iter().map(Vec::as_slice).collect::<Vec<_>>(),
            &instance_values
                .iter()
                .map(|i| i.as_slice())
                .collect::<Vec<_>>(),
            &fixed_polys,
            &challenges,
            y,
            beta,
            gamma,
            theta,
            trash_challenge,
            &lookups,
            &trashcans,
            &permutation,
            l0,
            l_last,
            l_active_row,
            permutation_pk_cosets,
        );

        let beta_powers = pow_vec(&self.beta_powers);
        let expected_result = witness_poly
            .values
            .into_par_iter()
            .zip(beta_powers.par_iter())
            .map(|(witness, beta_pow)| witness * beta_pow)
            .reduce(|| F::ZERO, |a, b| a + b);

        if expected_result == self.error_term {
            Ok(())
        } else {
            Err(Error::Opening)
        }
    }
}

/// Function to fold traces over an evaluation `\gamma`
fn fold_traces<F: WithSmallOrderMulGroup<3>, PCS: PolynomialCommitmentScheme<F>>(
    dk_domain: &EvaluationDomain<F>,
    traces: &[&VerifierFoldingTrace<F, PCS>],
    gamma: &F,
) -> VerifierFoldingTrace<F, PCS> {
    let lagrange_polys = (0..traces.len())
        .map(|i| {
            // For the moment we only support batching of traces of dimension one.
            assert_eq!(traces[i].advice_commitments.len(), 1);
            let mut l = dk_domain.empty_lagrange();
            l[i] = F::ONE;
            l
        })
        .map(|p| dk_domain.lagrange_to_coeff(p))
        .collect::<Vec<_>>();

    let buffer = VerifierFoldingTrace::init(
        traces[0].fixed_commitments.len(),
        traces[0].advice_commitments[0].len(),
        traces[0].lookups[0].len(),
        traces[0].trashcans[0].len(),
        traces[0].permutations[0].permutation_product_commitments.len(),
        traces[0].challenges.len(),
    );
    let lagranges_in_gamma = lagrange_polys
        .iter()
        .map(|poly| eval_polynomial(poly, *gamma))
        .collect::<Vec<_>>();

    linear_combination(buffer, traces, &lagranges_in_gamma)
}
