//! TODO

use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, IndexedParallelIterator, ParallelIterator};
use crate::plonk::{Error, Evaluator, parse_trace, VerifyingKey};
use crate::plonk::traces::{FoldingProverTrace, VerifierFoldingTrace};
use crate::poly::commitment::PolynomialCommitmentScheme;
use crate::poly::{EvaluationDomain, LagrangeCoeff, Polynomial};
use crate::transcript::{Hashable, Sampleable, Transcript};
use crate::utils::arithmetic::eval_polynomial;

/// This verifier can perform a 2**K - 1 to one folding
#[derive(Debug)]
pub struct ProtogalaxyVerifier<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const K: usize> {
    // TODO Still need to verify this
    _verifier_folding_trace: VerifierFoldingTrace<F, CS>,
    error_term: F,
    beta_powers: [F; K],
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const K: usize> ProtogalaxyVerifier<F, CS, K> {
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
            #[cfg(feature = "committed-instances")] committed_instances,
            instances,
            transcript
        )?.into_folding_trace(vk.fixed_commitments());

        Ok(Self {
            _verifier_folding_trace: folded_trace,
            error_term: F::ZERO,
            beta_powers: [F::ONE; K],
        })
    }

    /// Fold the given traces. Concretely, the verifier receives [Transcript]s from [K] proofs,
    /// parses them to extract the [VerifierTrace], and folds them following the protogalaxy
    /// protocol.
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
        let dk_domain = EvaluationDomain::new(vk.cs().degree() as u32 + 3, (instances.len() + 1).trailing_zeros());

        // TODO: Is this sufficient to check H-consistency? I'm not 'checking' anything, but I'm computing
        // the challenges myself - I believe that is enough.
        let _traces = instances
            .into_iter()
            .map(|instance| {
                let trace = parse_trace(
                    vk,
                    #[cfg(feature = "committed-instances")] committed_instances,
                    &[instance],
                    transcript
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

        let _committed_f: CS::Commitment = transcript.read()?;
        let alpha: F = transcript.squeeze_challenge();
        let eval_commited_f: F = transcript.read()?;

        let f_at_alpha = self.error_term + eval_commited_f;

        self.beta_powers = self
            .beta_powers
            .iter()
            .zip(delta_powers.iter())
            .map(|(beta, delta)| *beta + alpha * delta)
            .collect::<Vec<_>>().try_into().unwrap();

        let _poly_k: CS::Commitment = transcript.read()?;
        let gamma: F = transcript.squeeze_challenge();
        let k_at_gamma: F = transcript.read()?;
        let z_in_gamma = gamma.pow_vartime([dk_domain.n]) - F::ONE;

        let mut l0 = dk_domain.empty_lagrange();
        l0[0] = F::ONE;
        let l0_coeff = dk_domain.lagrange_to_coeff(l0);
        let l0_at_gamma = eval_polynomial(&l0_coeff, gamma);

        self.error_term = f_at_alpha * l0_at_gamma + z_in_gamma * k_at_gamma;

        // TODO: need to verify the polynomial commitment openings
        Ok(self)
    }

    /// This function verifies that a folde trace satisfies the relaxed relation.
    // TODO: need to verify that the commitment is correct as well.
    pub fn is_sat<PCS: PolynomialCommitmentScheme<F>>(
        &self,
        vk: &VerifyingKey<F, PCS>,
        evaluator: &Evaluator<F>,
        folded_witness: FoldingProverTrace<F>,
        l0: &Polynomial<F, LagrangeCoeff>,
        l_last: &Polynomial<F, LagrangeCoeff>,
        l_active_row: &Polynomial<F, LagrangeCoeff>,
        permutation_pk_cosets: &[Polynomial<F, LagrangeCoeff>],
    ) -> Result<(), Error> {
        let FoldingProverTrace {
            fixed_polys,
            advice_polys,
            instance_values,
            lookups,
            permutations: permutation,
            challenges,
            beta,
            gamma,
            theta,
            y,
            ..
        } = folded_witness;

        let advice_lagrange = advice_polys
            .iter()
            .map(|a| {
                a.iter()
                    .map(|p| vk.get_domain().coeff_to_lagrange(p.clone()))
                    .collect()
            })
            .collect::<Vec<_>>();

        let witness_poly = evaluator.evaluate_h::<LagrangeCoeff>(
            vk.get_domain(),
            vk.cs(),
            &advice_lagrange
                .iter()
                .map(Vec::as_slice)
                .collect::<Vec<_>>(),
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
            &lookups,
            &permutation,
            l0,
            l_last,
            l_active_row,
            permutation_pk_cosets,
        );

        let expected_result = witness_poly
            .values
            .into_par_iter()
            .zip(self.beta_powers.par_iter())
            .map(|(witness, beta_pow)| witness * beta_pow)
            .reduce(|| F::ZERO, |a, b| a + b);

        if expected_result == self.error_term {
            return Ok(())
        } else {
            Err(Error::Opening)
        }
    }
}