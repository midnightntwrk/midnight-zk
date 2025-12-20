use std::iter;

use ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::{
        logup::FlattenArgument,
        Error, VerifyingKey,
    },
    poly::{commitment::PolynomialCommitmentScheme, Rotation, VerifierQuery},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    multiplicities: CS::Commitment,
    helper_poly: CS::Commitment,
    accumulator: CS::Commitment,
}

pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    committed: Committed<F, CS>,
    multiplicities_eval: F,
    helper_eval: F,
    accumulator_eval: F,
    accumulator_next_eval: F,
}

impl<F: WithSmallOrderMulGroup<3>> FlattenArgument<F> {
    pub(in crate::plonk) fn read_commitment<T: Transcript, CS: PolynomialCommitmentScheme<F>>(
        &self,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let multiplicities = transcript.read()?;
        let helper_poly = transcript.read()?;
        let accumulator = transcript.read()?;

        Ok(Committed {
            multiplicities,
            helper_poly,
            accumulator,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    pub(crate) fn evaluate<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let multiplicities_eval = transcript.read()?;
        let helper_eval = transcript.read()?;
        let accumulator_eval = transcript.read()?;
        let accumulator_next_eval = transcript.read()?;

        Ok(Evaluated {
            committed: self,
            multiplicities_eval,
            helper_eval,
            accumulator_eval,
            accumulator_next_eval,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        l_last: F,
        l_blind: F,
        argument: &'a FlattenArgument<F>,
        theta: F,
        beta: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> impl Iterator<Item = F> + 'a {
        use crate::plonk::circuit::Expression;

        // dbg!(&argument
        //     .input_expressions);

        let active_rows = F::ONE - (l_last + l_blind);
        // Evaluate expressions the same way the prover does
        let evaluate_expressions = |expressions: &[Expression<F>]| {
            expressions
                .iter()
                .map(|expression| {
                    expression.evaluate(
                        &|scalar| scalar,
                        &|_| panic!("virtual selectors are removed during optimization"),
                        &|query| fixed_evals[query.index.unwrap()],
                        &|query| advice_evals[query.index.unwrap()],
                        &|query| instance_evals[query.index.unwrap()],
                        &|challenge| challenges[challenge.index()],
                        &|a| -a,
                        &|a, b| a + &b,
                        &|a, b| a * &b,
                        &|a, scalar| a * &scalar,
                    )
                }).collect::<Vec<_>>()
        };
        // Compress expressions the same way the prover does
        let compress_expressions = |expressions: &[Expression<F>]| {
            evaluate_expressions(expressions)
                .iter()
                .fold(F::ZERO, |acc, eval| acc * &theta + eval)
        };

        let compressed_table = compress_expressions(&argument.table_expressions);

        let compressed_inputs_with_beta = argument
            .input_expressions
            .iter()
            .map(|input| {
                let compressed = compress_expressions(input);
                compressed + beta
            })
            .collect::<Vec<_>>();

        let partial_products: Vec<F> = (0..compressed_inputs_with_beta.len()).map(|i| {
            let mut acc = F::ONE;
            for j in 0..compressed_inputs_with_beta.len() {
                if j != i {
                    acc *= compressed_inputs_with_beta[j];
                }
            }
            acc
        }).collect();

        // Helper polynomial constraint: h(X) * ∏_j(f_j(X) + β) = Σ_j ∏_{k≠j}(f_k(X) + β)
        // This ensures the helper polynomial has the correct structure for LogUp soundness.
        // Note: This must hold everywhere (as a polynomial identity), not just at active rows.
        let product: F = compressed_inputs_with_beta.iter().product();
        let sum: F = partial_products.iter().sum();
        let helper_expression = || self.helper_eval * product - sum;

        // LogUp accumulator constraint: Z(ωX) * (S(X) + β) = (Z(X) + h(X)) * (S(X) + β) - m(X)
        // Rearranging: Z(ωX) * (S(X) + β) - (Z(X) + h(X)) * (S(X) + β) + m(X) = 0
        let accumulator_constraint = || {
            let diff = self.accumulator_next_eval * (compressed_table + &beta)
                - (self.accumulator_eval + self.helper_eval) * (compressed_table + &beta)
                + self.multiplicities_eval;
            diff * &active_rows
        };

        std::iter::empty()
            .chain(Some(helper_expression()))
            .chain(Some(accumulator_constraint()))
    }

    pub(in crate::plonk) fn queries(
        &self,
        vk: &VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<F, CS>> + Clone {
        let x_next = vk.domain.rotate_omega(x, Rotation::next());

        iter::empty()
            // Open Z polynomial at 1
            .chain(Some(VerifierQuery::new(
                F::ONE,
                &self.committed.accumulator,
                F::ZERO,
            )))
            // Open multiplicities commitments at x
            .chain(Some(VerifierQuery::new(
                x,
                &self.committed.multiplicities,
                self.multiplicities_eval,
            )))
            // Open helper commitment at x
            .chain(Some(VerifierQuery::new(
                x,
                &self.committed.helper_poly,
                self.helper_eval,
            )))
            // Open lookup running sum commitments at x
            .chain(Some(VerifierQuery::new(
                x,
                &self.committed.accumulator,
                self.accumulator_eval,
            )))
            // Open lookup running sum commitments at \omega x
            .chain(Some(VerifierQuery::new(
                x_next,
                &self.committed.accumulator,
                self.accumulator_next_eval,
            )))
    }
}
