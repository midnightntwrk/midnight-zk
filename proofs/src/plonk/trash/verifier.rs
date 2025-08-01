use ff::{PrimeField, WithSmallOrderMulGroup};

use super::Argument;
use crate::{
    plonk::Error,
    poly::{commitment::PolynomialCommitmentScheme, VerifierQuery},
    transcript::{Hashable, Transcript},
};

pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    trash_commitment: CS::Commitment,
}

pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    committed: Committed<F, CS>,
    trash_eval: F,
}

impl<F: PrimeField> Argument<F> {
    pub(crate) fn read_committed<CS: PolynomialCommitmentScheme<F>, T: Transcript>(
        &self,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let trash_commitment = transcript.read()?;
        Ok(Committed { trash_commitment })
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
        let trash_eval = transcript.read()?;

        Ok(Evaluated {
            committed: self,
            trash_eval,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        argument: &'a Argument<F>,
        trash_challenge: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> impl Iterator<Item = F> + 'a {
        let compressed_expressions = argument
            .constraint_expressions
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
            })
            .fold(F::ZERO, |acc, eval| acc * &trash_challenge + &eval);

        let q = fixed_evals[argument.selector_index];
        vec![compressed_expressions - (F::ONE - q) * self.trash_eval].into_iter()
    }

    pub(in crate::plonk) fn queries(
        &self,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<F, CS>> + Clone {
        vec![VerifierQuery::new(
            x,
            &self.committed.trash_commitment,
            self.trash_eval,
        )]
        .into_iter()
    }
}
