use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};

use super::{super::Error, Argument};
use crate::{
    plonk::evaluation::evaluate,
    poly::{
        commitment::PolynomialCommitmentScheme, Coeff, EvaluationDomain, LagrangeCoeff, Polynomial,
        ProverQuery,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::eval_polynomial,
};

#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField> {
    pub(crate) trash_poly: Polynomial<F, Coeff>,
}

pub(crate) struct Evaluated<F: PrimeField>(Committed<F>);

impl<F: WithSmallOrderMulGroup<3> + Ord> Argument<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn commit<'a, 'params: 'a, CS, T>(
        &self,
        params: &'params CS::Parameters,
        domain: &EvaluationDomain<F>,
        trash_challenge: F,
        advice_values: &'a [Polynomial<F, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<F, LagrangeCoeff>],
        instance_values: &'a [Polynomial<F, LagrangeCoeff>],
        challenges: &'a [F],
        transcript: &mut T,
    ) -> Result<Committed<F>, Error>
    where
        F: FromUniformBytes<64>,
        CS: PolynomialCommitmentScheme<F>,
        CS::Commitment: Hashable<T::Hash>,
        T: Transcript,
    {
        let compressed_expression = self
            .constraint_expressions
            .iter()
            .map(|expression| {
                domain.lagrange_from_vec(evaluate(
                    expression,
                    domain.n as usize,
                    1,
                    fixed_values,
                    advice_values,
                    instance_values,
                    challenges,
                ))
            })
            .fold(domain.empty_lagrange(), |acc, expression| {
                acc * trash_challenge + &expression
            });

        let trash_commitment = CS::commit_lagrange(params, &compressed_expression);
        let trash_poly = domain.lagrange_to_coeff(compressed_expression);

        // Hash permuted input commitment
        transcript.write(&trash_commitment)?;

        Ok(Committed { trash_poly })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Committed<F> {
    pub(crate) fn evaluate<T>(self, x: F, transcript: &mut T) -> Result<Evaluated<F>, Error>
    where
        F: Hashable<T::Hash>,
        T: Transcript,
    {
        let trash_eval = eval_polynomial(&self.trash_poly, x);
        transcript.write(&trash_eval)?;

        Ok(Evaluated(self))
    }
}

impl<F: WithSmallOrderMulGroup<3>> Evaluated<F> {
    pub(crate) fn open(&self, x: F) -> impl Iterator<Item = ProverQuery<'_, F>> + Clone {
        vec![ProverQuery {
            point: x,
            poly: &self.0.trash_poly,
        }]
        .into_iter()
    }
}
