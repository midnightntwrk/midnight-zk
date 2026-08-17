use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use super::{super::Error, Argument};
use crate::{
    plonk::{evaluation::evaluate, trash},
    poly::{
        Coeff, EvaluationDomain, LagrangeCoeff, Polynomial, PolynomialLabel, ProverQuery,
        commitment::PolynomialCommitmentScheme,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::eval_polynomial,
};

#[cfg_attr(feature = "bench-internal", derive(Clone))]
#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField> {
    pub(crate) argument_index: usize,
    pub(crate) trash_poly: Polynomial<F, Coeff>,
}

pub(crate) struct Evaluated<F: PrimeField> {
    committed: Committed<F>,
    pub(crate) evaluated: trash::Evaluated<F>,
}

/// Compresses the constraints of every trash argument into one polynomial each,
/// commits to all of them in a single batched call, and writes the result to
/// the transcript. Mirrors the verifier's `read_trashcans`.
#[allow(clippy::too_many_arguments)]
pub(in crate::plonk) fn commit_trashcans<F, CS, T>(
    arguments: &[Argument<F>],
    params: &CS::Parameters,
    domain: &EvaluationDomain<F>,
    trash_challenge: F,
    advice_values: &[Polynomial<F, LagrangeCoeff>],
    fixed_values: &[Polynomial<F, LagrangeCoeff>],
    instance_values: &[Polynomial<F, LagrangeCoeff>],
    transcript: &mut T,
) -> Result<Vec<Committed<F>>, Error>
where
    F: WithSmallOrderMulGroup<3> + Ord + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    if arguments.is_empty() {
        return Ok(Vec::new());
    }

    let compressed_expressions: Vec<Polynomial<F, LagrangeCoeff>> = arguments
        .par_iter()
        .map(|argument| {
            argument
                .constraint_expressions
                .iter()
                .map(|expression| {
                    domain.lagrange_from_vec(evaluate(
                        expression,
                        domain.n as usize,
                        0,
                        fixed_values,
                        advice_values,
                        instance_values,
                    ))
                })
                .fold(domain.empty_lagrange(), |acc, expression| {
                    acc * trash_challenge + &expression
                })
        })
        .collect();

    let refs: Vec<_> = compressed_expressions.iter().collect();
    let labels: Vec<_> = (0..arguments.len()).map(PolynomialLabel::Trash).collect();
    let trash_com = CS::commit_many(params, &refs, &labels);
    CS::write_commitment(transcript, &trash_com)?;

    Ok(compressed_expressions
        .into_par_iter()
        .enumerate()
        .map(|(argument_index, compressed_expression)| Committed {
            argument_index,
            trash_poly: domain.lagrange_to_coeff(compressed_expression),
        })
        .collect())
}

impl<F: WithSmallOrderMulGroup<3>> Committed<F> {
    pub(crate) fn evaluate<T>(self, x: F, transcript: &mut T) -> Result<Evaluated<F>, Error>
    where
        F: Hashable<T::Hash>,
        T: Transcript,
    {
        let trash_eval = eval_polynomial(&self.trash_poly, x);
        transcript.write(&trash_eval)?;

        Ok(Evaluated {
            committed: self,
            evaluated: trash::Evaluated { trash_eval },
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Evaluated<F> {
    pub(crate) fn open(&self, x: F) -> impl Iterator<Item = ProverQuery<'_, F>> + Clone {
        vec![ProverQuery::new(
            x,
            &self.committed.trash_poly,
            PolynomialLabel::Trash(self.committed.argument_index),
        )]
        .into_iter()
    }
}
