use std::iter;

use ff::{PrimeField, WithSmallOrderMulGroup};

use super::{Argument, VerifyingKey};
use crate::{
    plonk::{self, permutation, Error},
    poly::{commitment::PolynomialCommitmentScheme, Rotation, VerifierQuery},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permutation_product_commitments: Vec<CS::Commitment>,
}

pub(crate) struct CommonEvaluated<F: PrimeField> {
    pub(in crate::plonk) permutation_evals: Vec<F>,
}

pub(crate) struct EvaluatedSets<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    coms: Vec<CS::Commitment>,
    pub(in crate::plonk) sets: Vec<permutation::EvaluatedSet<F, CS>>,
}

impl Argument {
    pub(crate) fn read_product_commitments<
        F: PrimeField,
        CS: PolynomialCommitmentScheme<F>,
        T: Transcript,
    >(
        &self,
        vk: &plonk::VerifyingKey<F, CS>,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let chunk_len = vk.cs_degree - 2;

        let permutation_product_commitments = self
            .columns
            .chunks(chunk_len)
            .map(|_| transcript.read())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Committed {
            permutation_product_commitments,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> VerifyingKey<F, CS> {
    pub(in crate::plonk) fn evaluate<T: Transcript>(
        &self,
        transcript: &mut T,
    ) -> Result<CommonEvaluated<F>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let permutation_evals = self
            .commitments
            .iter()
            .map(|_| transcript.read())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(CommonEvaluated { permutation_evals })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    pub(crate) fn evaluate<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<EvaluatedSets<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
        F: Hashable<T::Hash>,
    {
        let mut coms = vec![];
        let mut sets = vec![];

        let mut iter = self.permutation_product_commitments.into_iter();

        while let Some(permutation_product_commitment) = iter.next() {
            let permutation_product_eval = transcript.read()?;
            let permutation_product_next_eval = transcript.read()?;
            let permutation_product_last_eval = if iter.len() > 0 {
                Some(transcript.read()?)
            } else {
                None
            };

            let evaluated = permutation::EvaluatedSet {
                permutation_product_eval,
                permutation_product_next_eval,
                permutation_product_last_eval,
                _marker: std::marker::PhantomData,
            };

            coms.push(permutation_product_commitment);

            sets.push(evaluated);
        }

        Ok(EvaluatedSets { coms, sets })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> EvaluatedSets<F, CS> {
    pub(in crate::plonk) fn queries<'r>(
        &'r self,
        vk: &'r plonk::VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'r, F, CS>> + Clone + 'r {
        let nr_blinding_factors = vk.cs.nr_blinding_factors();
        let x_next = vk.domain.rotate_omega(x, Rotation::next());
        let x_last = vk.domain.rotate_omega(x, Rotation(-((nr_blinding_factors + 1) as i32)));

        iter::empty()
            .chain(
                self.coms.iter().zip(self.sets.iter()).flat_map(move |(com, set)| {
                    iter::empty()
                        // Open permutation product commitments at x and \omega x
                        .chain(Some(VerifierQuery::new(
                            x,
                            com,
                            set.permutation_product_eval,
                        )))
                        .chain(Some(VerifierQuery::new(
                            x_next,
                            com,
                            set.permutation_product_next_eval,
                        )))
                }),
            )
            // Open it at \omega^{last} x for all but the last set
            .chain(
                self.coms.iter().rev().skip(1).zip(self.sets.iter().rev().skip(1)).flat_map(
                    move |(com, set)| {
                        Some(VerifierQuery::new(
                            x_last,
                            com,
                            set.permutation_product_last_eval.unwrap(),
                        ))
                    },
                ),
            )
    }
}

impl<F: PrimeField> CommonEvaluated<F> {
    pub(in crate::plonk) fn queries<'r, CS: PolynomialCommitmentScheme<F>>(
        &'r self,
        vkey: &'r VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'r, F, CS>> + Clone {
        // Open permutation commitments for each permutation argument at x
        vkey.commitments
            .iter()
            .zip(self.permutation_evals.iter())
            .map(move |(commitment, &eval)| VerifierQuery::new(x, commitment, eval))
    }
}
