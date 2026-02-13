use std::iter;

use ff::{PrimeField, WithSmallOrderMulGroup};

use super::{Argument, VerifyingKey};
use crate::{
    plonk::{self, permutation, Error},
    poly::{commitment::PolynomialCommitmentScheme, CommitmentLabel, Rotation, VerifierQuery},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permutation_product_commitments: Vec<CS::Commitment>,
}

pub(crate) struct CommonEvaluated<F: PrimeField> {
    pub(crate) permutation_evals: Vec<F>,
}

pub(crate) struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    coms: Committed<F, CS>,
    pub(crate) sets: Vec<plonk::permutation::Evaluated<F>>,
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
    ) -> Result<Evaluated<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
        F: Hashable<T::Hash>,
    {
        let mut sets = vec![];

        let mut iter = self.permutation_product_commitments.iter();

        while let Some(_) = iter.next() {
            let permutation_product_eval = transcript.read()?;
            let permutation_product_next_eval = transcript.read()?;
            let permutation_product_last_eval = if iter.len() > 0 {
                Some(transcript.read()?)
            } else {
                None
            };

            sets.push(permutation::Evaluated {
                permutation_product_eval,
                permutation_product_next_eval,
                permutation_product_last_eval,
            });
        }

        Ok(Evaluated { coms: self, sets })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    pub(in crate::plonk) fn queries<'r>(
        &'r self,
        vk: &'r plonk::VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'r, F, CS>> + Clone + 'r {
        let blinding_factors = vk.cs.blinding_factors();
        let x_next = vk.domain.rotate_omega(x, Rotation::next());
        let x_last = vk.domain.rotate_omega(x, Rotation(-((blinding_factors + 1) as i32)));

        iter::empty()
            .chain(
                self.coms.permutation_product_commitments.iter().zip(self.sets.iter()).flat_map(
                    move |(com, set)| {
                        iter::empty()
                            // Open permutation product commitments at x and \omega x
                            .chain(Some(VerifierQuery::new(
                                x,
                                CommitmentLabel::NoLabel,
                                com,
                                set.permutation_product_eval,
                            )))
                            .chain(Some(VerifierQuery::new(
                                x_next,
                                CommitmentLabel::NoLabel,
                                com,
                                set.permutation_product_next_eval,
                            )))
                    },
                ),
            )
            // Open it at \omega^{last} x for all but the last set
            .chain(
                self.coms
                    .permutation_product_commitments
                    .iter()
                    .rev()
                    .skip(1)
                    .zip(self.sets.iter().rev().skip(1))
                    .flat_map(move |(com, set)| {
                        Some(VerifierQuery::new(
                            x_last,
                            CommitmentLabel::NoLabel,
                            com,
                            set.permutation_product_last_eval.unwrap(),
                        ))
                    }),
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
        vkey.commitments.iter().zip(self.permutation_evals.iter()).enumerate().map(
            move |(i, (commitment, &eval))| {
                VerifierQuery::new(x, CommitmentLabel::Permutation(i), commitment, eval)
            },
        )
    }
}
