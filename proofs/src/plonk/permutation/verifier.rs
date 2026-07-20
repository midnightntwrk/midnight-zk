use ff::{PrimeField, WithSmallOrderMulGroup};

use super::{Argument, VerifyingKey};
use crate::{
    plonk::{self, permutation, Error},
    poly::{
        commitment::{Labelable, PolynomialCommitmentScheme},
        PolynomialLabel, Rotation, VerifierQuery,
    },
    transcript::{Hashable, Transcript},
};

/// Holds the single batched commitment to all permutation accumulator
/// polynomials, together with the number of chunks (which we need at
/// `evaluate` time and which is reconstructible from the verifying key).
#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permutation_product_commitment: CS::Commitment,
    num_chunks: usize,
    _f: std::marker::PhantomData<F>,
}

pub(crate) struct CommonEvaluated<F: PrimeField> {
    pub(crate) permutation_evals: Vec<F>,
}

pub(crate) struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    coms: Committed<F, CS>,
    pub(crate) sets: Vec<permutation::Evaluated<F>>,
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
        let num_chunks = self.columns.chunks(chunk_len).count();
        // Real circuits always have at least one chunk (the permutation
        // argument is mandatory under PLONK as configured here); the
        // prover-side `compute()` would panic before reaching the transcript
        // write if there were zero columns, so we mirror that assumption.
        assert!(
            num_chunks > 0,
            "permutation argument with zero columns is unsupported"
        );

        let labels: Vec<_> = (0..num_chunks).map(PolynomialLabel::PermutationAccumulator).collect();
        let commitment = transcript.read::<CS::Commitment>()?.label(&labels);

        Ok(Committed {
            permutation_product_commitment: commitment,
            num_chunks,
            _f: std::marker::PhantomData,
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
        let mut sets = Vec::with_capacity(self.num_chunks);

        for i in 0..self.num_chunks {
            let permutation_product_eval = transcript.read()?;
            let permutation_product_next_eval = transcript.read()?;
            // All chunks except the last emit an additional x_last evaluation.
            let permutation_product_last_eval = if i + 1 < self.num_chunks {
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
    pub(in crate::plonk) fn queries(
        &self,
        vk: &plonk::VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'_, F, CS>> + Clone {
        let blinding_factors = vk.cs.blinding_factors();
        let x_next = vk.domain.rotate_omega(x, Rotation::next());
        let x_last = vk.domain.rotate_omega(x, Rotation(-((blinding_factors + 1) as i32)));

        // All chunks share the same batched commitment object; fflonk's
        // `find_bundle` (inside `multi_prepare`) routes each query to the
        // correct sub-bundle via the label.
        let product_com = &self.coms.permutation_product_commitment;
        let mut queries = Vec::new();
        for (i, set) in self.sets.iter().enumerate() {
            queries.push(VerifierQuery::new(
                x,
                product_com,
                PolynomialLabel::PermutationAccumulator(i),
                set.permutation_product_eval,
            ));
            queries.push(VerifierQuery::new(
                x_next,
                product_com,
                PolynomialLabel::PermutationAccumulator(i),
                set.permutation_product_next_eval,
            ));
        }
        for (i, set) in self.sets.iter().enumerate().rev().skip(1) {
            queries.push(VerifierQuery::new(
                x_last,
                product_com,
                PolynomialLabel::PermutationAccumulator(i),
                set.permutation_product_last_eval.unwrap(),
            ));
        }
        queries.into_iter()
    }
}

impl<F: PrimeField> CommonEvaluated<F> {
    pub(in crate::plonk) fn queries<'vkey, CS: PolynomialCommitmentScheme<F>>(
        &self,
        vkey: &'vkey VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'vkey, F, CS>> + Clone {
        let evals = self.permutation_evals.clone();
        vkey.commitments
            .iter()
            .zip(evals)
            .enumerate()
            .map(move |(i, (commitment, eval))| {
                VerifierQuery::new(x, commitment, PolynomialLabel::PermutationFixed(i), eval)
            })
    }
}
