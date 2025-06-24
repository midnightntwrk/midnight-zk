use std::iter;

use ff::{PrimeField, WithSmallOrderMulGroup};

use super::Argument;
use crate::{
    plonk::{Error, VerifyingKey},
    poly::{commitment::PolynomialCommitmentScheme, VerifierQuery},
    transcript::{read_n, Hashable, Transcript},
};

pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    random_poly_commitment: CS::Commitment,
}

pub struct Constructed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    h_commitments: Vec<CS::Commitment>,
    random_poly_commitment: CS::Commitment,
}

pub struct PartiallyEvaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    h_commitments: Vec<CS::Commitment>,
    random_poly_commitment: CS::Commitment,
    random_eval: F,
}

pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    h_commitments: Vec<CS::Commitment>,
    random_poly_commitment: CS::Commitment,
    expected_h_eval: F,
    random_eval: F,
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Argument<F, CS> {
    pub(in crate::plonk) fn read_commitments_before_y<T: Transcript>(
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let random_poly_commitment = transcript.read()?;

        Ok(Committed {
            random_poly_commitment,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    pub(in crate::plonk) fn read_commitments_after_y<T: Transcript>(
        self,
        vk: &VerifyingKey<F, CS>,
        transcript: &mut T,
    ) -> Result<Constructed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        // Obtain a commitment to h(X) in the form of multiple pieces of degree n - 1
        let h_commitments = read_n(transcript, vk.domain.get_quotient_poly_degree())?;

        Ok(Constructed {
            h_commitments,
            random_poly_commitment: self.random_poly_commitment,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Constructed<F, CS> {
    pub(in crate::plonk) fn evaluate_after_x<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<PartiallyEvaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let random_eval = transcript.read()?;

        Ok(PartiallyEvaluated {
            h_commitments: self.h_commitments,
            random_poly_commitment: self.random_poly_commitment,
            random_eval,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> PartiallyEvaluated<F, CS> {
    pub(in crate::plonk) fn verify(
        self,
        expressions: impl Iterator<Item = F>,
        y: F,
        xn: F,
    ) -> Evaluated<F, CS> {
        let expected_h_eval = expressions.fold(F::ZERO, |h_eval, v| h_eval * &y + &v);
        let expected_h_eval = expected_h_eval * ((xn - F::ONE).invert().unwrap());

        Evaluated {
            h_commitments: self.h_commitments,
            random_poly_commitment: self.random_poly_commitment,
            expected_h_eval,
            random_eval: self.random_eval,
        }
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    pub(in crate::plonk) fn queries(
        &self,
        x: F,
        n: u64,
    ) -> impl Iterator<Item = VerifierQuery<F, CS>> + Clone + '_ {
        iter::empty()
            .chain(Some(VerifierQuery::from_parts(
                x,
                &self.h_commitments.iter().collect::<Vec<_>>(),
                self.expected_h_eval,
                n,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                &self.random_poly_commitment,
                self.random_eval,
            )))
    }
}
