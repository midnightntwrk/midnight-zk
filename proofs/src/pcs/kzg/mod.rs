//! We implement the multi-open technique developed in Halo 2. It is designed to
//! efficiently open multiple polynomials at multiple points while minimizing
//! proof size and verification time. In a nutshell, multiple opening queries
//! are batched into a single query by combining the target
//! polynomials/commitments and evaluation points using verifier-chosen
//! random scalars.
//!
//! For a more detailed explanation, see the [Halo 2 Book](https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html) on Multipoint Openings.

use std::{
    collections::HashMap,
    io::{self, Read},
    marker::PhantomData,
};

use midnight_curves::pairing::Engine;

/// KZG commitment type
pub mod commitment;

use std::{fmt::Debug, hash::Hash};

use commitment::{KZGCommitment, KZGMultiCommitment};
use midnight_curves::pairing::MultiMillerLoop;
use rand_core::OsRng;

#[cfg(feature = "fewer-point-sets")]
use crate::{pcs::compute_dummy_queries, utils::arithmetic::eval_polynomial};
use crate::{
    pcs::{
        msm::{msm_specific, DualMSM},
        multi_open::{multi_open_core, multi_prepare_core},
        params::{ParamsKZG, ParamsVerifierKZG},
        PolynomialCommitmentScheme,
    },
    poly::{
        query::{PolynomialLabel, VerifierQuery},
        Error, Polynomial, PolynomialRepresentation, ProverQuery,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{
        arithmetic::{CurveAffine, CurveExt},
        helpers::{ProcessedSerdeObject, SerdeFormat},
    },
};

#[derive(Clone, Debug)]
/// KZG verifier
pub struct KZGCommitmentScheme<E: Engine> {
    _marker: PhantomData<E>,
}

impl<E: MultiMillerLoop> PolynomialCommitmentScheme<E::Fr> for KZGCommitmentScheme<E>
where
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    type Parameters = ParamsKZG<E>;
    type VerifierParameters = ParamsVerifierKZG<E>;
    type Commitment = KZGMultiCommitment<E>;
    type VerificationGuard = DualMSM<E>;

    fn gen_params(k: u32) -> Self::Parameters {
        ParamsKZG::unsafe_setup(k, OsRng)
    }

    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters {
        params.verifier_params()
    }

    fn commit_many<B: PolynomialRepresentation>(
        params: &Self::Parameters,
        polynomials: &[&Polynomial<E::Fr, B>],
        labels: &[PolynomialLabel],
    ) -> Self::Commitment {
        assert_eq!(
            polynomials.len(),
            labels.len(),
            "polynomials and labels must have the same length"
        );
        assert!(!polynomials.is_empty(), "cannot commit to zero polynomials");
        let bases = params.bases::<B>();
        KZGMultiCommitment(
            polynomials
                .iter()
                .zip(labels)
                .map(|(polynomial, label)| {
                    let size = polynomial.values.len();
                    assert!(bases.len() >= size);
                    KZGCommitment::Simple(
                        msm_specific::<E::G1Affine>(&polynomial.values, &bases[..size]),
                        label.clone(),
                    )
                })
                .collect(),
        )
    }

    fn read_commitment<T: Transcript>(
        transcript: &mut T,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self::Commitment>
    where
        Self::Commitment: Hashable<T::Hash>,
    {
        // KZG commits each polynomial independently, so a commitment to
        // `labels.len()` polynomials is `labels.len()` points read (and hashed)
        // one after another, each tagged with its label.
        let inners = labels
            .iter()
            .map(|label| {
                let com: KZGMultiCommitment<E> = transcript.read()?;
                Ok(KZGCommitment::Simple(
                    com.into_single().into_point(),
                    label.clone(),
                ))
            })
            .collect::<io::Result<Vec<_>>>()?;
        Ok(KZGMultiCommitment(inners))
    }

    fn deserialize_commitment<R: Read>(
        reader: &mut R,
        format: SerdeFormat,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self::Commitment> {
        let inners = labels
            .iter()
            .map(|label| {
                let point = E::G1::read(reader, format)?;
                Ok(KZGCommitment::Simple(point, label.clone()))
            })
            .collect::<io::Result<Vec<_>>>()?;
        Ok(KZGMultiCommitment(inners))
    }

    fn write_commitment<T: Transcript>(
        transcript: &mut T,
        commitment: &Self::Commitment,
    ) -> io::Result<()>
    where
        Self::Commitment: Hashable<T::Hash>,
    {
        // KZG commits each polynomial independently.
        for inner in &commitment.0 {
            transcript.write(&KZGMultiCommitment(vec![inner.clone()]))?;
        }
        Ok(())
    }

    fn multi_open<T: Transcript>(
        params: &Self::Parameters,
        queries: &[ProverQuery<E::Fr>],
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        E::Fr: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        KZGMultiCommitment<E>: Hashable<T::Hash>,
    {
        // Add dummy queries to reduce the number of distinct multi-open point sets.
        #[cfg(feature = "fewer-point-sets")]
        let queries = &{
            let mut queries = queries.to_vec();
            let pairs: Vec<_> = queries.iter().map(|q| (q.label.clone(), q.point)).collect();
            for (idx, dummy_point) in compute_dummy_queries(&pairs) {
                let poly = queries[idx].poly;
                let label = queries[idx].label.clone();
                transcript
                    .write(&eval_polynomial(&poly[..], dummy_point))
                    .map_err(|_| Error::OpeningError)?;
                queries.push(ProverQuery {
                    point: dummy_point,
                    poly,
                    label,
                });
            }
            queries
        };

        multi_open_core::<E::Fr, Self, T>(params, queries, transcript)
    }

    fn multi_prepare<'com, T: Transcript>(
        queries: &[VerifierQuery<'com, E::Fr, KZGCommitmentScheme<E>>],
        transcript: &mut T,
    ) -> Result<DualMSM<E>, Error>
    where
        E::Fr: Sampleable<T::Hash> + Ord + Hash + Hashable<T::Hash>,
        E::G1: CurveExt<ScalarExt = E::Fr>,
        KZGMultiCommitment<E>: Hashable<T::Hash> + 'com,
    {
        // Add dummy queries to reduce the number of distinct multi-open point sets.
        #[cfg(feature = "fewer-point-sets")]
        let queries = &{
            let mut queries = queries.to_vec();
            let pairs: Vec<_> = queries.iter().map(|q| (q.label.clone(), q.point)).collect();
            for (idx, dummy_point) in compute_dummy_queries(&pairs) {
                let commitment = queries[idx].commitment;
                let label = queries[idx].label.clone();
                let eval = transcript.read().map_err(|_| Error::SamplingError)?;
                queries.push(VerifierQuery {
                    point: dummy_point,
                    commitment,
                    label,
                    eval,
                });
            }
            queries
        };

        // Peel each query's multi-commitment down to the single inner
        // `KZGCommitment` it targets, keyed by the query label.
        //
        // A length-1 commitment (the common case, including the `Linear`
        // linearization commitment) peels to its sole inner. A batched
        // commitment holds several `Simple`s, so we pick the one whose own label
        // matches the query.
        let label_to_commitment: HashMap<PolynomialLabel, KZGCommitment<E>> = queries
            .iter()
            .map(|q| {
                let inners = &q.commitment.0;
                let inner = if inners.len() == 1 {
                    &inners[0]
                } else {
                    inners
                        .iter()
                        .find(|c| matches!(c, KZGCommitment::Simple(_, label) if *label == q.label))
                        .expect("batched commitment has no polynomial matching the query label")
                };
                (q.label.clone(), inner.clone())
            })
            .collect();

        let triples = queries
            .iter()
            .map(|query| (query.label.clone(), query.point, query.eval))
            .collect::<Vec<_>>();

        multi_prepare_core::<E, KZGCommitment<E>, T>(
            &triples,
            &label_to_commitment,
            transcript,
            |transcript| {
                Ok(transcript
                    .read::<KZGMultiCommitment<E>>()
                    .map_err(|_| Error::SamplingError)?
                    .into_single()
                    .into_point())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use std::hash::Hash;

    use blake2b_simd::State as Blake2bState;
    use ff::WithSmallOrderMulGroup;
    use midnight_curves::{pairing::MultiMillerLoop, serde::SerdeObject, CurveAffine, CurveExt};
    use rand_core::OsRng;

    use crate::{
        pcs::{
            kzg::{commitment::KZGMultiCommitment, KZGCommitmentScheme},
            params::{ParamsKZG, ParamsVerifierKZG},
            Guard, PolynomialCommitmentScheme,
        },
        poly::{
            query::{ProverQuery, VerifierQuery},
            EvaluationDomain, PolynomialLabel,
        },
        transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
        utils::arithmetic::eval_polynomial,
    };

    #[test]
    fn test_roundtrip_gwc() {
        use midnight_curves::Bls12;

        const K: u32 = 4;

        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);

        let proof = create_proof::<_, CircuitTranscript<Blake2bState>>(&params);

        let verifier_params = params.verifier_params();
        verify::<Bls12, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], false);

        verify::<Bls12, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], true);
    }

    fn verify<E, T>(verifier_params: &ParamsVerifierKZG<E>, proof: &[u8], should_fail: bool)
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
        KZGMultiCommitment<E>: Hashable<T::Hash>,
    {
        let mut transcript = T::init_from_bytes(proof);

        let a = KZGCommitmentScheme::<E>::read_commitment(
            &mut transcript,
            &[PolynomialLabel::Custom("a".into())],
        )
        .unwrap();
        let b = KZGCommitmentScheme::<E>::read_commitment(
            &mut transcript,
            &[PolynomialLabel::Custom("b".into())],
        )
        .unwrap();
        let c = KZGCommitmentScheme::<E>::read_commitment(
            &mut transcript,
            &[PolynomialLabel::Custom("c".into())],
        )
        .unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y: E::Fr = transcript.squeeze_challenge();

        let avx: E::Fr = transcript.read().unwrap();
        let bvx: E::Fr = transcript.read().unwrap();
        let cvy: E::Fr = transcript.read().unwrap();

        let valid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(
                x,
                &a,
                PolynomialLabel::Custom("a".into()),
                avx,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                &b,
                PolynomialLabel::Custom("b".into()),
                bvx,
            )))
            .chain(Some(VerifierQuery::new(
                y,
                &c,
                PolynomialLabel::Custom("c".into()),
                cvy,
            )));

        let invalid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(
                x,
                &a,
                PolynomialLabel::Custom("a".into()),
                avx,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                &b,
                PolynomialLabel::Custom("b".into()),
                avx,
            )))
            .chain(Some(VerifierQuery::new(
                y,
                &c,
                PolynomialLabel::Custom("c".into()),
                cvy,
            )));

        let queries = if should_fail {
            invalid_queries
        } else {
            valid_queries
        };

        let result =
            KZGCommitmentScheme::multi_prepare(&queries.collect::<Vec<_>>(), &mut transcript)
                .unwrap();

        if should_fail {
            assert!(result.verify(verifier_params).is_err());
        } else {
            assert!(result.verify(verifier_params).is_ok());
        }
    }

    fn create_proof<E, T>(kzg_params: &ParamsKZG<E>) -> Vec<u8>
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
    {
        let k = (kzg_params.g.len() - 1).ilog2() + 1;
        let domain = EvaluationDomain::new(1, k);

        let mut ax = domain.empty_coeff();
        for (i, a) in ax.iter_mut().enumerate() {
            *a = <E::Fr>::from(10 + i as u64);
        }

        let mut bx = domain.empty_coeff();
        for (i, a) in bx.iter_mut().enumerate() {
            *a = <E::Fr>::from(100 + i as u64);
        }

        let mut cx = domain.empty_coeff();
        for (i, a) in cx.iter_mut().enumerate() {
            *a = <E::Fr>::from(100 + i as u64);
        }

        let mut transcript = T::init();

        let a = KZGCommitmentScheme::commit(kzg_params, &ax, PolynomialLabel::Custom("a".into()));
        let b = KZGCommitmentScheme::commit(kzg_params, &bx, PolynomialLabel::Custom("b".into()));
        let c = KZGCommitmentScheme::commit(kzg_params, &cx, PolynomialLabel::Custom("c".into()));

        transcript.write(&a).unwrap();
        transcript.write(&b).unwrap();
        transcript.write(&c).unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenge();

        let avx = eval_polynomial(&ax, x);
        let bvx = eval_polynomial(&bx, x);
        let cvy = eval_polynomial(&cx, y);

        transcript.write(&avx).unwrap();
        transcript.write(&bvx).unwrap();
        transcript.write(&cvy).unwrap();

        let queries = [
            ProverQuery {
                point: x,
                poly: &ax,
                label: PolynomialLabel::Custom("a".into()),
            },
            ProverQuery {
                point: x,
                poly: &bx,
                label: PolynomialLabel::Custom("b".into()),
            },
            ProverQuery {
                point: y,
                poly: &cx,
                label: PolynomialLabel::Custom("c".into()),
            },
        ]
        .into_iter();

        KZGCommitmentScheme::multi_open(kzg_params, &queries.collect::<Vec<_>>(), &mut transcript)
            .unwrap();

        transcript.finalize()
    }
}
