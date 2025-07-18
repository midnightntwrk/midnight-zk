//! We implement the multi-open technique developed in Halo 2. It is designed to
//! efficiently open multiple polynomials at multiple points while minimizing
//! proof size and verification time. In a nutshell, multiple opening queries
//! are batched into a single query by combining the target
//! polynomials/commitments and evaluation points using verifier-chosen
//! random scalars.
//!
//! For a more detailed explanation, see the [Halo 2 Book](https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html) on Multipoint Openings.

use std::marker::PhantomData;

use halo2curves::pairing::Engine;

/// Multiscalar multiplication engines
pub mod msm;
/// KZG commitment scheme
pub mod params;
mod utils;

use std::fmt::Debug;

use ff::Field;
use group::{prime::PrimeCurveAffine, Curve, Group};
use halo2curves::{msm::msm_best, pairing::MultiMillerLoop};
use rand_core::OsRng;

#[cfg(feature = "truncated-challenges")]
use crate::utils::arithmetic::{truncate, truncated_powers};
use crate::{
    poly::{
        commitment::{Params, PolynomialCommitmentScheme},
        kzg::{
            msm::{DualMSM, MSMKZG},
            params::{ParamsKZG, ParamsVerifierKZG},
            utils::construct_intermediate_sets,
        },
        query::VerifierQuery,
        Coeff, Error, LagrangeCoeff, Polynomial, ProverQuery,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{
        arithmetic::{
            eval_polynomial, evals_inner_product, inner_product, kate_division,
            lagrange_interpolate, msm_inner_product, powers, CurveAffine, CurveExt, MSM,
        },
        helpers::ProcessedSerdeObject,
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
    type Commitment = E::G1;
    type VerificationGuard = DualMSM<E>;

    fn gen_params(k: u32) -> Self::Parameters {
        ParamsKZG::unsafe_setup(k, OsRng)
    }

    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters {
        params.verifier_params()
    }

    fn commit(
        params: &Self::Parameters,
        polynomial: &Polynomial<E::Fr, Coeff>,
    ) -> Self::Commitment {
        let mut scalars = Vec::with_capacity(polynomial.len());
        scalars.extend(polynomial.iter());
        let mut bases = vec![<E::G1 as Curve>::AffineRepr::identity(); params.g.len()];
        <E::G1 as Curve>::batch_normalize(&params.g, bases.as_mut_slice());
        let size = scalars.len();
        assert!(bases.len() >= size);
        msm_best(&scalars, &bases[0..size])
    }

    fn commit_lagrange(
        params: &Self::Parameters,
        poly: &Polynomial<E::Fr, LagrangeCoeff>,
    ) -> E::G1 {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let size = scalars.len();

        let mut bases = vec![<E::G1 as Curve>::AffineRepr::identity(); params.g.len()];
        <E::G1 as Curve>::batch_normalize(&params.g_lagrange, bases.as_mut_slice());
        assert!(bases.len() >= size);

        msm_best(&scalars, &bases[0..size])
    }

    fn multi_open<'com, T: Transcript>(
        params: &Self::Parameters,
        prover_query: impl IntoIterator<Item = ProverQuery<'com, E::Fr>> + Clone,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        E::Fr: Sampleable<T::Hash> + Ord + Hashable<T::Hash>,
        E::G1: Hashable<T::Hash>,
    {
        // Refer to the halo2 book for docs:
        // https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html
        let x1: E::Fr = transcript.squeeze_challenge();
        let x2: E::Fr = transcript.squeeze_challenge();

        let (poly_map, point_sets) = construct_intermediate_sets(prover_query)?;

        let mut q_polys = vec![vec![]; point_sets.len()];

        for com_data in poly_map.iter() {
            q_polys[com_data.set_index].push(com_data.commitment.poly.clone());
        }

        let q_polys = q_polys
            .iter()
            .map(|polys| {
                #[cfg(feature = "truncated-challenges")]
                let x1 = truncated_powers(x1);

                #[cfg(not(feature = "truncated-challenges"))]
                let x1 = powers(x1);

                inner_product(polys, x1)
            })
            .collect::<Vec<_>>();

        let f_poly = {
            let f_polys = point_sets
                .iter()
                .zip(q_polys.clone())
                .map(|(points, q_poly)| {
                    let mut poly = points.iter().fold(q_poly.clone().values, |poly, point| {
                        kate_division(&poly, *point)
                    });
                    poly.resize(1 << params.max_k() as usize, E::Fr::ZERO);
                    Polynomial {
                        values: poly,
                        _marker: PhantomData,
                    }
                })
                .collect::<Vec<_>>();
            inner_product(&f_polys, powers(x2))
        };

        let f_com = Self::commit(params, &f_poly);
        transcript.write(&f_com).map_err(|_| Error::OpeningError)?;

        let x3: E::Fr = transcript.squeeze_challenge();
        #[cfg(feature = "truncated-challenges")]
        let x3 = truncate(x3);

        for q_poly in q_polys.iter() {
            transcript
                .write(&eval_polynomial(&q_poly.values, x3))
                .map_err(|_| Error::OpeningError)?;
        }

        let x4: E::Fr = transcript.squeeze_challenge();

        let final_poly = {
            let mut polys = q_polys;
            polys.push(f_poly);
            #[cfg(feature = "truncated-challenges")]
            let powers = truncated_powers(x4);

            #[cfg(not(feature = "truncated-challenges"))]
            let powers = powers(x4);

            inner_product(&polys, powers)
        };
        let v = eval_polynomial(&final_poly, x3);

        let pi = {
            let pi_poly = Polynomial {
                values: kate_division(&(&final_poly - v).values, x3),
                _marker: PhantomData,
            };
            Self::commit(params, &pi_poly)
        };

        transcript.write(&pi).map_err(|_| Error::OpeningError)
    }

    fn multi_prepare<'com, T: Transcript>(
        verifier_query: impl IntoIterator<Item = VerifierQuery<'com, E::Fr, KZGCommitmentScheme<E>>>
            + Clone,
        transcript: &mut T,
    ) -> Result<DualMSM<E>, Error>
    where
        E::Fr: Sampleable<T::Hash> + Ord + Hashable<T::Hash>,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr>,
    {
        // Refer to the halo2 book for docs:
        // https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html
        let x1: E::Fr = transcript.squeeze_challenge();
        let x2: E::Fr = transcript.squeeze_challenge();

        let (commitment_map, point_sets) = construct_intermediate_sets(verifier_query)?;

        let mut q_coms: Vec<_> = vec![vec![]; point_sets.len()];
        let mut q_eval_sets = vec![vec![]; point_sets.len()];

        for com_data in commitment_map.into_iter() {
            let mut msm = MSMKZG::init();
            let eval_point_opt = if com_data.commitment.is_chopped() {
                // When the commitment is in chopped form, we require that it be evaluated
                // in a single point.
                debug_assert!(com_data.point_indices.len() == 1);
                Some(point_sets[com_data.set_index][com_data.point_indices[0]])
            } else {
                None
            };
            for (scalar, commitment) in com_data.commitment.as_terms(eval_point_opt) {
                msm.append_term(scalar, commitment);
            }
            q_coms[com_data.set_index].push(msm);
            q_eval_sets[com_data.set_index].push(com_data.evals);
        }

        let q_coms = q_coms
            .iter()
            .map(|msms| {
                #[cfg(feature = "truncated-challenges")]
                let powers = truncated_powers(x1);

                #[cfg(not(feature = "truncated-challenges"))]
                let powers = powers(x1);

                msm_inner_product(msms, powers)
            })
            .collect::<Vec<_>>();

        let q_eval_sets = q_eval_sets
            .iter()
            .map(|evals| {
                #[cfg(feature = "truncated-challenges")]
                let powers = truncated_powers(x1);

                #[cfg(not(feature = "truncated-challenges"))]
                let powers = powers(x1);

                evals_inner_product(evals, powers)
            })
            .collect::<Vec<_>>();

        let f_com: E::G1 = transcript.read().map_err(|_| Error::SamplingError)?;

        // Sample a challenge x_3 for checking that f(X) was committed to
        // correctly.
        let x3: E::Fr = transcript.squeeze_challenge();
        #[cfg(feature = "truncated-challenges")]
        let x3 = truncate(x3);

        let mut q_evals_on_x3 = Vec::<E::Fr>::with_capacity(q_eval_sets.len());
        for _ in 0..q_eval_sets.len() {
            q_evals_on_x3.push(transcript.read().map_err(|_| Error::SamplingError)?);
        }

        // We can compute the expected msm_eval at x_3 using the u provided
        // by the prover and from x_2
        let f_eval = point_sets
            .iter()
            .zip(q_eval_sets.iter())
            .zip(q_evals_on_x3.iter())
            .rev()
            .fold(E::Fr::ZERO, |acc_eval, ((points, evals), proof_eval)| {
                let r_poly = lagrange_interpolate(points, evals);
                let r_eval = eval_polynomial(&r_poly, x3);
                // eval = (proof_eval - r_eval) / prod_i (x3 - point_i)
                let den = points
                    .iter()
                    .fold(E::Fr::ONE, |acc, point| acc * &(x3 - point));
                let eval = (*proof_eval - &r_eval) * den.invert().unwrap();
                acc_eval * &(x2) + &eval
            });

        let x4: E::Fr = transcript.squeeze_challenge();

        let final_com = {
            let mut coms = q_coms;
            let mut f_com_as_msm = MSMKZG::init();

            f_com_as_msm.append_term(E::Fr::ONE, f_com);
            coms.push(f_com_as_msm);

            #[cfg(feature = "truncated-challenges")]
            let powers = truncated_powers(x4);

            #[cfg(not(feature = "truncated-challenges"))]
            let powers = powers(x4);

            msm_inner_product(&coms, powers)
        };

        let v = {
            let mut evals = q_evals_on_x3;
            evals.push(f_eval);

            #[cfg(feature = "truncated-challenges")]
            let powers = truncated_powers(x4);

            #[cfg(not(feature = "truncated-challenges"))]
            let powers = powers(x4);

            inner_product(&evals, powers)
        };

        let pi: E::G1 = transcript.read().map_err(|_| Error::SamplingError)?;

        let mut pi_msm = MSMKZG::<E>::init();
        pi_msm.append_term(E::Fr::ONE, pi);

        // Scale zπ
        let mut scaled_pi = MSMKZG::<E>::init();
        scaled_pi.append_term(x3, pi);

        let mut msm_accumulator = DualMSM::init();

        // (π, C − vG + zπ)
        msm_accumulator.left.add_msm(&pi_msm); // π

        msm_accumulator.right.add_msm(&final_com); // C
        msm_accumulator.right.append_term(v, -E::G1::generator()); // -vG
        msm_accumulator.right.add_msm(&scaled_pi); // zπ

        Ok(msm_accumulator)
    }
}

#[cfg(test)]
mod tests {
    use blake2b_simd::State as Blake2bState;
    use ff::WithSmallOrderMulGroup;
    use halo2curves::{pairing::MultiMillerLoop, serde::SerdeObject, CurveAffine, CurveExt};
    use rand_core::OsRng;

    use crate::{
        poly::{
            commitment::{Guard, PolynomialCommitmentScheme},
            kzg::{
                params::{ParamsKZG, ParamsVerifierKZG},
                KZGCommitmentScheme,
            },
            query::{ProverQuery, VerifierQuery},
            EvaluationDomain,
        },
        transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
        utils::arithmetic::eval_polynomial,
    };

    #[test]
    fn test_roundtrip_gwc() {
        use halo2curves::bn256::Bn256;

        const K: u32 = 4;

        let params: ParamsKZG<Bn256> = ParamsKZG::unsafe_setup(K, OsRng);

        let proof = create_proof::<_, CircuitTranscript<Blake2bState>>(&params);

        let verifier_params = params.verifier_params();
        verify::<Bn256, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], false);

        verify::<Bn256, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], true);
    }

    fn verify<E, T>(verifier_params: &ParamsVerifierKZG<E>, proof: &[u8], should_fail: bool)
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: Hashable<T::Hash> + Sampleable<T::Hash> + Ord,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
    {
        let mut transcript = T::init_from_bytes(proof);

        let a: E::G1 = transcript.read().unwrap();
        let b: E::G1 = transcript.read().unwrap();
        let c: E::G1 = transcript.read().unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y: E::Fr = transcript.squeeze_challenge();

        let avx: E::Fr = transcript.read().unwrap();
        let bvx: E::Fr = transcript.read().unwrap();
        let cvy: E::Fr = transcript.read().unwrap();

        let valid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(x, &a, avx)))
            .chain(Some(VerifierQuery::new(x, &b, bvx)))
            .chain(Some(VerifierQuery::new(y, &c, cvy)));

        let invalid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(x, &a, avx)))
            .chain(Some(VerifierQuery::new(x, &b, avx)))
            .chain(Some(VerifierQuery::new(y, &c, cvy)));

        let queries = if should_fail {
            invalid_queries
        } else {
            valid_queries
        };

        let result = KZGCommitmentScheme::multi_prepare(queries, &mut transcript).unwrap();

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
        E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord,
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

        let a = KZGCommitmentScheme::commit(kzg_params, &ax);
        let b = KZGCommitmentScheme::commit(kzg_params, &bx);
        let c = KZGCommitmentScheme::commit(kzg_params, &cx);

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
            },
            ProverQuery {
                point: x,
                poly: &bx,
            },
            ProverQuery {
                point: y,
                poly: &cx,
            },
        ]
        .into_iter();

        KZGCommitmentScheme::multi_open(kzg_params, queries, &mut transcript).unwrap();

        transcript.finalize()
    }
}
