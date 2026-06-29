use std::hash::Hash;

use blake2b_simd::State as Blake2bState;
use ff::{Field, WithSmallOrderMulGroup};
use midnight_curves::{pairing::MultiMillerLoop, serde::SerdeObject, CurveAffine, CurveExt};
use rand_core::OsRng;

use super::primitives::{pow_omega_signed, primitive_root_of_unity, FflonkRoots};
use crate::{
    poly::{
        commitment::{Guard, Labelable, PolynomialCommitmentScheme},
        fflonk::{
            params::ParamsVerifierFflonk, FflonkCommitment, FflonkScheme,
            FflonkVerificationGuard, ParamsFflonk,
        },
        kzg::params::ParamsKZG,
        query::{ProverQuery, VerifierQuery},
        EvaluationDomain, PolynomialLabel,
    },
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// Round-trip test mirroring `kzg::tests::test_roundtrip_gwc`. Commits
/// three polynomials, runs `multi_open` + `multi_prepare` end-to-end,
/// and asserts the pairing check passes (and fails when one eval is
/// tampered with).
///
/// In v1 every sub-bundle is `t=1`, so this is algebraically the same
/// proof KZG produces; we still run it to validate the trait wiring
/// (commitment serde, Hashable, Labelable, Add/Mul, Guard).
#[test]
fn test_roundtrip_gwc() {
    use midnight_curves::Bls12;

    const K: u32 = 4;

    let params: ParamsFflonk<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);

    // `T_MAX_LOG = 0` ⇒ no bundling (KZG-equivalent path).
    let proof = create_proof::<_, CircuitTranscript<Blake2bState>, 0>(&params);

    let verifier_params = params.verifier_params();
    verify::<Bls12, CircuitTranscript<Blake2bState>, 0>(&verifier_params, &proof[..], false, K);
    verify::<Bls12, CircuitTranscript<Blake2bState>, 0>(&verifier_params, &proof[..], true, K);
}

fn verify<E, T, const T_MAX_LOG: u32>(
    verifier_params: &ParamsVerifierFflonk<E>,
    proof: &[u8],
    should_fail: bool,
    k: u32,
) where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
    FflonkCommitment<E, T_MAX_LOG>: Hashable<T::Hash>,
{
    let mut transcript = T::init_from_bytes(proof);

    let a: FflonkCommitment<E, T_MAX_LOG> = transcript
        .read::<FflonkCommitment<E, T_MAX_LOG>>()
        .unwrap()
        .label(vec![PolynomialLabel::Custom("a".into())]);
    let b: FflonkCommitment<E, T_MAX_LOG> = transcript
        .read::<FflonkCommitment<E, T_MAX_LOG>>()
        .unwrap()
        .label(vec![PolynomialLabel::Custom("b".into())]);
    let c: FflonkCommitment<E, T_MAX_LOG> = transcript
        .read::<FflonkCommitment<E, T_MAX_LOG>>()
        .unwrap()
        .label(vec![PolynomialLabel::Custom("c".into())]);

    let x: E::Fr = transcript.squeeze_challenge();
    let y: E::Fr = transcript.squeeze_challenge();

    let avx: E::Fr = transcript.read().unwrap();
    let bvx: E::Fr = transcript.read().unwrap();
    let cvy: E::Fr = transcript.read().unwrap();

    let valid_queries = std::iter::empty()
        .chain(Some(VerifierQuery::new(
            x,
            &a,
            avx,
            PolynomialLabel::Custom("a".into()),
        )))
        .chain(Some(VerifierQuery::new(
            x,
            &b,
            bvx,
            PolynomialLabel::Custom("b".into()),
        )))
        .chain(Some(VerifierQuery::new(
            y,
            &c,
            cvy,
            PolynomialLabel::Custom("c".into()),
        )));

    // Tamper: swap `bvx` for `avx` to force the pairing check to fail.
    let invalid_queries = std::iter::empty()
        .chain(Some(VerifierQuery::new(
            x,
            &a,
            avx,
            PolynomialLabel::Custom("a".into()),
        )))
        .chain(Some(VerifierQuery::new(
            x,
            &b,
            avx,
            PolynomialLabel::Custom("b".into()),
        )))
        .chain(Some(VerifierQuery::new(
            y,
            &c,
            cvy,
            PolynomialLabel::Custom("c".into()),
        )));

    let queries = if should_fail {
        invalid_queries
    } else {
        valid_queries
    };

    let result = FflonkScheme::<E, T_MAX_LOG>::multi_prepare(
        &queries.collect::<Vec<_>>(),
        k,
        &mut transcript,
    )
    .unwrap();

    if should_fail {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_err()
        );
    } else {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_ok()
        );
    }
}

fn create_proof<E, T, const T_MAX_LOG: u32>(params: &ParamsFflonk<E>) -> Vec<u8>
where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    let k = (params.g.len() - 1).ilog2() + 1;
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

    let a = FflonkScheme::<E, T_MAX_LOG>::commit(
        params,
        &[&ax],
        &[PolynomialLabel::Custom("a".into())],
    );
    let b = FflonkScheme::<E, T_MAX_LOG>::commit(
        params,
        &[&bx],
        &[PolynomialLabel::Custom("b".into())],
    );
    let c = FflonkScheme::<E, T_MAX_LOG>::commit(
        params,
        &[&cx],
        &[PolynomialLabel::Custom("c".into())],
    );

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
        ProverQuery::new(x, &ax, PolynomialLabel::Custom("a".into())),
        ProverQuery::new(x, &bx, PolynomialLabel::Custom("b".into())),
        ProverQuery::new(y, &cx, PolynomialLabel::Custom("c".into())),
    ]
    .into_iter();

    FflonkScheme::<E, T_MAX_LOG>::multi_open(
        params,
        &queries.collect::<Vec<_>>(),
        &mut transcript,
    )
    .unwrap();

    transcript.finalize()
}

/// Real bundling round-trip: 4 polynomials of length `n = 16` committed in
/// ONE `commit` call → a single `t = 4` sub-bundle. Each poly is opened at
/// one logical point `x = s^t` (a t-th power, so `t_th_root` succeeds).
///
/// The PCS commits a *single* G1 point for all 4 polynomials and opens at
/// the 4 t-th roots of `x`; the verifier reconstructs `g(root)` via
/// Lemma 5.1 from the 4 per-poly evaluations at `x`. Tampering with any
/// single claim must make the pairing check fail.
#[test]
fn test_bundle_t4_single_rotation() {
    use midnight_curves::Bls12;

    // SRS sized 2^6 = 64; polys of length 2^4 = 16; T_MAX = 2^2 = 4 ⇒ 4·16 = 64 ≤
    // 64. ✓
    const K_SRS: u32 = 6;
    const K_DOMAIN: u32 = 4;
    const T_MAX_LOG: u32 = 2;

    let params: ParamsFflonk<Bls12> = ParamsKZG::unsafe_setup(K_SRS, OsRng);

    let proof =
        create_bundle_proof::<_, CircuitTranscript<Blake2bState>, T_MAX_LOG>(&params, K_DOMAIN);

    let verifier_params = params.verifier_params();
    verify_bundle::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        false,
        K_DOMAIN,
    );
    verify_bundle::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        true,
        K_DOMAIN,
    );
}

fn create_bundle_proof<E, T, const T_MAX_LOG: u32>(
    params: &ParamsFflonk<E>,
    k_domain: u32,
) -> Vec<u8>
where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    let domain = EvaluationDomain::new(1, k_domain);

    // 4 distinct polynomials of length n=16 in coefficient form.
    let polys: Vec<_> = (0..4u64)
        .map(|seed| {
            let mut p = domain.empty_coeff();
            for (i, v) in p.iter_mut().enumerate() {
                *v = <E::Fr>::from(seed * 1000 + i as u64 + 1);
            }
            p
        })
        .collect();

    let labels: Vec<_> = (0..4).map(PolynomialLabel::Advice).collect();

    let mut transcript = T::init();

    // ONE multi-poly commit → ONE `t=4` bundle.
    let poly_refs: Vec<&_> = polys.iter().collect();
    let comm = FflonkScheme::<E, T_MAX_LOG>::commit(params, &poly_refs, &labels);
    assert_eq!(comm.0.len(), 1, "expected a single t=4 bundle");
    assert_eq!(
        <FflonkCommitment<E, T_MAX_LOG> as crate::poly::commitment::Labelable>::length(&comm),
        4,
        "expected the bundle to carry 4 polynomials"
    );
    transcript.write(&comm).unwrap();

    // Use the trait method — symmetric across prover and verifier now
    // that `T_MAX` lives in the type and `squeeze_evaluation_point` does
    // not take `params`.
    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);

    // Write `t` per-poly claims `f_i(x)` to the transcript — these are
    // exactly what the verifier consumes to reconstruct `g(root)` via
    // Lemma 5.1.
    let claims: Vec<E::Fr> = polys.iter().map(|p| eval_polynomial(p, x)).collect();
    for c in &claims {
        transcript.write(c).unwrap();
    }

    let queries: Vec<ProverQuery<E::Fr>> = polys
        .iter()
        .enumerate()
        .map(|(i, p)| ProverQuery::new(x, p, PolynomialLabel::Advice(i)))
        .collect();

    FflonkScheme::<E, T_MAX_LOG>::multi_open(params, &queries, &mut transcript).unwrap();

    transcript.finalize()
}

/// Real bundling with **Lagrange-form input**: polys are committed in
/// Lagrange basis, but the trait still requires Coeff-form polys at
/// open time. `commit` internally IFFTs each Lagrange poly before
/// combining; the test verifies that the result agrees with what the
/// verifier computes via Coeff polys converted externally.
#[test]
fn test_bundle_t4_lagrange_input() {
    use midnight_curves::Bls12;

    const K_SRS: u32 = 6;
    const K_DOMAIN: u32 = 4;
    const T_MAX_LOG: u32 = 2;

    let params: ParamsFflonk<Bls12> = ParamsKZG::unsafe_setup(K_SRS, OsRng);
    let proof = create_lagrange_bundle_proof::<_, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &params, K_DOMAIN,
    );

    let verifier_params = params.verifier_params();
    verify_bundle::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        false,
        K_DOMAIN,
    );
    verify_bundle::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        true,
        K_DOMAIN,
    );
}

fn create_lagrange_bundle_proof<E, T, const T_MAX_LOG: u32>(
    params: &ParamsFflonk<E>,
    k_domain: u32,
) -> Vec<u8>
where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    let domain = EvaluationDomain::new(1, k_domain);

    // Build polys in Lagrange basis.
    let lagrange_polys: Vec<_> = (0..4u64)
        .map(|seed| {
            let mut p = domain.empty_lagrange();
            for (i, v) in p.iter_mut().enumerate() {
                *v = <E::Fr>::from(seed * 1000 + i as u64 + 1);
            }
            p
        })
        .collect();

    // Compute the Coeff form externally (for queries) — should agree with
    // what `commit` does internally.
    let coeff_polys: Vec<_> =
        lagrange_polys.iter().cloned().map(|lp| domain.lagrange_to_coeff(lp)).collect();

    let labels: Vec<_> = (0..4).map(PolynomialLabel::Advice).collect();
    let mut transcript = T::init();

    // Commit with LagrangeCoeff polys — exercises `commit`'s internal
    // `lagrange_to_coeff` path for `t > 1` sub-bundles.
    let lagrange_refs: Vec<&_> = lagrange_polys.iter().collect();
    let comm = FflonkScheme::<E, T_MAX_LOG>::commit(params, &lagrange_refs, &labels);
    transcript.write(&comm).unwrap();

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);

    let claims: Vec<E::Fr> = coeff_polys.iter().map(|p| eval_polynomial(p, x)).collect();
    for c in &claims {
        transcript.write(c).unwrap();
    }

    let queries: Vec<ProverQuery<E::Fr>> = coeff_polys
        .iter()
        .enumerate()
        .map(|(i, p)| ProverQuery::new(x, p, PolynomialLabel::Advice(i)))
        .collect();

    FflonkScheme::<E, T_MAX_LOG>::multi_open(params, &queries, &mut transcript).unwrap();
    transcript.finalize()
}

/// Real bundling, **mixed cohort**: 4 advice polys in one bundle, but
/// only 2 of them are opened at the second rotation. The PCS must
/// over-open the missing slots (i.e. compute `f_2(ωx)` and `f_3(ωx)`
/// on the prover side, write them to the transcript) so the verifier
/// can reconstruct `g(root)` at the t-th roots of `ωx` via Lemma 5.1.
/// Without the over-opening, the verifier would fill those slots with
/// 0 and produce a wrong `g(root)`.
#[test]
fn test_bundle_t4_mixed_cohort() {
    use midnight_curves::Bls12;

    const K_SRS: u32 = 6;
    const K_DOMAIN: u32 = 4;
    const T_MAX_LOG: u32 = 2;

    let params: ParamsFflonk<Bls12> = ParamsKZG::unsafe_setup(K_SRS, OsRng);
    let proof = create_mixed_cohort_proof::<_, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &params, K_DOMAIN,
    );

    let verifier_params = params.verifier_params();
    verify_mixed_cohort::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        false,
        K_DOMAIN,
    );
    verify_mixed_cohort::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        true,
        K_DOMAIN,
    );
}

fn create_mixed_cohort_proof<E, T, const T_MAX_LOG: u32>(
    params: &ParamsFflonk<E>,
    k_domain: u32,
) -> Vec<u8>
where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    let domain = EvaluationDomain::new(1, k_domain);
    let n_log = k_domain;

    let polys: Vec<_> = (0..4u64)
        .map(|seed| {
            let mut p = domain.empty_coeff();
            for (i, v) in p.iter_mut().enumerate() {
                *v = <E::Fr>::from(seed * 1000 + i as u64 + 1);
            }
            p
        })
        .collect();

    let labels: Vec<_> = (0..4).map(PolynomialLabel::Advice).collect();

    let mut transcript = T::init();

    // ONE multi-poly commit → ONE `t=4` bundle.
    let poly_refs: Vec<&_> = polys.iter().collect();
    let comm = FflonkScheme::<E, T_MAX_LOG>::commit(params, &poly_refs, &labels);
    transcript.write(&comm).unwrap();

    // `x = s^T_MAX` via the trait method. `ω_n · x` is also a `T_MAX`-th
    // power because `T_MAX | n` (`ω_n = α^T_MAX` for `α` a primitive
    // `T_MAX·n`-th root of unity).
    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);
    let omega_n = primitive_root_of_unity::<E::Fr>(1usize << n_log);
    let omega_x = omega_n * x;

    // Open all 4 polys at `x`, but only `f_0, f_1` at `ωx` — mixed cohort.
    let claims: Vec<(usize, E::Fr, E::Fr)> = vec![
        (0, x, eval_polynomial(&polys[0], x)),
        (0, omega_x, eval_polynomial(&polys[0], omega_x)),
        (1, x, eval_polynomial(&polys[1], x)),
        (1, omega_x, eval_polynomial(&polys[1], omega_x)),
        (2, x, eval_polynomial(&polys[2], x)),
        (3, x, eval_polynomial(&polys[3], x)),
    ];
    for (_, _, e) in &claims {
        transcript.write(e).unwrap();
    }

    let queries: Vec<ProverQuery<E::Fr>> = claims
        .iter()
        .map(|(slot, point, _)| {
            ProverQuery::new(*point, &polys[*slot], PolynomialLabel::Advice(*slot))
        })
        .collect();

    FflonkScheme::<E, T_MAX_LOG>::multi_open(params, &queries, &mut transcript).unwrap();

    transcript.finalize()
}

fn verify_mixed_cohort<E, T, const T_MAX_LOG: u32>(
    verifier_params: &ParamsVerifierFflonk<E>,
    proof: &[u8],
    should_fail: bool,
    k_domain: u32,
) where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
    FflonkCommitment<E, T_MAX_LOG>: Hashable<T::Hash>,
{
    let mut transcript = T::init_from_bytes(proof);

    let labels: Vec<_> = (0..4).map(PolynomialLabel::Advice).collect();
    let comm = transcript.read::<FflonkCommitment<E, T_MAX_LOG>>().unwrap().label(labels.clone());

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);
    let omega_n = primitive_root_of_unity::<E::Fr>(16);
    let omega_x = omega_n * x;

    // Same six (slot, point) pairs the prover wrote — keep the order!
    let pairs: Vec<(usize, E::Fr)> =
        vec![(0, x), (0, omega_x), (1, x), (1, omega_x), (2, x), (3, x)];
    let mut claims: Vec<E::Fr> = (0..pairs.len()).map(|_| transcript.read().unwrap()).collect();

    if should_fail {
        // Tamper with one of the explicit claims.
        claims[0] += E::Fr::ONE;
    }

    let queries: Vec<VerifierQuery<E::Fr, FflonkScheme<E, T_MAX_LOG>>> = pairs
        .iter()
        .zip(claims.iter())
        .map(|(&(slot, point), &eval)| {
            VerifierQuery::new(point, &comm, eval, PolynomialLabel::Advice(slot))
        })
        .collect();

    let result =
        FflonkScheme::<E, T_MAX_LOG>::multi_prepare(&queries, k_domain, &mut transcript).unwrap();
    if should_fail {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_err()
        );
    } else {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_ok()
        );
    }
}

fn verify_bundle<E, T, const T_MAX_LOG: u32>(
    verifier_params: &ParamsVerifierFflonk<E>,
    proof: &[u8],
    should_fail: bool,
    k: u32,
) where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
    FflonkCommitment<E, T_MAX_LOG>: Hashable<T::Hash>,
{
    let mut transcript = T::init_from_bytes(proof);

    let labels: Vec<_> = (0..4).map(PolynomialLabel::Advice).collect();
    let comm = transcript.read::<FflonkCommitment<E, T_MAX_LOG>>().unwrap().label(labels.clone());

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);

    let mut claims: Vec<E::Fr> = (0..4).map(|_| transcript.read().unwrap()).collect();

    if should_fail {
        // Tamper with the first claim — verifier should reject.
        claims[0] += E::Fr::ONE;
    }

    let queries: Vec<VerifierQuery<E::Fr, FflonkScheme<E, T_MAX_LOG>>> = claims
        .iter()
        .enumerate()
        .map(|(i, &eval)| VerifierQuery::new(x, &comm, eval, PolynomialLabel::Advice(i)))
        .collect();

    let result =
        FflonkScheme::<E, T_MAX_LOG>::multi_prepare(&queries, k, &mut transcript).unwrap();

    if should_fail {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_err()
        );
    } else {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_ok()
        );
    }
}

/// Explicit multi-rotation test: 2 advice polys in one `t=2` bundle, each
/// opened at three rotated logical points `x · ω_n^r` for
/// `r ∈ {0, +1, −1}` (uniform cohort, so no over-opening).
///
/// Drives the paper's rotation arithmetic (`omega_n`, `omega_tn`,
/// `omega_t`) through [`FflonkRoots`] — its constructor asserts the
/// invariant `omega_tn[i]^{t_i} == omega_n`, so building it on both
/// sides exercises that check. Uses [`pow_omega_signed`] for the
/// negative-rotation logical point (`x · ω_n^{−1}`), which is the
/// idiomatic way the protocol will phrase rotations once the
/// `FflonkRoots` precompute lifts into [`FflonkScheme::multi_open`].
///
/// Both `FflonkRoots` and `pow_omega_signed` are otherwise dead-code
/// today — this test is what holds them in place pending the rotation-
/// arithmetic optimization (avoiding the repeated `sqrt` inside
/// `t_th_root` by building roots directly from `s · omega_tn^r`).
#[test]
fn test_bundle_t2_signed_rotations() {
    use midnight_curves::Bls12;

    // T_MAX=2, n=8, t·n=16 ≤ 2^4 ⇒ K_SRS=4.
    const K_SRS: u32 = 4;
    const K_DOMAIN: u32 = 3;
    const T_MAX_LOG: u32 = 1;

    let params: ParamsFflonk<Bls12> = ParamsKZG::unsafe_setup(K_SRS, OsRng);
    let proof = create_signed_rotation_proof::<_, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &params, K_DOMAIN,
    );

    let verifier_params = params.verifier_params();
    verify_signed_rotation::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        K_DOMAIN,
        false,
    );
    verify_signed_rotation::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        K_DOMAIN,
        true,
    );
}

fn create_signed_rotation_proof<E, T, const T_MAX_LOG: u32>(
    params: &ParamsFflonk<E>,
    k_domain: u32,
) -> Vec<u8>
where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    let domain = EvaluationDomain::new(1, k_domain);

    // Two distinct length-`n` advice polys.
    let polys: Vec<_> = (0..2u64)
        .map(|seed| {
            let mut p = domain.empty_coeff();
            for (i, v) in p.iter_mut().enumerate() {
                *v = <E::Fr>::from(seed * 1000 + i as u64 + 1);
            }
            p
        })
        .collect();
    let labels: Vec<_> = (0..2).map(PolynomialLabel::Advice).collect();

    // Paper's rotation precompute. Constructor asserts
    // `omega_tn[0]^t == omega_n`; verifying the same on the other side
    // catches any regression in the 2-adic-root construction.
    let roots: FflonkRoots<E::Fr> = FflonkRoots::new(&[2], k_domain);
    assert_eq!(
        roots.omega_tn[0].pow_vartime([2u64]),
        roots.omega_n,
        "FflonkRoots invariant"
    );

    let mut transcript = T::init();

    let poly_refs: Vec<&_> = polys.iter().collect();
    let comm = FflonkScheme::<E, T_MAX_LOG>::commit(params, &poly_refs, &labels);
    assert_eq!(comm.0.len(), 1, "expected a single t=2 bundle");
    transcript.write(&comm).unwrap();

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);

    // Three rotations: r ∈ {0, +1, −1}. `pow_omega_signed` handles the
    // negative case via `omega^{|r|}.invert()`.
    let rotations: [i64; 3] = [0, 1, -1];
    let logicals: Vec<E::Fr> = rotations
        .iter()
        .map(|&r| x * pow_omega_signed::<E::Fr>(roots.omega_n, r))
        .collect();

    // Write all 2 × 3 = 6 claims (slot-major to match the read order).
    let mut claims: Vec<(usize, E::Fr, E::Fr)> = Vec::with_capacity(6);
    for &logical in &logicals {
        #[allow(clippy::needless_range_loop)]
        for slot in 0..2 {
            claims.push((slot, logical, eval_polynomial(&polys[slot], logical)));
        }
    }
    for (_, _, e) in &claims {
        transcript.write(e).unwrap();
    }

    let queries: Vec<ProverQuery<E::Fr>> = claims
        .iter()
        .map(|(slot, point, _)| {
            ProverQuery::new(*point, &polys[*slot], PolynomialLabel::Advice(*slot))
        })
        .collect();

    FflonkScheme::<E, T_MAX_LOG>::multi_open(params, &queries, &mut transcript).unwrap();
    transcript.finalize()
}

fn verify_signed_rotation<E, T, const T_MAX_LOG: u32>(
    verifier_params: &ParamsVerifierFflonk<E>,
    proof: &[u8],
    k_domain: u32,
    should_fail: bool,
) where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
    FflonkCommitment<E, T_MAX_LOG>: Hashable<T::Hash>,
{
    let mut transcript = T::init_from_bytes(proof);

    let labels: Vec<_> = (0..2).map(PolynomialLabel::Advice).collect();
    let comm = transcript.read::<FflonkCommitment<E, T_MAX_LOG>>().unwrap().label(labels.clone());

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);
    let roots: FflonkRoots<E::Fr> = FflonkRoots::new(&[2], k_domain);
    assert_eq!(
        roots.omega_tn[0].pow_vartime([2u64]),
        roots.omega_n,
        "FflonkRoots invariant (verifier)"
    );

    let rotations: [i64; 3] = [0, 1, -1];
    let logicals: Vec<E::Fr> = rotations
        .iter()
        .map(|&r| x * pow_omega_signed::<E::Fr>(roots.omega_n, r))
        .collect();

    let pairs: Vec<(usize, E::Fr)> = logicals
        .iter()
        .flat_map(|&logical| (0..2usize).map(move |slot| (slot, logical)))
        .collect();
    assert_eq!(pairs.len(), 6);

    let mut claims: Vec<E::Fr> = (0..pairs.len()).map(|_| transcript.read().unwrap()).collect();

    if should_fail {
        claims[0] += E::Fr::ONE;
    }

    let queries: Vec<VerifierQuery<E::Fr, FflonkScheme<E, T_MAX_LOG>>> = pairs
        .iter()
        .zip(claims.iter())
        .map(|(&(slot, point), &eval)| {
            VerifierQuery::new(point, &comm, eval, PolynomialLabel::Advice(slot))
        })
        .collect();

    let result =
        FflonkScheme::<E, T_MAX_LOG>::multi_prepare(&queries, k_domain, &mut transcript).unwrap();
    if should_fail {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_err()
        );
    } else {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_ok()
        );
    }
}

/// Combined-features test: a `t = 2` advice bundle (uniform cohort)
/// alongside two singleton commitments — `Quotient` opened at
/// `{x, ωx}` and `Fixed(0)` opened at `{x}` only. With
/// `fewer-point-sets` ON, the verifier-side pad sees a multi-point
/// group (`Quotient`) and a singleton (`Fixed(0)`); the heuristic adds
/// a dummy opening of `Fixed(0)` at `ωx` so both commitments share the
/// `{x, ωx}` point set. With the feature OFF, no dummies fire. The
/// test passes in both modes — the assertion is a clean round-trip,
/// not a transcript-byte equality.
///
/// What this catches: any divergence between prover and verifier in
/// the ordering of (over-opening → fewer-point-sets) transcript I/O,
/// or in the bundle/singleton classification at the boundary of the
/// two padding calls.
#[test]
fn test_fflonk_with_fewer_point_sets() {
    use midnight_curves::Bls12;

    // T_MAX=2, n=8, t·n=16 ≤ 2^4 ⇒ K_SRS=4. Inner f_com/π commits use
    // params.g (length 16), which is enough for f_poly/pi_poly ≤ 15.
    const K_SRS: u32 = 4;
    const K_DOMAIN: u32 = 3;
    const T_MAX_LOG: u32 = 1;

    let params: ParamsFflonk<Bls12> = ParamsKZG::unsafe_setup(K_SRS, OsRng);
    let proof = create_combined_proof::<_, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &params, K_DOMAIN,
    );
    let verifier_params = params.verifier_params();
    verify_combined::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        K_DOMAIN,
        false,
    );
    verify_combined::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        K_DOMAIN,
        true,
    );
}

fn create_combined_proof<E, T, const T_MAX_LOG: u32>(
    params: &ParamsFflonk<E>,
    k_domain: u32,
) -> Vec<u8>
where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    let domain = EvaluationDomain::new(1, k_domain);

    let advice_polys: Vec<_> = (0..2u64)
        .map(|seed| {
            let mut p = domain.empty_coeff();
            for (i, v) in p.iter_mut().enumerate() {
                *v = <E::Fr>::from(seed * 100 + i as u64 + 1);
            }
            p
        })
        .collect();
    let advice_labels: Vec<_> = (0..2).map(PolynomialLabel::Advice).collect();

    let mut quot_poly = domain.empty_coeff();
    for (i, v) in quot_poly.iter_mut().enumerate() {
        *v = <E::Fr>::from(700 + i as u64);
    }
    let mut fixed_poly = domain.empty_coeff();
    for (i, v) in fixed_poly.iter_mut().enumerate() {
        *v = <E::Fr>::from(50 + i as u64);
    }

    let mut transcript = T::init();

    let advice_refs: Vec<&_> = advice_polys.iter().collect();
    let comm_advice =
        FflonkScheme::<E, T_MAX_LOG>::commit(params, &advice_refs, &advice_labels);
    let comm_quot = FflonkScheme::<E, T_MAX_LOG>::commit(
        params,
        &[&quot_poly],
        &[PolynomialLabel::Quotient],
    );
    let comm_fixed = FflonkScheme::<E, T_MAX_LOG>::commit(
        params,
        &[&fixed_poly],
        &[PolynomialLabel::Fixed(0)],
    );
    transcript.write(&comm_advice).unwrap();
    transcript.write(&comm_quot).unwrap();
    transcript.write(&comm_fixed).unwrap();

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);
    let omega_n = primitive_root_of_unity::<E::Fr>(1usize << k_domain);
    let omega_x = omega_n * x;

    let a0_x = eval_polynomial(&advice_polys[0], x);
    let a1_x = eval_polynomial(&advice_polys[1], x);
    let q_x = eval_polynomial(&quot_poly, x);
    let q_ox = eval_polynomial(&quot_poly, omega_x);
    let f_x = eval_polynomial(&fixed_poly, x);
    for e in &[a0_x, a1_x, q_x, q_ox, f_x] {
        transcript.write(e).unwrap();
    }

    let queries = vec![
        ProverQuery::new(x, &advice_polys[0], PolynomialLabel::Advice(0)),
        ProverQuery::new(x, &advice_polys[1], PolynomialLabel::Advice(1)),
        ProverQuery::new(x, &quot_poly, PolynomialLabel::Quotient),
        ProverQuery::new(omega_x, &quot_poly, PolynomialLabel::Quotient),
        ProverQuery::new(x, &fixed_poly, PolynomialLabel::Fixed(0)),
    ];

    FflonkScheme::<E, T_MAX_LOG>::multi_open(params, &queries, &mut transcript).unwrap();
    transcript.finalize()
}

fn verify_combined<E, T, const T_MAX_LOG: u32>(
    verifier_params: &ParamsVerifierFflonk<E>,
    proof: &[u8],
    k_domain: u32,
    should_fail: bool,
) where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
    FflonkCommitment<E, T_MAX_LOG>: Hashable<T::Hash>,
{
    let mut transcript = T::init_from_bytes(proof);

    let advice_labels: Vec<_> = (0..2).map(PolynomialLabel::Advice).collect();
    let comm_advice = transcript.read::<FflonkCommitment<E, T_MAX_LOG>>().unwrap().label(advice_labels);
    let comm_quot = transcript
        .read::<FflonkCommitment<E, T_MAX_LOG>>()
        .unwrap()
        .label(vec![PolynomialLabel::Quotient]);
    let comm_fixed = transcript
        .read::<FflonkCommitment<E, T_MAX_LOG>>()
        .unwrap()
        .label(vec![PolynomialLabel::Fixed(0)]);

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);
    let omega_n = primitive_root_of_unity::<E::Fr>(1usize << k_domain);
    let omega_x = omega_n * x;

    let mut claims: Vec<E::Fr> = (0..5).map(|_| transcript.read().unwrap()).collect();
    if should_fail {
        claims[0] += E::Fr::ONE;
    }

    let queries: Vec<VerifierQuery<E::Fr, FflonkScheme<E, T_MAX_LOG>>> = vec![
        VerifierQuery::new(x, &comm_advice, claims[0], PolynomialLabel::Advice(0)),
        VerifierQuery::new(x, &comm_advice, claims[1], PolynomialLabel::Advice(1)),
        VerifierQuery::new(x, &comm_quot, claims[2], PolynomialLabel::Quotient),
        VerifierQuery::new(omega_x, &comm_quot, claims[3], PolynomialLabel::Quotient),
        VerifierQuery::new(x, &comm_fixed, claims[4], PolynomialLabel::Fixed(0)),
    ];

    let result =
        FflonkScheme::<E, T_MAX_LOG>::multi_prepare(&queries, k_domain, &mut transcript).unwrap();
    if should_fail {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_err()
        );
    } else {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params
            )
            .is_ok()
        );
    }
}

/// Padding-B end-to-end: 3 advice polynomials with `T_MAX_LOG = 2` (so
/// `T_MAX = 4`) — the partition packs them into a single `t = 4` bundle
/// with the 4th slot padded by a zero polynomial. The prover commits one
/// G1 (combined over the 4-slot `g`, with the pad slot contributing zero),
/// writes 3 evaluations (one per real slot, none for the pad), and emits
/// 4 synthetic queries on `g` at the 4 t-th roots of the opening point.
/// The verifier reconstructs `g(root)` for each t-th root via Lemma 5.1
/// with `slot_evals[3] = 0` for the pad slot.
///
/// What this catches: any prover/verifier disagreement at the pad slot —
/// either writing/reading a transcript byte for the pad (would desync),
/// or missing the zero-fill at the verifier (would feed garbage to
/// `eval_claims_as_poly`). Tampering with any real claim must reject.
#[test]
fn test_bundle_t4_padded_with_one_pad_slot() {
    use midnight_curves::Bls12;

    // SRS 2^6 = 64, polys length 2^4 = 16, T_MAX = 4 ⇒ 4·16 = 64 ≤ 64. ✓
    const K_SRS: u32 = 6;
    const K_DOMAIN: u32 = 4;
    const T_MAX_LOG: u32 = 2;

    let params: ParamsFflonk<Bls12> = ParamsKZG::unsafe_setup(K_SRS, OsRng);

    let proof = create_padded_bundle_proof::<_, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &params, K_DOMAIN,
    );

    let verifier_params = params.verifier_params();
    verify_padded_bundle::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        false,
        K_DOMAIN,
    );
    verify_padded_bundle::<Bls12, CircuitTranscript<Blake2bState>, T_MAX_LOG>(
        &verifier_params,
        &proof[..],
        true,
        K_DOMAIN,
    );
}

fn create_padded_bundle_proof<E, T, const T_MAX_LOG: u32>(
    params: &ParamsFflonk<E>,
    k_domain: u32,
) -> Vec<u8>
where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    let domain = EvaluationDomain::new(1, k_domain);

    // 3 advice polynomials (not a power of two) — partition packs them
    // into one bundle with t = next_pow2(3) = 4, one pad slot.
    let polys: Vec<_> = (0..3u64)
        .map(|seed| {
            let mut p = domain.empty_coeff();
            for (i, v) in p.iter_mut().enumerate() {
                *v = <E::Fr>::from(seed * 1000 + i as u64 + 1);
            }
            p
        })
        .collect();
    let labels: Vec<_> = (0..3).map(PolynomialLabel::Advice).collect();

    let mut transcript = T::init();

    let poly_refs: Vec<&_> = polys.iter().collect();
    let comm = FflonkScheme::<E, T_MAX_LOG>::commit(params, &poly_refs, &labels);
    assert_eq!(comm.0.len(), 1, "expected a single padded bundle");
    assert_eq!(
        <FflonkCommitment<E, T_MAX_LOG> as crate::poly::commitment::Labelable>::length(&comm),
        3,
        "bundle should carry 3 REAL polynomials (pad slot not counted)"
    );
    transcript.write(&comm).unwrap();

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);

    // Three claims, one per real slot. No write for the pad slot —
    // verifier reconstructs its eval as 0 implicitly.
    let claims: Vec<E::Fr> = polys.iter().map(|p| eval_polynomial(p, x)).collect();
    for c in &claims {
        transcript.write(c).unwrap();
    }

    let queries: Vec<ProverQuery<E::Fr>> = polys
        .iter()
        .enumerate()
        .map(|(i, p)| ProverQuery::new(x, p, PolynomialLabel::Advice(i)))
        .collect();

    FflonkScheme::<E, T_MAX_LOG>::multi_open(params, &queries, &mut transcript).unwrap();
    transcript.finalize()
}

fn verify_padded_bundle<E, T, const T_MAX_LOG: u32>(
    verifier_params: &ParamsVerifierFflonk<E>,
    proof: &[u8],
    should_fail: bool,
    k_domain: u32,
) where
    E: MultiMillerLoop,
    T: Transcript,
    E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
    E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
    FflonkCommitment<E, T_MAX_LOG>: Hashable<T::Hash>,
{
    let mut transcript = T::init_from_bytes(proof);

    let labels: Vec<_> = (0..3).map(PolynomialLabel::Advice).collect();
    let comm = transcript.read::<FflonkCommitment<E, T_MAX_LOG>>().unwrap().label(labels);

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);

    let mut claims: Vec<E::Fr> = (0..3).map(|_| transcript.read().unwrap()).collect();

    if should_fail {
        claims[0] += E::Fr::ONE;
    }

    let queries: Vec<VerifierQuery<E::Fr, FflonkScheme<E, T_MAX_LOG>>> = claims
        .iter()
        .enumerate()
        .map(|(i, &eval)| VerifierQuery::new(x, &comm, eval, PolynomialLabel::Advice(i)))
        .collect();

    let result =
        FflonkScheme::<E, T_MAX_LOG>::multi_prepare(&queries, k_domain, &mut transcript).unwrap();
    if should_fail {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params,
            )
            .is_err()
        );
    } else {
        assert!(
            <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>>::verify(
                result,
                verifier_params,
            )
            .is_ok()
        );
    }
}

/// At `T_MAX_LOG = 0`, fflonk's `commit`/`multi_open` go through the
/// singleton path: each polynomial gets its own G1 commitment, the partition
/// is the identity, and the GWC multi-open argument is the same one KZG
/// runs. We claim the wire format is byte-identical to `KZGMultiCommitment`
/// — this test pins that claim by running the same workload through both
/// schemes and comparing the produced proof bytes verbatim.
///
/// If this ever diverges (someone adds a fflonk-specific transcript
/// emission, or changes a commitment write order), the assertion fails
/// loudly. That's the contract we depend on for `FflonkScheme<E, 0>` to be
/// a drop-in replacement for `KZGCommitmentScheme<E>` without forcing VK
/// or goldenfile regeneration.
#[test]
fn fflonk_t_max_log_0_proof_matches_kzg() {
    use midnight_curves::Bls12;

    use midnight_curves::pairing::Engine;

    use crate::poly::kzg::KZGCommitmentScheme;

    type Fr = <Bls12 as Engine>::Fr;

    const K: u32 = 4;

    // Same SRS for both setups (KZG and fflonk share `ParamsKZG`).
    let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);

    let domain = EvaluationDomain::<Fr>::new(1, K);
    let mut ax = domain.empty_coeff();
    for (i, a) in ax.iter_mut().enumerate() {
        *a = Fr::from(10 + i as u64);
    }
    let mut bx = domain.empty_coeff();
    for (i, a) in bx.iter_mut().enumerate() {
        *a = Fr::from(100 + i as u64);
    }
    let mut cx = domain.empty_coeff();
    for (i, a) in cx.iter_mut().enumerate() {
        *a = Fr::from(1000 + i as u64);
    }

    // -------- KZG side --------
    let mut kzg_transcript = CircuitTranscript::<Blake2bState>::init();
    let a_kzg = KZGCommitmentScheme::<Bls12>::commit(
        &params,
        &[&ax],
        &[PolynomialLabel::Custom("a".into())],
    );
    let b_kzg = KZGCommitmentScheme::<Bls12>::commit(
        &params,
        &[&bx],
        &[PolynomialLabel::Custom("b".into())],
    );
    let c_kzg = KZGCommitmentScheme::<Bls12>::commit(
        &params,
        &[&cx],
        &[PolynomialLabel::Custom("c".into())],
    );
    kzg_transcript.write(&a_kzg).unwrap();
    kzg_transcript.write(&b_kzg).unwrap();
    kzg_transcript.write(&c_kzg).unwrap();
    let x_kzg: Fr =
        KZGCommitmentScheme::<Bls12>::squeeze_evaluation_point(&mut kzg_transcript);
    let y_kzg: Fr =
        KZGCommitmentScheme::<Bls12>::squeeze_evaluation_point(&mut kzg_transcript);
    let avx_kzg = eval_polynomial(&ax, x_kzg);
    let bvx_kzg = eval_polynomial(&bx, x_kzg);
    let cvy_kzg = eval_polynomial(&cx, y_kzg);
    kzg_transcript.write(&avx_kzg).unwrap();
    kzg_transcript.write(&bvx_kzg).unwrap();
    kzg_transcript.write(&cvy_kzg).unwrap();
    let kzg_queries = [
        ProverQuery::new(x_kzg, &ax, PolynomialLabel::Custom("a".into())),
        ProverQuery::new(x_kzg, &bx, PolynomialLabel::Custom("b".into())),
        ProverQuery::new(y_kzg, &cx, PolynomialLabel::Custom("c".into())),
    ];
    KZGCommitmentScheme::<Bls12>::multi_open(&params, &kzg_queries, &mut kzg_transcript).unwrap();
    let kzg_proof = kzg_transcript.finalize();

    // -------- fflonk side, T_MAX_LOG = 0 --------
    let mut fflonk_transcript = CircuitTranscript::<Blake2bState>::init();
    let a_ff = FflonkScheme::<Bls12, 0>::commit(
        &params,
        &[&ax],
        &[PolynomialLabel::Custom("a".into())],
    );
    let b_ff = FflonkScheme::<Bls12, 0>::commit(
        &params,
        &[&bx],
        &[PolynomialLabel::Custom("b".into())],
    );
    let c_ff = FflonkScheme::<Bls12, 0>::commit(
        &params,
        &[&cx],
        &[PolynomialLabel::Custom("c".into())],
    );
    fflonk_transcript.write(&a_ff).unwrap();
    fflonk_transcript.write(&b_ff).unwrap();
    fflonk_transcript.write(&c_ff).unwrap();
    let x_ff: Fr =
        FflonkScheme::<Bls12, 0>::squeeze_evaluation_point(&mut fflonk_transcript);
    let y_ff: Fr =
        FflonkScheme::<Bls12, 0>::squeeze_evaluation_point(&mut fflonk_transcript);
    let avx_ff = eval_polynomial(&ax, x_ff);
    let bvx_ff = eval_polynomial(&bx, x_ff);
    let cvy_ff = eval_polynomial(&cx, y_ff);
    fflonk_transcript.write(&avx_ff).unwrap();
    fflonk_transcript.write(&bvx_ff).unwrap();
    fflonk_transcript.write(&cvy_ff).unwrap();
    let ff_queries = [
        ProverQuery::new(x_ff, &ax, PolynomialLabel::Custom("a".into())),
        ProverQuery::new(x_ff, &bx, PolynomialLabel::Custom("b".into())),
        ProverQuery::new(y_ff, &cx, PolynomialLabel::Custom("c".into())),
    ];
    FflonkScheme::<Bls12, 0>::multi_open(&params, &ff_queries, &mut fflonk_transcript).unwrap();
    let fflonk_proof = fflonk_transcript.finalize();

    // Same transcript bytes ⇒ same Fiat-Shamir squeezes.
    assert_eq!(
        x_kzg, x_ff,
        "fflonk@0 and KZG must squeeze identical evaluation points"
    );
    assert_eq!(y_kzg, y_ff);

    // Proofs must match byte-for-byte.
    assert_eq!(
        kzg_proof, fflonk_proof,
        "fflonk@T_MAX_LOG=0 must produce byte-identical proofs to baseline KZG"
    );
}

/// `t = 2` bundling with **LagrangeDelta-form input** — the basis used by
/// PermutationAccumulator / LogupMultiplicities. The bench at K=13 fails
/// here at T>0; this test isolates whether the bug is in the
/// `LagrangeDelta → LagrangeCoeff → Coeff` conversion path inside the
/// `FflonkScheme::commit` `t > 1` branch, or somewhere else.
///
/// Setup: two polys, both committed as `LagrangeDelta` (via
/// `to_delta`). Labels `PermutationAccumulator(0)` and
/// `PermutationAccumulator(1)` — partition's `BundleFamily::PermutationAccumulator`
/// bin produces a single `t = 2` bundle. Queries are constructed against
/// the Coeff form of the original Lagrange polys (so the verifier sees
/// the correct claims).
#[test]
fn test_bundle_t2_lagrange_delta_input() {
    use midnight_curves::Bls12;

    const K_SRS: u32 = 5;
    const K_DOMAIN: u32 = 3;
    const T_MAX_LOG: u32 = 1;

    type E = Bls12;
    type T = CircuitTranscript<Blake2bState>;

    let params: ParamsFflonk<E> = ParamsKZG::unsafe_setup(K_SRS, OsRng);

    let domain = EvaluationDomain::<<E as midnight_curves::pairing::Engine>::Fr>::new(1, K_DOMAIN);

    // Build two Lagrange-form polynomials, then convert to LagrangeDelta.
    let lagrange_polys: Vec<_> = (0..2u64)
        .map(|seed| {
            let mut p = domain.empty_lagrange();
            for (i, v) in p.iter_mut().enumerate() {
                *v = <<E as midnight_curves::pairing::Engine>::Fr>::from(seed * 100 + i as u64 + 1);
            }
            p
        })
        .collect();

    let delta_polys: Vec<_> = lagrange_polys.iter().map(|p| p.to_delta()).collect();

    // Sanity 1: `to_delta().into_lagrange()` must recover the original
    // Lagrange polynomial.
    for (orig, delta) in lagrange_polys.iter().zip(delta_polys.iter()) {
        let roundtrip = delta.clone().into_lagrange();
        assert_eq!(
            orig.values, roundtrip.values,
            "to_delta.into_lagrange is not the identity"
        );
    }

    let delta_refs: Vec<&_> = delta_polys.iter().collect();

    // Coeff-form polynomials, computed externally — used for the queries +
    // claim values. The commit's internal `LagrangeDelta → LagrangeCoeff
    // → Coeff` path must produce the same combined polynomial as the
    // external chain `to_delta⁻¹ → lagrange_to_coeff → combine`.
    let coeff_polys: Vec<_> =
        lagrange_polys.iter().cloned().map(|p| domain.lagrange_to_coeff(p)).collect();

    // Labels in the PermutationAccumulator family — partition bundles them
    // at t=2.
    let labels: Vec<_> = (0..2).map(PolynomialLabel::PermutationAccumulator).collect();

    let mut transcript = T::init();
    let comm = FflonkScheme::<E, T_MAX_LOG>::commit(&params, &delta_refs, &labels);
    transcript.write(&comm).unwrap();

    let x = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);

    let claims: Vec<<E as midnight_curves::pairing::Engine>::Fr> =
        coeff_polys.iter().map(|p| eval_polynomial(p, x)).collect();
    for c in &claims {
        transcript.write(c).unwrap();
    }

    let queries: Vec<ProverQuery<<E as midnight_curves::pairing::Engine>::Fr>> = coeff_polys
        .iter()
        .enumerate()
        .map(|(i, p)| ProverQuery::new(x, p, PolynomialLabel::PermutationAccumulator(i)))
        .collect();

    FflonkScheme::<E, T_MAX_LOG>::multi_open(&params, &queries, &mut transcript).unwrap();
    let proof = transcript.finalize();

    // Verifier side.
    let verifier_params = params.verifier_params();
    let mut transcript = T::init_from_bytes(&proof[..]);

    let labeled_com: FflonkCommitment<E, T_MAX_LOG> =
        transcript.read::<FflonkCommitment<E, T_MAX_LOG>>().unwrap().label(labels.clone());

    let x_v = FflonkScheme::<E, T_MAX_LOG>::squeeze_evaluation_point(&mut transcript);
    assert_eq!(x, x_v, "evaluation point must match");

    let claims_v: Vec<<E as midnight_curves::pairing::Engine>::Fr> =
        claims.iter().map(|_| transcript.read().unwrap()).collect();
    assert_eq!(claims, claims_v, "claims must match");

    let queries_v: Vec<VerifierQuery<<E as midnight_curves::pairing::Engine>::Fr, FflonkScheme<E, T_MAX_LOG>>> = (0
        ..2)
        .map(|i| {
            VerifierQuery::new(
                x_v,
                &labeled_com,
                claims_v[i],
                PolynomialLabel::PermutationAccumulator(i),
            )
        })
        .collect();

    let guard: FflonkVerificationGuard<E, T_MAX_LOG> =
        FflonkScheme::<E, T_MAX_LOG>::multi_prepare(&queries_v, K_DOMAIN, &mut transcript).unwrap();

    assert!(
        <FflonkVerificationGuard<E, T_MAX_LOG> as Guard<
            <E as midnight_curves::pairing::Engine>::Fr,
            FflonkScheme<E, T_MAX_LOG>,
        >>::verify(guard, &verifier_params)
        .is_ok(),
        "LagrangeDelta-input t=2 bundle: pairing check failed — bug likely in \
         FflonkScheme::commit's LagrangeDelta arm or in the multi_open/multi_prepare \
         handling of the converted polynomial"
    );
}
