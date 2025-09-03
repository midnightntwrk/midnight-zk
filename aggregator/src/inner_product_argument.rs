//! A module implementing a simple inner product argument for relation:
//!
//!   PoK { w in ℕ^{2^k} : <w, v1> = r1 and <w, v2> = r2 }
//!
//! where v1, v2 in G^{2^k} and r1, r2 in G, for group G (in practice, an
//! elliptic curve).
//!
//! For the original works on inner-product arguments, see:
//!  - <https://eprint.iacr.org/2016/263.pdf>
//!  - <https://eprint.iacr.org/2017/1066.pdf>
//!
//! Here, we use slightly different notation and a simpler relation.
//! For a description closer to this implementation, see:
//!  - <https://eprint.iacr.org/2019/1021.pdf> (Section 3.1)
//!  - <https://eprint.iacr.org/2022/1352.pdf> (Figure 3 and Lemma 4)

use std::ops::{Add, Mul};

use ff::Field;
use group::prime::PrimeCurveAffine;
use halo2curves::{msm::msm_best, CurveExt};
use midnight_proofs::{
    plonk::Error,
    transcript::{Hashable, Sampleable, Transcript},
};

/// Creates a proof of knowledge of `scalars` such that
/// `<scalars, bases1> = res1` and `<scalars, bases2> = res2`.
///
/// The proof is appended to the given running transcript.
///
/// # Panics
///
/// - If `|scalars| != |bases1|`.
/// - If `|scalars| != |bases2|`.
/// - If `|scalars|` is not a power of 2.
///
/// This function does not panic if the given results are incorrect.
/// However, the IPA.verify will not accept the proof in that case.
pub fn ipa_prove<T, C>(
    scalars: &[C::Scalar],
    bases1: &[C],
    bases2: &[C],
    res1: &C,
    res2: &C,
    transcript: &mut T,
) -> Result<(), Error>
where
    T: Transcript,
    C: CurveExt + Hashable<T::Hash>,
    C::Scalar: Sampleable<T::Hash> + Hashable<T::Hash>,
{
    assert_eq!(scalars.len(), bases1.len());
    assert_eq!(scalars.len(), bases2.len());
    assert!(scalars.len().is_power_of_two());
    let k = scalars.len().trailing_zeros() as usize;

    bases1.iter().try_for_each(|b| transcript.common(b))?;
    bases2.iter().try_for_each(|b| transcript.common(b))?;
    transcript.common(res1)?;
    transcript.common(res2)?;

    // To share the argument, we batch `bases1` and `bases2` with randomness.
    // The expected result will be `res1 + r * res2`.
    let r: C::Scalar = transcript.squeeze_challenge();
    let bases = fold((C::Scalar::from(1), bases1), (r, bases2));

    let mut s = scalars.to_vec();
    let mut b = bases.to_vec();

    for _ in 0..k {
        let half = s.len() / 2;
        let l = inner_product::<C>(&s[..half], &b[half..]); // <s_left,  b_right>
        let r = inner_product::<C>(&s[half..], &b[..half]); // <s_right, b_left>

        transcript.write(&l)?;
        transcript.write(&r)?;

        let uj: C::Scalar = transcript.squeeze_challenge();
        let uj_inv = uj.invert().unwrap();

        s = fold((uj, &s[..half]), (uj_inv, &s[half..]));
        b = fold((uj, &b[half..]), (uj_inv, &b[..half]));
    }

    debug_assert_eq!(s.len(), 1);
    transcript.write(&s[0])?;

    Ok(())
}

/// Verifies a proof of knowledge of `scalars` such that
/// `<scalars, bases1> = res1 /\ <scalars, bases2> = res2`.
///
/// # Panics
///
/// If `|bases1| != |bases2|`.
/// If `|bases1|` is not a power of 2.
pub fn ipa_verify<T, C>(
    bases1: &[C],
    bases2: &[C],
    res1: &C,
    res2: &C,
    transcript: &mut T,
) -> Result<(), Error>
where
    T: Transcript,
    C: CurveExt + Hashable<T::Hash>,
    C::Scalar: Sampleable<T::Hash> + Hashable<T::Hash>,
{
    assert_eq!(bases1.len(), bases2.len());
    assert!(bases1.len().is_power_of_two());
    let k = bases1.len().trailing_zeros() as usize;

    bases1.iter().try_for_each(|b| transcript.common(b))?;
    bases2.iter().try_for_each(|b| transcript.common(b))?;
    transcript.common(res1)?;
    transcript.common(res2)?;

    // To share the argument, we batch `bases1` and `bases2` with randomness.
    // The expected result will be `res1 + r * res2`.
    let r = transcript.squeeze_challenge();

    // The verification check is:
    // b[0] * s == (res1 + r * res2) + sum_j (L_j * uj^2 + R_j * uj^(-2))
    //
    // where the proof contains {L_j, R_j}_j and s and {uj}_j are the
    // Fiat-Shamir challenges, and b[0] is the result of folding the bases
    // `bases1 + r * bases2` just like the prover did.

    let mut msm_bases: Vec<C> = vec![];
    let mut msm_scalars = vec![];

    let mut ujs = vec![];

    for _ in 0..k {
        let lhs_j = transcript.read()?;
        let rhs_j = transcript.read()?;

        let uj: C::Scalar = transcript.squeeze_challenge();
        let uj_inv = uj.invert().unwrap();

        // L_j * uj^2 + R_j * uj^(-2)
        msm_bases.push(lhs_j);
        msm_bases.push(rhs_j);
        msm_scalars.push(uj.square());
        msm_scalars.push(uj_inv.square());

        ujs.push((uj, uj_inv));
    }

    let s: C::ScalarExt = transcript.read()?;

    let mut ipa_scalars = vec![-s];
    for (uj, uj_inv) in ujs.iter().rev() {
        ipa_scalars = [
            ipa_scalars.iter().map(|s| *s * uj_inv).collect::<Vec<_>>(),
            ipa_scalars.iter().map(|s| *s * uj).collect::<Vec<_>>(),
        ]
        .concat();
    }

    // -b[0] * proof.s (the `ipa_scalars` were built from -proof.s)
    msm_bases.extend(bases1);
    msm_bases.extend(bases2);
    msm_scalars.extend(ipa_scalars.clone());
    msm_scalars.extend(ipa_scalars.iter().map(|s| *s * r).collect::<Vec<_>>());

    // res1 + r * res2
    msm_bases.push(*res1);
    msm_bases.push(*res2);
    msm_scalars.push(C::Scalar::from(1));
    msm_scalars.push(r);

    if (!inner_product::<C>(&msm_scalars, &msm_bases)
        .to_affine()
        .is_identity())
    .into()
    {
        return Err(Error::Opening);
    }

    Ok(())
}

/// Computes the inner-product between the bases and the scalars.
///
/// # Panics
///
/// If `|scalars| != |bases|`.
fn inner_product<C: CurveExt>(scalars: &[C::ScalarExt], bases: &[C]) -> C {
    assert_eq!(scalars.len(), bases.len());
    assert!(!scalars.is_empty());
    let mut affine_bases = vec![C::AffineExt::default(); bases.len()];
    C::batch_normalize(bases, &mut affine_bases);
    msm_best(scalars, &affine_bases)
}

/// Given two vectors two vectors v0, v1 and two coefficients c0, c1, computes
/// c0 * v0 + c1 * v1.
///
/// # Panics
///
/// If `|v0| != |v1|`.
fn fold<S, T>((c0, v0): (S, &[T]), (c1, v1): (S, &[T])) -> Vec<T>
where
    S: Copy,
    T: Copy + Add<Output = T> + Mul<S, Output = T>,
{
    assert_eq!(v0.len(), v1.len());
    v0.iter()
        .zip(v1.iter())
        .map(|(v0_i, v1_i)| *v0_i * c0 + *v1_i * c1)
        .collect()
}

#[cfg(test)]
mod tests {

    use group::Group;
    use midnight_proofs::transcript::CircuitTranscript;
    use rand::rngs::OsRng;

    use super::*;

    type S = midnight_curves::Fq;
    type C = midnight_curves::G1Projective;
    type H = blake2b_simd::State;

    #[test]
    fn test_inner_product_argument() {
        fn test<const N: usize>() {
            let scalars: [S; N] = core::array::from_fn(|_| S::random(OsRng));
            let bases1: [C; N] = core::array::from_fn(|_| C::random(OsRng));
            let bases2: [C; N] = core::array::from_fn(|_| C::random(OsRng));
            let res1 = inner_product::<C>(&scalars, &bases1);
            let res2 = inner_product::<C>(&scalars, &bases2);

            let mut transcript = CircuitTranscript::<H>::init();
            ipa_prove(&scalars, &bases1, &bases2, &res1, &res2, &mut transcript).unwrap();

            let mut transcript = CircuitTranscript::<H>::init_from_bytes(&transcript.finalize());
            assert!(ipa_verify(&bases1, &bases2, &res1, &res2, &mut transcript).is_ok());
        }
        test::<2>();
        test::<4>();
        test::<8>();
        test::<16>();
        test::<32>();
        test::<64>();
        test::<1024>();
    }
}
