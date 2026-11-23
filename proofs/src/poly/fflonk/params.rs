//! The commitments of [`Fflonk`](super::Fflonk) to interleaved polynomials
//! over KZG.

use std::{
    collections::HashMap,
    fmt::Debug,
    sync::{Arc, RwLock},
};

use midnight_curves::pairing::{Engine, MultiMillerLoop};

use crate::{
    poly::{
        Coeff, LagrangeCoeff, LagrangeDeltaCoeff, Polynomial, PolynomialBasis, PolynomialLabel,
        PolynomialRepresentation,
        commitment::InterleavedCommit,
        kzg::{
            KZGCommitmentScheme, KZGEngine, commit_msm,
            commitment::{KZGCommitment, KZGMultiCommitment},
            params::{ParamsKZG, suffix_sum},
        },
    },
    utils::arithmetic::{CurveAffine, g_to_lagrange},
};

/// Residue `i` modulo `t`, identifying the bases for committing to `X^i f(X^t)`
/// from the `n` values of `f`, the `i`-th part of `g(X) = Σ_i X^i f_i(X^t)`.
/// These bases depend heavily on the representation `basis` of the values, as
/// detailed below. The name comes from `X^i f(X^t)` being made of the monomials
/// `X^e` with `e ≡ i (mod t)`.
///
/// - `Coeff`: the strided monomials `[s^(i + t·j)]`. For `f = Σ_j c_j X^j`,
///   `X^i f(X^t) = Σ_j c_j X^(i + t·j)`.
///
/// - `Lagrange`: `[s^i L_j(s^t)]`, for `L_j` the Lagrange basis of the domain
///   of size `n`: the Lagrange basis built from the strided monomials.
///
/// - `LagrangeDelta`: `[s^i Σ_{k ≥ j} L_k(s^t)]`, the suffix sums of the
///   `Lagrange` bases, as `g_lagrange_delta` is of `g_lagrange`.
///
/// - `LagrangeDoubleDelta`: `[s^i Σ_{k ≥ j} (k - j + 1) L_k(s^t)]`, the suffix
///   sums of the `LagrangeDelta` bases.
///
/// Committing to every `f_i` on its own bases keeps the zeros of its values
/// free. The bases are computed on first use, as the `Lagrange` ones take a
/// group FFT of size `n`, and cached in `ParamsKZG`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Residue {
    /// The representation of the values of `f_i`.
    basis: PolynomialBasis,
    /// The modulus, a power of two.
    t: usize,
    /// The number of values of `f_i`.
    n: usize,
    /// The residue, smaller than `t`.
    i: usize,
}

/// The bases of every [`Residue`] committed to so far.
pub(crate) type ResidueBases<C> = Arc<RwLock<HashMap<Residue, Arc<[C]>>>>;

impl<E> ParamsKZG<E>
where
    E: Engine + Debug,
    E::G1Affine: CurveAffine,
{
    /// The bases of the [`Residue`] `i` modulo `t`, for committing to
    /// `X^i f(X^t)` from the `n` values of `f` in the representation `B`.
    ///
    /// # Panics
    ///
    /// If `B` is the extended Lagrange basis, if `t·n` is larger than the SRS,
    /// or if `B` is Lagrange or one of its delta forms and `n` is not a power
    /// of two.
    pub(crate) fn residue_bases<B: PolynomialRepresentation>(
        &self,
        t: usize,
        n: usize,
        i: usize,
    ) -> Arc<[E::G1Affine]> {
        let residue = Residue {
            basis: B::BASIS,
            t,
            n,
            i,
        };
        if let Some(bases) =
            self.residue_bases.read().expect("residue bases lock poisoned").get(&residue)
        {
            return bases.clone();
        }
        let bases: Arc<[_]> = match B::BASIS {
            PolynomialBasis::Coeff => {
                assert!(
                    t * n <= self.g.len(),
                    "no residue bases of size {n} modulo {t}"
                );
                self.g[i..].iter().step_by(t).take(n).copied().collect()
            }
            PolynomialBasis::Lagrange => {
                assert!(n.is_power_of_two(), "no Lagrange residue bases of size {n}");
                g_to_lagrange(&self.residue_bases::<Coeff>(t, n, i), n.ilog2()).into()
            }
            PolynomialBasis::LagrangeDelta => {
                suffix_sum(&self.residue_bases::<LagrangeCoeff>(t, n, i)).into()
            }
            PolynomialBasis::LagrangeDoubleDelta => {
                suffix_sum(&self.residue_bases::<LagrangeDeltaCoeff>(t, n, i)).into()
            }
            basis => panic!("no residue bases in the {basis:?} basis"),
        };
        let mut cache = self.residue_bases.write().expect("residue bases lock poisoned");
        cache.entry(residue).or_insert(bases).clone()
    }
}

impl<E: KZGEngine, const LOG2_T_MAX: u32> InterleavedCommit<E::Fr, LOG2_T_MAX>
    for KZGCommitmentScheme<E>
{
    type Parameters = ParamsKZG<E>;

    fn commit_interleaved<B: PolynomialRepresentation>(
        params: &<Self as InterleavedCommit<E::Fr, LOG2_T_MAX>>::Parameters,
        chunks: &[&[&Polynomial<E::Fr, B>]],
        labels: &[PolynomialLabel],
    ) -> Self::Commitment {
        assert_eq!(
            chunks.len(),
            labels.len(),
            "chunks and labels must have the same length"
        );
        PolynomialLabel::assert_distinct(labels);

        KZGMultiCommitment(
            (chunks.iter().zip(labels))
                .map(|(chunk, label)| {
                    KZGCommitment::Simple(commit_chunk(params, chunk), label.clone())
                })
                .collect(),
        )
    }
}

/// Commitment to `Σ_i X^i f_i(X^t)`, for `chunk` the polynomials `f_i` and
/// `t` the next power of two of their number.
fn commit_chunk<E, B>(params: &ParamsKZG<E>, chunk: &[&Polynomial<E::Fr, B>]) -> E::G1
where
    E: MultiMillerLoop,
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
    B: PolynomialRepresentation,
{
    let t = chunk.len().next_power_of_two();
    let n = chunk[0].len();
    assert!(
        chunk.iter().all(|poly| poly.len() == n),
        "the polynomials of a chunk have different lengths"
    );
    (chunk.iter().enumerate())
        .map(|(i, poly)| commit_msm(&poly.values, &params.residue_bases::<B>(t, n, i)))
        .sum()
}
