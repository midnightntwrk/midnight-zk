// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

//! The parameters of [`Fflonk`](super::Fflonk) over KZG, and the commitments to
//! interleaved polynomials made with them.

use std::{
    borrow::Borrow,
    collections::HashMap,
    fmt::Debug,
    io,
    sync::{Arc, RwLock},
};

use ff::{Field, PrimeField};
use group::{Curve, Group};
use midnight_curves::{
    pairing::{Engine, MultiMillerLoop},
    serde::SerdeObject,
};
use rayon::prelude::*;

use crate::{
    poly::{
        Coeff, LagrangeCoeff, LagrangeDeltaCoeff, LagrangeDoubleDeltaCoeff, Polynomial,
        PolynomialBasis, PolynomialLabel, PolynomialRepresentation,
        commitment::InterleavedCommit,
        kzg::{
            KZGCommitmentScheme, KZGEngine, commit_msm,
            commitment::{KZGCommitment, KZGMultiCommitment},
            params::{ParamsKZG, ParamsVerifierKZG, read_points, suffix_sum, write_points},
        },
    },
    utils::{
        SerdeFormat,
        arithmetic::{CurveAffine, g_to_lagrange},
        helpers::ProcessedSerdeObject,
    },
};

/// The parameters for committing with [`Fflonk`](super::Fflonk) over KZG, to
/// chunks of up to `T_MAX = 2^LOG2_T_MAX` polynomials of `n` values, `T_MAX·n`
/// being the size of the SRS: the [`ParamsKZG`], with the bases of the
/// [`Residue`]s modulo every power of two `t ≤ T_MAX`.
///
/// The `Lagrange`, `LagrangeDelta` and `LagrangeDoubleDelta` bases of size
/// `n` are built once, by [`Self::from_kzgs`] or [`Self::from_kzg`], and can be
/// stored on disk with [`Self::write`]. Any other bases are built on first use
/// and cached.
#[derive(Clone, Debug)]
pub struct ParamsFflonkKZG<E: Engine, const LOG2_T_MAX: u32> {
    kzg: ParamsKZG<E>,
    /// The bases of every [`Residue`] built so far.
    residue_bases: ResidueBases<E::G1Affine>,
}

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
/// free.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Residue {
    /// The representation of the values of `f_i`.
    basis: PolynomialBasis,
    /// The modulus, a power of two.
    t: usize,
    /// The number of values of `f_i`.
    n: usize,
    /// The residue, smaller than `t`.
    i: usize,
}

/// The bases of every [`Residue`] built so far.
type ResidueBases<C> = Arc<RwLock<HashMap<Residue, Arc<[C]>>>>;

/// Costly: see [`ParamsFflonkKZG::from_kzg`].
impl<E, const LOG2_T_MAX: u32> From<ParamsKZG<E>> for ParamsFflonkKZG<E, LOG2_T_MAX>
where
    E: MultiMillerLoop + Debug,
    E::G1Affine: CurveAffine,
{
    fn from(kzg: ParamsKZG<E>) -> Self {
        Self::from_kzg(kzg)
    }
}

impl<E: Engine, const LOG2_T_MAX: u32> Borrow<ParamsKZG<E>> for ParamsFflonkKZG<E, LOG2_T_MAX> {
    fn borrow(&self) -> &ParamsKZG<E> {
        &self.kzg
    }
}

impl<E, const LOG2_T_MAX: u32> ParamsFflonkKZG<E, LOG2_T_MAX>
where
    E: MultiMillerLoop + Debug,
    E::G1Affine: CurveAffine,
{
    /// The pairs `(t, i)`, for every power of two `t ≤ T_MAX` and every
    /// `i < t`.
    fn residues() -> impl Iterator<Item = (usize, usize)> {
        (0..=LOG2_T_MAX)
            .map(|log2_t| 1 << log2_t)
            .flat_map(|t| (0..t).map(move |i| (t, i)))
    }

    /// Builds the parameters from the KZG ones. The residues modulo `t` need
    /// the Lagrange SRS of size `t·n`: for `t < T_MAX`, it is computed with a
    /// group FFT, which is costly.
    pub fn from_kzg(kzg: ParamsKZG<E>) -> Self {
        let n = kzg.g.len() >> LOG2_T_MAX;
        let smaller_lagrange = (0..LOG2_T_MAX)
            .into_par_iter()
            .map(|log2_t| g_to_lagrange(&kzg.g[..n << log2_t], n.ilog2() + log2_t))
            .collect();
        Self::with_lagrange(kzg, smaller_lagrange)
    }

    /// Builds the parameters from `srs`, the KZG SRSs of sizes `2^l·n` for
    /// `l ≤ LOG2_T_MAX`, by increasing size, from the same ceremony. Unlike
    /// [`Self::from_kzg`], it needs no FFT.
    ///
    /// # Panics
    ///
    /// If `srs` does not have `LOG2_T_MAX + 1` SRSs of these sizes, or if
    /// they do not share the same `g`.
    pub fn from_kzgs(mut srs: Vec<ParamsKZG<E>>) -> Self {
        assert_eq!(srs.len(), LOG2_T_MAX as usize + 1, "expected one SRS per t");
        let kzg = srs.pop().expect("at least one SRS");
        let smaller_lagrange = (srs.into_iter())
            .map(|smaller| {
                assert!(
                    kzg.g.starts_with(&smaller.g),
                    "the SRSs come from different ceremonies"
                );
                smaller.g_lagrange
            })
            .collect();
        Self::with_lagrange(kzg, smaller_lagrange)
    }

    /// Builds the parameters from the KZG ones and `smaller_lagrange`, the
    /// Lagrange SRS of size `2^l·n` for every `l < LOG2_T_MAX`.
    fn with_lagrange(kzg: ParamsKZG<E>, smaller_lagrange: Vec<Vec<E::G1Affine>>) -> Self {
        let n = kzg.g.len() >> LOG2_T_MAX;
        let lagrange = (smaller_lagrange.iter())
            .chain([&kzg.g_lagrange])
            .enumerate()
            .flat_map(|(log2_t, g_lagrange)| {
                let t = 1 << log2_t;
                assert_eq!(g_lagrange.len(), t * n, "no Lagrange SRS of size {t}·{n}");
                lagrange_residues(g_lagrange, t)
                    .into_iter()
                    .enumerate()
                    .map(move |(i, bases)| (t, i, bases))
            })
            .collect::<Vec<_>>();
        let residue_bases = (lagrange.into_par_iter())
            .flat_map_iter(|(t, i, lagrange)| {
                let delta = suffix_sum(&lagrange);
                let double_delta = suffix_sum(&delta);
                [
                    (PolynomialBasis::Lagrange, lagrange),
                    (PolynomialBasis::LagrangeDelta, delta),
                    (PolynomialBasis::LagrangeDoubleDelta, double_delta),
                ]
                .map(|(basis, bases)| (Residue { basis, t, n, i }, Arc::from(bases)))
            })
            .collect();
        Self {
            kzg,
            residue_bases: Arc::new(RwLock::new(residue_bases)),
        }
    }

    /// The verifier parameters, those of the [`ParamsKZG`].
    pub fn verifier_params(&self) -> ParamsVerifierKZG<E> {
        self.kzg.verifier_params()
    }

    /// The bases of the [`Residue`] `i` modulo `t`, for committing to
    /// `X^i f(X^t)` from the `n` values of `f` in the representation `B`.
    ///
    /// # Panics
    ///
    /// If `B` is the extended Lagrange basis, if `t·n` is larger than the SRS,
    /// or if `B` is Lagrange or one of its delta forms and `n` is not a power
    /// of two.
    fn residue_bases<B: PolynomialRepresentation>(
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
                    t * n <= self.kzg.g.len(),
                    "no residue bases of size {n} modulo {t}"
                );
                self.kzg.g[i..].iter().step_by(t).take(n).copied().collect()
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

    /// Writes the [`ParamsKZG`], as [`ParamsKZG::write`] does, then
    /// `LOG2_T_MAX` and the `LagrangeDelta` and `LagrangeDoubleDelta` bases of
    /// size `n`.
    pub fn write<W>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        E::G1Affine: SerdeObject,
        E::G2: ProcessedSerdeObject,
        W: io::Write,
    {
        self.kzg.write(writer, format)?;
        writer.write_all(&LOG2_T_MAX.to_le_bytes())?;
        let n = self.kzg.g.len() >> LOG2_T_MAX;
        for (t, i) in Self::residues() {
            let delta = self.residue_bases::<LagrangeDeltaCoeff>(t, n, i);
            write_points(&delta, writer, format)?;
            let double_delta = self.residue_bases::<LagrangeDoubleDeltaCoeff>(t, n, i);
            write_points(&double_delta, writer, format)?;
        }
        Ok(())
    }

    /// Reads parameters written by [`Self::write`]. The `Lagrange` bases are
    /// the adjacent differences of the `LagrangeDelta` ones.
    pub fn read<R>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>
    where
        E::G1Affine: SerdeObject,
        E::G2: ProcessedSerdeObject,
        R: io::Read,
    {
        Self::read_with_max_k(reader, format, None)
    }

    /// Like [`Self::read`], but fails if `k` exceeds `max_k`, before
    /// allocating anything of that size.
    pub fn read_with_max_k<R>(
        reader: &mut R,
        format: SerdeFormat,
        max_k: Option<u32>,
    ) -> io::Result<Self>
    where
        E::G1Affine: SerdeObject,
        E::G2: ProcessedSerdeObject,
        R: io::Read,
    {
        let kzg = ParamsKZG::<E>::read_with_max_k(reader, format, max_k)?;
        let mut log2_t_max = [0u8; 4];
        reader.read_exact(&mut log2_t_max)?;
        let log2_t_max = u32::from_le_bytes(log2_t_max);
        if log2_t_max != LOG2_T_MAX {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("parameters for T_MAX = 2^{log2_t_max}, expected 2^{LOG2_T_MAX}"),
            ));
        }
        let n = kzg.g.len() >> LOG2_T_MAX;
        let mut residue_bases = HashMap::new();
        for (t, i) in Self::residues() {
            let delta: Vec<E::G1Affine> = read_points(reader, format, n)?;
            let double_delta: Vec<E::G1Affine> = read_points(reader, format, n)?;
            let mut insert = |basis, bases: Vec<_>| {
                residue_bases.insert(Residue { basis, t, n, i }, Arc::from(bases));
            };
            insert(PolynomialBasis::Lagrange, adjacent_differences(&delta));
            insert(PolynomialBasis::LagrangeDelta, delta);
            insert(PolynomialBasis::LagrangeDoubleDelta, double_delta);
        }
        Ok(Self {
            kzg,
            residue_bases: Arc::new(RwLock::new(residue_bases)),
        })
    }
}

impl<E: KZGEngine, const LOG2_T_MAX: u32> InterleavedCommit<E::Fr, LOG2_T_MAX>
    for KZGCommitmentScheme<E>
{
    /// Building them is costly: see [`ParamsFflonkKZG`].
    type Parameters = ParamsFflonkKZG<E, LOG2_T_MAX>;

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

/// The `Lagrange` bases of the residues modulo `t` of size `n`, from the
/// Lagrange SRS `g_lagrange` of size `t·n`, of domain generator `ω`:
/// `B_i[j] = ω^(ij) \sum_r ω^(nri) g_lagrange[j + n r]`, a `t`-point DFT per
/// `j`.
fn lagrange_residues<C: CurveAffine>(g_lagrange: &[C], t: usize) -> Vec<Vec<C>> {
    let n = g_lagrange.len() / t;
    let log2_t = t.ilog2();
    let mut omega = C::ScalarExt::ROOT_OF_UNITY;
    for _ in g_lagrange.len().ilog2()..C::ScalarExt::S {
        omega = omega.square();
    }
    let omega_t = omega.pow_vartime([n as u64]);
    let twiddles: Vec<_> = (0..t / 2).map(|k| omega_t.pow_vartime([k as u64])).collect();

    // `residues[j·t + i] = B_i[j]`.
    let mut residues = vec![C::CurveExt::identity(); t * n];
    residues.par_chunks_mut(t).enumerate().for_each(|(j, y)| {
        // Radix-2 DIT, from the inputs in bit-reversed order.
        for (r, y) in y.iter_mut().enumerate() {
            let r = r.reverse_bits().checked_shr(usize::BITS - log2_t).unwrap_or(0);
            *y = g_lagrange[j + n * r].into();
        }
        let mut h = 1;
        while h < t {
            for block in y.chunks_mut(2 * h) {
                let (lo, hi) = block.split_at_mut(h);
                for (k, (a, b)) in lo.iter_mut().zip(hi).enumerate() {
                    if k > 0 {
                        *b *= twiddles[k * t / (2 * h)];
                    }
                    let a0 = *a;
                    *a += *b;
                    *b = a0 - *b;
                }
            }
            h *= 2;
        }
        let omega_j = omega.pow_vartime([j as u64]);
        let mut twist = omega_j;
        for y in y.iter_mut().skip(1) {
            *y *= twist;
            twist *= omega_j;
        }
    });

    (0..t)
        .into_par_iter()
        .map(|i| {
            let column: Vec<_> = residues.iter().skip(i).step_by(t).copied().collect();
            let mut bases = vec![C::identity(); n];
            C::CurveExt::batch_normalize(&column, &mut bases);
            bases
        })
        .collect()
}

/// The inverse of [`suffix_sum`]: `out[j] = input[j] - input[j + 1]`, and
/// `out[n - 1] = input[n - 1]`.
fn adjacent_differences<C: CurveAffine>(input: &[C]) -> Vec<C> {
    let differences: Vec<C::CurveExt> = (0..input.len())
        .into_par_iter()
        .map(|j| match input.get(j + 1) {
            Some(next) => input[j].to_curve() - next,
            None => input[j].into(),
        })
        .collect();
    let mut out = vec![C::identity(); input.len()];
    C::CurveExt::batch_normalize(&differences, &mut out);
    out
}

/// Commitment to `Σ_i X^i f_i(X^t)`, for `chunk` the polynomials `f_i` and
/// `t` the next power of two of their number.
fn commit_chunk<E, B, const LOG2_T_MAX: u32>(
    params: &ParamsFflonkKZG<E, LOG2_T_MAX>,
    chunk: &[&Polynomial<E::Fr, B>],
) -> E::G1
where
    E: MultiMillerLoop + Debug,
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
