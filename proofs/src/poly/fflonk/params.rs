// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

//! The parameters of [`Fflonk`](super::Fflonk) over KZG, and the commitments to
//! interleaved polynomials made with them.

use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    fmt::Debug,
    io,
    sync::{Arc, RwLock},
};

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
/// The `LagrangeDelta` and `LagrangeDoubleDelta` bases of size `n`, those the
/// prover commits with, only depend on the SRS, `n` and `T_MAX`, but building
/// them takes `2·T_MAX - 1` group FFTs of size `n`: build them once, with
/// [`Self::from_kzg`], and store them on disk, with [`Self::write`].
/// Any other bases are built on first use and cached.
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

    /// Builds the parameters from the KZG ones. This is costly: see
    /// [`ParamsFflonkKZG`].
    pub fn from_kzg(kzg: ParamsKZG<E>) -> Self {
        let n = kzg.g.len() >> LOG2_T_MAX;
        let params = Self {
            kzg,
            residue_bases: Default::default(),
        };
        for (t, i) in Self::residues() {
            params.residue_bases::<LagrangeDoubleDeltaCoeff>(t, n, i);
        }
        params
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

    /// Reads parameters written by [`Self::write`].
    pub fn read<R>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>
    where
        E::G1Affine: SerdeObject,
        E::G2: ProcessedSerdeObject,
        R: io::Read,
    {
        let kzg = ParamsKZG::<E>::read(reader, format)?;
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
            for basis in [
                PolynomialBasis::LagrangeDelta,
                PolynomialBasis::LagrangeDoubleDelta,
            ] {
                let bases = read_points(reader, format, n)?;
                residue_bases.insert(Residue { basis, t, n, i }, bases.into());
            }
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

        // Build each missing residue basis once, before the chunks ask for it
        // concurrently.
        let residues: HashSet<_> = (chunks.iter())
            .flat_map(|chunk| {
                let (t, n) = (chunk.len().next_power_of_two(), chunk[0].len());
                (0..chunk.len()).map(move |i| (t, n, i))
            })
            .collect();
        residues.par_iter().for_each(|&(t, n, i)| {
            params.residue_bases::<B>(t, n, i);
        });

        KZGMultiCommitment(
            (chunks.par_iter().zip(labels.par_iter()))
                .map(|(chunk, label)| {
                    KZGCommitment::Simple(commit_chunk(params, chunk), label.clone())
                })
                .collect(),
        )
    }
}

/// Commitment to `Σ_i X^i f_i(X^t)`, for `chunk` the polynomials `f_i` and
/// `t` the next power of two of their number: one MSM of the values of every
/// `f_i` against the bases of its residue.
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
    let (scalars, points): (Vec<E::Fr>, Vec<E::G1Affine>) = (chunk.par_iter().enumerate())
        .map(|(i, poly)| {
            let bases = params.residue_bases::<B>(t, n, i);
            (poly.values.to_vec(), bases.to_vec())
        })
        .reduce(Default::default, |(mut scalars, mut points), (s, p)| {
            scalars.extend(s);
            points.extend(p);
            (scalars, points)
        });
    commit_msm(&scalars, &points)
}
