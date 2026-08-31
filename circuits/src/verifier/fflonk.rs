// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! In-circuit fflonk commitment scheme.
//!
//! In-circuit analog of `proofs/src/pcs/fflonk`. Holds the in-circuit
//! commitment type, the wire format of a bundled commitment, and the bundle
//! pre-expansion that turns queries on a `t > 1` bundle into synthetic queries
//! on its combined polynomial `g`. The scheme-independent remainder of the
//! multi-open argument lives in `super::multi_open`.
//!
//! # Bundling ceiling
//!
//! The gadget imposes the layout instead of parsing it: the number of bundles
//! and the labels each one packs come from `partition` over the labels the
//! protocol expects, at the compile-time ceiling [`FFLONK_T_MAX_LOG`]. That
//! ceiling has to be a circuit constant, since the whole shape of the gadget
//! depends on it, so the `t_max_log` the prover writes to the transcript is
//! constrained to it rather than read. A proof produced against an SRS with
//! too little monomial room degrades to a smaller exponent off-circuit
//! (`effective_t_max_log`) and is rejected here.

use std::{collections::HashMap, marker::PhantomData};

use group::Group;
use midnight_curves::pairing::MultiMillerLoop;
use midnight_proofs::{
    circuit::{Layouter, Value},
    pcs::fflonk::{
        FFLONK_T_MAX_LOG, FflonkCommitment, FflonkScheme, bundle_t, missing_openings, partition,
        primitive_root_of_unity, t_th_root,
    },
    plonk::Error::{self, Synthesis},
    poly::PolynomialLabel,
};

use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssertionInstructions, AssignmentInstructions},
    types::InnerValue,
    verifier::{
        AssignedAccumulator, SelfEmulation, SingletonCommitment,
        msm::{AssignedMsm, AssignedPoint},
        multi_open::{QueryTriple, multi_prepare_core},
        pcs::{InCircuitHomomorphicCommitment, InCircuitPCS, VerifierQuery},
        transcript_gadget::TranscriptGadget,
        utils::{AssignedBoundedScalar, mul_add, mul_bounded_scalars},
    },
};

/// The bundling ceiling every fflonk gadget is built at.
const T_MAX: usize = 1 << FFLONK_T_MAX_LOG;

/// The terms of a lazy linear combination: bases, scalars and labels, flat and
/// parallel.
type LinearParts<S> = (
    Vec<AssignedPoint<S>>,
    Vec<AssignedBoundedScalar<<S as SelfEmulation>::F>>,
    Vec<PolynomialLabel>,
);

// ----------------------------------------
// See proofs/src/pcs/fflonk/commitment.rs
// ----------------------------------------

/// In-circuit analog of [`FflonkCommitment`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssignedFflonkCommitment<S: SelfEmulation> {
    /// One `(point, labels)` pair per bundle, where `point` commits to the
    /// `labels.len()` polynomials combined into it.
    Regular(Vec<(AssignedPoint<S>, Vec<PolynomialLabel>)>),
    /// A lazy linear combination `∑ scalars[i] * points[i]` with per-term
    /// labels, accumulated during verification for MSM batching. Produced by
    /// `Add`/`Mul` on singleton bundles, as its off-circuit counterpart.
    Linear(
        Vec<AssignedPoint<S>>,
        Vec<AssignedBoundedScalar<S::F>>,
        Vec<PolynomialLabel>,
    ),
}

impl<S: SelfEmulation> InnerValue for AssignedFflonkCommitment<S> {
    type Element = FflonkCommitment<S::Engine>;

    fn value(&self) -> Value<Self::Element> {
        match self {
            Self::Regular(pairs) => {
                let points: Vec<Value<S::C>> =
                    pairs.iter().map(|(p, _)| p.value().map(|p| *p.get_point())).collect();
                let labels: Vec<_> = pairs.iter().map(|(_, l)| l.clone()).collect();
                Value::from_iter(points).map(|ps: Vec<S::C>| {
                    FflonkCommitment::Regular(ps.into_iter().zip(labels).collect())
                })
            }
            Self::Linear(points, scalars, labels) => {
                let points: Vec<Value<S::C>> =
                    points.iter().map(|p| p.value().map(|p| *p.get_point())).collect();
                let scalars: Vec<Value<S::F>> =
                    scalars.iter().map(|s| s.scalar.value().copied()).collect();
                let labels = labels.clone();
                Value::from_iter(points)
                    .zip(Value::from_iter(scalars))
                    .map(|(ps, ss)| FflonkCommitment::Linear(ps, ss, labels))
            }
        }
    }
}

impl<S: SelfEmulation> AssignedFflonkCommitment<S> {
    /// A commitment to a single polynomial at a variable-base assigned point.
    pub fn singleton(point: S::AssignedPoint, label: PolynomialLabel) -> Self {
        Self::Regular(vec![(AssignedPoint::Variable(point), vec![label])])
    }

    /// A commitment to a single polynomial at a globally-known constant point.
    ///
    /// No circuit cell is allocated for the point; it is identified by its
    /// label and will be looked up from a fixed-bases map when the accumulator
    /// is resolved.
    pub fn fixed(label: PolynomialLabel) -> Self {
        Self::Regular(vec![(AssignedPoint::Fixed, vec![label])])
    }

    /// In-circuit commitment to the zero polynomial (the identity point),
    /// tagged with `label`. Used e.g. for empty committed-instance columns.
    pub fn commitment_to_zero(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        label: PolynomialLabel,
    ) -> Result<Self, Error>
    where
        S::CurveChip: AssignmentInstructions<S::F, S::AssignedPoint>,
    {
        let point = curve_chip.assign_fixed(layouter, S::C::identity())?;
        Ok(Self::singleton(point, label))
    }

    /// The bundle of a `Regular` commitment whose label set contains `label`.
    fn find_bundle(
        &self,
        label: &PolynomialLabel,
    ) -> Result<&(AssignedPoint<S>, Vec<PolynomialLabel>), Error> {
        match self {
            Self::Regular(pairs) => pairs
                .iter()
                .find(|(_, labels)| labels.contains(label))
                .ok_or_else(|| Synthesis(format!("no bundle of this commitment holds {label}"))),
            Self::Linear(_, _, labels) => Err(Synthesis(format!(
                "a linear commitment has no bundles: {labels:?}"
            ))),
        }
    }

    /// Decomposes into `(points, scalars, labels)` for `mul`/`add`. A singleton
    /// bundle becomes a one-term combination with scalar `1`; a `Linear`
    /// returns its parts unchanged.
    fn into_linear_parts(self, one: &AssignedBoundedScalar<S::F>) -> Result<LinearParts<S>, Error> {
        match self {
            Self::Regular(pairs) => match pairs.as_slice() {
                [(point, labels)] if labels.len() == 1 => {
                    Ok((vec![point.clone()], vec![one.clone()], labels.clone()))
                }
                _ => Err(Synthesis(
                    "linearization requires a commitment to a single polynomial".into(),
                )),
            },
            Self::Linear(points, scalars, labels) => Ok((points, scalars, labels)),
        }
    }
}

impl<S: SelfEmulation> InCircuitHomomorphicCommitment<S> for AssignedFflonkCommitment<S> {
    fn mul(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        scalar: &AssignedNative<S::F>,
    ) -> Result<Self, Error> {
        let scalar = AssignedBoundedScalar::new(scalar, None);
        match self {
            Self::Linear(points, scalars, labels) => Ok(Self::Linear(
                points,
                scalars
                    .iter()
                    .map(|s| mul_bounded_scalars(layouter, scalar_chip, s, &scalar))
                    .collect::<Result<Vec<_>, _>>()?,
                labels,
            )),
            committed => {
                let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;
                let (points, _, labels) = committed.into_linear_parts(&one)?;
                Ok(Self::Linear(points, vec![scalar], labels))
            }
        }
    }

    fn add(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        other: Self,
    ) -> Result<Self, Error> {
        let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;
        let (mut points, mut scalars, mut labels) = self.into_linear_parts(&one)?;
        let (other_points, other_scalars, other_labels) = other.into_linear_parts(&one)?;
        points.extend(other_points);
        scalars.extend(other_scalars);
        labels.extend(other_labels);
        Ok(Self::Linear(points, scalars, labels))
    }
}

// ---------------------------------------------
// See proofs/src/pcs/fflonk/bundle_expansion.rs
// ---------------------------------------------

/// A bundle's claimed slot evaluations, keyed by `(slot, logical point)`.
type SlotEvals<S> = Vec<(
    (usize, AssignedNative<<S as SelfEmulation>::F>),
    AssignedNative<<S as SelfEmulation>::F>,
)>;

/// Per-bundle verifier-side accumulator, the in-circuit analog of
/// `bundle_expansion::BundleAcc`.
///
/// `pairs` and `evals` are association lists rather than maps: their point keys
/// are `AssignedNative` cells, and a lookup by cell is exactly the identity
/// this gadget needs (see [`t_th_roots_cells`]).
struct BundleAcc<S: SelfEmulation> {
    point: AssignedPoint<S>,
    /// Real labels of the bundle's polynomials, in canonical order. Shorter
    /// than `t` for a padded trailing bundle.
    canonical_labels: Vec<PolynomialLabel>,
    /// Logical bundle size. Slots `[canonical_labels.len(), t)` are pad slots
    /// whose evals are zero and never travel on the transcript.
    t: usize,
    pairs: Vec<(usize, AssignedNative<S::F>)>,
    evals: SlotEvals<S>,
}

impl<S: SelfEmulation> BundleAcc<S> {
    fn eval_at(
        &self,
        slot: usize,
        point: &AssignedNative<S::F>,
    ) -> Result<&AssignedNative<S::F>, Error> {
        self.evals
            .iter()
            .find(|((s, p), _)| *s == slot && p == point)
            .map(|(_, eval)| eval)
            .ok_or_else(|| {
                Synthesis("fflonk: over-opening should have filled every real slot".into())
            })
    }
}

/// The `t`-th roots computed so far, keyed by the cell of the logical point and
/// the bundle size. See [`t_th_roots_cells`].
type RootsCache<S> = Vec<(
    (AssignedNative<<S as SelfEmulation>::F>, usize),
    Vec<AssignedNative<<S as SelfEmulation>::F>>,
)>;

/// The `t` t-th roots of `x`, i.e. `[z, z ω_t, ..., z ω_t^{t-1}]` for a witness
/// `z` constrained by `z^t = x`.
///
/// Cheaper in-circuit than the `log2(t)` square roots the off-circuit verifier
/// chains: one witness, `log2(t)` squarings and one equality. Which of the `t`
/// roots the witness lands on does not matter, since the coset it spans is the
/// same either way.
///
/// `cache` is keyed by the *cell* of `x`, not its value, and returns the very
/// same root cells for a repeated `(x, t)`. That is load-bearing:
/// `construct_intermediate_sets` identifies points by cell, so two bundles
/// opened at a shared logical point must share their whole root set, or they
/// land in distinct point sets in-circuit and a single one off-circuit. Worse,
/// the pairwise `assert_not_equal` of `evaluate_interpolated_polynomial` would
/// then compare two cells holding the same value and make the circuit
/// unsatisfiable.
fn t_th_roots_cells<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    cache: &mut RootsCache<S>,
    x: &AssignedNative<S::F>,
    t: usize,
) -> Result<Vec<AssignedNative<S::F>>, Error> {
    if let Some((_, roots)) = cache.iter().find(|((p, s), _)| p == x && *s == t) {
        return Ok(roots.clone());
    }

    let z = scalar_chip.assign(layouter, x.value().map(|x| t_th_root(*x, t)))?;
    let z_pow_t = scalar_chip.pow(layouter, &z, t as u64)?;
    scalar_chip.assert_equal(layouter, &z_pow_t, x)?;

    // `z * ω_t^i` rather than a chain of multiplications by `ω_t`: same cost,
    // and it avoids the dead cell `z * ω_t^t` a chain would end on.
    let omega_t = primitive_root_of_unity::<S::F>(t);
    let mut roots = Vec::with_capacity(t);
    roots.push(z.clone());
    let mut omega_pow = omega_t;
    for _ in 1..t {
        roots.push(scalar_chip.mul_by_constant(layouter, &z, omega_pow)?);
        omega_pow *= omega_t;
    }

    cache.push(((x.clone(), t), roots.clone()));
    Ok(roots)
}

/// Paper's `S̄(root)`: `Σ_i root^i · claimed[i]`, by Horner. Equals `g(root)`
/// when `root` is a `t`-th root of `x` and `claimed` holds the slot
/// evaluations at `x` (Lemma 5.1). Trailing pad slots are zero and simply
/// omitted from `claimed`.
fn eval_claims_as_poly<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    claimed: &[&AssignedNative<S::F>],
    root: &AssignedNative<S::F>,
) -> Result<AssignedNative<S::F>, Error> {
    let (last, rest) = claimed.split_last().expect("a bundle has at least one real slot");
    rest.iter().rev().try_fold((*last).clone(), |acc, c| {
        mul_add(layouter, scalar_chip, &acc, root, c)
    })
}

/// Synthetic `(synth_label, root, g(root))` triples for one `t > 1` bundle.
///
/// Unlike the off-circuit mirror, the logical points are *not* sorted: their
/// values are witnesses, so no order over them is available at synthesis time.
/// It does not have to be: the triples of one bundle all carry the same label,
/// so a different order only permutes the point indices
/// `construct_intermediate_sets` hands out, and every consumer of a point set
/// (the interpolation and the vanishing product) is symmetric in it.
fn synth_triples_for_bundle<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    synth_label: &PolynomialLabel,
    acc: &BundleAcc<S>,
    roots_cache: &mut RootsCache<S>,
) -> Result<Vec<QueryTriple<S>>, Error> {
    let real_count = acc.canonical_labels.len();

    let mut union_logicals: Vec<AssignedNative<S::F>> = vec![];
    for (_, p) in acc.pairs.iter() {
        if !union_logicals.contains(p) {
            union_logicals.push(p.clone());
        }
    }

    let mut triples = Vec::with_capacity(union_logicals.len() * acc.t);
    for logical in union_logicals.iter() {
        let slot_evals = (0..real_count)
            .map(|slot| acc.eval_at(slot, logical))
            .collect::<Result<Vec<_>, Error>>()?;

        for root in t_th_roots_cells::<S>(layouter, scalar_chip, roots_cache, logical, acc.t)? {
            let eval = eval_claims_as_poly::<S>(layouter, scalar_chip, &slot_evals, &root)?;
            triples.push((synth_label.clone(), root, eval));
        }
    }
    Ok(triples)
}

// -----------------------------------
// See proofs/src/pcs/fflonk/mod.rs
// -----------------------------------

/// fflonk instantiation of [`InCircuitPCS`].
#[derive(Clone, Copy, Debug)]
pub struct InCircuitFflonk<S: SelfEmulation>(PhantomData<S>);

impl<E: MultiMillerLoop> SingletonCommitment<E::G1> for FflonkCommitment<E> {
    fn point(&self) -> E::G1 {
        *self.as_point()
    }
}

impl<S: SelfEmulation> InCircuitPCS<S> for InCircuitFflonk<S> {
    type OffCircuit = FflonkScheme<S::Engine>;
    type AssignedCommitment = AssignedFflonkCommitment<S>;

    fn fixed_commitment(label: PolynomialLabel) -> Self::AssignedCommitment {
        AssignedFflonkCommitment::fixed(label)
    }

    fn read_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error> {
        // The wire carries `u8 nb_bundles`, then per bundle a `u8` polynomial
        // count and its point. Only the points are read: the grouping is
        // re-derived from the labels, and the counts are skipped.
        let bundles = partition(T_MAX, labels);
        transcript.skip_bytes(1)?;

        let mut pairs = Vec::with_capacity(bundles.len());
        for indices in bundles.iter() {
            transcript.skip_bytes(1)?;
            let point = transcript.read_point(layouter)?;
            pairs.push((
                AssignedPoint::Variable(point),
                indices.iter().map(|&i| labels[i].clone()).collect(),
            ));
        }

        let commitment = AssignedFflonkCommitment::Regular(pairs);
        Self::common_commitment(transcript, layouter, &commitment)?;

        Ok(commitment)
    }

    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        value: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self::AssignedCommitment, Error> {
        let point = curve_chip.assign(layouter, value)?;
        Ok(AssignedFflonkCommitment::singleton(point, label))
    }

    fn common_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        commitment: &Self::AssignedCommitment,
    ) -> Result<(), Error> {
        match commitment {
            AssignedFflonkCommitment::Regular(pairs) => {
                pairs.iter().try_for_each(|(p, labels)| match p {
                    AssignedPoint::Variable(p) => transcript.absorb_point(layouter, p),
                    AssignedPoint::Fixed => Err(Synthesis(format!(
                        "Fixed commitments cannot be added to the transcript: {labels:?}"
                    ))),
                })
            }
            AssignedFflonkCommitment::Linear(_, _, labels) => Err(Synthesis(format!(
                "Linear commitments cannot be added to the transcript: {labels:?}"
            ))),
        }
    }

    /// fflonk opens each bundle at the `t`-th roots of the evaluation point, so
    /// that point must be a `T_MAX`-th power. Squeezes `s` and returns
    /// `s^T_MAX`, mirroring
    /// [`FflonkScheme::squeeze_evaluation_point`](midnight_proofs::pcs::PolynomialCommitmentScheme::squeeze_evaluation_point).
    fn squeeze_evaluation_point(
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
    ) -> Result<AssignedNative<S::F>, Error> {
        let s = transcript.squeeze_challenge(layouter)?;
        if T_MAX == 1 {
            return Ok(s);
        }
        scalar_chip.pow(layouter, &s, T_MAX as u64)
    }

    fn multi_prepare(
        layouter: &mut impl Layouter<S::F>,
        _curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
        queries: &[VerifierQuery<'_, S, Self>],
    ) -> Result<AssignedAccumulator<S>, Error> {
        let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;

        // The prover's bundling ceiling. Off-circuit it selects the partition;
        // here the partition is a circuit constant, so the claim is bound to it
        // instead. See the module doc.
        let claimed_t_max_log = transcript.read_scalar(layouter)?;
        scalar_chip.assert_equal_to_fixed(
            layouter,
            &claimed_t_max_log,
            S::F::from(FFLONK_T_MAX_LOG as u64),
        )?;

        // === Bundle pre-expansion (fflonk-specific) ===
        //
        // Singletons and `Linear` commitments pass through with their own
        // (label, point, eval) triple. Queries on a `t > 1` bundle are gathered
        // per logical point and expanded, below, into synthetic triples on the
        // bundle's `g`.
        let mut singleton_triples: Vec<QueryTriple<S>> = Vec::new();
        let mut label_to_com: HashMap<PolynomialLabel, AssignedMsm<S>> = HashMap::new();
        let mut bundles: Vec<(PolynomialLabel, BundleAcc<S>)> = Vec::new();

        for q in queries.iter() {
            match q.commitment {
                AssignedFflonkCommitment::Linear(points, scalars, labels) => {
                    singleton_triples.push((q.label.clone(), q.point.clone(), q.eval.clone()));
                    label_to_com.insert(q.label.clone(), AssignedMsm::new(scalars, points, labels));
                }
                regular => {
                    let (point, labels) = regular.find_bundle(&q.label)?;
                    if labels.len() == 1 {
                        singleton_triples.push((q.label.clone(), q.point.clone(), q.eval.clone()));
                        label_to_com.insert(
                            q.label.clone(),
                            AssignedMsm::from_term(one.clone(), point.clone(), q.label.clone()),
                        );
                    } else {
                        let synth = FflonkCommitment::<S::Engine>::synthetic_bundle_label(labels);
                        let idx = match bundles.iter().position(|(l, _)| *l == synth) {
                            Some(idx) => idx,
                            None => {
                                bundles.push((
                                    synth,
                                    BundleAcc {
                                        point: point.clone(),
                                        canonical_labels: labels.clone(),
                                        t: bundle_t(labels.len(), T_MAX),
                                        pairs: Vec::new(),
                                        evals: Vec::new(),
                                    },
                                ));
                                bundles.len() - 1
                            }
                        };
                        let acc = &mut bundles[idx].1;
                        let slot = acc
                            .canonical_labels
                            .iter()
                            .position(|l| *l == q.label)
                            .expect("the bundle was found by this very label");
                        acc.pairs.push((slot, q.point.clone()));
                        acc.evals.push(((slot, q.point.clone()), q.eval.clone()));
                    }
                }
            }
        }

        // Sorted by synthetic label, as off-circuit, so the over-opening reads
        // below land in the prover's write order.
        bundles.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));

        // Over-opening reads: the verifier reconstructs `g` at a root from the
        // evaluations of *all* slots, so every slot is opened at every logical
        // point of the bundle's union.
        for (_synth, acc) in bundles.iter_mut() {
            let missing = missing_openings(&acc.pairs);
            for (pair_idx, point) in missing {
                let slot = acc.pairs[pair_idx].0;
                let eval = transcript.read_scalar(layouter)?;
                acc.evals.push(((slot, point), eval));
            }
        }

        // Add dummy queries to reduce the number of distinct multi-open point
        // sets. As off-circuit, this applies to the singleton slice only: the
        // bundled queries are about to become synthetic ones on `g`, whose
        // point sets are the `t`-th roots.
        #[cfg(feature = "fewer-point-sets")]
        {
            let pairs: Vec<_> =
                singleton_triples.iter().map(|(l, p, _)| (l.clone(), p.clone())).collect();
            for (idx, dummy_point) in midnight_proofs::pcs::compute_dummy_queries(&pairs) {
                let label = singleton_triples[idx].0.clone();
                let eval = transcript.read_scalar(layouter)?;
                // `label_to_com` already maps `label`, so no new entry is needed.
                singleton_triples.push((label, dummy_point, eval));
            }
        }

        let mut triples = singleton_triples;
        let mut roots_cache = RootsCache::<S>::new();
        for (synth_label, acc) in bundles.iter() {
            triples.extend(synth_triples_for_bundle::<S>(
                layouter,
                scalar_chip,
                synth_label,
                acc,
                &mut roots_cache,
            )?);
            label_to_com.insert(
                synth_label.clone(),
                AssignedMsm::from_term(one.clone(), acc.point.clone(), synth_label.clone()),
            );
        }

        multi_prepare_core(
            layouter,
            #[cfg(feature = "truncated-challenges")]
            _curve_chip,
            scalar_chip,
            transcript,
            &triples,
            &label_to_com,
            |layouter, transcript, label| {
                // `f` and `π` commit to a single polynomial, so their wire form
                // is a one-bundle, one-polynomial commitment.
                match Self::read_commitment(transcript, layouter, &[label])? {
                    AssignedFflonkCommitment::Regular(pairs) => match pairs.as_slice() {
                        [(point, _)] => Ok(point.clone()),
                        _ => Err(Synthesis(
                            "the multi-open argument reads single-bundle commitments".into(),
                        )),
                    },
                    AssignedFflonkCommitment::Linear(_, _, labels) => Err(Synthesis(format!(
                        "the multi-open argument reads plain commitments, got a linear one: \
                         {labels:?}"
                    ))),
                }
            },
        )
    }
}
