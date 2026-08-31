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

//! In-circuit KZG commitment scheme.
//!
//! Holds the in-circuit commitment type and the KZG-specific parts of the
//! multi-open argument: the wire format of a commitment and the peeling of a
//! multi-commitment down to the polynomial a query targets. The
//! scheme-independent remainder lives in `super::multi_open`.

use std::{collections::HashMap, marker::PhantomData};

use group::Group;
use midnight_curves::pairing::MultiMillerLoop;
use midnight_proofs::{
    circuit::{Layouter, Value},
    pcs::kzg::{
        KZGCommitmentScheme,
        commitment::{KZGCommitment, KZGMultiCommitment},
    },
    plonk::Error::{self, Synthesis},
    poly::PolynomialLabel,
};

use crate::{
    field::AssignedNative,
    instructions::AssignmentInstructions,
    types::InnerValue,
    verifier::{
        AssignedAccumulator, SelfEmulation, SingletonCommitment,
        msm::{AssignedMsm, AssignedPoint},
        multi_open::multi_prepare_core,
        pcs::{InCircuitHomomorphicCommitment, InCircuitPCS, VerifierQuery},
        transcript_gadget::TranscriptGadget,
        utils::{AssignedBoundedScalar, mul_bounded_scalars},
    },
};

// -------------------------------------
// See proofs/src/pcs/kzg/commitment.rs
// -------------------------------------

/// In-circuit analog of
/// [`KZGCommitment`].
///
/// Carries a polynomial commitment (or a lazy linear combination of them)
/// together with its `PolynomialLabel`(s).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssignedKZGCommitment<S: SelfEmulation> {
    /// A single committed point with its label.
    Simple(AssignedPoint<S>, PolynomialLabel),
    /// A lazy linear combination `∑ scalars[i] * points[i]` with per-term
    /// labels, accumulated during verification for MSM batching.
    Linear(
        Vec<AssignedPoint<S>>,
        Vec<AssignedBoundedScalar<S::F>>,
        Vec<PolynomialLabel>,
    ),
}

impl<S: SelfEmulation> InnerValue for AssignedKZGCommitment<S> {
    type Element = KZGCommitment<S::Engine>;

    fn value(&self) -> Value<Self::Element> {
        match self.clone() {
            Self::Simple(p, label) => {
                p.value().map(|p| KZGCommitment::Simple(*p.get_point(), label))
            }
            Self::Linear(points, scalars, labels) => {
                let points: Vec<Value<S::C>> =
                    points.iter().map(|p| p.value().map(|p| *p.get_point())).collect();
                let scalars: Vec<Value<S::F>> =
                    scalars.iter().map(|s| s.scalar.value().copied()).collect();
                Value::from_iter(points)
                    .zip(Value::from_iter(scalars))
                    .map(|(ps, ss)| KZGCommitment::Linear(ps, ss, labels))
            }
        }
    }
}

impl<S: SelfEmulation> AssignedKZGCommitment<S> {
    /// Creates a `Simple` commitment from a variable-base assigned point and
    /// label.
    pub fn simple(point: S::AssignedPoint, label: PolynomialLabel) -> Self {
        AssignedKZGCommitment::Simple(AssignedPoint::Variable(point), label)
    }

    /// Creates a `Simple` commitment for a globally-known constant point.
    ///
    /// No circuit cell is allocated for the point; it is identified by its
    /// label and will be looked up from a fixed-bases map when the
    /// accumulator is resolved.
    pub fn fixed(label: PolynomialLabel) -> Self {
        AssignedKZGCommitment::Simple(AssignedPoint::Fixed, label)
    }

    /// Assigns a curve point in the circuit and wraps it in a labeled `Simple`
    /// commitment.
    pub fn assign(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        point: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self, Error> {
        curve_chip.assign(layouter, point).map(|p| Self::simple(p, label))
    }

    /// Views this commitment as an [`AssignedMsm`] for use in the multiopen
    /// accumulation. `one` is an assigned constant 1.
    ///
    /// `Simple(p, l)` becomes a one-term MSM `[(1, p, l)]`.
    /// `Linear(points, scalars, labels)` becomes the corresponding multi-term
    /// MSM.
    pub fn to_msm(&self, one: &AssignedBoundedScalar<S::F>) -> AssignedMsm<S> {
        match self {
            Self::Simple(p, label) => AssignedMsm::from_term(one.clone(), p.clone(), label.clone()),
            Self::Linear(points, scalars, labels) => AssignedMsm::new(scalars, points, labels),
        }
    }
}

impl<S: SelfEmulation> AssignedKZGCommitment<S> {
    /// Scales this commitment by a scalar.
    ///
    /// `Simple(p, l)` becomes `Linear([p], [scalar], [l])`.
    /// For `Linear`, all existing scalars are multiplied by `scalar`.
    fn mul(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        scalar: &AssignedNative<S::F>,
    ) -> Result<Self, Error> {
        let scalar = AssignedBoundedScalar::new(scalar, None);
        match self {
            Self::Simple(p, label) => Ok(Self::Linear(vec![p], vec![scalar], vec![label])),
            Self::Linear(points, scalars, labels) => Ok(Self::Linear(
                points,
                scalars
                    .iter()
                    .map(|s| mul_bounded_scalars(layouter, scalar_chip, s, &scalar))
                    .collect::<Result<Vec<_>, _>>()?,
                labels,
            )),
        }
    }

    /// Adds two commitments, merging them into a `Linear` combination.
    fn add(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        other: Self,
    ) -> Result<Self, Error> {
        let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;
        let (mut points, mut scalars, mut labels) = match self {
            Self::Simple(p, label) => (vec![p], vec![one.clone()], vec![label]),
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        };
        let (other_points, other_scalars, other_labels) = match other {
            Self::Simple(p, label) => (vec![p], vec![one.clone()], vec![label]),
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        };
        points.extend(other_points);
        scalars.extend(other_scalars);
        labels.extend(other_labels);
        Ok(Self::Linear(points, scalars, labels))
    }
}

/// In-circuit analog of
/// [`KZGMultiCommitment`]:
/// a commitment to one or more polynomials.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignedKZGMultiCommitment<S: SelfEmulation>(pub Vec<AssignedKZGCommitment<S>>);

impl<S: SelfEmulation> AssignedKZGMultiCommitment<S> {
    fn assert_single(&self) {
        assert_eq!(
            self.0.len(),
            1,
            "operation on AssignedKZGMultiCommitment requires exactly one polynomial"
        );
    }

    /// Returns the single inner [`AssignedKZGCommitment`], panicking if this
    /// commitment does not hold exactly one polynomial.
    pub(crate) fn into_single(self) -> AssignedKZGCommitment<S> {
        self.assert_single();
        self.0.into_iter().next().unwrap()
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
        Ok(Self(vec![AssignedKZGCommitment::simple(point, label)]))
    }
}

impl<S: SelfEmulation> InnerValue for AssignedKZGMultiCommitment<S> {
    type Element = midnight_proofs::pcs::kzg::commitment::KZGMultiCommitment<S::Engine>;

    fn value(&self) -> Value<Self::Element> {
        Value::from_iter(self.0.iter().map(|c| c.value()))
            .map(midnight_proofs::pcs::kzg::commitment::KZGMultiCommitment)
    }
}

impl<S: SelfEmulation> InCircuitHomomorphicCommitment<S> for AssignedKZGMultiCommitment<S> {
    fn mul(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        scalar: &AssignedNative<S::F>,
    ) -> Result<Self, Error> {
        self.assert_single();
        let inner = self.0.into_iter().next().unwrap().mul(layouter, scalar_chip, scalar)?;
        Ok(Self(vec![inner]))
    }

    fn add(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        other: Self,
    ) -> Result<Self, Error> {
        self.assert_single();
        other.assert_single();
        let inner = self.0.into_iter().next().unwrap().add(
            layouter,
            scalar_chip,
            other.0.into_iter().next().unwrap(),
        )?;
        Ok(Self(vec![inner]))
    }
}

/// KZG instantiation of [`InCircuitPCS`].
#[derive(Clone, Copy, Debug)]
pub struct InCircuitKZG<S: SelfEmulation>(PhantomData<S>);

impl<E: MultiMillerLoop> SingletonCommitment<E::G1> for KZGMultiCommitment<E> {
    fn point(&self) -> E::G1 {
        *self.0[0].as_point()
    }
}

impl<S: SelfEmulation> InCircuitPCS<S> for InCircuitKZG<S> {
    type OffCircuit = KZGCommitmentScheme<S::Engine>;
    type AssignedCommitment = AssignedKZGMultiCommitment<S>;

    fn fixed_commitment(label: PolynomialLabel) -> Self::AssignedCommitment {
        AssignedKZGMultiCommitment(vec![AssignedKZGCommitment::fixed(label)])
    }

    fn read_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error> {
        // KZG commits each polynomial independently, so a commitment to
        // `labels.len()` polynomials is that many points on the wire.
        let points = labels
            .iter()
            .map(|_| transcript.read_point(layouter))
            .collect::<Result<Vec<_>, Error>>()?;

        let commitment = AssignedKZGMultiCommitment(
            points
                .into_iter()
                .zip(labels)
                .map(|(point, label)| AssignedKZGCommitment::simple(point, label.clone()))
                .collect(),
        );
        Self::common_commitment(transcript, layouter, &commitment)?;

        Ok(commitment)
    }

    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        value: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self::AssignedCommitment, Error> {
        Ok(AssignedKZGMultiCommitment(vec![
            AssignedKZGCommitment::assign(layouter, curve_chip, value, label)?,
        ]))
    }

    fn common_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        commitment: &AssignedKZGMultiCommitment<S>,
    ) -> Result<(), Error> {
        for inner in commitment.0.iter() {
            match inner {
                AssignedKZGCommitment::Simple(AssignedPoint::Variable(p), _label) => {
                    transcript.absorb_point(layouter, p)
                }
                AssignedKZGCommitment::Simple(AssignedPoint::Fixed, label) => Err(Synthesis(
                    format!("Fixed commitments cannot be added to the transcript: {label}"),
                )),
                AssignedKZGCommitment::Linear(_, _, labels) => Err(Synthesis(format!(
                    "Linear commitments cannot be added to the transcript: {labels:?}"
                ))),
            }?
        }
        Ok(())
    }

    fn multi_prepare(
        layouter: &mut impl Layouter<S::F>,
        _curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
        queries: &[VerifierQuery<'_, S, Self>],
    ) -> Result<AssignedAccumulator<S>, Error> {
        let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;

        // Add dummy queries to reduce the number of distinct multi-open point sets.
        #[cfg(feature = "fewer-point-sets")]
        let queries = &{
            let pairs: Vec<_> =
                queries.iter().map(|q| (q.label.clone(), q.point.clone())).collect();
            let dummy_openings = midnight_proofs::pcs::compute_dummy_queries(&pairs);
            let mut queries = queries.to_vec();
            for (idx, dummy_point) in dummy_openings {
                queries.push(VerifierQuery {
                    point: dummy_point,
                    commitment: queries[idx].commitment,
                    label: queries[idx].label.clone(),
                    eval: transcript.read_scalar(layouter)?,
                });
            }
            queries
        };

        // Peel each query's multi-commitment down to the single inner commitment it
        // targets, keyed by the query label. A length-1 commitment (the common case,
        // including the `Linear` linearization commitment) peels to its sole inner;
        // a batched commitment holds several `Simple`s, so we pick the one whose own
        // label matches the query.
        let label_to_com: HashMap<PolynomialLabel, AssignedMsm<S>> = queries
            .iter()
            .map(|q| {
                let inners = &q.commitment.0;
                let inner = if inners.len() == 1 {
                    &inners[0]
                } else {
                    inners
                        .iter()
                        .find(|c| matches!(c, AssignedKZGCommitment::Simple(_, label) if *label == q.label))
                        .expect("batched commitment has no polynomial matching the query label")
                };
                (q.label.clone(), inner.to_msm(&one))
            })
            .collect();

        let triples = queries
            .iter()
            .map(|query| (query.label.clone(), query.point.clone(), query.eval.clone()))
            .collect::<Vec<_>>();

        multi_prepare_core(
            layouter,
            #[cfg(feature = "truncated-challenges")]
            _curve_chip,
            scalar_chip,
            transcript,
            &triples,
            &label_to_com,
            |layouter, transcript, label| match Self::read_commitment(
                transcript,
                layouter,
                &[label],
            )?
            .into_single()
            {
                AssignedKZGCommitment::Simple(p, _) => Ok(p),
                AssignedKZGCommitment::Linear(_, _, labels) => Err(Synthesis(format!(
                    "the multi-open argument reads plain commitments, got a linear one: {labels:?}"
                ))),
            },
        )
    }
}
