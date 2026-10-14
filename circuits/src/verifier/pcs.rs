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

//! In-circuit abstraction layer for Polynomial Commitment Schemes.
//!
//! Mirrors [`midnight_proofs::poly::commitment`] for the in-circuit setting.

use std::fmt::Debug;

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme},
};

use crate::{
    field::AssignedNative,
    verifier::{AssignedAccumulator, SelfEmulation, transcript_gadget::TranscriptGadget},
};

// ---------------------------------------------------------------------------
// VerifierQuery  (mirrors proofs/src/poly/query.rs)
// ---------------------------------------------------------------------------

/// An in-circuit verifier query: a commitment evaluated at a point.
///
/// `PCS` is the scheme checking the query (`S::PCS` by default), so that a PCS
/// can query an inner one, as fflonk does with KZG.
#[derive(Clone, Debug)]
pub struct VerifierQuery<'a, S: SelfEmulation, PCS: InCircuitPCS<S> = <S as SelfEmulation>::PCS> {
    pub(crate) point: AssignedNative<S::F>,
    pub(crate) commitment: &'a PCS::AssignedCommitment,
    pub(crate) label: PolynomialLabel,
    pub(crate) eval: AssignedNative<S::F>,
}

impl<'a, S: SelfEmulation, PCS: InCircuitPCS<S>> VerifierQuery<'a, S, PCS> {
    pub fn new(
        point: &AssignedNative<S::F>,
        commitment: &'a PCS::AssignedCommitment,
        label: PolynomialLabel,
        eval: &AssignedNative<S::F>,
    ) -> Self {
        Self {
            point: point.clone(),
            commitment,
            label,
            eval: eval.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// Traits
// ---------------------------------------------------------------------------

/// In-circuit operations on an additively homomorphic commitment.
pub trait InCircuitHomomorphicCommitment<S: SelfEmulation>: Clone + Debug + Sized {
    /// Scales this commitment by an assigned scalar.
    fn mul(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        scalar: &AssignedNative<S::F>,
    ) -> Result<Self, Error>;

    /// Adds another commitment to this one.
    fn add(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        other: Self,
    ) -> Result<Self, Error>;
}

/// An off-circuit commitment whose curve points can be read with the labels
/// they carry.
///
/// Commitments in the in-circuit verifier are assumed to have this structure:
/// a commitment is a list of curve points, each carrying a label. The labels
/// are attached by the commitment scheme and need not be those of the
/// committed polynomials: a scheme may commit to several polynomials together
/// under a single label, such as a [`PolynomialLabel::Collection`] of theirs.
/// The points of a verifying-key commitment are its fixed bases, collected by
/// [`fixed_bases`](super::fixed_bases) under these labels.
pub trait CommitmentBases<C> {
    /// The (label, point) pairs of this commitment, in order.
    ///
    /// # Panics
    ///
    /// If the commitment is not made of labelled points only.
    fn bases(&self) -> Vec<(PolynomialLabel, C)>;
}

/// In-circuit abstraction over a Polynomial Commitment Scheme.
///
/// Analog of [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme`]
/// for the in-circuit verifier.
pub trait InCircuitPCS<S: SelfEmulation>: Sized + Clone + Debug {
    /// The off-circuit scheme whose proofs this gadget verifies. Fixes the
    /// verifying-key type the gadget accepts.
    type OffCircuitPCS: PolynomialCommitmentScheme<S::F, Commitment: CommitmentBases<S::C>>;

    /// The in-circuit type representing a committed polynomial.
    type AssignedCommitment: InCircuitHomomorphicCommitment<S>;

    /// Creates the fixed (VK-embedded) commitment to the group of `labels`.
    ///
    /// The labels are matched to the group's polynomials in the order given,
    /// as in [`Self::read_commitment`]. Its points carry the labels given by
    /// [`Self::fixed_base_labels`].
    ///
    /// # Panics
    ///
    /// Panics if a label is repeated.
    fn fixed_commitment(labels: &[PolynomialLabel]) -> Self::AssignedCommitment;

    /// The labels of the curve points making up [`Self::fixed_commitment`] for
    /// the group of `labels`, in order.
    ///
    /// Commitments are assumed to be made of labelled curve points, whose
    /// labels may differ from those of the committed polynomials (see
    /// [`CommitmentBases`]). These are the keys of
    /// [`fixed_bases`](super::fixed_bases) for this group.
    fn fixed_base_labels(labels: &[PolynomialLabel]) -> Vec<PolynomialLabel>;

    /// Assigns a commitment from an off-circuit curve point.
    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        value: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self::AssignedCommitment, Error>;

    /// Reads one commitment to `labels.len()` polynomials from the proof
    /// transcript, tagging each polynomial with its label.
    fn read_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error>;

    /// Absorbs a commitment into the proof transcript.
    fn common_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        commitment: &Self::AssignedCommitment,
    ) -> Result<(), Error>;

    /// Squeezes the point at which the protocol opens its committed
    /// polynomials; the default squeezes a plain challenge. Mirrors
    /// [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme::squeeze_evaluation_point`].
    fn squeeze_evaluation_point(
        layouter: &mut impl Layouter<S::F>,
        _scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
    ) -> Result<AssignedNative<S::F>, Error> {
        transcript.squeeze_challenge(layouter)
    }

    /// In-circuit multi-open verification; produces an accumulator.
    fn multi_prepare(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
        queries: &[VerifierQuery<'_, S, Self>],
    ) -> Result<AssignedAccumulator<S>, Error>;
}

/// The in-circuit commitment type of the PCS declared by `S`.
pub type AssignedCommitment<S> = <<S as SelfEmulation>::PCS as InCircuitPCS<S>>::AssignedCommitment;
