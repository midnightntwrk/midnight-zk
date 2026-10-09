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
#[derive(Clone, Debug)]
pub struct VerifierQuery<'a, S: SelfEmulation, PCS: InCircuitPCS<S>> {
    pub(crate) point: AssignedNative<S::F>,
    pub(crate) commitment: &'a PCS::AssignedCommitment,
    pub(crate) label: PolynomialLabel,
    pub(crate) eval: AssignedNative<S::F>,
    /// `Some((x, t))` if `point` is one of the `t`-th roots of `x`, and the
    /// commitment is queried at all of them.
    pub(crate) root_of: Option<(AssignedNative<S::F>, usize)>,
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
            root_of: None,
        }
    }

    /// Marks `self.point` as one of the `t`-th roots of `x`.
    ///
    /// The caller guarantees that the commitment is queried at all `t` roots of
    /// `x`, and that `point^t = x` is constrained.
    pub(crate) fn with_root_of(mut self, x: &AssignedNative<S::F>, t: usize) -> Self {
        self.root_of = Some((x.clone(), t));
        self
    }
}

// ---------------------------------------------------------------------------
// Traits
// ---------------------------------------------------------------------------

/// An off-circuit PCS whose proofs some in-circuit PCS verifies.
pub trait InCircuitCounterpart<S: SelfEmulation>: PolynomialCommitmentScheme<S::F> {
    /// The in-circuit PCS verifying the proofs of this one.
    type InCircuit: InCircuitPCS<S, OffCircuit = Self>;
}

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
/// they carry, as the fixed bases of a verifying key are.
pub trait CommitmentBases<C> {
    /// The (label, point) pairs of this commitment, one per inner commitment.
    ///
    /// # Panics
    ///
    /// If an inner commitment is not a single labelled point.
    fn bases(&self) -> Vec<(PolynomialLabel, C)>;
}

/// In-circuit abstraction over a Polynomial Commitment Scheme.
///
/// Analog of [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme`]
/// for the in-circuit verifier.
pub trait InCircuitPCS<S: SelfEmulation>: Sized + Clone + Debug {
    /// The off-circuit scheme whose proofs this gadget verifies. Fixes the
    /// verifying-key type the gadget accepts.
    type OffCircuit: PolynomialCommitmentScheme<S::F>;

    /// The in-circuit type representing a committed polynomial.
    type AssignedCommitment: InCircuitHomomorphicCommitment<S>;

    /// Creates the fixed (VK-embedded) commitment to the group of `labels`.
    ///
    /// The labels are matched to the group's polynomials in the order given,
    /// as in [`Self::read_commitment`].
    ///
    /// # Panics
    ///
    /// Panics if a label is repeated.
    fn fixed_commitment(labels: &[PolynomialLabel]) -> Self::AssignedCommitment;

    /// Assigns a commitment from an off-circuit curve point.
    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        value: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self::AssignedCommitment, Error>;

    /// The commitment to the zero polynomial under each of `labels`, as
    /// [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme::commitment_to_zero`].
    /// Used e.g. for empty committed-instance columns.
    ///
    /// # Panics
    ///
    /// Panics if a label is repeated.
    fn commitment_to_zero(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        labels: &[PolynomialLabel],
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

    /// The labels `commitment` tags its polynomials with. Mirrors
    /// [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme::commitment_labels`].
    fn commitment_labels(commitment: &Self::AssignedCommitment) -> Vec<PolynomialLabel>;

    /// Squeezes the point at which the protocol opens its committed
    /// polynomials. The default squeezes a plain challenge; fflonk needs a
    /// `t`-th power. Mirrors
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
