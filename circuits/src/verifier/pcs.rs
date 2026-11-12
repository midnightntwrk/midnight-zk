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
    transcript::Hashable,
};

use crate::{
    field::AssignedNative,
    types::{InnerValue, Instantiable},
    verifier::{
        AssignedAccumulator, ScalarChip, SelfEmulation, transcript_gadget::InCircuitTranscript,
    },
};

// ---------------------------------------------------------------------------
// VerifierQuery  (mirrors proofs/src/poly/query.rs)
// ---------------------------------------------------------------------------

/// An in-circuit verifier query: a commitment evaluated at a point.
///
/// `PCS` is the scheme checking the query, so that a PCS can query an inner
/// one, as fflonk does with KZG.
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

/// In-circuit verification of the proofs of an off-circuit Polynomial
/// Commitment Scheme, implemented by the off-circuit scheme itself.
///
/// Analog of [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme`]
/// for the in-circuit verifier.
pub trait InCircuitPCS<S: SelfEmulation>:
    PolynomialCommitmentScheme<S::F, Commitment: CommitmentBases<S::C>> + Sized + Clone + Debug
{
    /// The chip this scheme operates on its commitments with.
    type CommitmentChip: Clone;

    /// The in-circuit type representing a committed polynomial, whose
    /// off-circuit value is a commitment of this scheme.
    type AssignedCommitment: Clone
        + Debug
        + Instantiable<S::F>
        + InnerValue<Element = <Self as PolynomialCommitmentScheme<S::F>>::Commitment>;

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

    /// Assigns the commitment to the group of `labels` from its off-circuit
    /// value. As in [`Self::read_commitment`], its points are not checked to be
    /// in the prime-order subgroup.
    ///
    /// # Panics
    ///
    /// Panics if a label is repeated or if `value` does not commit to
    /// `|labels|` polynomials.
    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        commitment_chip: &Self::CommitmentChip,
        value: Value<<Self::AssignedCommitment as InnerValue>::Element>,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error>;

    /// The in-circuit counterpart of [`Instantiable::as_public_input`] for
    /// commitments.
    ///
    /// # Panics
    ///
    /// Panics if `commitment` has no assigned points, e.g. if it was created
    /// with [`Self::fixed_commitment`].
    fn commitment_as_public_input(
        layouter: &mut impl Layouter<S::F>,
        commitment_chip: &Self::CommitmentChip,
        commitment: &Self::AssignedCommitment,
    ) -> Result<Vec<AssignedNative<S::F>>, Error>;

    /// Reads one commitment to `labels.len()` polynomials from the proof
    /// transcript, tagging each polynomial with its label.
    fn read_commitment<T: InCircuitTranscript<S::F>>(
        transcript: &mut T,
        layouter: &mut impl Layouter<S::F>,
        commitment_chip: &Self::CommitmentChip,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error>
    where
        Self::Commitment: Hashable<T::Hash>;

    /// Absorbs a commitment into the proof transcript.
    fn common_commitment<T: InCircuitTranscript<S::F>>(
        transcript: &mut T,
        layouter: &mut impl Layouter<S::F>,
        commitment_chip: &Self::CommitmentChip,
        commitment: &Self::AssignedCommitment,
    ) -> Result<(), Error>;

    /// Squeezes the point at which the protocol opens its committed
    /// polynomials; the default squeezes a plain challenge. Mirrors
    /// [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme::squeeze_evaluation_point`].
    fn squeeze_evaluation_point<T: InCircuitTranscript<S::F>>(
        layouter: &mut impl Layouter<S::F>,
        _scalar_chip: &ScalarChip<S::F>,
        transcript: &mut T,
    ) -> Result<AssignedNative<S::F>, Error> {
        transcript.squeeze_challenge(layouter)
    }

    /// The labels `commitment` tags its polynomials with. Mirrors
    /// [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme::commitment_labels`].
    fn commitment_labels(commitment: &Self::AssignedCommitment) -> Vec<PolynomialLabel>;

    /// In-circuit multi-open verification; produces an accumulator.
    fn multi_prepare<T: InCircuitTranscript<S::F>>(
        layouter: &mut impl Layouter<S::F>,
        commitment_chip: &Self::CommitmentChip,
        scalar_chip: &ScalarChip<S::F>,
        queries: &[VerifierQuery<'_, S, Self>],
        transcript: &mut T,
    ) -> Result<AssignedAccumulator<S>, Error>
    where
        S::F: Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>;
}

/// The in-circuit commitment type of `PCS`.
pub type AssignedCommitment<S, PCS> = <PCS as InCircuitPCS<S>>::AssignedCommitment;
