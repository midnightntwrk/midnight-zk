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
    poly::{commitment::Labelable, PolynomialLabel},
};

use crate::{
    field::AssignedNative,
    verifier::{transcript_gadget::TranscriptGadget, AssignedAccumulator, SelfEmulation},
};

// ---------------------------------------------------------------------------
// CommitmentReference  (mirrors proofs/src/poly/query.rs)
// ---------------------------------------------------------------------------

/// A pointer to an in-circuit commitment, with pointer-based equality.
///
/// Two references are equal iff they point to the same allocation, so
/// commitments are grouped by identity rather than by value.
pub(crate) struct CommitmentReference<'a, C>(pub(crate) &'a C);

impl<C> Clone for CommitmentReference<'_, C> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<C> Copy for CommitmentReference<'_, C> {}
impl<C: Debug> Debug for CommitmentReference<'_, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl<C> PartialEq for CommitmentReference<'_, C> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

// ---------------------------------------------------------------------------
// VerifierQuery  (mirrors proofs/src/poly/query.rs)
// ---------------------------------------------------------------------------

/// An in-circuit verifier query: a commitment evaluated at a point.
#[derive(Clone, Debug)]
pub struct VerifierQuery<'a, S: SelfEmulation, PCS: InCircuitPCS<S>> {
    pub(crate) point: AssignedNative<S::F>,
    pub(crate) commitment_ref: CommitmentReference<'a, PCS::AssignedCommitment>,
    pub(crate) eval: AssignedNative<S::F>,
}

impl<'a, S: SelfEmulation, PCS: InCircuitPCS<S>> VerifierQuery<'a, S, PCS> {
    pub fn new(
        point: &AssignedNative<S::F>,
        commitment: &'a PCS::AssignedCommitment,
        eval: &AssignedNative<S::F>,
    ) -> Self {
        Self {
            point: point.clone(),
            commitment_ref: CommitmentReference(commitment),
            eval: eval.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// Traits
// ---------------------------------------------------------------------------

/// In-circuit operations on an additively homomorphic commitment.
pub trait InCircuitHomomorphicCommitment<S: SelfEmulation>:
    Clone + Debug + Labelable + Sized
{
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

/// In-circuit abstraction over a Polynomial Commitment Scheme.
///
/// Analog of [`midnight_proofs::poly::commitment::PolynomialCommitmentScheme`]
/// for the in-circuit verifier.
pub trait InCircuitPCS<S: SelfEmulation>: Sized + Clone + Debug {
    /// The in-circuit type representing a committed polynomial.
    type AssignedCommitment: InCircuitHomomorphicCommitment<S>;

    /// Creates a fixed (VK-embedded) commitment identified by `label`.
    fn fixed_commitment(label: PolynomialLabel) -> Self::AssignedCommitment;

    /// Assigns a commitment from an off-circuit curve point.
    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        value: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self::AssignedCommitment, Error>;

    /// Reads one commitment from the proof transcript.
    fn read_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
    ) -> Result<Self::AssignedCommitment, Error>;

    /// Absorbs a commitment into the proof transcript.
    fn common_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        commitment: &Self::AssignedCommitment,
    ) -> Result<(), Error>;

    /// In-circuit multi-open verification; produces an accumulator.
    fn multi_prepare(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
        queries: &[VerifierQuery<'_, S, Self>],
    ) -> Result<AssignedAccumulator<S>, Error>;
}
