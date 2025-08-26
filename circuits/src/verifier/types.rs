// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

//! Module that contains type and generic bounds.
//! Its purpose is to minimize complexity in the rest of the verifier chip.

use std::fmt::Debug;

use ff::{PrimeField, WithSmallOrderMulGroup};
use group::{prime::PrimeCurveAffine, Curve};
use halo2curves::{
    pairing::{Engine, MultiMillerLoop},
    serde::SerdeObject,
    CurveExt,
};
use midnight_proofs::{
    circuit::Layouter,
    plonk::Error,
    transcript::{Hashable, TranscriptHash},
};
use pasta_curves::arithmetic::CurveAffine;

#[cfg(not(feature = "truncated-challenges"))]
use crate::instructions::FieldInstructions;
#[cfg(feature = "truncated-challenges")]
use crate::instructions::NativeInstructions;
use crate::{
    ecc::{
        curves::{CircuitCurve, WeierstrassCurve},
        foreign::ForeignEccChip,
    },
    field::{decomposition::chip::P2RDecompositionChip, AssignedNative, NativeChip, NativeGadget},
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{
        ecc::EccInstructions, public_input::CommittedInstanceInstructions, AssignmentInstructions,
        HashInstructions, PublicInputInstructions, SpongeInstructions,
    },
    types::{AssignedForeignPoint, InnerValue, Instantiable},
};

/// A trait for parametrizing the VerifierGadget.
pub trait SelfEmulation: Clone + Debug {
    /// The native field.
    type F: PrimeField + WithSmallOrderMulGroup<3> + Hashable<Self::Hash>;

    /// The underlying curve of the self-emulation proof.
    type C: CurveExt<ScalarExt = Self::F, AffineExt = Self::G1Affine>
        + WeierstrassCurve<CryptographicGroup = Self::C, Base = <Self::C as CurveExt>::Base>
        + Hashable<Self::Hash>;

    /// An assigned point of curve C.
    type AssignedPoint: InnerValue<Element = Self::C> + Instantiable<Self::F> + PartialEq + Eq;

    /// A type for the Fiat-Shamir hashing.
    type Hash: TranscriptHash;

    #[cfg(feature = "truncated-challenges")]
    /// A chip implementing native field arithmetic operations.
    type ScalarChip: NativeInstructions<Self::F>;
    #[cfg(not(feature = "truncated-challenges"))]
    /// A chip implementing native field arithmetic operations.
    type ScalarChip: FieldInstructions<Self::F, AssignedNative<Self::F>>;

    /// A chip implementing assignment operations for [Self::AssignedPoint].
    type CurveChip: Clone
        + AssignmentInstructions<Self::F, Self::AssignedPoint>
        + PublicInputInstructions<Self::F, Self::AssignedPoint>;

    /// A chip implementing sponge operations over the native field.
    type SpongeChip: Clone
        + SpongeInstructions<Self::F, AssignedNative<Self::F>, AssignedNative<Self::F>>
        + HashInstructions<Self::F, AssignedNative<Self::F>, AssignedNative<Self::F>>;

    /// C in affine form (first source group).
    type G1Affine: CurveAffine<ScalarExt = Self::F, CurveExt = Self::C, Base = <Self::C as CircuitCurve>::Base>
        + Into<Self::C>
        + From<Self::C>
        + SerdeObject;

    /// The second source group.
    type G2Affine: PrimeCurveAffine + From<<Self::Engine as Engine>::G2> + SerdeObject;

    /// Wrapper type for the pairing engine.
    type Engine: Engine
        + MultiMillerLoop<
            Fr = Self::F,
            G1 = Self::C,
            G1Affine = <Self::C as Curve>::AffineRepr,
            G2Affine = Self::G2Affine,
        >;

    /// Variable-base multi-scalar multiplication, the `usize` next to each
    /// scalar is an (inclusive) upper-bound on their bit-length.
    ///
    /// # Panics
    ///
    /// If `scalars.len() != bases.len()`.
    fn msm(
        layouter: &mut impl Layouter<Self::F>,
        curve_chip: &Self::CurveChip,
        scalars: &[(AssignedNative<Self::F>, usize)],
        bases: &[Self::AssignedPoint],
    ) -> Result<Self::AssignedPoint, Error>;

    /// Constrains the given scalar as a committed public input.
    fn constrain_scalar_as_committed_public_input(
        layouter: &mut impl Layouter<Self::F>,
        scalar_chip: &Self::ScalarChip,
        assigned_scalar: &AssignedNative<Self::F>,
    ) -> Result<(), Error>;
}

// Implementations

/// Implementation of the SelfEmulation trait for blstrs.
#[derive(Clone, Debug)]
pub struct BlstrsEmulation {}

impl SelfEmulation for BlstrsEmulation {
    type F = midnight_curves::Fq;
    type C = midnight_curves::G1Projective;
    type AssignedPoint = AssignedForeignPoint<Self::F, Self::C, Self::C>;
    type Hash = PoseidonState<Self::F>;

    type ScalarChip = NativeGadget<Self::F, P2RDecompositionChip<Self::F>, NativeChip<Self::F>>;
    type CurveChip = ForeignEccChip<Self::F, Self::C, Self::C, Self::ScalarChip, Self::ScalarChip>;
    type SpongeChip = PoseidonChip<Self::F>;

    type G1Affine = midnight_curves::G1Affine;
    type G2Affine = midnight_curves::G2Affine;
    type Engine = midnight_curves::Bls12;

    fn msm(
        layouter: &mut impl Layouter<Self::F>,
        curve_chip: &Self::CurveChip,
        scalars: &[(AssignedNative<Self::F>, usize)],
        bases: &[Self::AssignedPoint],
    ) -> Result<Self::AssignedPoint, Error> {
        curve_chip.msm_by_bounded_scalars(layouter, scalars, bases)
    }

    fn constrain_scalar_as_committed_public_input(
        layouter: &mut impl Layouter<Self::F>,
        scalar_chip: &Self::ScalarChip,
        assigned_scalar: &AssignedNative<Self::F>,
    ) -> Result<(), Error> {
        scalar_chip.constrain_as_committed_public_input(layouter, assigned_scalar)
    }
}
