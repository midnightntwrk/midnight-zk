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

//! Elliptic curve (in twisted Edwards form) operations over foreign fields.
//! This module supports curves of the form `a*x^2 + y^2 = 1 + d*x^2*y^2`, where
//! `a` is square and `d` is non-square.
//!
//! We require that the emulated elliptic curve do not have low-order points.
//! In particular, the curve (or the relevant subgroup) must have a large prime
//! order.

use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use super::common::msm_preprocess;
use ff::{Field, PrimeField};
use group::Group;
use midnight_curves::ff_ext::Legendre;
#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::{Column, Instance};
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{ConstraintSystem, Error},
};

#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::{FromScratch, Sampleable},
    rand::RngCore,
};

use crate::{
    ecc::{
        curves::EdwardsCurve,
        foreign::gates::coord::{self, CoordConfig},
    },
    field::{
        foreign::{
            field_chip::{FieldChip, FieldChipConfig},
            params::FieldEmulationParams,
        },
        AssignedNative,
    },
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
        DecompositionInstructions, EccInstructions, EqualityInstructions, NativeInstructions,
        PublicInputInstructions, ScalarFieldInstructions, ZeroInstructions,
    },
    types::{AssignedBit, AssignedField, InnerConstants, InnerValue, Instantiable},
    CircuitField,
};

/// Foreign Edwards ECC configuration.
#[derive(Clone, Debug)]
pub struct ForeignEdwardsEccConfig<C>
where
    C: EdwardsCurve,
{
    base_field_config: FieldChipConfig,
    coord_config: CoordConfig<C>,
    _marker: PhantomData<C>,
}

/// ECC chip to perform foreign Edwards EC operations.
#[derive(Clone, Debug)]
pub struct ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    config: ForeignEdwardsEccConfig<C>,
    native_gadget: N,
    base_field_chip: FieldChip<F, C::Base, B, N>,
    scalar_field_chip: S,
}

impl<F, C, B, S, N> ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    C::Base: Legendre,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    /// Configures the foreign Edwards ECC chip.
    pub fn configure(
        _meta: &mut ConstraintSystem<F>,
        base_field_config: &FieldChipConfig,
        nb_parallel_range_checks: usize,
        max_bit_len: u32,
    ) -> ForeignEdwardsEccConfig<C> {
        assert!(C::A.legendre() == 1);
        assert!(C::D.legendre() == -1);
        let coord_config = CoordConfig::<C>::configure::<F, B>(
            _meta,
            base_field_config,
            nb_parallel_range_checks,
            max_bit_len,
        );

        ForeignEdwardsEccConfig {
            base_field_config: base_field_config.clone(),
            coord_config,
            _marker: PhantomData,
        }
    }
}

impl<F, C, B, S, N> ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    /// Creates new foreign Edwards ECC chip from its building blocks.
    pub fn new(
        config: &ForeignEdwardsEccConfig<C>,
        native_gadget: &N,
        scalar_field_chip: &S,
    ) -> Self {
        let base_field_chip = FieldChip::new(&config.base_field_config, native_gadget);
        Self {
            config: config.clone(),
            native_gadget: native_gadget.clone(),
            base_field_chip,
            scalar_field_chip: scalar_field_chip.clone(),
        }
    }

    /// The emulated base field chip of this foreign Edwards ECC chip.
    pub fn base_field_chip(&self) -> &FieldChip<F, C::Base, B, N> {
        &self.base_field_chip
    }

    /// A chip with instructions for the scalar field of this ECC chip.
    pub fn scalar_field_chip(&self) -> &S {
        &self.scalar_field_chip
    }

    /// Asserts that the given point lies in the subgroup (and thus also on the
    /// curve).
    fn assert_in_subgroup(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<(), Error> {
        // Let h be the cofactor of the subgroup.
        //
        // To prove that a point P lies in the subgroup,
        // we exhibit a curve point Q such that h * Q = P.
        //
        // In other words, we prove that P lies in the image
        // of the multiplication-by-h map.
        //
        // Above check needs to be asserted (in-circuit) with the
        // following constraints:
        //  1. Q satisfies the curve equation.
        //  2. h * Q is equal to P.
        let cofactor = C::ScalarField::from_u128(C::COFACTOR);
        let q = self.assign_point_unchecked(
            layouter,
            p.value().map(|p| {
                p * cofactor
                    .invert()
                    .expect("cofactor must be nonzero and coprime to subgroup order")
            }),
        )?;

        self.assert_on_curve(layouter, &q.x, &q.y)?;

        let cofactor_times_q = self.mul_by_constant(layouter, cofactor, &q)?;
        self.assert_equal(layouter, p, &cofactor_times_q)
    }
}

/// Type for foreign Edwards EC points.
#[derive(Clone, Debug)]
#[must_use]
pub struct AssignedForeignEdwardsPoint<F, C, B>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    point: Value<C::CryptographicGroup>,
    x: AssignedField<F, C::Base, B>,
    y: AssignedField<F, C::Base, B>,
}

impl<F, C, B> PartialEq for AssignedForeignEdwardsPoint<F, C, B>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl<F, C, B> Eq for AssignedForeignEdwardsPoint<F, C, B>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
}

impl<F, C, B> Hash for AssignedForeignEdwardsPoint<F, C, B>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.x.hash(state);
        self.y.hash(state);
    }
}

impl<F, C, B> Instantiable<F> for AssignedForeignEdwardsPoint<F, C, B>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn as_public_input(p: &C::CryptographicGroup) -> Vec<F> {
        let (x, y) = (*p).into().coordinates().unwrap_or((C::Base::ZERO, C::Base::ZERO));
        [
            AssignedField::<F, C::Base, B>::as_public_input(&x).as_slice(),
            AssignedField::<F, C::Base, B>::as_public_input(&y).as_slice(),
        ]
        .concat()
    }
}

impl<F, C, B> InnerValue for AssignedForeignEdwardsPoint<F, C, B>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    type Element = C::CryptographicGroup;

    fn value(&self) -> Value<Self::Element> {
        self.point
    }
}

impl<F, C, B> InnerConstants for AssignedForeignEdwardsPoint<F, C, B>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn inner_zero() -> C::CryptographicGroup {
        C::CryptographicGroup::identity()
    }

    fn inner_one() -> Self::Element {
        C::CryptographicGroup::generator()
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F, C, B> Sampleable for AssignedForeignEdwardsPoint<F, C, B>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn sample_inner(rng: impl RngCore) -> C::CryptographicGroup {
        C::CryptographicGroup::random(rng)
    }
}

impl<F, C, B, S, N> Chip<F> for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    type Config = ForeignEdwardsEccConfig<C>;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F, C, B, S, N> ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    /// Converts a subgroup point to [AssignedForeignEdwardsPoint].
    /// The point is _not_ asserted (with constraints) to be on the curve.
    fn assign_point_unchecked(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let (val_x, val_y) = value
            .map(|v| v.into().coordinates().expect("assign_unchecked: valid point"))
            .unzip();
        let x = self.base_field_chip().assign(layouter, val_x)?;
        let y = self.base_field_chip().assign(layouter, val_y)?;
        let p = AssignedForeignEdwardsPoint::<F, C, B> { point: value, x, y };

        Ok(p)
    }

    /// Asserts the curve equation `a*x^2 + y^2 = 1 + d*x^2*y^2` of an emulated
    /// twisted Edwards curve, given the x and y coordinates in form of
    /// [AssignedField].
    fn assert_on_curve(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, C::Base, B>,
        y: &AssignedField<F, C::Base, B>,
    ) -> Result<(), Error> {
        let base_chip = self.base_field_chip();

        // Compute x^2, y^2 and a*x^2 + y^2 - 1 - d*x^2*y^2 in-circuit
        let x_x = base_chip.mul(layouter, x, x, None)?;
        let y_y = base_chip.mul(layouter, y, y, None)?;
        let id = base_chip.add_and_mul(
            layouter,
            (C::A, &x_x),
            (C::Base::ONE, &y_y),
            (C::Base::ZERO, &x_x), // using x_x as dummy value here
            -C::Base::ONE,
            -C::D,
        )?;

        // Assert a*x^2 + y^2 - 1 - d*x^2*y^2 = 0
        base_chip.assert_zero(layouter, &id)
    }
}

impl<F, C, B, S, N> AssignmentInstructions<F, AssignedForeignEdwardsPoint<F, C, B>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let p = self.assign_point_unchecked(layouter, value)?;

        self.assert_in_subgroup(layouter, &p)?;

        Ok(p)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let (x, y) = constant.into().coordinates().expect("assign_fixed: valid point");
        let x = self.base_field_chip().assign_fixed(layouter, x)?;
        let y = self.base_field_chip().assign_fixed(layouter, y)?;

        Ok(AssignedForeignEdwardsPoint::<F, C, B> {
            point: Value::known(constant),
            x,
            y,
        })
    }
}

impl<F, C, B, S, N> PublicInputInstructions<F, AssignedForeignEdwardsPoint<F, C, B>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F> + PublicInputInstructions<F, AssignedBit<F>>,
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok([
            self.base_field_chip.as_public_input(layouter, &p.x)?.as_slice(),
            self.base_field_chip.as_public_input(layouter, &p.y)?.as_slice(),
        ]
        .concat())
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<(), Error> {
        self.as_public_input(layouter, assigned)?
            .iter()
            .try_for_each(|c| self.native_gadget.constrain_as_public_input(layouter, c))
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let point = self.assign(layouter, value)?;
        self.constrain_as_public_input(layouter, &point)?;
        Ok(point)
    }
}

/// Inherit assignment instructions for [AssignedField], from the
/// `scalar_field_chip`.
impl<F, C, B, S, SP, N> AssignmentInstructions<F, AssignedField<F, C::ScalarField, SP>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F, Scalar = AssignedField<F, C::ScalarField, SP>>,
    SP: FieldEmulationParams<F, C::ScalarField>,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<<S::Scalar as InnerValue>::Element>,
    ) -> Result<S::Scalar, Error> {
        self.scalar_field_chip().assign(layouter, value)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: <S::Scalar as InnerValue>::Element,
    ) -> Result<S::Scalar, Error> {
        self.scalar_field_chip().assign_fixed(layouter, constant)
    }
}

impl<F, C, B, S, N> AssertionInstructions<F, AssignedForeignEdwardsPoint<F, C, B>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        q: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<(), Error> {
        self.base_field_chip().assert_equal(layouter, &p.x, &q.x)?;
        self.base_field_chip().assert_equal(layouter, &p.y, &q.y)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        q: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<(), Error> {
        let p_eq_q = self.is_equal(layouter, p, q)?;
        self.native_gadget.assert_equal_to_fixed(layouter, &p_eq_q, false)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        constant: C::CryptographicGroup,
    ) -> Result<(), Error> {
        let coordinates = constant.into().coordinates().expect("valid point");
        self.base_field_chip().assert_equal_to_fixed(layouter, &p.x, coordinates.0)?;
        self.base_field_chip().assert_equal_to_fixed(layouter, &p.y, coordinates.1)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        constant: C::CryptographicGroup,
    ) -> Result<(), Error> {
        let p_eq_constant = self.is_equal_to_fixed(layouter, p, constant)?;
        self.native_gadget.assert_equal_to_fixed(layouter, &p_eq_constant, false)
    }
}

impl<F, C, B, S, N> EqualityInstructions<F, AssignedForeignEdwardsPoint<F, C, B>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        q: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedBit<F>, Error> {
        let eq_x = self.base_field_chip().is_equal(layouter, &p.x, &q.x)?;
        let eq_y = self.base_field_chip().is_equal(layouter, &p.y, &q.y)?;
        self.native_gadget.and(layouter, &[eq_x, eq_y])
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        constant: <AssignedForeignEdwardsPoint<F, C, B> as InnerValue>::Element,
    ) -> Result<AssignedBit<F>, Error> {
        let coordinates = constant.into().coordinates().expect("Valid point");
        let eq_x = self.base_field_chip().is_equal_to_fixed(layouter, &p.x, coordinates.0)?;
        let eq_y = self.base_field_chip().is_equal_to_fixed(layouter, &p.y, coordinates.1)?;
        self.native_gadget.and(layouter, &[eq_x, eq_y])
    }

    fn is_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedForeignEdwardsPoint<F, C, B>,
        y: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedBit<F>, Error> {
        let b = self.is_equal(layouter, x, y)?;
        self.native_gadget.not(layouter, &b)
    }

    fn is_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedForeignEdwardsPoint<F, C, B>,
        constant: <AssignedForeignEdwardsPoint<F, C, B> as InnerValue>::Element,
    ) -> Result<AssignedBit<F>, Error> {
        let b = self.is_equal_to_fixed(layouter, x, constant)?;
        self.native_gadget.not(layouter, &b)
    }
}

impl<F, C, B, S, N> ZeroInstructions<F, AssignedForeignEdwardsPoint<F, C, B>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    fn is_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedBit<F>, Error> {
        self.is_equal_to_fixed(layouter, p, C::CryptographicGroup::identity())
    }
}

impl<F, C, B, S, N> ControlFlowInstructions<F, AssignedForeignEdwardsPoint<F, C, B>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    /// Returns `p` if `cond = 1` and `q` otherwise. In essence, this enforces
    /// `cond * p + (1 - cond) * q = 0` over the emulated twisted Edwards curve.
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        q: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let x = self.base_field_chip().select(layouter, cond, &p.x, &q.x)?;
        let y = self.base_field_chip().select(layouter, cond, &p.y, &q.y)?;

        // point = p if cond is unknown or 1, q if cond is known and 0
        let a = cond.value().error_if_known_and(|&v| !v);
        let point = if a.is_ok() { p.point } else { q.point };

        Ok(AssignedForeignEdwardsPoint::<F, C, B> { point, x, y })
    }
}

impl<F, C, B, S, N> EccInstructions<F, C> for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    type Point = AssignedForeignEdwardsPoint<F, C, B>;
    type Coordinate = AssignedField<F, C::Base, B>;
    type Scalar = S::Scalar;

    fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
        q: &Self::Point,
    ) -> Result<Self::Point, Error> {
        // Complete addition law on twisted edwards curve:
        // (see https://eprint.iacr.org/2008/013.pdf)
        //
        // P + Q = R
        // <=>
        // (Px, Py) + (Qx, Qy) = (Rx, Ry)
        // <=>
        // Rx = (Px * Qy +     Py * Qx) / (1 + d * Px * Py * Qx * Qy)
        // Ry = (Py * Qy - a * Px * Qx) / (1 - d * Px * Py * Qx * Qy)
        // <=> (denominators are non-zero)
        // Rx * (1 + d * Px * Py * Qx * Qy) = (Px * Qy +     Py * Qx)
        // Ry * (1 - d * Px * Py * Qx * Qy) = (Py * Qy - a * Px * Qx)

        let base_chip = self.base_field_chip();

        let r_value = p.value().zip(q.value()).map(|(p, q)| p + q);
        let r = self.assign_point_unchecked(layouter, r_value)?;

        let px_qy = base_chip.mul(layouter, &p.x, &q.y, None)?;
        let py_qx = base_chip.mul(layouter, &p.y, &q.x, None)?;
        let py_qy = base_chip.mul(layouter, &p.y, &q.y, None)?;
        let px_qx = base_chip.mul(layouter, &p.x, &q.x, None)?;
        let neg_a_px_qx = base_chip.mul_by_constant(layouter, &px_qx, -C::A)?;
        let d_px_py_qx_qy = base_chip.mul(layouter, &px_qx, &py_qy, Some(C::D))?;
        let neg_d_px_py_qx_qy = base_chip.neg(layouter, &d_px_py_qx_qy)?;

        // Constraint for Rx coordinate
        // Rx * (1 + d * Px * Py * Qx * Qy) = (Px * Qy + Py * Qx)
        coord::assert_coord(
            layouter,
            &r.x,
            &px_qy,
            &py_qx,
            &d_px_py_qx_qy,
            base_chip,
            &self.config.coord_config,
        )?;

        // Constraint for Ry coordinate
        // Ry * (1 - d * Px * Py * Qx * Qy) = (Py * Qy - a * Px * Qx)
        coord::assert_coord(
            layouter,
            &r.y,
            &py_qy,
            &neg_a_px_qx,
            &neg_d_px_py_qx_qy,
            base_chip,
            &self.config.coord_config,
        )?;

        Ok(AssignedForeignEdwardsPoint {
            point: r_value,
            x: r.x,
            y: r.y,
        })
    }

    fn double(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        self.add(layouter, p, p)
    }

    fn negate(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
    ) -> Result<Self::Point, Error> {
        // The negation of `P = (x, y)` on a twisted Edwards curve is `-P = (-x, y)`
        let neg_x = self.base_field_chip().neg(layouter, &p.x)?;
        let neg_x = self.base_field_chip().normalize(layouter, &neg_x)?;
        Ok(AssignedForeignEdwardsPoint::<F, C, B> {
            point: -p.point,
            x: neg_x,
            y: p.y.clone(),
        })
    }

    fn msm(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[Self::Scalar],
        bases: &[Self::Point],
    ) -> Result<Self::Point, Error> {
        if scalars.len() != bases.len() {
            panic!("Number of scalars and points should be the same.")
        }
        let scalar_chip = self.scalar_field_chip();
        let identity = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;
        let one = self.scalar_field_chip().assign_fixed(layouter, C::ScalarField::ONE)?;

        // Add max bound to scalars + preprocess.
        let scalars: Vec<_> =
            scalars.iter().map(|s| (s.clone(), C::ScalarField::NUM_BITS as usize)).collect();
        let (scalars, bases, bases_with_1bit_scalar) =
            msm_preprocess(self, scalar_chip, layouter, &scalars, bases)?;
        let scalar_bits = scalars
            .iter()
            .map(|s| scalar_chip.assigned_to_le_bits(layouter, &s.0, None, true))
            .collect::<Result<Vec<_>, Error>>()?;

        // Windowed msm with shared doubling.
        let res = self.windowed_msm::<3>(layouter, &scalar_bits, &bases)?;

        // Add 1-bit scalar bases.
        bases_with_1bit_scalar.iter().try_fold(res, |acc, (b, s)| {
            let s_times_b = if s == &one {
                b.clone()
            } else {
                let s_is_zero = scalar_chip.is_zero(layouter, s)?;
                self.select(layouter, &s_is_zero, &identity, b)?
            };
            self.add(layouter, &acc, &s_times_b)
        })
    }

    // Per-base windowed MSM with adaptive window size. Unlike `msm`, this does
    // not share doublings across bases, avoiding padding waste when scalar
    // bounds differ significantly.
    fn msm_by_bounded_scalars(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[(S::Scalar, usize)],
        bases: &[AssignedForeignEdwardsPoint<F, C, B>],
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        if scalars.len() != bases.len() {
            panic!("Number of scalars and points should be the same.")
        }
        let scalar_chip = self.scalar_field_chip();
        let identity = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;
        let one = self.scalar_field_chip().assign_fixed(layouter, C::ScalarField::ONE)?;

        let (scalars, bases, bases_with_1bit_scalar) =
            msm_preprocess(self, scalar_chip, layouter, scalars, bases)?;

        // We do not share doublings because we assume the difference in
        // scalar upper bounds negate the benefits, since we will double
        // until the max of the bounds.
        let mut res = identity.clone();
        for ((s, num_bits), b) in scalars.iter().zip(bases.iter()) {
            let bits = scalar_chip.assigned_to_le_bits(layouter, s, Some(*num_bits), true)?;
            let term = if *num_bits <= 3 {
                self.windowed_msm::<1>(layouter, &[bits], &[b.clone()])?
            } else if *num_bits <= 32 {
                self.windowed_msm::<2>(layouter, &[bits], &[b.clone()])?
            } else {
                self.windowed_msm::<3>(layouter, &[bits], &[b.clone()])?
            };
            res = self.add(layouter, &res, &term)?;
        }

        // Add 1-bit scalar bases.
        bases_with_1bit_scalar.iter().try_fold(res, |acc, (b, s)| {
            let s_times_b = if s == &one {
                b.clone()
            } else {
                let s_is_zero = scalar_chip.is_zero(layouter, s)?;
                self.select(layouter, &s_is_zero, &identity, b)?
            };
            self.add(layouter, &acc, &s_times_b)
        })
    }

    fn mul_by_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar: C::ScalarField,
        base: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        if scalar == C::ScalarField::ZERO {
            return self.assign_fixed(layouter, C::CryptographicGroup::identity());
        } else if scalar == C::ScalarField::ONE {
            return Ok(base.clone());
        }

        let scalar_bits = scalar.to_bits_le(None);
        let mut p = base.clone();
        let mut res = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;

        // Simple double-and-add
        for (i, b) in scalar_bits.iter().enumerate() {
            if *b {
                res = self.add(layouter, &res, &p)?;
            }
            // The doubling in the last iteration is not needed
            if i + 1 < scalar_bits.len() {
                p = self.double(layouter, &p)?;
            }
        }

        Ok(res)
    }

    fn point_from_coordinates(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, C::Base, B>,
        y: &AssignedField<F, C::Base, B>,
    ) -> Result<Self::Point, Error> {
        let point = x
            .value()
            .zip(y.value())
            .map(|(x, y)| C::from_xy(x, y).expect("valid coordinates").into_subgroup());

        let p = AssignedForeignEdwardsPoint::<F, C, B> {
            point,
            x: x.clone(),
            y: y.clone(),
        };

        self.assert_in_subgroup(layouter, &p)?;

        Ok(p)
    }

    fn x_coordinate(&self, point: &Self::Point) -> Self::Coordinate {
        point.x.clone()
    }

    fn y_coordinate(&self, point: &Self::Point) -> Self::Coordinate {
        point.y.clone()
    }

    fn base_field(&self) -> &impl DecompositionInstructions<F, Self::Coordinate> {
        self.base_field_chip()
    }

    fn assign_without_subgroup_check(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<Self::Point, Error> {
        self.assign_point_unchecked(layouter, value)
    }
}

/// Precomputed table of points for windowed MSM.
#[derive(Clone, Debug)]
struct PrecomputedTable<F, C, B, const WS: usize>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    /// Table of precomputed points, where table[i] = i * base.
    table: Vec<AssignedForeignEdwardsPoint<F, C, B>>,
}

impl<F, C, B, S, N> ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F>,
{
    /// Builds table `[0*base, 1*base, ..., (2^WS-1)*base]`. Cost: 2^WS - 2 adds.
    fn precompute<const WS: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        base: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<PrecomputedTable<F, C, B, WS>, Error> {
        let identity = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;
        let mut table = vec![identity, base.clone()];
        let mut acc = base.clone();
        for _ in 2..1 << WS {
            acc = self.add(layouter, &acc, base)?;
            table.push(acc.clone());
        }
        Ok(PrecomputedTable { table })
    }

    /// Selects `table[w]` where `w` is the LE value of `bits`, using a binary
    /// mux tree. Cost: 2^WS - 1 point selects.
    fn multi_select<const WS: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>; WS],
        table: &PrecomputedTable<F, C, B, WS>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        assert_eq!(table.table.len(), 1 << WS);
        let mut res = table.table.clone();

        let mut len = 1 << WS;
        for b in bits.iter().rev() {
            let half_len = len / 2;
            for i in 0..half_len {
                res[i] = self.select(layouter, b, &res[i + half_len], &res[i])?;
            }
            len = half_len;
        }
        Ok(res[0].clone())
    }

    /// Windowed interleaved MSM over LE bit-decomposed scalars. Shares the
    /// doubling chain across all bases. MSB-first Horner evaluation.
    fn windowed_msm<const WS: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[Vec<AssignedBit<F>>],
        bases: &[AssignedForeignEdwardsPoint<F, C, B>],
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        assert_eq!(scalars.len(), bases.len());

        if bases.is_empty() {
            return self.assign_fixed(layouter, C::CryptographicGroup::identity());
        }

        // Pad all bit vectors to a common length that is a multiple of WS.
        let max_bits = scalars.iter().map(|s| s.len()).max().unwrap_or(0);
        let padded_len = max_bits.div_ceil(WS) * WS;
        let zero_bit: AssignedBit<F> = self.native_gadget.assign_fixed(layouter, false)?;
        let scalars: Vec<Vec<AssignedBit<F>>> = scalars
            .iter()
            .map(|bits| {
                let mut padded = bits.clone();
                padded.resize(padded_len, zero_bit.clone());
                padded
            })
            .collect();
        let num_windows = padded_len / WS;

        // Precompute tables for each base.
        let tables: Vec<PrecomputedTable<F, C, B, WS>> = bases
            .iter()
            .map(|b| self.precompute::<WS>(layouter, b))
            .collect::<Result<Vec<_>, _>>()?;

        let mut res = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;
        for w in (0..num_windows).rev() {
            // Skip doubling in first window.
            if w < num_windows - 1 {
                for _ in 0..WS {
                    res = self.double(layouter, &res)?;
                }
            }
            for (bits, table) in scalars.iter().zip(tables.iter()) {
                let window_bits: &[AssignedBit<F>; WS] =
                    bits[w * WS..(w + 1) * WS].try_into().expect("window slice length must equal WS");
                let addend = self.multi_select::<WS>(layouter, window_bits, table)?;
                res = self.add(layouter, &res, &addend)?;
            }
        }

        Ok(res)
    }
}

#[derive(Clone, Debug)]
#[cfg(any(test, feature = "testing"))]
/// Configuration used to implement `FromScratch` for the
/// `ForeignEdwardsEccChip` chip. This should only be used for testing.
pub struct ForeignEdwardsEccTestConfig<F, C, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    S: ScalarFieldInstructions<F> + FromScratch<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F> + FromScratch<F>,
{
    native_gadget_config: <N as FromScratch<F>>::Config,
    scalar_field_config: <S as FromScratch<F>>::Config,
    ff_ecc_config: ForeignEdwardsEccConfig<C>,
}

#[cfg(any(test, feature = "testing"))]
impl<F, C, B, S, N> FromScratch<F> for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: CircuitField,
    C: EdwardsCurve,
    C::Base: Legendre,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F> + FromScratch<F>,
    S::Scalar: InnerValue<Element = C::ScalarField>,
    N: NativeInstructions<F> + FromScratch<F>,
{
    type Config = ForeignEdwardsEccTestConfig<F, C, S, N>;

    fn new_from_scratch(config: &Self::Config) -> Self {
        let native_gadget = <N as FromScratch<F>>::new_from_scratch(&config.native_gadget_config);
        let scalar_field_chip =
            <S as FromScratch<F>>::new_from_scratch(&config.scalar_field_config);
        ForeignEdwardsEccChip::new(&config.ff_ecc_config, &native_gadget, &scalar_field_chip)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.native_gadget.load_from_scratch(layouter)?;
        self.scalar_field_chip.load_from_scratch(layouter)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> ForeignEdwardsEccTestConfig<F, C, S, N> {
        use crate::field::foreign::nb_field_chip_columns;

        let native_gadget_config =
            <N as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let scalar_field_config =
            <S as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let nb_advice_cols = nb_field_chip_columns::<F, C::Base, B>();
        let advice_columns = (0..nb_advice_cols).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let nb_parallel_range_checks = 4;
        let max_bit_len = 8;
        let base_field_config = FieldChip::<F, C::Base, B, N>::configure(
            meta,
            &advice_columns,
            nb_parallel_range_checks,
            max_bit_len,
        );
        let ff_ecc_config = ForeignEdwardsEccChip::<F, C, B, S, N>::configure(
            meta,
            &base_field_config,
            nb_parallel_range_checks,
            max_bit_len,
        );
        ForeignEdwardsEccTestConfig {
            native_gadget_config,
            scalar_field_config,
            ff_ecc_config,
        }
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use group::Group;
    use midnight_curves::{curve25519::Curve25519, BlsScalar, JubjubExtended};
    use midnight_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        ecc::curves::CircuitCurve,
        field::{
            decomposition::chip::P2RDecompositionChip, foreign::params::MultiEmulationParams,
            NativeChip, NativeGadget,
        },
        instructions::{assertions, control_flow, ecc, equality, public_input, zero},
    };

    type F = BlsScalar;
    type Native<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
    type EmulatedField<F, C> = FieldChip<F, <C as Group>::Scalar, MultiEmulationParams, Native<F>>;

    macro_rules! test_generic {
        ($mod:ident, $op:ident, $native:ty, $curve:ty, $scalar_field:ty,
    $name:expr) => {
            $mod::tests::$op::<
                $native,
                AssignedForeignEdwardsPoint<$native, $curve, MultiEmulationParams>,
                ForeignEdwardsEccChip<
                    $native,
                    $curve,
                    MultiEmulationParams,
                    $scalar_field,
                    Native<$native>,
                >,
            >($name);
        };
    }

    macro_rules! test {
        ($mod:ident, $op:ident) => {
            #[test]
            fn $op() {
                test_generic!($mod, $op, F, JubjubExtended, EmulatedField<F, JubjubExtended>, "emulated_jubjub");
                test_generic!($mod, $op, F, Curve25519, EmulatedField<F, Curve25519>, "emulated_curve25519");
            }
        };
    }

    test!(assertions, test_assertions);

    test!(public_input, test_public_inputs);

    test!(equality, test_is_equal);

    test!(zero, test_zero_assertions);
    test!(zero, test_is_zero);

    test!(control_flow, test_select);
    test!(control_flow, test_cond_assert_equal);
    test!(control_flow, test_cond_swap);

    macro_rules! ecc_test {
        ($op:ident, $native:ty, $curve:ty, $scalar_field:ty, $name:expr) => {
            ecc::tests::$op::<
                $native,
                $curve,
                ForeignEdwardsEccChip<
                    $native,
                    $curve,
                    MultiEmulationParams,
                    $scalar_field,
                    Native<$native>,
                >,
            >($name);
        };
    }

    macro_rules! ecc_tests {
        ($op:ident) => {
            #[test]
            fn $op() {
                ecc_test!($op, BlsScalar, JubjubExtended, EmulatedField<BlsScalar, JubjubExtended>, "emulated_jubjub");
                ecc_test!($op, BlsScalar, Curve25519, EmulatedField<BlsScalar, Curve25519>, "emulated_curve25519");
            }
        };
    }

    ecc_tests!(test_assign);
    ecc_tests!(test_assign_without_subgroup_check);
    ecc_tests!(test_add);
    ecc_tests!(test_double);
    ecc_tests!(test_negate);
    ecc_tests!(test_msm);
    ecc_tests!(test_msm_by_bounded_scalars);
    ecc_tests!(test_mul_by_constant);
    ecc_tests!(test_coordinates_edwards);

    #[test]
    fn test_assert_in_subgroup() {
        run_test_assert_in_subgroup::<Curve25519>();
        run_test_assert_in_subgroup::<JubjubExtended>();
    }

    #[test]
    fn test_assert_on_curve() {
        run_test_assert_on_curve::<Curve25519>();
        run_test_assert_on_curve::<JubjubExtended>();
    }

    fn run_test_assert_in_subgroup<C>()
    where
        C: EdwardsCurve,
        C::Base: Legendre,
        MultiEmulationParams: FieldEmulationParams<BlsScalar, C::Base>
            + FieldEmulationParams<BlsScalar, C::ScalarField>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0x0);
        let point = C::CryptographicGroup::random(&mut rng);

        let circuit = InSubgroupCheckCircuit::<C> { point };
        let prover = MockProver::run(&circuit, vec![vec![], vec![]])
            .expect("proof generation should not fail");
        prover.verify().expect("random subgroup point should verify");
    }

    fn run_test_assert_on_curve<C>()
    where
        C: EdwardsCurve,
        C::Base: Legendre,
        MultiEmulationParams: FieldEmulationParams<BlsScalar, C::Base>
            + FieldEmulationParams<BlsScalar, C::ScalarField>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0x0);

        // Sample random subgroup point
        let point = C::CryptographicGroup::random(&mut rng);
        let (x, y) = point.into().coordinates().expect("valid curve point");

        // Valid point: identity (0, 1)
        let circuit = OnCurveCheckCircuit::<C> {
            x: C::Base::ZERO,
            y: C::Base::ONE,
        };
        let prover = MockProver::run(&circuit, vec![vec![], vec![]])
            .expect("proof generation should not fail");
        prover.verify().expect("identity (0,1) should pass verification");

        // Valid point: generator
        let gen = C::CryptographicGroup::generator();
        let (gx, gy) = gen.into().coordinates().expect("valid generator");
        let circuit = OnCurveCheckCircuit::<C> { x: gx, y: gy };
        let prover = MockProver::run(&circuit, vec![vec![], vec![]])
            .expect("proof generation should not fail");
        prover.verify().expect("generator should pass verification");

        // Invalid point: offset the y coordinate of a random curve point by 1, so the
        // curve equation is not satisfied with overwhelming probability (there
        // is a negligible probability this test fails)
        let circuit = OnCurveCheckCircuit::<C> {
            x,
            y: y + C::Base::ONE,
        };
        let prover = MockProver::run(&circuit, vec![vec![], vec![]])
            .expect("proof generation should not fail");
        assert!(
            prover.verify().is_err(),
            "invalid point should fail verification"
        );

        // Invalid point: (1,1)
        let circuit = OnCurveCheckCircuit::<C> {
            x: C::Base::ONE,
            y: C::Base::ONE,
        };
        let prover = MockProver::run(&circuit, vec![vec![], vec![]])
            .expect("proof generation should not fail");
        assert!(
            prover.verify().is_err(),
            "invalid point (1,1) should fail verification"
        );

        // Invalid point: (0, 0)
        let circuit = OnCurveCheckCircuit::<C> {
            x: C::Base::ZERO,
            y: C::Base::ZERO,
        };
        let prover = MockProver::run(&circuit, vec![vec![], vec![]])
            .expect("proof generation should not fail");
        assert!(
            prover.verify().is_err(),
            "invalid point (0,0) should fail verification"
        );
    }

    type EdwardsChip<C> = ForeignEdwardsEccChip<
        F,
        C,
        MultiEmulationParams,
        FieldChip<F, <C as CircuitCurve>::ScalarField, MultiEmulationParams, Native<F>>,
        Native<F>,
    >;

    /// Test circuit that calls `assert_in_subgroup` and `assert_on_curve` for a
    /// given point of a twisted Edwards curve.
    ///
    /// Since `assert_in_subgroup` already takes as input a point in form of
    /// [AssignedForeignEdwardsPoint], which, in turn, wraps a valid subgroup
    /// point, this circuit checks correctness of `assert_in_subgroup` and
    /// `assert_on_curve` for valid subgroup points.
    #[derive(Clone, Debug)]
    struct InSubgroupCheckCircuit<C: EdwardsCurve> {
        point: C::CryptographicGroup,
    }

    impl<C> Circuit<F> for InSubgroupCheckCircuit<C>
    where
        C: EdwardsCurve,
        C::Base: Legendre,
        MultiEmulationParams:
            FieldEmulationParams<F, C::Base> + FieldEmulationParams<F, C::ScalarField>,
    {
        type Config = <EdwardsChip<C> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed = meta.instance_column();
            let instance = meta.instance_column();
            EdwardsChip::<C>::configure_from_scratch(meta, &[committed, instance])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = EdwardsChip::<C>::new_from_scratch(&config);

            let curve_point: C = self.point.into();
            let (x, y) = curve_point.coordinates().expect("valid curve point");

            let x = chip.base_field_chip().assign(&mut layouter, Value::known(x))?;
            let y = chip.base_field_chip().assign(&mut layouter, Value::known(y))?;
            let p = AssignedForeignEdwardsPoint {
                point: Value::known(self.point),
                x,
                y,
            };

            chip.assert_in_subgroup(&mut layouter, &p)?;
            chip.assert_on_curve(&mut layouter, &p.x, &p.y)?; // redundant
            chip.load_from_scratch(&mut layouter)
        }
    }

    /// Test circuit that calls `assert_on_curve` for arbitrary (x, y)
    /// coordinates (not necessarily representing a valid curve point).
    ///
    /// This circuit checks if `assert_on_curve` correctly verifies, or fails,
    /// on a selected set of inputs.
    #[derive(Clone, Debug)]
    struct OnCurveCheckCircuit<C: EdwardsCurve> {
        x: C::Base,
        y: C::Base,
    }

    impl<C> Circuit<F> for OnCurveCheckCircuit<C>
    where
        C: EdwardsCurve,
        C::Base: Legendre,
        MultiEmulationParams:
            FieldEmulationParams<F, C::Base> + FieldEmulationParams<F, C::ScalarField>,
    {
        type Config = <EdwardsChip<C> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed = meta.instance_column();
            let instance = meta.instance_column();
            EdwardsChip::<C>::configure_from_scratch(meta, &[committed, instance])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = EdwardsChip::<C>::new_from_scratch(&config);

            let x = chip.base_field_chip().assign(&mut layouter, Value::known(self.x))?;
            let y = chip.base_field_chip().assign(&mut layouter, Value::known(self.y))?;

            chip.assert_on_curve(&mut layouter, &x, &y)?;
            chip.load_from_scratch(&mut layouter)
        }
    }

    /// Test circuit for `windowed_msm`: computes sum_i(scalar_i * base_i) and
    /// asserts the result equals the expected point.
    #[derive(Clone, Debug)]
    struct WindowedMsmCircuit<C: EdwardsCurve> {
        scalars: Vec<C::ScalarField>,
        bases: Vec<C::CryptographicGroup>,
        expected: C::CryptographicGroup,
    }

    impl<C> Circuit<F> for WindowedMsmCircuit<C>
    where
        C: EdwardsCurve,
        C::Base: Legendre,
        MultiEmulationParams:
            FieldEmulationParams<F, C::Base> + FieldEmulationParams<F, C::ScalarField>,
    {
        type Config = <EdwardsChip<C> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed = meta.instance_column();
            let instance = meta.instance_column();
            EdwardsChip::<C>::configure_from_scratch(meta, &[committed, instance])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = EdwardsChip::<C>::new_from_scratch(&config);

            // Assign bases.
            let bases: Vec<_> = self
                .bases
                .iter()
                .map(|b| chip.assign(&mut layouter, Value::known(*b)))
                .collect::<Result<Vec<_>, _>>()?;

            // Decompose scalars to LE bits.
            let scalar_chip = chip.scalar_field_chip();
            let scalar_bits: Vec<Vec<AssignedBit<F>>> = self
                .scalars
                .iter()
                .map(|s| {
                    let assigned = scalar_chip.assign_fixed(&mut layouter, *s)?;
                    scalar_chip.assigned_to_le_bits(
                        &mut layouter,
                        &assigned,
                        Some(C::ScalarField::NUM_BITS as usize),
                        true,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;

            let result = chip.windowed_msm::<3>(&mut layouter, &scalar_bits, &bases)?;

            // Assert result matches expected.
            let expected = chip.assign_fixed(&mut layouter, self.expected)?;
            chip.assert_equal(&mut layouter, &result, &expected)?;

            chip.load_from_scratch(&mut layouter)
        }
    }

    fn run_test_windowed_msm<C>()
    where
        C: EdwardsCurve,
        C::Base: Legendre,
        MultiEmulationParams:
            FieldEmulationParams<F, C::Base> + FieldEmulationParams<F, C::ScalarField>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc00ffee);
        type S<C> = <C as CircuitCurve>::ScalarField;
        type P<C> = <C as CircuitCurve>::CryptographicGroup;

        let check = |scalars, bases, expected| {
            let circuit = WindowedMsmCircuit::<C> {
                scalars,
                bases,
                expected,
            };
            MockProver::run(17, &circuit, vec![vec![], vec![]])
                .expect("proof generation should not fail")
                .verify()
                .expect("windowed MSM should verify");
        };

        let (s, p) = (S::<C>::random(&mut rng), P::<C>::random(&mut rng));
        check(vec![s], vec![p], p * s);

        let (s1, s2) = (S::<C>::random(&mut rng), S::<C>::random(&mut rng));
        let (p1, p2) = (P::<C>::random(&mut rng), P::<C>::random(&mut rng));
        check(vec![s1, s2], vec![p1, p2], p1 * s1 + p2 * s2);

        let p = P::<C>::random(&mut rng);
        check(vec![S::<C>::ZERO], vec![p], P::<C>::identity());

        let p = P::<C>::random(&mut rng);
        check(vec![S::<C>::ONE], vec![p], p);
    }

    #[test]
    fn test_windowed_msm() {
        run_test_windowed_msm::<JubjubExtended>();
    }
}
