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
//! This module supports curves of the form a*x^2 + y^2 = 1 + d*x^2*y^2.
//!
//! We require that the emulated elliptic curve do not have low-order points.
//! In particular, the curve (or the relevant subgroup) must have a large prime
//! order.

use core::panic;
use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use ff::{Field, PrimeField};
use group::Group;
#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::{Column, Instance};
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{ConstraintSystem, Error},
};
#[cfg(any(test, feature = "testing"))]
use {crate::testing_utils::Sampleable, rand::RngCore};

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;
use crate::{
    ecc::{
        curves::EdwardsCurve,
        foreign::gates::coord::{self, CoordConfig},
    },
    field::{
        foreign::{
            self,
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

/// ['ECChip'] to perform foreign Edwards EC operations.
#[derive(Clone, Debug)]
pub struct ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    N: NativeInstructions<F>,
{
    config: ForeignEdwardsEccConfig<C>,
    native_gadget: N,
    base_field_chip: FieldChip<F, C::Base, B, N>,
    scalar_field_chip: S,
}

impl<F, C, B, S, N> ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
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

    /// Configures the foreign Edwards ECC chip.
    pub fn configure(
        _meta: &mut ConstraintSystem<F>,
        base_field_config: &FieldChipConfig,
    ) -> ForeignEdwardsEccConfig<C> {
        let coord_config = CoordConfig::<C>::configure::<F, B>(_meta, base_field_config);

        ForeignEdwardsEccConfig {
            base_field_config: base_field_config.clone(),
            coord_config,
            _marker: PhantomData,
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
}

/// Type for foreign Edwards EC points.
#[derive(Clone, Debug)]
#[must_use]
pub struct AssignedForeignEdwardsPoint<F, C, B>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    point: Value<C::CryptographicGroup>,
    x: AssignedField<F, C::Base, B>,
    y: AssignedField<F, C::Base, B>,
}

impl<F, C, B> PartialEq for AssignedForeignEdwardsPoint<F, C, B>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl<F, C, B> Hash for AssignedForeignEdwardsPoint<F, C, B>
where
    F: PrimeField,
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    // TODO: why default to 0?
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
    F: PrimeField,
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
    F: PrimeField,
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn sample_inner(rng: impl RngCore) -> C::CryptographicGroup {
        C::CryptographicGroup::random(rng)
    }
}

impl<F, C, B, S, N> Chip<F> for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    N: NativeInstructions<F>,
{
    /// Converts an Edwards curve point to [AssignedForeignEdwardsPoint].
    /// The point is not asserted (with constraints) to be on the curve.
    fn assign_point_unchecked(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let (val_x, val_y) = value
            .map(|v| v.into().coordinates().expect("assign_unchecked: valid curve point"))
            .unzip();
        let x = self.base_field_chip().assign(layouter, val_x)?;
        let y = self.base_field_chip().assign(layouter, val_y)?;
        let p = AssignedForeignEdwardsPoint::<F, C, B> { point: value, x, y };

        Ok(p)
    }

    /// Asserts the curve equation `a*x^2 + y^2 = 1 + d*x^2*y^2` of an emulated
    /// twisted Edwards curve, given the x and y coordinate in form of
    /// [AssignedField].
    fn assert_curve_equation(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, C::Base, B>,
        y: &AssignedField<F, C::Base, B>,
    ) -> Result<(), Error> {
        let base_chip = self.base_field_chip();

        // Compute x^2, y^2 and a*x^2 + y^2 - 1 - d*x^2*y^2
        let x_x = base_chip.mul(layouter, x, x, None)?;
        let y_y = base_chip.mul(layouter, y, y, None)?;
        let id = base_chip.add_and_mul(
            layouter,
            (C::A, &x_x),
            (C::Base::ONE, &y_y),
            (C::Base::ZERO, &x_x),
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let point = self.assign_point_unchecked(layouter, value)?;

        self.assert_curve_equation(layouter, &point.x, &point.y)?;

        Ok(point)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let (x, y) = {
            constant
                .into()
                .coordinates()
                .expect("assign_point_unchecked: invalid point given")
        };
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
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
impl<F, C, B, S, SP, N> AssignmentInstructions<F, AssignedField<F, C::Scalar, SP>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F, Scalar = AssignedField<F, C::Scalar, SP>>,
    SP: FieldEmulationParams<F, C::Scalar>,
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
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
        let coordinates = constant.into().coordinates().expect("Valid point");
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
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
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
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
        let a_px_qx = base_chip.mul_by_constant(layouter, &px_qx, C::A)?;
        let neg_a_px_qx = base_chip.neg(layouter, &a_px_qx)?;
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

    /// The negation of a point `P = (Px, Py)` on a twisted Edwards curve is
    /// given by `-P = (-Px, Py)`.
    fn negate(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
    ) -> Result<Self::Point, Error> {
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
        let scalars = scalars
            .iter()
            .map(|s| (s.clone(), C::Scalar::NUM_BITS as usize))
            .collect::<Vec<_>>();

        self.msm_by_bounded_scalars(layouter, &scalars, bases)
    }

    fn msm_by_bounded_scalars(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[(S::Scalar, usize)],
        bases: &[AssignedForeignEdwardsPoint<F, C, B>],
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        if scalars.len() != bases.len() {
            panic!("Nr of scalars and points should be the same.")
        }

        let identity = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;
        let mut res = identity.clone();

        for ((s, bit_size), b) in scalars.iter().zip(bases.iter()) {
            let scalar_bits =
                self.scalar_field_chip()
                    .assigned_to_le_bits(layouter, s, Some(*bit_size), true)?;
            let mut p = b.clone();

            // Simple double-and-add
            for b in scalar_bits.iter() {
                let addend = self.select(layouter, b, &p, &identity)?;
                res = self.add(layouter, &res, &addend)?;
                p = self.double(layouter, &p)?;
            }
        }

        Ok(res)
    }

    fn mul_by_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar: C::Scalar,
        base: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        if scalar == C::Scalar::ZERO {
            return self.assign_fixed(layouter, C::CryptographicGroup::identity());
        } else if scalar == C::Scalar::ONE {
            return Ok(base.clone());
        }

        let scalar_bits = crate::utils::util::fe_to_le_bits(&scalar, None);
        let mut p = base.clone();
        let mut res = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;

        // Simple double-and-add
        for b in scalar_bits {
            if b {
                res = self.add(layouter, &res, &p)?;
            }
            p = self.double(layouter, &p)?;
        }

        Ok(res)
    }

    fn point_from_coordinates(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, C::Base, B>,
        y: &AssignedField<F, C::Base, B>,
    ) -> Result<Self::Point, Error> {
        self.assert_curve_equation(layouter, x, y)?;

        let point = x
            .value()
            .zip(y.value())
            .map(|(x, y)| C::from_xy(x, y).expect("valid coordinates").into_subgroup());

        Ok(AssignedForeignEdwardsPoint::<F, C, B> {
            point,
            x: x.clone(),
            y: y.clone(),
        })
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
}

#[derive(Clone, Debug)]
#[cfg(any(test, feature = "testing"))]
/// Configuration used to implement `FromScratch` for the
/// `ForeignEdwardsEccChip` chip. This should only be used for testing.
pub struct ForeignEccTestConfig<F, C, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    S: ScalarFieldInstructions<F> + FromScratch<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F> + FromScratch<F>,
{
    native_gadget_config: <N as FromScratch<F>>::Config,
    scalar_field_config: <S as FromScratch<F>>::Config,
    ff_ecc_config: ForeignEdwardsEccConfig<C>,
}

#[cfg(any(test, feature = "testing"))]
impl<F, C, B, S, N> FromScratch<F> for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F> + FromScratch<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F> + FromScratch<F>,
{
    type Config = ForeignEccTestConfig<F, C, S, N>;

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
    ) -> ForeignEccTestConfig<F, C, S, N> {
        use crate::field::foreign::nb_field_chip_columns;

        let native_gadget_config =
            <N as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let scalar_field_config =
            <S as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let nb_advice_cols = nb_field_chip_columns::<F, C::Base, B>();
        let advice_columns = (0..nb_advice_cols).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let base_field_config = FieldChip::<F, C::Base, B, N>::configure(meta, &advice_columns);
        let ff_ecc_config =
            ForeignEdwardsEccChip::<F, C, B, S, N>::configure(meta, &base_field_config);
        ForeignEccTestConfig {
            native_gadget_config,
            scalar_field_config,
            ff_ecc_config,
        }
    }
}

/// Implement subgroup membership checks for emulated JubJub
/// over the scalar field of BLS12-381.
use midnight_curves::{Fr, JubjubExtended};

use crate::field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget};

type F = midnight_curves::BlsScalar;
type EP = foreign::params::MultiEmulationParams;
type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
type EF = FieldChip<F, <JubjubExtended as Group>::Scalar, EP, NG>;
type JubJubChip = ForeignEdwardsEccChip<F, JubjubExtended, EP, EF, NG>;

impl JubJubChip {
    /// Asserts that the given point belongs to the JubJub subgroup.
    pub fn assert_in_jubjub_subgroup(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &<JubJubChip as EccInstructions<F, JubjubExtended>>::Point,
    ) -> Result<(), Error> {
        // Let
        //    * r be the order of the prime-order JubJub subgroup,
        //    * h be the cofactor of this subgroup.
        //
        // To check that a point p is in the prime-order JubJub subgroup,
        // we exhibit a cofactor-rth root of p. We do the following:
        //    1. Compute inv := h^{-1} mod r.
        //    2. Check that h * (inv * p) = p.
        // If the equality in 2. holds, then inv * p is the cofactor-th root of p.
        //
        // Note: step 1. is possible, since gcd(h,r) = 1.

        // The prime-order JubJub sugroup has a cofactor of 8
        // See: https://std.neuromancer.sk/other/JubJub
        let cofactor = Fr::from_raw([0x08, 0, 0, 0]);

        let q: <JubJubChip as EccInstructions<F, JubjubExtended>>::Point =
            self.assign(layouter, p.value().map(|p| p * cofactor.invert().unwrap()))?;

        let cofactor_times_q = self.mul_by_constant(layouter, cofactor, &q)?;
        self.assert_equal(layouter, p, &cofactor_times_q)
    }
}

#[cfg(test)]
mod tests {
    use group::Group;
    use midnight_curves::{BlsScalar, JubjubExtended};

    use super::*;
    use crate::{
        field::{
            decomposition::chip::P2RDecompositionChip, foreign::params::MultiEmulationParams,
            NativeChip, NativeGadget,
        },
        instructions::{assertions, control_flow, ecc, equality, public_input, zero},
    };

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
                test_generic!($mod, $op, BlsScalar, JubjubExtended, EmulatedField<BlsScalar, JubjubExtended>, "emulated_jubjub");
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
             }
         };
     }

    ecc_tests!(test_add);
    ecc_tests!(test_double);
    ecc_tests!(test_negate);
    ecc_tests!(test_msm);
    ecc_tests!(test_msm_by_bounded_scalars);
    ecc_tests!(test_mul_by_constant);
    ecc_tests!(test_coordinates_edwards);
}
