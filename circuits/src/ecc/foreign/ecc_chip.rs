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

//! Elliptic curve operations over foreign fields.
//! This module supports curves of the form y^2 = x^3 + b (i.e. with a = 0).
//!
//! We require that the emulated elliptic curve do not have low-order points.
//! In particular, the curve (or the relevant subgroup) must have a large prime
//! order.

use std::{
    cell::RefCell,
    cmp::max,
    collections::HashMap,
    fmt::Debug,
    hash::{Hash, Hasher},
    ops::Mul,
    rc::Rc,
};

use ff::{Field, PrimeField};
use group::Group;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
use num_bigint::BigUint;
use num_traits::One;
use rand::rngs::OsRng;
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::Sampleable, crate::utils::util::FromScratch,
    midnight_proofs::plonk::Instance, rand::RngCore,
};

use super::gates::{
    lambda_squared,
    lambda_squared::LambdaSquaredConfig,
    on_curve,
    on_curve::OnCurveConfig,
    slope::{self, SlopeConfig},
    tangent,
    tangent::TangentConfig,
};
use crate::{
    ecc::curves::WeierstrassCurve,
    field::foreign::{
        field_chip::{FieldChip, FieldChipConfig},
        params::FieldEmulationParams,
    },
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
        DecompositionInstructions, EccInstructions, EqualityInstructions, NativeInstructions,
        PublicInputInstructions, ScalarFieldInstructions, ZeroInstructions,
    },
    types::{AssignedBit, AssignedField, AssignedNative, InnerConstants, InnerValue, Instantiable},
    utils::util::{
        big_to_fe, bigint_to_fe, concat, fe_to_big, fe_to_le_bits, glv_scalar_decomposition,
    },
};

/// Foreign ECC configuration.
#[derive(Clone, Debug)]
pub struct ForeignEccConfig<C>
where
    C: WeierstrassCurve,
{
    base_field_config: FieldChipConfig,
    on_curve_config: on_curve::OnCurveConfig<C>,
    slope_config: slope::SlopeConfig<C>,
    tangent_config: tangent::TangentConfig<C>,
    lambda_squared_config: lambda_squared::LambdaSquaredConfig<C>,
    // columns for the dynamic lookup
    q_multi_select: Selector,
    idx_col_multi_select: Column<Advice>,
    tag_col_multi_select: Column<Fixed>,
}

/// Number of columns required by the custom gates of this chip.
pub fn nb_foreign_ecc_chip_columns<F, C, B, S>() -> usize
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    // The scalar field is treated as a gadget. Here we only account for the columns
    // that this chip requires for its own custom gates.
    // The 2 in `2 + |moduli|` corresponds to `u_col` + `cond_col`.
    // The outer `+ 1` corresponds to the advice column for the index of
    // `multi_select`.
    B::NB_LIMBS as usize + max(B::NB_LIMBS as usize, 2 + B::moduli().len()) + 1
}

/// ['ECChip'] to perform foreign EC operations.
#[derive(Clone, Debug)]
pub struct ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    config: ForeignEccConfig<C>,
    native_gadget: N,
    base_field_chip: FieldChip<F, C::Base, B, N>,
    scalar_field_chip: S,
    // A table tag counter to make sure all dynamic lookup tables are independent.
    // This counter is always increased after loading a new table.
    // It will never overflow unless you include more than 2^64 tables, will you?
    // Even in that case, we would get a compile-time error.
    tag_cnt: Rc<RefCell<u64>>,
}

/// Type for foreign EC points.
/// The identity is represented with field `is_id`, whose value is `1` iff the
/// point is the identity. If `is_id` is set, the values of `x` and `y` are
/// irrelevant and can be anything.
/// x2 is a ModInt encoding the square of x, which is computed once and stored.
/// This value is used by our custom gates, it allows us to implement all
/// custom gates without degree-3 terms, so we can reuse the same auxiliary
/// moduli as for ModArith.mul.
#[derive(Clone, Debug)]
#[must_use]
pub struct AssignedForeignPoint<F, C, B>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    point: Value<C::CryptographicGroup>,
    is_id: AssignedBit<F>,
    x: AssignedField<F, C::Base, B>,
    y: AssignedField<F, C::Base, B>,
}

impl<F, C, B> PartialEq for AssignedForeignPoint<F, C, B>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn eq(&self, other: &Self) -> bool {
        self.is_id == other.is_id && self.x == other.x && self.y == other.y
    }
}

impl<F, C, B> Eq for AssignedForeignPoint<F, C, B>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
{
}

impl<F, C, B> Hash for AssignedForeignPoint<F, C, B>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.is_id.hash(state);
        self.x.hash(state);
        self.y.hash(state);
    }
}

impl<F, C, B> Instantiable<F> for AssignedForeignPoint<F, C, B>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn as_public_input(p: &C::CryptographicGroup) -> Vec<F> {
        let b = p.is_identity().into();
        let (x, y) = (*p)
            .into()
            .coordinates()
            .unwrap_or((C::Base::ZERO, C::Base::ZERO));
        concat(&[
            AssignedBit::<F>::as_public_input(&b),
            AssignedField::<F, C::Base, B>::as_public_input(&x),
            AssignedField::<F, C::Base, B>::as_public_input(&y),
        ])
    }
}

impl<F, C, B> InnerValue for AssignedForeignPoint<F, C, B>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    type Element = C::CryptographicGroup;

    fn value(&self) -> Value<Self::Element> {
        self.point
    }
}

impl<F, C, B> InnerConstants for AssignedForeignPoint<F, C, B>
where
    F: PrimeField,
    C: WeierstrassCurve,
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
impl<F, C, B> Sampleable for AssignedForeignPoint<F, C, B>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    fn sample_inner(rng: impl RngCore) -> C::CryptographicGroup {
        C::CryptographicGroup::random(rng)
    }
}

impl<F, C, B, S, N> Chip<F> for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    type Config = ForeignEccConfig<C>;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F, C, B, S, N> AssignmentInstructions<F, AssignedForeignPoint<F, C, B>>
    for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        let p = self.assign_point_unchecked(layouter, value)?;
        let is_not_id = self.native_gadget.not(layouter, &p.is_id)?;
        on_curve::assert_is_on_curve::<F, C, B, N>(
            layouter,
            &is_not_id,
            &p.x,
            &p.y,
            self.base_field_chip(),
            &self.config.on_curve_config,
        )?;
        Ok(p)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        let (xv, yv, is_id_value) = if C::CryptographicGroup::is_identity(&constant).into() {
            (C::Base::ZERO, C::Base::ZERO, true)
        } else {
            let coordinates = constant
                .into()
                .coordinates()
                .expect("assign_point_unchecked: invalid point given");
            (coordinates.0, coordinates.1, false)
        };
        let is_id = self.native_gadget.assign_fixed(layouter, is_id_value)?;
        let x = self.base_field_chip().assign_fixed(layouter, xv)?;
        let y = self.base_field_chip().assign_fixed(layouter, yv)?;
        let p = AssignedForeignPoint::<F, C, B> {
            point: Value::known(constant),
            is_id,
            x,
            y,
        };
        Ok(p)
    }
}

impl<F, C, B, S, N> PublicInputInstructions<F, AssignedForeignPoint<F, C, B>>
    for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F> + PublicInputInstructions<F, AssignedBit<F>>,
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(concat(&[
            self.native_gadget.as_public_input(layouter, &p.is_id)?,
            self.base_field_chip.as_public_input(layouter, &p.x)?,
            self.base_field_chip.as_public_input(layouter, &p.y)?,
        ]))
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedForeignPoint<F, C, B>,
    ) -> Result<(), Error> {
        self.as_public_input(layouter, assigned)?
            .iter()
            .try_for_each(|c| self.native_gadget.constrain_as_public_input(layouter, c))
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        let b_val = value.map(|p| C::CryptographicGroup::is_identity(&p).into());
        let x_val = value.map(|p| {
            p.into()
                .coordinates()
                .map(|opt| opt.0)
                .unwrap_or(C::Base::ZERO)
        });
        let y_val = value.map(|p| {
            p.into()
                .coordinates()
                .map(|opt| opt.1)
                .unwrap_or(C::Base::ZERO)
        });

        let base_chip = self.base_field_chip();
        let is_id = self.native_gadget.assign_as_public_input(layouter, b_val)?;
        let x = base_chip.assign_as_public_input(layouter, x_val)?;
        let y = base_chip.assign_as_public_input(layouter, y_val)?;
        let point = value;
        Ok(AssignedForeignPoint::<F, C, B> { point, is_id, x, y })
    }
}

/// Inherit assignment instructions for [AssignedNative], from the
/// `scalar_field_chip` when the scalar field is the same as the SNARK native
/// field.
/// Mind the binding `S: ScalarFieldInstructions<F, Scalar = AssignedNative<F>>`
/// of this implementation.
impl<F, C, B, S, N> AssignmentInstructions<F, AssignedNative<F>> for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F, Scalar = AssignedNative<F>>,
    S::Scalar: InnerValue<Element = C::Scalar>,
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

/// Inherit assignment instructions for [AssignedField], from the
/// `scalar_field_chip` when the emulated field field is the scalar field.
/// Mind the binding `S: ScalarFieldInstructions<F, Scalar = AssignedField<F,
/// C::Scalar>>` of this implementation.
impl<F, C, B, S, SP, N> AssignmentInstructions<F, AssignedField<F, C::Scalar, SP>>
    for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F, Scalar = AssignedField<F, C::Scalar, SP>>,
    S::Scalar: InnerValue<Element = C::Scalar>,
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

impl<F, C, B, S, N> AssertionInstructions<F, AssignedForeignPoint<F, C, B>>
    for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        q: &AssignedForeignPoint<F, C, B>,
    ) -> Result<(), Error> {
        // This function assumes that all AssignedForeignPoints that have the `is_id`
        // field set use the same (canonical) value for coordinates x and y.
        // Otherwise the circuit becomes unsatisfiable, so a malicious prover does not
        // gain anything from violating this assumption.
        self.native_gadget
            .assert_equal(layouter, &p.is_id, &q.is_id)?;
        self.base_field_chip().assert_equal(layouter, &p.x, &q.x)?;
        self.base_field_chip().assert_equal(layouter, &p.y, &q.y)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        q: &AssignedForeignPoint<F, C, B>,
    ) -> Result<(), Error> {
        let equal = self.is_equal(layouter, p, q)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &equal, false)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        constant: C::CryptographicGroup,
    ) -> Result<(), Error> {
        if constant.is_identity().into() {
            self.native_gadget
                .assert_equal_to_fixed(layouter, &p.is_id, true)
        } else {
            let coordinates = constant.into().coordinates().expect("Valid point");
            self.base_field_chip()
                .assert_equal_to_fixed(layouter, &p.x, coordinates.0)?;
            self.base_field_chip()
                .assert_equal_to_fixed(layouter, &p.y, coordinates.1)?;
            self.native_gadget
                .assert_equal_to_fixed(layouter, &p.is_id, false)
        }
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        constant: C::CryptographicGroup,
    ) -> Result<(), Error> {
        if constant.is_identity().into() {
            self.native_gadget
                .assert_equal_to_fixed(layouter, &p.is_id, false)
        } else {
            let equal = self.is_equal_to_fixed(layouter, p, constant)?;
            self.native_gadget
                .assert_equal_to_fixed(layouter, &equal, false)
        }
    }
}

impl<F, C, B, S, N> EqualityInstructions<F, AssignedForeignPoint<F, C, B>>
    for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    /// Returns `1` if the given points are equal and `0` otherwise.
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        q: &AssignedForeignPoint<F, C, B>,
    ) -> Result<AssignedBit<F>, Error> {
        // This function needs to return `true` when given two points with the `is_id`
        // field set, even if their coordinates are different.
        let eq_coordinates = {
            let eq_x = self.base_field_chip().is_equal(layouter, &p.x, &q.x)?;
            let eq_y = self.base_field_chip().is_equal(layouter, &p.y, &q.y)?;
            let eq_x_and_y = self.native_gadget.and(layouter, &[eq_x, eq_y])?;
            let both_are_id = self
                .native_gadget
                .and(layouter, &[p.is_id.clone(), q.is_id.clone()])?;
            self.native_gadget
                .or(layouter, &[eq_x_and_y, both_are_id])?
        };
        let eq_id_flag = self.native_gadget.is_equal(layouter, &p.is_id, &q.is_id)?;
        self.native_gadget
            .and(layouter, &[eq_id_flag, eq_coordinates])
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedBit<F>, Error> {
        if constant.is_identity().into() {
            Ok(p.is_id.clone())
        } else {
            let coordinates = constant.into().coordinates().expect("Valid point");
            let eq_x = self
                .base_field_chip()
                .is_equal_to_fixed(layouter, &p.x, coordinates.0)?;
            let eq_y = self
                .base_field_chip()
                .is_equal_to_fixed(layouter, &p.y, coordinates.1)?;
            let p_is_not_id = self.native_gadget.not(layouter, &p.is_id)?;
            self.native_gadget.and(layouter, &[eq_x, eq_y, p_is_not_id])
        }
    }
}

impl<F, C, B, S, N> ZeroInstructions<F, AssignedForeignPoint<F, C, B>>
    for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    fn is_zero(
        &self,
        _layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
    ) -> Result<AssignedBit<F>, Error> {
        Ok(p.is_id.clone())
    }
}

impl<F, C, B, S, N> ControlFlowInstructions<F, AssignedForeignPoint<F, C, B>>
    for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    /// Returns `p` if `cond = 1` and `q` otherwise.
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        p: &AssignedForeignPoint<F, C, B>,
        q: &AssignedForeignPoint<F, C, B>,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        let is_id = self
            .native_gadget
            .select(layouter, cond, &p.is_id, &q.is_id)?;
        let x = self.base_field_chip().select(layouter, cond, &p.x, &q.x)?;
        let y = self.base_field_chip().select(layouter, cond, &p.y, &q.y)?;

        // This is kind of hacky:
        // When the value of the condition is unknown (during the setup phase)
        // we select the first point, instead of passing an unknown value.
        // In reality, this is equivalent, since in the setup phase the
        // value of the points will be unknown as well.

        // point = p if cond is unknown or 1, q if cond is known and 0
        let a = cond.value().error_if_known_and(|&v| !v);
        let point = if a.is_ok() { p.point } else { q.point };

        Ok(AssignedForeignPoint::<F, C, B> { point, is_id, x, y })
    }
}

impl<F, C, B, S, N> EccInstructions<F, C> for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    type Point = AssignedForeignPoint<F, C, B>;
    type Coordinate = AssignedField<F, C::Base, B>;
    type Scalar = S::Scalar;

    fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
        q: &Self::Point,
    ) -> Result<Self::Point, Error> {
        let r_curve = p.value().zip(q.value()).map(|(p, q)| (p + q));
        let r = self.assign_point_unchecked(layouter, r_curve)?;

        // Define some auxiliary variables.
        let p_or_q_or_r_are_id = self.native_gadget.or(
            layouter,
            &[p.is_id.clone(), q.is_id.clone(), r.is_id.clone()],
        )?;
        let none_is_id = self.native_gadget.not(layouter, &p_or_q_or_r_are_id)?;
        let px_eq_qx = self.base_field_chip().is_equal(layouter, &p.x, &q.x)?;
        let py_eq_qy = self.base_field_chip().is_equal(layouter, &p.y, &q.y)?;
        let px_neq_qx = self.native_gadget.not(layouter, &px_eq_qx)?;
        let py_eq_neg_qy = {
            let py_plus_qy = self.base_field_chip().add(layouter, &p.y, &q.y)?;
            self.base_field_chip().is_zero(layouter, &py_plus_qy)?
        };

        // p = id  =>  r = q.
        self.cond_assert_equal(layouter, &p.is_id, &r, q)?;

        // q = id  =>  r = p.
        self.cond_assert_equal(layouter, &q.is_id, &r, p)?;

        // p = -q  =>  r = id.
        // (The following constraint also encodes <=, which is fine.)
        let p_eq_nq = self
            .native_gadget
            .and(layouter, &[px_eq_qx.clone(), py_eq_neg_qy])?;
        self.native_gadget
            .assert_equal(layouter, &p_eq_nq, &r.is_id)?;

        // If p = q (and we are not in an id case), we double.
        // The following call satisfies the preconditions of [assert_double],
        // since we have set cond = 0 when p or r are the identity.
        let cond = self
            .native_gadget
            .and(layouter, &[px_eq_qx, py_eq_qy, none_is_id.clone()])?;
        self.assert_double(layouter, p, &r, &cond)?;

        // If p != q (and we are not in an id case), we enforce the standard
        // add relation. The following call satisfies the preconditions of
        // [assert_add], since we have set cond = 0 when p, q or r are the
        // the identity, or when p.x = q.x.
        let cond = self.native_gadget.and(layouter, &[px_neq_qx, none_is_id])?;
        self.assert_add(layouter, p, q, &r, &cond)?;

        Ok(r)
    }

    fn double(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        let r_curve = p.value().map(|p| (p + p));
        let r = self.assign_point_unchecked(layouter, r_curve)?;

        // (There are no points of order 2 by assumption.)
        self.native_gadget
            .assert_equal(layouter, &p.is_id, &r.is_id)?;

        // If `p` is not the identity, make sure the double relation is satisfied.
        // Note that the following call to [assert_double] satisfies the required
        // preconditions because we set cond := (p != id) and we have asserted that
        // p = id <=> r = id, so both preconditions of [assert_double] are guaranteed.
        let cond = self.native_gadget.not(layouter, &p.is_id)?;
        self.assert_double(layouter, p, &r, &cond)?;

        Ok(r)
    }

    fn negate(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
    ) -> Result<Self::Point, Error> {
        let neg_y = self.base_field_chip().neg(layouter, &p.y)?;
        let neg_y = self.base_field_chip().normalize(layouter, &neg_y)?;
        Ok(AssignedForeignPoint::<F, C, B> {
            point: -p.point,
            is_id: p.is_id.clone(),
            x: p.x.clone(),
            y: neg_y,
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
        bases: &[AssignedForeignPoint<F, C, B>],
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        const WS: usize = 4;

        // If some of the scalars is known to be 1, remove it (with its base) from the
        // list and simply add it at the end.
        let one: S::Scalar = self
            .scalar_field_chip
            .assign_fixed(layouter, C::Scalar::ONE)?;
        let mut bases_without_coeff = vec![];
        let mut filtered_scalars = vec![];
        let mut filtered_bases = vec![];
        for (scalar, base) in scalars.iter().zip(bases.iter()) {
            if scalar.0 == one {
                bases_without_coeff.push(base.clone());
            } else {
                filtered_scalars.push(scalar.clone());
                filtered_bases.push(base.clone());
            }
        }

        let scalars = filtered_scalars;
        let bases = filtered_bases;

        // If two bases are exactly the same (as symbolic PLONK variables), we
        // deduplicate them by adding their scalars.
        let mut cache_bases: HashMap<AssignedForeignPoint<F, C, B>, (S::Scalar, usize)> =
            HashMap::new();
        let mut unique_bases: Vec<AssignedForeignPoint<F, C, B>> = vec![];
        for (base, scalar) in bases.iter().zip(scalars.iter()) {
            if let Some(acc) = cache_bases.insert(base.clone(), scalar.clone()) {
                let new_scalar = self.scalar_field_chip.add(layouter, &acc.0, &scalar.0)?;
                let new_bound = max(acc.1, scalar.1) + 1;
                cache_bases.insert(base.clone(), (new_scalar, new_bound));
            } else {
                unique_bases.push(base.clone());
            }
        }
        let scalars = unique_bases
            .iter()
            .map(|b| cache_bases.get(b).unwrap().clone())
            .collect::<Vec<_>>();
        let bases = unique_bases;

        // If two scalars are exactly the same (as symbolic PLONK variables), we
        // deduplicate them by adding their bases.
        let mut cache_scalars: HashMap<(S::Scalar, usize), AssignedForeignPoint<F, C, B>> =
            HashMap::new();
        let mut unique_scalars: Vec<(S::Scalar, usize)> = vec![];
        for (scalar, base) in scalars.iter().zip(bases.iter()) {
            if let Some(acc) = cache_scalars.insert(scalar.clone(), base.clone()) {
                let new_acc = self.add(layouter, &acc, base)?;
                cache_scalars.insert(scalar.clone(), new_acc);
            } else {
                unique_scalars.push(scalar.clone());
            }
        }
        let bases = unique_scalars
            .iter()
            .map(|s| cache_scalars.get(s).unwrap().clone())
            .collect::<Vec<_>>();
        let scalars = unique_scalars;

        // In order to support the identity point for some bases, we select in-circuit
        // based on the value of is_id and put a 0 scalar and an arbitrary non-id point
        // (e.g. the generator) for the base when is_id equals 1.

        let mut non_id_bases = vec![];
        let mut scalars_of_non_id_bases = vec![];
        let scalar_chip = self.scalar_field_chip();
        let zero: S::Scalar = scalar_chip.assign_fixed(layouter, C::Scalar::ZERO)?;
        let gen = self.assign_fixed(layouter, C::CryptographicGroup::generator())?;
        for (s, b) in scalars.iter().zip(bases.iter()) {
            let new_b = self.select(layouter, &b.is_id, &gen, b)?;
            let new_s = scalar_chip.select(layouter, &b.is_id, &zero, &s.0)?;
            non_id_bases.push(new_b);
            scalars_of_non_id_bases.push((new_s, s.1));
        }

        // Scalars with a "bad" bound will be split with GLV into 2 scalars with a
        // half-size bound.
        // (The GLV scalars are guaranteed to have half-size.)
        let nb_bits_per_glv_scalar = C::Scalar::NUM_BITS.div_ceil(2) as usize;
        let mut non_glv_scalars = vec![];
        let mut non_glv_bases = vec![];
        let mut glv_scalars = vec![];
        let mut glv_bases = vec![];
        for (s, b) in scalars_of_non_id_bases.iter().zip(non_id_bases.iter()) {
            // We heuristically say a bound is "bad" if it far from NUM_BITS / 2 in the
            // following sense. Note that, ATM, in windowed_msm all sequences
            // are padded with zeros to meet the longest one.
            if s.1 > nb_bits_per_glv_scalar + WS {
                let ((s1, s2), (b1, b2)) = self.glv_split(layouter, &s.0, b)?;
                glv_scalars.push((s1, nb_bits_per_glv_scalar));
                glv_scalars.push((s2, nb_bits_per_glv_scalar));
                glv_bases.push(b1);
                glv_bases.push(b2);
            } else {
                non_glv_scalars.push(s.clone());
                non_glv_bases.push(b.clone());
            }
        }

        let scalars = [glv_scalars, non_glv_scalars].concat();
        let bases = [glv_bases, non_glv_bases].concat();

        let mut decomposed_scalars = vec![];
        for (s, nb_bits_s) in scalars.iter() {
            let s_bits = self.scalar_field_chip().assigned_to_le_chunks(
                layouter,
                s,
                WS,
                Some(nb_bits_s.div_ceil(WS)),
            )?;
            decomposed_scalars.push(s_bits)
        }
        let res = self.windowed_msm::<WS>(layouter, &decomposed_scalars, &bases)?;

        bases_without_coeff
            .iter()
            .try_fold(res, |acc, b| self.add(layouter, &acc, b))
    }

    fn mul_by_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar: C::Scalar,
        base: &Self::Point,
    ) -> Result<Self::Point, Error> {
        // We leverage the existing implementation for `mul_by_u128` when the scalar has
        // 128 bits. Otherwise, we just default to a standard multiplication by an
        // assigned-fixed scalar.
        let scalar_as_big = fe_to_big(scalar);
        if scalar_as_big.bits() <= 128 {
            let n = scalar_as_big
                .to_u64_digits()
                .iter()
                .fold(0u128, |acc, limb| acc + *limb as u128);

            // `mul_by_u128` is incomplete (it cannot take the identity).
            // Change the base in case it is the identity and then change
            // the result back when necessary.
            let id = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;
            let g = self.assign_fixed(layouter, C::CryptographicGroup::generator())?;
            let p = self.select(layouter, &base.is_id, &g, base)?;
            let r = self.mul_by_u128(layouter, n, &p)?;
            return self.select(layouter, &base.is_id, &id, &r);
        }
        let scalar_bits = fe_to_le_bits(&scalar, None)
            .iter()
            .map(|b| self.native_gadget.assign_fixed(layouter, *b))
            .collect::<Result<Vec<_>, Error>>()?;
        self.msm_by_le_bits(layouter, &[scalar_bits], &[base.clone()])
    }

    fn point_from_coordinates(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, C::Base, B>,
        y: &AssignedField<F, C::Base, B>,
    ) -> Result<Self::Point, Error> {
        let is_id = self.native_gadget.assign_fixed(layouter, false)?;
        let cond = self.native_gadget.assign_fixed(layouter, true)?;
        on_curve::assert_is_on_curve::<F, C, B, N>(
            layouter,
            &cond,
            x,
            y,
            self.base_field_chip(),
            &self.config.on_curve_config,
        )?;
        // If from_xy fails, we give the identity as a default value, but note that
        // the above constraints will make the circuit unsatisfiable.
        // This is intentional.
        let point = x
            .value()
            .zip(y.value())
            .map(|(x, y)| C::from_xy(x, y).unwrap_or(C::identity()).into_subgroup());
        Ok(AssignedForeignPoint::<F, C, B> {
            point,
            is_id,
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

impl<F, C, B, S, N> ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    /// Given config creates new chip that implements foreign ECC
    pub fn new(config: &ForeignEccConfig<C>, native_gadget: &N, scalar_field_chip: &S) -> Self {
        let base_field_chip = FieldChip::new(&config.base_field_config, native_gadget);
        Self {
            config: config.clone(),
            native_gadget: native_gadget.clone(),
            base_field_chip,
            scalar_field_chip: scalar_field_chip.clone(),
            tag_cnt: Rc::new(RefCell::new(1)),
        }
    }

    /// The emulated base field chip of this foreign ECC chip
    pub fn base_field_chip(&self) -> &FieldChip<F, C::Base, B, N> {
        &self.base_field_chip
    }

    /// A chip with instructions for the scalar field of this ECC chip.
    pub fn scalar_field_chip(&self) -> &S {
        &self.scalar_field_chip
    }

    /// Configures the foreign ECC chip
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        base_field_config: &FieldChipConfig,
        advice_columns: &[Column<Advice>],
    ) -> ForeignEccConfig<C> {
        // Assert that there is room for the cond_col in the existing columns of the
        // field_chip configurations.
        let cond_col_idx = base_field_config.x_cols.len() + base_field_config.v_cols.len() + 1;
        assert!(advice_columns.len() > cond_col_idx);
        let cond_col = advice_columns[cond_col_idx];
        meta.enable_equality(cond_col);

        let on_curve_config =
            OnCurveConfig::<C>::configure::<F, B>(meta, base_field_config, &cond_col);

        let slope_config = SlopeConfig::<C>::configure::<F, B>(meta, base_field_config, &cond_col);

        let tangent_config =
            TangentConfig::<C>::configure::<F, B>(meta, base_field_config, &cond_col);

        let lambda_squared_config =
            LambdaSquaredConfig::<C>::configure::<F, B>(meta, base_field_config, &cond_col);

        // We prepare a dynamic lookup of points for an efficient multi_select.
        // It counts with a selector, an index column (the selected item) and a table
        // tag (a label to enforce different tables are independent), as well as
        // columns for the limbs of the point coordinates (x,y).
        //
        // Given a list of points `p1, ..., pn` (the table), and a table `tag`, we'll
        // prepare the following set of rows:
        //
        //   | p1.x limbs | p1.y limbs |  0  | tag |
        //   | p2.x limbs | p2.y limbs |  1  | tag |
        //   |     ...    |     ...    | ... | tag |
        //   | pn.x limbs | pn.y limbs | n-1 | tag |
        //
        // This will allow us to then select the `i`-th table point, by witnessing a
        // fresh point `q` and enforcing that:
        //
        //   | q.x limbs | q.y limbs |  i  | tag |
        //
        // is in the lookup table.
        let q_multi_select = meta.complex_selector();
        assert!(advice_columns.len() > 2 * base_field_config.x_cols.len());
        let idx_col_multi_select = *advice_columns.last().unwrap();
        meta.enable_equality(idx_col_multi_select);

        // The tag column should not be shared with other fixed columns since it is used
        // as a separator. It could be done if an extra selector were used as a
        // separator instead.
        let tag_col_multi_select = meta.fixed_column();

        meta.lookup_any("multi_select lookup", |meta| {
            let sel = meta.query_selector(q_multi_select);
            let not_sel = Expression::Constant(F::ONE) - sel.clone();

            // All identities are of the form: `(sel * value, (1 - sel) * value)`.
            // The selector `sel` will only be enabled when "selecting a point" and it will
            // be disabled in all other rows (including those defining a table of points).
            // By multiplying by `(1 - sel)`, we make sure that the rows where the selector
            // is enabled are not part of the table. (Otherwise they would be trivially on
            // the table.)
            // All other rows are part of the lookup table, including those that correspond
            // to unrelated parts of the circuit. This is not a problem, as the tag column
            // (which is fixed) makes sure that the multi_selected point is restricted with
            // respect to the relevant section of the lookup table, thus an adversary cannot
            // leverage unexpected parts of the circuit to bypass this check.
            let mut identities = [idx_col_multi_select]
                .iter()
                .chain(base_field_config.x_cols.iter())
                .chain(base_field_config.z_cols.iter())
                .map(|col| {
                    let val = meta.query_advice(*col, Rotation::cur());
                    (sel.clone() * val.clone(), not_sel.clone() * val)
                })
                .collect::<Vec<_>>();

            // Handle tag indpendently, since it is a fixed column
            let tag = meta.query_fixed(tag_col_multi_select, Rotation::cur());
            identities.push((sel * tag.clone(), not_sel * tag));

            identities
        });

        ForeignEccConfig {
            base_field_config: base_field_config.clone(),
            on_curve_config,
            slope_config,
            tangent_config,
            lambda_squared_config,
            q_multi_select,
            idx_col_multi_select,
            tag_col_multi_select,
        }
    }

    /// Converts a curve point in C : WeierstrassCurve to AssignedForeignPoint.
    /// Used for loading possibly secret points into the circuit.
    /// The point is not asserted (with constraints) to be on the curve.
    /// The point may be the identity.
    fn assign_point_unchecked(
        &self,
        layouter: &mut impl Layouter<F>,
        p: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        let values = p.map(|p| {
            if C::CryptographicGroup::is_identity(&p).into() {
                (C::Base::ZERO, C::Base::ZERO, true)
            } else {
                let coordinates = p
                    .into()
                    .coordinates()
                    .expect("assign_point_unchecked: invalid point given");
                (coordinates.0, coordinates.1, false)
            }
        });
        let x = self
            .base_field_chip()
            .assign(layouter, values.map(|v| v.0))?;
        let y = self
            .base_field_chip()
            .assign(layouter, values.map(|v| v.1))?;
        let is_id = self.native_gadget.assign(layouter, values.map(|v| v.2))?;
        let p = AssignedForeignPoint::<F, C, B> {
            point: p,
            is_id,
            x,
            y,
        };
        Ok(p)
    }

    /// Given `p` and `q`, returns `p + q`.
    ///
    /// This function is incomplete because it is not designed to deal with
    /// the cases where `p` or `q` are the identity nor cases where `p = ±q`
    /// (i.e. `p.x = q.x`).
    /// Consequently, this function will never return the identity point.
    ///
    /// # Preconditions
    ///
    /// - `p != id`
    /// - `q != id`
    /// - `p != q`
    ///
    /// It is the responsibility of the caller to guarantee that all
    /// preconditions are met, this function *does not* necessarily become
    /// unsatisfiable if they are violated.
    ///
    /// # Panics
    ///
    /// If `p = -q`, the system will become unsatisfiable.
    fn incomplete_add(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        q: &AssignedForeignPoint<F, C, B>,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        let r_curve = p.value().zip(q.value()).map(|(p, q)| (p + q));
        let r = self.assign_point_unchecked(layouter, r_curve)?;

        // Assert that r is not the identity.
        self.native_gadget
            .assert_equal(layouter, &p.is_id, &r.is_id)?;

        // The preconditions of [incomplete_add] (and the previous assertion
        // that r != id) guarantee that the following call satisfies all the
        // preconditions of [assert_add].
        // Note that the following call to [assert_add] will make the circuit
        // unsatisfiable if `p = -q`, but that is the intended behavior of
        // [incomplete_add].
        let one = self.native_gadget.assign_fixed(layouter, true)?;
        self.assert_add(layouter, p, q, &r, &one)?;

        Ok(r)
    }

    /// If `cond = 1`, it asserts that `r = 2p`.
    ///
    /// If `cond = 0`, it asserts nothing.
    ///
    /// # Preconditions
    ///
    ///  - `p != id` or `cond = 0`
    ///  - `r != id` or `cond = 0`
    ///
    /// It is the responsibility of the caller to guarantee that the
    /// precondition is met, this function may not become unsatisfiable even if
    /// the precondition is violated.
    fn assert_double(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        r: &AssignedForeignPoint<F, C, B>,
        cond: &AssignedBit<F>,
    ) -> Result<(), Error> {
        // λ = 3 * px^2 / (2 * py)
        let lambda = {
            let lambda_value = p.value().map(|p| {
                if C::CryptographicGroup::is_identity(&p).into() {
                    C::Base::ONE
                } else {
                    let p = p.into().coordinates().unwrap();
                    (C::Base::from(3) * p.0 * p.0) * (C::Base::from(2) * p.1).invert().unwrap()
                }
            });
            self.base_field_chip().assign(layouter, lambda_value)?
        };

        // Assert that λ is the correct slope of the tangent at p.
        tangent::assert_tangent::<F, C, B, N>(
            layouter,
            cond,
            (&p.x, &p.y),
            &lambda,
            self.base_field_chip(),
            &self.config.tangent_config,
        )?;

        // Assert that the value of r.x is correct.
        lambda_squared::assert_lambda_squared(
            layouter,
            cond,
            (&p.x, &p.x, &r.x),
            &lambda,
            self.base_field_chip(),
            &self.config.lambda_squared_config,
        )?;

        // Assert that the slope between p and r is λ (thus r.y is correct).
        //
        // The preconditions of [assert_double] guarantee that the following call
        // satisfies the two first preconditions of [assert_slope].
        // The third precondition of [assert_slope], i.e. p.x != r.x, is also
        // guaranteed because r.x has been constrained to be correct with
        // [assert_lambda_squared], based on a λ that has been constrained to be correct
        // with [assert_tangent]. Given our assumption that there do not exist order-3
        // points (and our precondition that p != id) we have that 2p != ±p, thus
        // r.x != p.x, as desired.
        self.assert_slope(layouter, cond, p, r, true, &lambda)?;

        Ok(())
    }

    /// If `cond = 1`, it asserts that `r = p + q`.
    ///
    /// If `cond = 0`, it asserts nothing.
    ///
    /// This function is incomplete because it is not designed to deal with
    /// the cases where `p` or `q` are the identity nor cases where `p = ±q`
    /// (i.e. `p.x = q.x`).
    ///
    /// # Preconditions
    ///
    /// - `p != id` or `cond = 0`
    /// - `q != id` or `cond = 0`
    /// - `r != id` or `cond = 0`
    /// - `p != q` or `cond = 0`
    ///
    /// It is the responsibility of the caller to guarantee that all
    /// preconditions are met, this function *does not* necessarily become
    /// unsatisfiable if they are violated.
    ///
    /// # Panics
    ///
    /// If `p = -q`, the system will become unsatisfiable.
    /// The official prover will also experiment a runtime error when trying to
    /// invert (q.x - p.x) in that case.
    fn assert_add(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        q: &AssignedForeignPoint<F, C, B>,
        r: &AssignedForeignPoint<F, C, B>,
        cond: &AssignedBit<F>,
    ) -> Result<(), Error> {
        // λ = (qy - py) / (qx - px)
        let lambda = {
            let lambda_value = p.value().zip(q.value()).map(|(p, q)| {
                if p.is_identity().into() || q.is_identity().into() {
                    C::Base::ONE
                } else {
                    let p = p.into().coordinates().unwrap();
                    let q = q.into().coordinates().unwrap();
                    if p.0 == q.0 {
                        C::Base::ONE
                    } else {
                        (q.1 - p.1) * (q.0 - p.0).invert().unwrap()
                    }
                }
            });
            self.base_field_chip().assign(layouter, lambda_value)?
        };

        // Assert that λ is the correct slope between p and q.
        // The preconditions of [assert_add] guarantee that the following call
        // satisfies all the preconditions of [assert_slope]. Indeed, we have:
        //  - `p != id` or `cond = 0`
        //  - `q != id` or `cond = 0`
        //  - `p != q` or `cond = 0`, so precondition (3) of [assert_slope] may be
        //    violated, but only with `cond = 1` and `p = -q`, in which case the call to
        //    [assert_slope] will make the circuit unsatisfiable. This is exactly the
        //    expected behavior of [assert_add].
        self.assert_slope(layouter, cond, p, q, false, &lambda)?;

        // Assert that the value of r.x is correct.
        lambda_squared::assert_lambda_squared(
            layouter,
            cond,
            (&p.x, &q.x, &r.x),
            &lambda,
            self.base_field_chip(),
            &self.config.lambda_squared_config,
        )?;

        // Assert that the slope between p and -r is λ (thus r.y is correct).
        //
        // The preconditions of [assert_add] guarantee that the following call
        // satisfies the two first preconditions of [assert_slope].
        // In general, we will additionally have p.x != r.x, so the third
        // precondition would also be satisfied.
        //
        // Let us carefully analyze the case p.x = r.x.
        // Since r.x has been constrained to be correct with [assert_lambda_squared],
        // based on a λ that has been constrained to be correct with [assert_slope]
        // (between p and q), r.x can be trusted to be the correct value of `(p + q).x`.
        // If p.x = r.x we must thus have p + q = ±p, but the + case is not possible
        // because q != id. Thus we must have p + q = -p (i.e. r = -p).
        // The following call to [assert_slope] would violate the third precondition,
        // which means that -r (mind the minus, since argument negate_q is enabled)
        // will be constrained to equal p, but this is exactly what we needed.
        self.assert_slope(layouter, cond, p, r, true, &lambda)?;

        Ok(())
    }

    /// If `cond = 1`, it asserts that `lambda` is the slope between `p` & `q`:
    ///   `lambda = (qy - py) / (qx - px)`.
    ///
    /// If `cond = 0`, it asserts nothing.
    ///
    /// If `negate_q` is set to `true`, the check is on the slope between
    /// `p` and `-q` instead.
    ///
    /// # Preconditions
    ///
    ///   (1) `p != id` or `cond = 0`
    ///   (2) `q != id` or `cond = 0`
    ///   (3) `p.x != q.x` or `cond = 0`  (non-strict)
    ///
    /// It is the responsibility of the caller to guarantee that preconditions
    /// (1) and (2) are met, this function *does not* become unsatisfiable if
    /// they are violated.
    ///
    /// On the other hand, if precondition (3) is violated, the circuit will
    /// become unsatisfiable unless `p = q` (respectively `p = -q` in case
    /// `negate_q` is enabled).
    fn assert_slope(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        p: &AssignedForeignPoint<F, C, B>,
        q: &AssignedForeignPoint<F, C, B>,
        negate_q: bool,
        lambda: &AssignedField<F, C::Base, B>,
    ) -> Result<(), Error> {
        slope::assert_slope::<F, C, B, N>(
            layouter,
            cond,
            (&p.x, &p.y),
            (&q.x, &q.y, negate_q),
            lambda,
            self.base_field_chip(),
            &self.config.slope_config,
        )
    }

    /// Assigns a region with only 1 row with the limbs of point.x, point.y the
    /// given assigned index and the given table_tag.
    ///
    /// Returns a pair of vectors corresponding to the assigned limbs of the
    /// x coordinate and the y coordinate respectively.
    /// (The assigned index and table_tag are not returned.)
    ///
    /// If `enable_lookup` is set, the selector `q_multi_select` is enabled at
    /// this row and the values of the coordinate limbs ARE NOT copied, but
    /// witnessed freely. It is the responsibility of the caller (with
    /// `enable_lookup = true`) to further restrict these cells, which are an
    /// output of this function.
    #[allow(clippy::type_complexity)]
    fn fill_dynamic_lookup_row(
        &self,
        layouter: &mut impl Layouter<F>,
        point: &AssignedForeignPoint<F, C, B>,
        index: &AssignedNative<F>,
        table_tag: F,
        enable_lookup: bool,
    ) -> Result<(Vec<AssignedNative<F>>, Vec<AssignedNative<F>>), Error> {
        layouter.assign_region(
            || "multi_select table",
            |mut region| {
                if enable_lookup {
                    self.config.q_multi_select.enable(&mut region, 0)?;
                };

                let x_limbs = point.x.limb_values();
                let x_cols = self.config.base_field_config.x_cols.clone();

                // we use z_cols for y_limbs (because y_cols := x_cols)
                let y_limbs = point.y.limb_values();
                let y_cols = self.config.base_field_config.z_cols.clone();

                let idx_col = self.config.idx_col_multi_select;
                let tag_col = self.config.tag_col_multi_select;

                let mut xs = vec![];
                let mut ys = vec![];
                for i in 0..x_limbs.len() {
                    // If the lookup is enabled, we do not copy the limbs into the current row,
                    // because copying imposes restrictions at compile-time (through the permutation
                    // argument). Instead, we want to give freedom to witness any value (from the
                    // table) and we will enforce that it is correct through the lookup check.
                    if enable_lookup {
                        let x_val = x_limbs[i].value().copied();
                        let y_val = y_limbs[i].value().copied();
                        xs.push(region.assign_advice(|| "x", x_cols[i], 0, || x_val)?);
                        ys.push(region.assign_advice(|| "y", y_cols[i], 0, || y_val)?);
                    }
                    // If the lookup is disabled we copy the limbs into the current row.
                    else {
                        xs.push(x_limbs[i].copy_advice(|| "x", &mut region, x_cols[i], 0)?);
                        ys.push(y_limbs[i].copy_advice(|| "y", &mut region, y_cols[i], 0)?);
                    }
                }
                index.copy_advice(|| "x", &mut region, idx_col, 0)?;
                region.assign_fixed(|| "assign tag", tag_col, 0, || Value::known(table_tag))?;

                Ok((xs, ys))
            },
        )
    }

    /// Prepares a lookup table for then applying multi_select.
    /// The i-th assigned point in `point_table` (starting from i = 0) will be
    /// paired with index selector i and the given table tag (a separator
    /// between different tables).
    ///
    /// # Precondition
    ///
    /// We require that all points in the table be different from the identity.
    /// Furthermore, the coordinates of all the points in the tables must have
    /// well-formed bounds.
    /// It is the responsibility of the caller to make sure this is satisfied.
    fn load_multi_select_table(
        &self,
        layouter: &mut impl Layouter<F>,
        point_table: &[AssignedForeignPoint<F, C, B>],
        table_tag: F,
    ) -> Result<(), Error> {
        // assign indices up to point_table.len(), this may not introduce new rows,
        // as we use a cache for assigned constants
        let indices: Vec<AssignedNative<F>> = (0..point_table.len())
            .map(|i| self.native_gadget.assign_fixed(layouter, F::from(i as u64)))
            .collect::<Result<_, Error>>()?;

        for (i, point) in point_table.iter().enumerate() {
            self.fill_dynamic_lookup_row(layouter, point, &indices[i], table_tag, false)?;
        }

        Ok(())
    }

    /// Returns the i-th point in `point_table` where `i` is the value contained
    /// in `selector`.
    ///
    /// # Precondition
    ///
    /// We require that all points in the table be different from the identity.
    /// Furthermore, the coordinates of all the points in the tables must have
    /// well-formed bounds.
    /// It is the responsibility of the caller to make sure this is satisfied.
    ///
    /// # Panics
    ///
    /// If `len(point_table) != 2^len(selector)`.
    fn multi_select(
        &self,
        layouter: &mut impl Layouter<F>,
        selector: &AssignedNative<F>,
        point_table: &[AssignedForeignPoint<F, C, B>],
        table_tag: F,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        // This is a hack, but it's good enough for now.
        let mut selector_idx = 0;
        selector.value().map(|v| {
            let digits = fe_to_big(*v).to_u32_digits();
            let digit = if digits.is_empty() { 0 } else { digits[0] };
            debug_assert!(digits.len() <= 1);
            debug_assert!(digit < point_table.len() as u32);
            selector_idx = digit;
        });

        let selected = point_table[selector_idx as usize].clone();

        // Make sure that the limbs of `selected` appear in the lookup for this table.
        // Only one point can appear next to `selector`, this ensures `selected` is
        // correct.
        let (xs, ys) =
            self.fill_dynamic_lookup_row(layouter, &selected, selector, table_tag, true)?;
        let x = AssignedField::<F, C::Base, B>::from_limbs_unsafe(xs);
        let y = AssignedField::<F, C::Base, B>::from_limbs_unsafe(ys);
        let is_id = self.native_gadget.assign_fixed(layouter, false)?;

        let result = AssignedForeignPoint::<F, C, B> {
            point: selected.point,
            is_id,
            x,
            y,
        };

        Ok(result)
    }

    /// Given a table of `n` assigned points and `k` unassigned points
    /// presumably on the table, it returns the `k` points assigned (in the
    /// same order) and introduces constraints that guarantee that:
    ///   1. All the `k` assigned points are on the table.
    ///   2. All the `k` assigned points correspond to different table entries
    ///      (they are pair-wise different if the table has no duplicates).
    ///
    /// # Precondition
    ///
    /// The `selected` points must be provided in order of occurrence in the
    /// table, otherwise a Synthesis error will be triggered.
    ///
    /// The `table` points cannot be the identity, otherwise the circuit will
    /// become unsatisfiable.
    //
    // This is implemented through dynamic lookups and with a careful design so that
    // the number of constraints is linear in `n` (and not quadratic).
    pub fn k_out_of_n_points(
        &self,
        layouter: &mut impl Layouter<F>,
        table: &[AssignedForeignPoint<F, C, B>],
        selected: &[Value<C::CryptographicGroup>],
    ) -> Result<Vec<AssignedForeignPoint<F, C, B>>, Error> {
        let n = table.len();
        let k = selected.len();
        assert!(k <= n);

        // Just to make sure, although we would have RAM issues otherwise.
        assert!((n as u128) < (1 << (F::NUM_BITS / 2)));

        // Assert that the table points are not the identity.
        table
            .iter()
            .try_for_each(|point| self.assert_non_zero(layouter, point))?;

        // Load the table with a fresh tag, and increase the tag for the next use.
        // This associates index i from 0 to k-1 to the i-th table entry.
        //
        // TODO: Having an independent function for loading the table of points would
        // allow us to share the table if this function is invoked several times on
        // a common table.
        let tag_cnt = *self.tag_cnt.borrow();
        self.tag_cnt.replace(tag_cnt + 1);
        self.load_multi_select_table(layouter, table, F::from(tag_cnt))?;

        // Find the index for each of the `k` selected points.
        let table_values =
            Value::<Vec<C::CryptographicGroup>>::from_iter(table.iter().map(|point| point.value()));
        let selected_idxs = selected
            .iter()
            .map(|point_value| {
                point_value
                    .zip(table_values.clone())
                    .map(|(p, ts)| ts.iter().position(|table_val| *table_val == p).unwrap_or(0))
            })
            .collect::<Vec<_>>();

        // Assert that the selected values were provided in order of occurrence, this is
        // just a sanity check on CPU.
        Value::<Vec<usize>>::from_iter(selected_idxs.clone())
            .error_if_known_and(|idxs| idxs.iter().zip(idxs.iter().skip(1)).any(|(i, j)| i >= j))?;

        // Witness the selected indices.
        let assigned_selected_idxs = selected_idxs
            .clone()
            .iter()
            .map(|i_value| {
                self.native_gadget
                    .assign(layouter, i_value.map(|i| F::from(i as u64)))
            })
            .collect::<Result<Vec<AssignedNative<F>>, Error>>()?;

        // Introduce constraints that guarantee that all the assigned indices are
        // different. For this, we will compute the delta between indices and enforce
        // that they are all in the range [1, l] where l is a small bound, greater than
        // or equal to `n` for completeness, that prevents wrap-arounds.
        // Choosing `l` as a power of 2 will make range-checks slightly more efficient.
        let l = BigUint::one() << BigUint::from(n).bits();
        assigned_selected_idxs
            .iter()
            .zip(assigned_selected_idxs.iter().skip(1))
            .try_for_each(|(idx, next_idx)| {
                let diff_minus_one = self.native_gadget.linear_combination(
                    layouter,
                    &[(F::ONE, next_idx.clone()), (-F::ONE, idx.clone())],
                    -F::ONE,
                )?;
                self.native_gadget
                    .assert_lower_than_fixed(layouter, &diff_minus_one, &l)
            })?;

        // Witness the selected points while asserting they are on the table.
        let mut unwrapped_selected_idxs = vec![0; k];
        selected_idxs.iter().enumerate().for_each(|(i, idx)| {
            idx.map(|j| unwrapped_selected_idxs[i] = j);
        });
        let selected_points = unwrapped_selected_idxs
            .iter()
            .zip(assigned_selected_idxs.iter())
            .map(|(i, selected_idx)| {
                let (xs, ys) = self.fill_dynamic_lookup_row(
                    layouter,
                    &table[*i],
                    selected_idx,
                    F::from(tag_cnt),
                    true,
                )?;
                let x = AssignedField::<F, C::Base, B>::from_limbs_unsafe(xs);
                let y = AssignedField::<F, C::Base, B>::from_limbs_unsafe(ys);
                let is_id = self.native_gadget.assign_fixed(layouter, false)?;
                Ok(AssignedForeignPoint::<F, C, B> {
                    point: table[*i].value(),
                    is_id,
                    x,
                    y,
                })
            })
            .collect::<Result<Vec<_>, Error>>()?;

        Ok(selected_points)
    }

    /// Assert that the given two points have a different x-coordinate.
    ///
    /// WARNING: This function is sound but not complete.
    /// Concretely, if p.x and q.x are different, but when interpreted as
    /// integers they are equal modulo the native modulus, this assertion will
    /// fail.
    fn incomplete_assert_different_x(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignPoint<F, C, B>,
        q: &AssignedForeignPoint<F, C, B>,
    ) -> Result<(), Error> {
        assert!(p.x.is_well_formed());
        assert!(q.x.is_well_formed());

        // Modular integers have at most two representations in limbs form,
        // because m <= B^(nb_limbs) < 2m, where m is the emulated modulus and B is
        // the base of representation.
        // In other words, an integer x may be represented with limbs x_i such that
        // sum_x = x or sum_x = x + m, where sum_x := 1 + sum_i B^i x_i.
        //
        // In order to check that x and y are different modulo m, it is enough to check
        // that (sum_x - sum_y) does not fall in one of the values {0, m, -m}.
        //
        // We will enforce this check modulo the native modulus only. This is
        // incomplete, but sound.

        let native_gadget = &self.native_gadget;
        let base = big_to_fe::<F>(BigUint::one() << B::LOG2_BASE);
        let m = bigint_to_fe::<F>(&p.x.modulus());

        let mut terms = vec![];
        let mut coeff = F::ONE;
        for (px_i, qx_i) in p.x.limb_values().iter().zip(q.x.limb_values().iter()) {
            terms.push((coeff, px_i.clone()));
            terms.push((-coeff, qx_i.clone()));
            coeff *= base;
        }

        let diff = native_gadget.linear_combination(layouter, &terms, F::ZERO)?;

        // We assert that `diff not in {0, m, -m}`.
        // TODO: the following could be done more efficiently if we had dedicated
        // instructions in the native gadget.
        native_gadget.assert_non_zero(layouter, &diff)?;
        native_gadget.assert_not_equal_to_fixed(layouter, &diff, m)?;
        native_gadget.assert_not_equal_to_fixed(layouter, &diff, -m)
    }

    /// Returns `n * p`, where `n` is a constant `u128`.
    ///
    /// # Precondition
    ///
    /// - `p != id`
    ///
    /// # Panics
    ///
    /// This function does not panic if the precondition is violated, it is the
    /// responsibility of the caller to make sure it is satisfied.
    fn mul_by_u128(
        &self,
        layouter: &mut impl Layouter<F>,
        n: u128,
        p: &AssignedForeignPoint<F, C, B>,
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        if n == 0 {
            return self.assign_fixed(layouter, C::CryptographicGroup::identity());
        };

        // Assert that (n : u128) is smaller than ORDER / 2.
        // This condition allows us to use incomplete addition in the loop below.
        assert!(129 < C::Scalar::NUM_BITS);

        // Double-and-add (starting from the LSB)

        let mut res = None;

        // tmp will encode (2^i p) on every iteration, to be added (selectively) to res.
        let mut tmp = p.clone();

        // We iterate over the bits of n.
        let mut n = n;
        while n > 0 {
            // In order to safetly use [incomplete_add] here, we need to show
            // that these three preconditions are met when res != None:
            //   (1) res != id
            //   (2) tmp != id
            //   (3) res.x != tmp.x   (i.e. res != ±tmp)
            //
            // Note that p != id holds by assumption.
            // Also, note that on the i-th iteration (counting from i = 0),
            // at this point we have:
            //    res := None or Some(k p) with 0 < k < 2^i
            //    tmp := 2^i p
            //
            // (1) & (2) hold because all non-identity points have Scalar.ORDER order by
            //           assumption, and 2^i is smaller than ORDER on every iteration.
            // (3) holds because otherwise we would have k p = ± 2^i p with 0 < k < 2^i.
            //     Thus (k ∓ 2^i) p = id, which means that (k ∓ 2^i) is
            //     a multiple of ORDER, however this is not possible as:
            //        (i) k ∓ 2^i != 0 because 0 < k < 2^i
            //       (ii) k - 2^i > -2^i > -ORDER    (because i < 128 < |ORDER|)
            //      (iii) k + 2^i < 2^(i+1) < ORDER  (because i+1 < 129 < |ORDER|)
            if n % 2 != 0 {
                res = match res {
                    None => Some(tmp.clone()),
                    Some(acc) => Some(self.incomplete_add(layouter, &acc, &tmp)?),
                };
            }
            n >>= 1;

            if n > 0 {
                tmp = self.double(layouter, &tmp)?
            }
        }

        Ok(res.unwrap())
    }

    /// Curve multi-scalar multiplication.
    /// This implementation uses a windowed double-and-add with `WS` window
    /// size.
    /// The scalars are represented by little-endian sequences of chunks in the
    /// range [0, 2^WS), represented by an AssignedNative value.
    ///
    /// # Preconditions
    ///
    /// (1) `scalars[i][j] in [0, 2^WS)` for every `i, j`.
    /// (2) `base_i != identity` for every `i`
    ///
    /// # Panics
    ///
    /// It is the responsibility of the caller to meet precondition (1).
    ///
    /// If precondition (2) is violated, the system will become unsatisfiable.
    ///
    /// Panics also if `scalars.len() != bases.len()`.
    fn windowed_msm<const WS: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[Vec<AssignedNative<F>>],
        bases: &[AssignedForeignPoint<F, C, B>],
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        if scalars.len() != bases.len() {
            panic!("msm: `scalars` and `bases` should have the same length")
        };

        if scalars.is_empty() {
            return self.assign_fixed(layouter, C::CryptographicGroup::identity());
        }

        // Assert that none of the bases is the identity point
        for p in bases.iter() {
            self.native_gadget
                .assert_equal_to_fixed(layouter, &p.is_id, false)?
        }

        // Pad all the sequences of chunks to have the same length.
        // TODO: This is not strictly necessary, we could be more efficient if some
        // sequences are shorter. For now we do not do this, as it is highly involved,
        // and not very compatible with our random accumulation trick below.
        let zero: AssignedNative<F> = self.native_gadget.assign_fixed(layouter, F::ZERO)?;
        let max_len = scalars.iter().fold(0, |m, chunks| max(m, chunks.len()));
        let mut padded_scalars = vec![];
        for s_bits in scalars.iter() {
            // Pad with zeros up to length `padded_len`.
            let mut s_bits = s_bits.to_vec();
            s_bits.resize(max_len, zero.clone());
            // Reverse to get big-endian order, for the double-and-add.
            let rev_s_bits = s_bits.into_iter().rev().collect::<Vec<_>>();
            padded_scalars.push(rev_s_bits)
        }

        // Sample `r`, a random point that allows us to use incomplete addition in the
        // double-and-add loop.
        // The value of `r` can be chosen by the prover (who will choose it uniformly
        // at random for statistical completeness) and this is not a problem for
        // soundness.
        //
        // Let l := bases.len(), the initial double-and-add accumulator will be
        // acc := l * r. On every double-and-add iteration i, we will double WS times
        // and then, for every j in [l], conditionally add (kj_i * base_j - α)
        // or (-α), depending on the relevant segment, kj_i, of scalars_j at
        // that iteration, where α := (2^WS - 1) r. After this, the total randomness in
        // the accumulator becomes:
        //   2^WS (l * r) - l * α = 2^WS (l * r) - l * (2^WS - 1) r = l * r.
        // This makes the total randomness invariant (l * r) at the beginning of every
        // iteration.
        //
        // To finish the computation we will thus need to subtract l * r, which will
        // be done in-circuit.
        //
        // FIXME: Can we directly sample a random C point? (The following is also fine.)
        // TODO: Maybe we should check that the sampled r will not have a completeness
        // problem. The probability should be overwhelming, but if the bad event
        // happened, the proof would fail. We could sample another r here instead.
        let r_dlog = C::Scalar::random(OsRng);
        let r_unassigned = C::CryptographicGroup::mul(C::CryptographicGroup::generator(), r_dlog);
        let r: AssignedForeignPoint<F, C, B> = self.assign(layouter, Value::known(r_unassigned))?;

        // Assert the chosen r is not the identity point
        self.base_field_chip
            .native_gadget
            .assert_equal_to_fixed(layouter, &r.is_id, false)?;

        let l_times_r = self.mul_by_u128(layouter, bases.len() as u128, &r)?;
        let alpha = self.mul_by_u128(layouter, (1u128 << WS) - 1, &r)?;
        let neg_alpha = self.negate(layouter, &alpha)?;

        // Get the global tag counter and increase it with |bases|
        let tag_cnt = *self.tag_cnt.clone().borrow();
        self.tag_cnt.replace(tag_cnt + bases.len() as u64);

        // Compute table, [-α, p-α, 2p-α, ..., (2^WS-1)p-α] for every p in bases.
        let mut tables = vec![];
        for (i, p) in bases.iter().enumerate() {
            self.incomplete_assert_different_x(layouter, &alpha, p)?;
            let mut acc = neg_alpha.clone();
            let mut p_table = vec![acc.clone()];
            for _ in 1..(1usize << WS) {
                // In order to safetly use [incomplete_add] here, we need to ensure that:
                //   (1) acc != id
                //   (2) p != id
                //   (3) acc != p
                //
                // (1) holds because acc is initially -α, which cannot be the identity,
                //     because r is not and we have asserted 2^WS < Scalar::ORDER. Then,
                //     acc is always the result of incomplete_add, which is guaranteed to
                //     not produce the identity.
                // (2) holds because all the bases were asserted to not be the identity.
                // (3) holds because acc is initially -α, which has been asserted to not
                //     share the x coordinate with p, so the first iteration is fine.
                //     In other iterations, acc will be of the form kp-α for some
                //     k = 1,...,(2^WS-2). Note that (k-1)p-α cannot be the identity as it is
                //     the result of a previous call to [incomplete_add], thus kp-α != p, so
                //     the third precondition of [incomplete_add] is met.
                acc = self.incomplete_add(layouter, &acc, p)?;

                assert!(acc.x.is_well_formed() && acc.y.is_well_formed());
                p_table.push(acc.clone())
            }
            self.load_multi_select_table(layouter, &p_table, F::from(tag_cnt + i as u64))?;
            tables.push(p_table)
        }

        let nb_iterations = max_len;
        let mut acc = l_times_r.clone();

        for i in 0..nb_iterations {
            for _ in 0..WS {
                acc = self.double(layouter, &acc)?;
            }
            for j in 0..bases.len() {
                let window = &padded_scalars[j][i];
                let addend =
                    self.multi_select(layouter, window, &tables[j], F::from(tag_cnt + j as u64))?;
                // In order to safetly use [incomplete_add] here, we need to ensure that:
                //   (1) acc != id
                //   (2) addend != id
                //   (3) acc != addend
                //
                // (1) holds because acc is the result of doubling a non-identity point
                //     (this is guaranteed because in the first iteration acc != id, and in
                //     any other iteration acc is the result of incomplete_add, which is
                //     guaranteed to not produce the identity.)
                // (2) holds because all the points in the tables are different from the
                //     identity, as asserted above (in the construction of the tables).
                // (3) is asserted here, this assertion will not hinder completeness except
                //     with negligible probability (over the choice of α).
                self.incomplete_assert_different_x(layouter, &acc, &addend)?;
                acc = self.incomplete_add(layouter, &acc, &addend)?;
            }
        }

        let r_correction = self.negate(layouter, &l_times_r)?;
        self.add(layouter, &acc, &r_correction)
    }

    /// Same as [self.msm], but the scalars are represented as little-endian
    /// sequences of bits. The length of the bit sequences can be arbitrary
    /// and possibly distinct between terms.
    ///
    /// # Preconditions
    ///
    /// - `base_i != identity` for every `i`
    ///
    /// # Panics
    ///
    /// - If `scalars.len() != bases.len()`.
    /// - If the precondition is violated, the circuit will become
    ///   unsatisfiable.
    pub fn msm_by_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[Vec<AssignedBit<F>>],
        bases: &[AssignedForeignPoint<F, C, B>],
    ) -> Result<AssignedForeignPoint<F, C, B>, Error> {
        // Windows of size 4 seem to be optimal for 256-bit scalar fields,
        // because k = 4 minimizes 2^k + 256 / k.
        // TODO: Pick window size based on C::Scalar::NUM_BITS?
        const WS: usize = 4;
        let scalars = scalars
            .iter()
            .map(|bits| {
                bits.chunks(WS)
                    .map(|chunk| self.native_gadget.assigned_from_le_bits(layouter, chunk))
                    .collect::<Result<Vec<_>, Error>>()
            })
            .collect::<Result<Vec<_>, Error>>()?;
        self.windowed_msm::<WS>(layouter, &scalars, bases)
    }

    /// Takes a (potentially full-size) assigned scalar `x` and an assigned
    /// point `P` and returns 2 assigned scalars `(x1, x2)` and 2 assigned
    /// points `(P1, P2)` that are guaranteed (with circuit constraints) to
    /// satisfy `x P = x1 P1 + x2 P2`.
    ///
    /// The returned scalars `(x1, x2)` are half-size, although this is not
    /// enforced with constraints here, so they can be decomposed into
    /// C::Scalar::NUM_BITS / 2 bits without completeness errors.
    #[allow(clippy::type_complexity)]
    fn glv_split(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar: &S::Scalar,
        base: &AssignedForeignPoint<F, C, B>,
    ) -> Result<
        (
            (S::Scalar, S::Scalar),
            (AssignedForeignPoint<F, C, B>, AssignedForeignPoint<F, C, B>),
        ),
        Error,
    > {
        let zeta_base = C::BASE_ZETA;
        let zeta_scalar = C::SCALAR_ZETA;

        let decomposed = scalar
            .value()
            .map(|x| glv_scalar_decomposition(&x, &zeta_scalar));
        let s1_value = decomposed.map(|((s1, _), _)| s1);
        let x1_value = decomposed.map(|((_, x1), _)| x1);
        let s2_value = decomposed.map(|(_, (s2, _))| s2);
        let x2_value = decomposed.map(|(_, (_, x2))| x2);

        let x1 = self.scalar_field_chip.assign(layouter, x1_value)?;
        let x2 = self.scalar_field_chip.assign(layouter, x2_value)?;

        let s1 = self.native_gadget.assign(layouter, s1_value)?;
        let s2 = self.native_gadget.assign(layouter, s2_value)?;

        let neg_x1 = self.scalar_field_chip.neg(layouter, &x1)?;
        let neg_x2 = self.scalar_field_chip.neg(layouter, &x2)?;

        let signed_x1 = self.scalar_field_chip.select(layouter, &s1, &x1, &neg_x1)?;
        let signed_x2 = self.scalar_field_chip.select(layouter, &s2, &x2, &neg_x2)?;

        // Assert that scalar = signed_x1 + zeta * signed_x2
        let x = self.scalar_field_chip.linear_combination(
            layouter,
            &[(C::Scalar::ONE, signed_x1), (zeta_scalar, signed_x2)],
            C::Scalar::ZERO,
        )?;
        self.scalar_field_chip.assert_equal(layouter, &x, scalar)?;

        let zeta_x = self
            .base_field_chip
            .mul_by_constant(layouter, &base.x, zeta_base)?;
        let zeta_p = AssignedForeignPoint::<F, C, B> {
            point: base.point.map(|p| {
                if p.is_identity().into() {
                    p
                } else {
                    let coordinates = p.into().coordinates().unwrap();
                    let zeta_x = zeta_base * coordinates.0;
                    C::from_xy(zeta_x, coordinates.1).unwrap().into_subgroup()
                }
            }),
            is_id: base.is_id.clone(),
            x: zeta_x,
            y: base.y.clone(),
        };

        let neg_zeta_p = self.negate(layouter, &zeta_p)?;
        let neg_base = self.negate(layouter, base)?;

        let p1 = self.select(layouter, &s1, base, &neg_base)?;
        let p2 = self.select(layouter, &s2, &zeta_p, &neg_zeta_p)?;

        Ok(((x1, x2), (p1, p2)))
    }
}

#[derive(Clone, Debug)]
#[cfg(any(test, feature = "testing"))]
/// Configuration used to implement `FromScratch` for the ForeignEcc chip. This
/// should only be used for testing.
pub struct ForeignEccTestConfig<F, C, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    S: ScalarFieldInstructions<F> + FromScratch<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F> + FromScratch<F>,
{
    native_gadget_config: <N as FromScratch<F>>::Config,
    scalar_field_config: <S as FromScratch<F>>::Config,
    ff_ecc_config: ForeignEccConfig<C>,
}

#[cfg(any(test, feature = "testing"))]
impl<F, C, B, S, N> FromScratch<F> for ForeignEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: WeierstrassCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F> + FromScratch<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F> + FromScratch<F>,
{
    type Config = ForeignEccTestConfig<F, C, S, N>;

    fn new_from_scratch(config: &ForeignEccTestConfig<F, C, S, N>) -> Self {
        let native_gadget = <N as FromScratch<F>>::new_from_scratch(&config.native_gadget_config);
        let scalar_field_chip =
            <S as FromScratch<F>>::new_from_scratch(&config.scalar_field_config);
        ForeignEccChip::new(&config.ff_ecc_config, &native_gadget, &scalar_field_chip)
    }

    fn load_from_scratch(
        layouter: &mut impl Layouter<F>,
        config: &ForeignEccTestConfig<F, C, S, N>,
    ) {
        <N as FromScratch<F>>::load_from_scratch(layouter, &config.native_gadget_config);
        <S as FromScratch<F>>::load_from_scratch(layouter, &config.scalar_field_config)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> ForeignEccTestConfig<F, C, S, N> {
        let native_gadget_config =
            <N as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let scalar_field_config =
            <S as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let nb_advice_cols = nb_foreign_ecc_chip_columns::<F, C, B, S>();
        let advice_columns = (0..nb_advice_cols)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();
        let base_field_config = FieldChip::<F, C::Base, B, N>::configure(meta, &advice_columns);
        let ff_ecc_config =
            ForeignEccChip::<F, C, B, S, N>::configure(meta, &base_field_config, &advice_columns);
        ForeignEccTestConfig {
            native_gadget_config,
            scalar_field_config,
            ff_ecc_config,
        }
    }
}

#[cfg(test)]
mod tests {
    use blstrs::{G1Projective as BlsG1, Fq as BlsScalar};
    use group::Group;
    use halo2curves::{
        pasta::{vesta::Point as VestaCurve, Fp as VestaScalar, Fq as PallasScalar},
        secp256k1::Secp256k1,
    };

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
        ($mod:ident, $op:ident, $native:ty, $curve:ty, $scalar_field:ty, $name:expr) => {
            $mod::tests::$op::<
                $native,
                AssignedForeignPoint<$native, $curve, MultiEmulationParams>,
                ForeignEccChip<
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
                test_generic!($mod, $op, BlsScalar, Secp256k1, EmulatedField<BlsScalar, Secp256k1>, "foreign_ecc_secp");
                test_generic!($mod, $op, PallasScalar, Secp256k1, EmulatedField<PallasScalar, Secp256k1>, "");
                test_generic!($mod, $op, VestaScalar, Secp256k1, EmulatedField<VestaScalar, Secp256k1>, "");

                // a test of Vesta over itself, where the scalar field is native
                test_generic!($mod, $op, VestaScalar, VestaCurve, Native<VestaScalar>, "foreign_ecc_vesta_over_vesta");

                // a test of BLS over itself, where the scalar field is native
                test_generic!($mod, $op, BlsScalar, BlsG1, Native<BlsScalar>, "foreign_ecc_bls_over_bls");
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

    macro_rules! ecc_test {
        ($op:ident, $native:ty, $curve:ty, $scalar_field:ty, $name:expr) => {
            ecc::tests::$op::<
                $native,
                $curve,
                ForeignEccChip<
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
                ecc_test!($op, BlsScalar, Secp256k1, EmulatedField<BlsScalar, Secp256k1>, "foreign_ecc_secp");
                ecc_test!($op, PallasScalar, Secp256k1, EmulatedField<PallasScalar, Secp256k1>, "");
                ecc_test!($op, VestaScalar, Secp256k1, EmulatedField<VestaScalar, Secp256k1>, "");

                // a test of Vesta over itself, where the scalar field is native
                ecc_test!($op, VestaScalar, VestaCurve, Native<VestaScalar>, "foreign_ecc_vesta_over_vesta");

                // a test of BLS over itself, where the scalar field is native
                ecc_test!($op, BlsScalar, BlsG1, Native<BlsScalar>, "foreign_ecc_bls_over_bls");
            }
        };
    }

    ecc_tests!(test_add);
    ecc_tests!(test_double);
    ecc_tests!(test_negate);
    ecc_tests!(test_msm);
    ecc_tests!(test_msm_by_bounded_scalars);
    ecc_tests!(test_mul_by_constant);
    ecc_tests!(test_coordinates);
}
