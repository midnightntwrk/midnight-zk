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
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    hash::{Hash, Hasher},
    rc::Rc,
};

use ff::{Field, PrimeField};
use group::Group;
use midnight_curves::{
    curve25519::{Curve25519, Curve25519Subgroup},
    ff_ext::Legendre,
};
#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::Instance;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
};
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::{FromScratch, Sampleable},
    rand::RngCore,
};

use super::common::{
    add_1bit_scalar_bases, configure_multi_select_lookup, fill_dynamic_lookup_row, msm_preprocess,
};
use crate::{
    ecc::{
        curves::{CircuitCurve, EdwardsCurve},
        foreign::gates::edwards::addition::{self, AdditionConfig},
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
    types::{AssignedBit, AssignedByte, AssignedField, InnerConstants, InnerValue, Instantiable},
    CircuitField,
};

/// Number of columns required by the custom gates of this chip.
pub fn nb_foreign_edwards_chip_columns<F, C, B>() -> usize
where
    F: CircuitField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
    // Here we only account for the columns that this chip requires for its own
    // custom gates.
    // The outer `+ 1` corresponds to the advice column for the index of
    // `multi_select`.
    B::NB_LIMBS as usize + std::cmp::max(B::NB_LIMBS as usize, 1 + B::moduli().len()) + 1
}

/// Foreign Edwards ECC configuration.
#[derive(Clone, Debug)]
pub struct ForeignEdwardsEccConfig<C>
where
    C: EdwardsCurve,
{
    base_field_config: FieldChipConfig,
    addition_config: AdditionConfig<C>,
    // Dynamic lookup columns for windowed MSM table selection.
    q_multi_select: Selector,
    idx_col_multi_select: Column<Advice>,
    tag_col_multi_select: Column<Fixed>,
}

/// Cache of assigned constant points to their known group element values.
type ConstantPointCache<F, C, B> = Rc<
    RefCell<HashMap<AssignedForeignEdwardsPoint<F, C, B>, <C as CircuitCurve>::CryptographicGroup>>,
>;

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
    /// Per-chip tag counter for dynamic lookup tables (tag 0 is reserved).
    tag_cnt: Rc<RefCell<u64>>,
    /// Cache mapping assigned constant points to their known values.
    constant_cache: ConstantPointCache<F, C, B>,
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
        meta: &mut ConstraintSystem<F>,
        base_field_config: &FieldChipConfig,
        advice_columns: &[Column<Advice>],
        fixed_columns: &[Column<Fixed>],
        nb_parallel_range_checks: usize,
        max_bit_len: u32,
    ) -> ForeignEdwardsEccConfig<C> {
        assert!(C::A.legendre() == 1);
        assert!(C::D.legendre() == -1);

        let addition_config = AdditionConfig::<C>::configure::<F, B>(
            meta,
            base_field_config,
            fixed_columns[0],
            nb_parallel_range_checks,
            max_bit_len,
        );

        let (q_multi_select, idx_col_multi_select, tag_col_multi_select) =
            configure_multi_select_lookup(meta, advice_columns, base_field_config);

        ForeignEdwardsEccConfig {
            base_field_config: base_field_config.clone(),
            addition_config,
            q_multi_select,
            idx_col_multi_select,
            tag_col_multi_select,
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
            tag_cnt: Rc::new(RefCell::new(1)),
            constant_cache: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    /// The emulated base field chip of this foreign Edwards ECC chip.
    pub fn base_field_chip(&self) -> &FieldChip<F, C::Base, B, N> {
        &self.base_field_chip
    }

    /// Returns the constant value of `point` if it was created via
    /// `assign_fixed`, or `None` otherwise.
    pub fn as_known_constant(
        &self,
        point: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Option<C::CryptographicGroup> {
        self.constant_cache.borrow().get(point).copied()
    }

    /// A chip with instructions for the scalar field of this ECC chip.
    pub fn scalar_field_chip(&self) -> &S {
        &self.scalar_field_chip
    }
}

impl<F, B, S, N> ForeignEdwardsEccChip<F, Curve25519, B, S, N>
where
    F: CircuitField,
    B: FieldEmulationParams<F, <Curve25519 as CircuitCurve>::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = <Curve25519 as CircuitCurve>::ScalarField>,
    N: NativeInstructions<F>,
{
    /// In-circuit compression of a given subgroup point into canonical
    /// little-endian bytes.
    ///
    /// Let p = 2^255 -19 be the base field modulus.
    ///
    /// A curve point (x,y), with coordinates in the range 0 <= x,y < p, is
    /// encoded as follows. First, encode the y-coordinate as a little-endian
    /// array of 32 bytes. The most significant bit of the final byte (i.e., the
    /// most significant byte) is always zero. To form the encoding of the
    /// point, copy the least significant bit of the x-coordinate to the
    /// most significant bit of the final byte of the y-coordinate.
    ///
    /// # Returns
    /// An array [`AssignedByte<F>`; 32] constrained to represent a canonical
    /// encoding.
    pub fn to_canonical_compressed_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        point: &AssignedForeignEdwardsPoint<F, Curve25519, B>,
    ) -> Result<[AssignedByte<F>; 32], Error> {
        // Decomposition into (LE) bytes enforces canonicity.
        let mut y_bytes = self.base_field_chip().assigned_to_le_bytes(
            layouter,
            &self.y_coordinate(point),
            None,
        )?;

        let x_bits = self.base_field_chip().assigned_to_le_bits(
            layouter,
            &self.x_coordinate(point),
            Some(255),
            true,
        )?;

        // Encode the sign bit of x (= x mod 2, i.e., the least significant bit of x)
        // into the most significant byte of y: MSB = MSB of y + LSBit of x * 128.
        //
        // (This is safe: y <= p - 1 = 2^255 - 19 - 1, which means MSB of y <= 127;
        // hence, adding 128 causes _no_ overflow.)
        let last_byte: AssignedNative<F> = self.native_gadget.linear_combination(
            layouter,
            &[
                (F::ONE, y_bytes[y_bytes.len() - 1].clone().into()),
                (F::from(128), x_bits[0].clone().into()),
            ],
            F::ZERO,
        )?;

        let last = y_bytes.len() - 1;
        y_bytes[last] = self.native_gadget.convert_unsafe(layouter, &last_byte)?;

        Ok(y_bytes.try_into().expect("exactly 32 bytes"))
    }

    /// In-circuit decompression of little-endian canonical compressed bytes.
    ///
    /// Decoding a point, given as an array of 32 bytes, works as follows: The
    /// caller of this function provides the claimed decoded point as a
    /// witness. The function loads this point into the circuit,
    /// calls [Self::to_canonical_compressed_bytes] and checks if the
    /// resulting byte encoding matches the provided byte encoding.
    ///
    /// # Returns
    /// An [AssignedForeignEdwardsPoint] constrained to lie in the subgroup.
    ///
    /// # Unsatisfiable Circuit
    /// If the given array of [AssignedByte] is a non-canonical encoding of the
    /// point provided by [`Value<Curve25519Subgroup>`].
    pub fn from_canonical_compressed_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        compressed_bytes: &[AssignedByte<F>; 32],
        value: Value<Curve25519Subgroup>,
    ) -> Result<AssignedForeignEdwardsPoint<F, Curve25519, B>, Error> {
        let point = self.assign(layouter, value)?;
        let canonical_bytes = self.to_canonical_compressed_bytes(layouter, &point)?;
        compressed_bytes.iter().zip(canonical_bytes.iter()).try_for_each(
            |(com_byte, can_byte)| self.native_gadget.assert_equal(layouter, com_byte, can_byte),
        )?;

        Ok(point)
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
        let (x, y) = (*p).into().coordinates().expect("Edwards coordinates cannot fail");
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
            .map(|v| v.into().coordinates().expect("Edwards coordinates cannot fail"))
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
        let x_sq = base_chip.mul(layouter, x, x, None)?;
        let y_sq = base_chip.mul(layouter, y, y, None)?;
        let d_xy_sq = base_chip.mul(layouter, &x_sq, &y_sq, Some(C::D))?;
        let lhs = base_chip.linear_combination(
            layouter,
            &[(C::A, x_sq), (C::Base::ONE, y_sq)],
            -C::Base::ONE,
        )?;

        // Assert a*x^2 + y^2 - 1 = d*x^2*y^2
        base_chip.assert_equal(layouter, &lhs, &d_xy_sq)
    }

    /// Adds an assigned point `p` to a constant point `q_val`. Cheaper than
    /// general `add` because the constant coordinates turn emulated `mul`
    /// calls into `mul_by_constant` calls.
    fn add_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        q_val: C::CryptographicGroup,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        // If both operands are known constants, compute off-circuit.
        if let Some(pv) = self.as_known_constant(p) {
            return self.assign_fixed(layouter, pv + q_val);
        }

        let (qx, qy) = q_val.into().coordinates().expect("Edwards coordinates cannot fail");

        let base_chip = self.base_field_chip();

        let r_value = p.value().map(|pv| pv + q_val);
        let r = self.assign_point_unchecked(layouter, r_value)?;

        let px_qx = base_chip.mul_by_constant(layouter, &p.x, qx)?;
        let py_qy = base_chip.mul_by_constant(layouter, &p.y, qy)?;
        let px_qy = base_chip.mul_by_constant(layouter, &p.x, qy)?;
        let py_qx = base_chip.mul_by_constant(layouter, &p.y, qx)?;
        let neg_a_px_qx = base_chip.mul_by_constant(layouter, &px_qx, -C::A)?;
        let d_px_py_qx_qy = base_chip.mul(layouter, &px_qx, &py_qy, Some(C::D))?;

        // Rx * (1 + d * Px * Py * Qx * Qy) = (Px * Qy + Py * Qx)
        addition::assert_addition_coordinate(
            layouter,
            &r.x,
            &px_qy,
            &py_qx,
            &d_px_py_qx_qy,
            false,
            base_chip,
            &self.config.addition_config,
        )?;

        // Ry * (1 - d * Px * Py * Qx * Qy) = (Py * Qy - a * Px * Qx)
        addition::assert_addition_coordinate(
            layouter,
            &r.y,
            &py_qy,
            &neg_a_px_qx,
            &d_px_py_qx_qy,
            true,
            base_chip,
            &self.config.addition_config,
        )?;

        Ok(AssignedForeignEdwardsPoint {
            point: r_value,
            x: r.x,
            y: r.y,
        })
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
        p_value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        // Let h be the cofactor of the subgroup.
        //
        // Instead of witnessing P, we witness an h-root Q, and return h * Q.
        // This guarantess that the returned point is in the desired subgroup.
        let cofactor = C::ScalarField::from_u128(C::COFACTOR);
        let q =
            self.assign_point_unchecked(layouter, p_value.map(|p| p * cofactor.invert().unwrap()))?;

        self.assert_on_curve(layouter, &q.x, &q.y)?;
        self.mul_by_constant(layouter, cofactor, &q)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let (x, y) = constant.into().coordinates().expect("Edwards coordinates cannot fail");
        let x = self.base_field_chip().assign_fixed(layouter, x)?;
        let y = self.base_field_chip().assign_fixed(layouter, y)?;

        let p = AssignedForeignEdwardsPoint::<F, C, B> {
            point: Value::known(constant),
            x,
            y,
        };
        self.constant_cache.borrow_mut().insert(p.clone(), constant);
        Ok(p)
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
        let coordinates = constant.into().coordinates().expect("Edwards coordinates cannot fail");
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
        let coordinates = constant.into().coordinates().expect("Edwards coordinates cannot fail");
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
        let point = p.point.zip(q.point).zip(cond.value()).map(|((p, q), b)| if b { p } else { q });
        let x = self.base_field_chip().select(layouter, cond, &p.x, &q.x)?;
        let y = self.base_field_chip().select(layouter, cond, &p.y, &q.y)?;
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
        if p == q {
            return self.double(layouter, p);
        }

        // If one operand is constant, use the cheaper `add_constant` path.
        if let Some(qv) = self.as_known_constant(q) {
            return self.add_constant(layouter, p, qv);
        }
        if let Some(pv) = self.as_known_constant(p) {
            return self.add_constant(layouter, q, pv);
        }

        // Complete addition law on twisted Edwards curve:
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

        let px_qx = base_chip.mul(layouter, &p.x, &q.x, None)?;
        let py_qy = base_chip.mul(layouter, &p.y, &q.y, None)?;
        let px_qy = base_chip.mul(layouter, &p.x, &q.y, None)?;
        let py_qx = base_chip.mul(layouter, &p.y, &q.x, None)?;
        let neg_a_px_qx = base_chip.mul_by_constant(layouter, &px_qx, -C::A)?;
        let d_px_py_qx_qy = base_chip.mul(layouter, &px_qx, &py_qy, Some(C::D))?;

        // Constraint for Rx coordinate
        // Rx * (1 + d * Px * Py * Qx * Qy) = (Px * Qy + Py * Qx)
        addition::assert_addition_coordinate(
            layouter,
            &r.x,
            &px_qy,
            &py_qx,
            &d_px_py_qx_qy,
            false,
            base_chip,
            &self.config.addition_config,
        )?;

        // Constraint for Ry coordinate
        // Ry * (1 - d * Px * Py * Qx * Qy) = (Py * Qy - a * Px * Qx)
        addition::assert_addition_coordinate(
            layouter,
            &r.y,
            &py_qy,
            &neg_a_px_qx,
            &d_px_py_qx_qy,
            true,
            base_chip,
            &self.config.addition_config,
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
        if let Some(pv) = self.as_known_constant(p) {
            return self.assign_fixed(layouter, pv + pv);
        }

        // Complete doubling on twisted Edwards curve.
        // (see https://eprint.iacr.org/2008/013.pdf)
        //
        // P + P = R
        // <=>
        // (Px, Py) + (Px, Py) = (Rx, Ry)
        // <=>
        // Rx = (Px * Py +     Py * Px) / (1 + d * Px * Py * Px * Py)
        // Ry = (Py * Py - a * Px * Px) / (1 - d * Px * Py * Px * Py)
        // <=> (denominators are non-zero)
        // Rx * (1 + d * Px^2 * Py^2) = 2 * Px * Py
        // Ry * (1 - d * Px^2 * Py^2) = Py^2 - a * Px^2
        //
        // Since P is on the curve: a * Px^2 + Py^2 = 1 + d * Px^2 * Py^2,
        // we substitute w = a * Px^2 + Py^2 - 1 for d * Px^2 * Py^2,
        // saving one emulated multiplication.

        let base_chip = self.base_field_chip();

        let r_value = p.value().map(|p| p + p);
        let r = self.assign_point_unchecked(layouter, r_value)?;

        let px_sq = base_chip.mul(layouter, &p.x, &p.x, None)?;
        let py_sq = base_chip.mul(layouter, &p.y, &p.y, None)?;
        let px_py = base_chip.mul(layouter, &p.x, &p.y, None)?;

        let neg_a_px_sq = base_chip.mul_by_constant(layouter, &px_sq, -C::A)?;

        // w = d * Px^2 * Py^2 = a * Px^2 + Py^2 - 1  (on-curve relation)
        let w = base_chip.linear_combination(
            layouter,
            &[(C::A, px_sq), (C::Base::ONE, py_sq.clone())],
            -C::Base::ONE,
        )?;

        // Rx * (1 + w) = 2 * Px * Py
        addition::assert_addition_coordinate(
            layouter,
            &r.x,
            &px_py,
            &px_py,
            &w,
            false,
            base_chip,
            &self.config.addition_config,
        )?;

        // Ry * (1 - w) = Py^2 - a * Px^2
        addition::assert_addition_coordinate(
            layouter,
            &r.y,
            &py_sq,
            &neg_a_px_sq,
            &w,
            true,
            base_chip,
            &self.config.addition_config,
        )?;

        Ok(AssignedForeignEdwardsPoint {
            point: r_value,
            x: r.x,
            y: r.y,
        })
    }

    fn negate(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
    ) -> Result<Self::Point, Error> {
        if let Some(pv) = self.as_known_constant(p) {
            return self.assign_fixed(layouter, -pv);
        }

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
        let scalars = scalars
            .iter()
            .map(|s| (s.clone(), C::ScalarField::NUM_BITS as usize))
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
            panic!("Number of scalars and points should be the same.")
        }
        let scalar_chip = self.scalar_field_chip();

        let (scalars, bases, bases_with_1bit_scalar) =
            msm_preprocess(self, scalar_chip, layouter, scalars, bases)?;

        // Decompose scalars to bits with tight bound, then chunk into windows.
        const WS: usize = 4;
        let scalar_windows: Vec<Vec<AssignedNative<F>>> = scalars
            .iter()
            .map(|(s, num_bits)| {
                let bits = scalar_chip.assigned_to_le_bits(layouter, s, Some(*num_bits), true)?;
                bits.chunks(WS)
                    .map(|chunk| self.native_gadget.assigned_from_le_bits(layouter, chunk))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        let res = self.windowed_msm::<WS>(layouter, &scalar_windows, &bases)?;

        // Add 1-bit scalar bases.
        add_1bit_scalar_bases(layouter, self, scalar_chip, &bases_with_1bit_scalar, res)
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

        // If the base is a known constant, compute off-circuit.
        if let Some(base_val) = self.as_known_constant(base) {
            return self.assign_fixed(layouter, base_val * scalar);
        }

        let scalar_bits = scalar.to_bits_le(None);
        let mut p = base.clone();
        let mut res = None;

        // Simple double-and-add
        for (i, b) in scalar_bits.iter().enumerate() {
            if *b {
                res = match res {
                    None => Some(p.clone()),
                    Some(acc) => Some(self.add(layouter, &acc, &p)?),
                }
            }
            // The doubling in the last iteration is not needed
            if i + 1 < scalar_bits.len() {
                p = self.double(layouter, &p)?;
            }
        }

        Ok(res.unwrap_or(self.assign_fixed(layouter, C::CryptographicGroup::identity())?))
    }

    fn point_from_coordinates(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, C::Base, B>,
        y: &AssignedField<F, C::Base, B>,
    ) -> Result<Self::Point, Error> {
        let p_value = x.value().zip(y.value()).map_with_result(|(x, y)| {
            C::from_xy(x, y)
                .map(|p| p.into_subgroup())
                .ok_or(Error::Synthesis("invalid coordinates".into()))
        })?;

        let p = self.assign(layouter, p_value)?;

        self.base_field_chip.assert_equal(layouter, x, &self.x_coordinate(&p))?;
        self.base_field_chip.assert_equal(layouter, y, &self.y_coordinate(&p))?;

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
        let p = self.assign_point_unchecked(layouter, value)?;
        self.assert_on_curve(layouter, &p.x, &p.y)?;
        Ok(p)
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
    /// Table of precomputed points, where `table[i] = i * base`.
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
    /// Builds table `[0*base, 1*base, ..., (2^WS-1)*base]`.
    /// Uses doubling for even indices (`table[2k] = double(table[k])`) and
    /// addition for odd indices (`table[2k+1] = add(table[2k], base)`),
    /// which is cheaper than a linear chain of additions.
    fn precompute<const WS: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        base: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<PrecomputedTable<F, C, B, WS>, Error> {
        let identity = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;
        let mut table = vec![identity, base.clone()];
        for i in 2..1 << WS {
            let entry = if i % 2 == 0 {
                self.double(layouter, &table[i / 2])?
            } else {
                self.add(layouter, &table[i - 1], base)?
            };
            table.push(entry);
        }
        Ok(PrecomputedTable { table })
    }

    /// Delegates to [`fill_dynamic_lookup_row`] with this chip's columns.
    #[allow(clippy::type_complexity)]
    fn fill_dynamic_lookup_row(
        &self,
        layouter: &mut impl Layouter<F>,
        point: &AssignedForeignEdwardsPoint<F, C, B>,
        index: &AssignedNative<F>,
        table_tag: F,
        enable_lookup: bool,
    ) -> Result<(Vec<AssignedNative<F>>, Vec<AssignedNative<F>>), Error> {
        fill_dynamic_lookup_row(
            layouter,
            &point.x.limb_values(),
            &point.y.limb_values(),
            index,
            &self.config.base_field_config.x_cols,
            &self.config.base_field_config.z_cols, // z_cols used for y (y_cols == x_cols)
            self.config.idx_col_multi_select,
            self.config.tag_col_multi_select,
            self.config.q_multi_select,
            table_tag,
            enable_lookup,
        )
    }

    /// Loads a precomputed point table into the dynamic lookup.  Entry `i` is
    /// paired with index `i` and the given `table_tag`.
    fn load_multi_select_table(
        &self,
        layouter: &mut impl Layouter<F>,
        point_table: &[AssignedForeignEdwardsPoint<F, C, B>],
        table_tag: F,
    ) -> Result<(), Error> {
        for (i, point) in point_table.iter().enumerate() {
            let index = self.native_gadget.assign_fixed(layouter, F::from(i as u64))?;
            self.fill_dynamic_lookup_row(layouter, point, &index, table_tag, false)?;
        }
        Ok(())
    }

    /// Returns `point_table[selector]` using the dynamic lookup.
    ///
    /// The table must have been loaded via [`Self::load_multi_select_table`]
    /// with the same `table_tag`.
    fn multi_select(
        &self,
        layouter: &mut impl Layouter<F>,
        selector: &AssignedNative<F>,
        point_table: &[AssignedForeignEdwardsPoint<F, C, B>],
        table_tag: F,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        let mut selector_idx = 0usize;
        selector.value().map(|v| {
            let digits = v.to_biguint().to_u32_digits();
            let digit = if digits.is_empty() { 0 } else { digits[0] };
            debug_assert!(digits.len() <= 1);
            debug_assert!((digit as usize) < point_table.len());
            selector_idx = digit as usize;
        });

        let selected = point_table[selector_idx].clone();

        let (xs, ys) =
            self.fill_dynamic_lookup_row(layouter, &selected, selector, table_tag, true)?;
        let x = AssignedField::<F, C::Base, B>::from_limbs_unsafe(xs);
        let y = AssignedField::<F, C::Base, B>::from_limbs_unsafe(ys);

        Ok(AssignedForeignEdwardsPoint::<F, C, B> {
            point: selected.point,
            x,
            y,
        })
    }

    /// Windowed interleaved MSM over pre-chunked scalars. Each scalar is a
    /// sequence of WS-bit window values (native field elements). Shares the
    /// doubling chain across all bases. Horner evaluation. Scalars may have
    /// different numbers of windows; short scalars are skipped in high windows.
    /// Point selection uses a dynamic-lookup table.
    fn windowed_msm<const WS: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[Vec<AssignedNative<F>>],
        bases: &[AssignedForeignEdwardsPoint<F, C, B>],
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        assert_eq!(scalars.len(), bases.len());

        if bases.is_empty() {
            return self.assign_fixed(layouter, C::CryptographicGroup::identity());
        }

        // Number of windows per scalar.
        let num_windows: Vec<usize> = scalars.iter().map(|s| s.len()).collect();
        let max_num_windows = *num_windows.iter().max().unwrap();

        // Precompute tables for each base and load them into the dynamic lookup.
        let tag_cnt = *self.tag_cnt.borrow();
        self.tag_cnt.replace(tag_cnt + bases.len() as u64);
        debug_assert!(F::NUM_BITS > 64);

        let mut tables = vec![];
        for (i, base) in bases.iter().enumerate() {
            let table = self.precompute::<WS>(layouter, base)?;
            self.load_multi_select_table(layouter, &table.table, F::from(tag_cnt + i as u64))?;
            tables.push(table);
        }

        let mut res = self.assign_fixed(layouter, C::CryptographicGroup::identity())?;
        for w in (0..max_num_windows).rev() {
            // Skip doubling in the most-significant window.
            if w < max_num_windows - 1 {
                for _ in 0..WS {
                    res = self.double(layouter, &res)?;
                }
            }
            for (i, (windows, nw)) in scalars.iter().zip(&num_windows).enumerate() {
                // Skip scalars that have no windows in this position.
                if w >= *nw {
                    continue;
                }
                let addend = self.multi_select(
                    layouter,
                    &windows[w],
                    &tables[i].table,
                    F::from(tag_cnt + i as u64),
                )?;
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
        advice_columns: &mut Vec<Column<Advice>>,
        fixed_columns: &mut Vec<Column<Fixed>>,
        instance_columns: &[Column<Instance>; 2],
    ) -> ForeignEdwardsEccTestConfig<F, C, S, N> {
        use crate::field::foreign::nb_field_chip_columns;

        let native_gadget_config = <N as FromScratch<F>>::configure_from_scratch(
            meta,
            advice_columns,
            fixed_columns,
            instance_columns,
        );
        let scalar_field_config = <S as FromScratch<F>>::configure_from_scratch(
            meta,
            advice_columns,
            fixed_columns,
            instance_columns,
        );
        let nb_advice_cols = nb_field_chip_columns::<F, C::Base, B>();
        while advice_columns.len() < nb_advice_cols {
            advice_columns.push(meta.advice_column());
        }
        let nb_parallel_range_checks = 4;
        let max_bit_len = 8;
        let base_field_config = FieldChip::<F, C::Base, B, N>::configure(
            meta,
            &advice_columns[..nb_advice_cols],
            nb_parallel_range_checks,
            max_bit_len,
        );
        let ff_ecc_config = ForeignEdwardsEccChip::<F, C, B, S, N>::configure(
            meta,
            &base_field_config,
            advice_columns,
            fixed_columns,
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
    use group::{Group, GroupEncoding};
    use midnight_curves::{curve25519::Curve25519, BlsScalar};
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
    ecc_tests!(test_coordinates);

    #[test]
    fn test_assert_on_curve() {
        run_test_assert_on_curve::<Curve25519>();
    }

    /// Negative tests for `assert_on_curve`. Positive cases (identity,
    /// generator, random points) are covered by the generic `test_assign`.
    fn run_test_assert_on_curve<C>()
    where
        C: EdwardsCurve,
        C::Base: Legendre,
        MultiEmulationParams: FieldEmulationParams<BlsScalar, C::Base>
            + FieldEmulationParams<BlsScalar, C::ScalarField>,
    {
        fn assert_not_on_curve<C: EdwardsCurve>(x: C::Base, y: C::Base)
        where
            C::Base: Legendre,
            MultiEmulationParams: FieldEmulationParams<BlsScalar, C::Base>
                + FieldEmulationParams<BlsScalar, C::ScalarField>,
        {
            let circuit = OnCurveCheckCircuit::<C> { x, y };
            let prover = MockProver::run(&circuit, vec![vec![], vec![]])
                .expect("proof generation should not fail");
            assert!(prover.verify().is_err());
        }

        let mut rng = ChaCha8Rng::seed_from_u64(0x0);

        // Random point with y offset by 1
        let point = C::CryptographicGroup::random(&mut rng);
        let (x, y) = point.into().coordinates().expect("valid curve point");

        assert_not_on_curve::<C>(x, y + C::Base::ONE);
        assert_not_on_curve::<C>(C::Base::ONE, C::Base::ONE);
        assert_not_on_curve::<C>(C::Base::ZERO, C::Base::ZERO);
    }

    type EdwardsChip<C> = ForeignEdwardsEccChip<
        F,
        C,
        MultiEmulationParams,
        FieldChip<F, <C as CircuitCurve>::ScalarField, MultiEmulationParams, Native<F>>,
        Native<F>,
    >;

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
            EdwardsChip::<C>::configure_from_scratch(
                meta,
                &mut vec![],
                &mut vec![],
                &[committed, instance],
            )
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

    /// Test circuit that calls `from_canonical_compressed_bytes` on a
    /// given byte array together with the claimed subgroup point.
    ///
    /// The proof succeeds if and only if the byte array is the canonical
    /// encoding of the subgroup point.
    #[derive(Clone, Debug)]
    struct FromCompressedBytesCheckCircuit {
        point: Curve25519Subgroup,
        bytes: [u8; 32],
    }

    impl Circuit<F> for FromCompressedBytesCheckCircuit {
        type Config = <EdwardsChip<Curve25519> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed = meta.instance_column();
            let instance = meta.instance_column();
            EdwardsChip::<Curve25519>::configure_from_scratch(
                meta,
                &mut vec![],
                &mut vec![],
                &[committed, instance],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = EdwardsChip::<Curve25519>::new_from_scratch(&config);

            let byte_cells: [AssignedByte<F>; 32] = self
                .bytes
                .iter()
                .map(|b| chip.native_gadget.assign(&mut layouter, Value::known(*b)))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .expect("exactly 32 bytes");

            let _ = chip.from_canonical_compressed_bytes(
                &mut layouter,
                &byte_cells,
                Value::known(self.point),
            )?;

            chip.load_from_scratch(&mut layouter)
        }
    }

    fn run_test_compressed_bytes(point: Curve25519Subgroup, bytes: [u8; 32], should_accept: bool) {
        let circuit = FromCompressedBytesCheckCircuit { point, bytes };
        let prover = MockProver::run(&circuit, vec![vec![], vec![]])
            .expect("proof generation should not fail");
        assert_eq!(prover.verify().is_ok(), should_accept);
    }

    #[test]
    fn test_compressed_bytes() {
        // Canonical LE encoding of the identity with y = 1 and sign_x = 0.
        let mut canonical = [0; 32];
        canonical[0] = 1;
        run_test_compressed_bytes(Curve25519Subgroup::identity(), canonical, true);

        // Non-canonical LE encoding of the identity with y = 2^255 - 18 and sign_x = 0.
        let mut non_canonical = [0xff_u8; 32];
        non_canonical[0] = 0xee;
        non_canonical[31] = 0x7f;
        run_test_compressed_bytes(Curve25519Subgroup::identity(), non_canonical, false);

        // Non-canonical LE encoding of the identity with y = 1 and sign_x = 1.
        let mut non_canonical_with_sign = canonical;
        non_canonical_with_sign[31] = 0x80;
        run_test_compressed_bytes(
            Curve25519Subgroup::identity(),
            non_canonical_with_sign,
            false,
        );

        // Canonical LE encoding of the subgroup generator.
        let g = Curve25519Subgroup::generator();
        run_test_compressed_bytes(g, Curve25519::from(g).to_bytes(), true);

        // Canonical LE encoding of a random subgroup point.
        let mut rng = ChaCha8Rng::seed_from_u64(0x7374727564656C);
        let p = Curve25519Subgroup::random(&mut rng);
        run_test_compressed_bytes(p, Curve25519::from(p).to_bytes(), true);
    }
}
