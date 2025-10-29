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

//! TODO: Doc the chip.

use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use ff::{Field, PrimeField};
use group::Group;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::Error,
};
#[cfg(any(test, feature = "testing"))]
use {crate::testing_utils::Sampleable, rand::RngCore};

use crate::{
    ecc::curves::{CircuitCurve, EdwardsCurve},
    field::{
        foreign::{
            field_chip::{FieldChip, FieldChipConfig},
            params::FieldEmulationParams,
        },
        AssignedNative,
    },
    instructions::{
        ArithInstructions, AssignmentInstructions, NativeInstructions, PublicInputInstructions,
        ScalarFieldInstructions, ZeroInstructions,
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
    S::Scalar: InnerValue<Element = C::Scalar>,
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
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    /// The emulated base field chip of this foreign ECC chip
    pub fn base_field_chip(&self) -> &FieldChip<F, C::Base, B, N> {
        &self.base_field_chip
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

impl<F, C, B> Eq for AssignedForeignEdwardsPoint<F, C, B>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
{
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
    S::Scalar: InnerValue<Element = C::Scalar>,
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

impl<F, C, B, S, N> AssignmentInstructions<F, AssignedForeignEdwardsPoint<F, C, B>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        // Recreate twisted edwards curve equation over foreign
        // field Fq with x,y in Fq emulated over
        //
        // a*x^2 + y^2 - 1 - d*x^2 *y^2 = 0
        //
        let base_chip = self.base_field_chip();

        let (valx, valy) = value
            .map(|v| v.into().coordinates().expect("assign: valid curve point"))
            .unzip();

        let x: AssignedField<F, <C as CircuitCurve>::Base, B> = base_chip.assign(layouter, valx)?;
        let y: AssignedField<F, <C as CircuitCurve>::Base, B> = base_chip.assign(layouter, valy)?;

        let x_x = base_chip.mul(layouter, &x, &x, None)?;
        let y_y = base_chip.mul(layouter, &y, &y, None)?;

        // Computes a*x^2 + y^2 - 1 - d*x^2*y^2
        let id = base_chip.add_and_mul(
            layouter,
            (C::A, &x_x),
            (C::Base::ONE, &y_y),
            (C::Base::ZERO, &x_x),
            -C::Base::ONE,
            -C::D,
        )?;

        base_chip.assert_zero(layouter, &id)?;

        // Add subgroup check
        // TODO

        Ok(AssignedForeignEdwardsPoint { point: value, x, y })
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
                .expect("assign fixed unchecked: valid curve point")
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
    S::Scalar: InnerValue<Element = C::Scalar>,
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
        // Given our optimized way of constraining a point as public input, we
        // cannot optimize the direct assignment as PI. We just compose `assign`
        // with `constrain_as_public_input`.
        let point = self.assign(layouter, value)?;
        self.constrain_as_public_input(layouter, &point)?;
        Ok(point)
    }
}

impl<F, C, B, S, N> ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F> + PublicInputInstructions<F, AssignedBit<F>>,
{
    fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
        q: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        // Addition law on twisted edwards curve:
        //      P    +    Q
        // = (Px,Py) + (Qx,Qy)
        // = ( (Px*Qy + Py*Qx)/(1+d*Px*Py*Qx*Qy) ,
        //              (Py*Qy - a*Px*Qx)/(1-d*Px*Py*Qx*Qy) )
        // = (Rx, Ry) = R
        let base_chip = self.base_field_chip();
        let px_py = base_chip.mul(layouter, &p.x, &p.y, None)?;
        let qx_qy = base_chip.mul(layouter, &q.x, &q.y, None)?;
        let py_qy = base_chip.mul(layouter, &p.y, &q.y, None)?;
        let px_qx = base_chip.mul(layouter, &p.x, &q.x, None)?;
        let a_px_qx = base_chip.mul_by_constant(layouter, &px_qx, C::A)?;
        let d_px_py_qx_qy = base_chip.mul(layouter, &px_py, &qx_qy, Some(C::D))?;
        let neg_d_px_py_qx_qy = base_chip.neg(layouter, &d_px_py_qx_qy)?;

        let px_qy = base_chip.mul(layouter, &p.x, &q.y, None)?;
        let py_qx = base_chip.mul(layouter, &p.y, &q.x, None)?;

        // Rx coordinate
        let num1 = base_chip.add(layouter, &px_qy, &py_qx)?;
        let den1 = base_chip.add_constant(layouter, &d_px_py_qx_qy, C::Base::ONE)?;
        let rx = base_chip.div(layouter, &num1, &den1)?;

        // Ry coordinate
        let num2 = base_chip.sub(layouter, &py_qy, &a_px_qx)?;
        let den2 = base_chip.add_constant(layouter, &neg_d_px_py_qx_qy, C::Base::ONE)?;
        let ry = base_chip.div(layouter, &num2, &den2)?;

        let point = rx
            .value()
            .zip(ry.value())
            .map(|(x, y)| C::from_xy(x, y).expect("valid coordinates").into_subgroup());

        Ok(AssignedForeignEdwardsPoint {
            point,
            x: rx,
            y: ry,
        })
    }

    fn double(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<AssignedForeignEdwardsPoint<F, C, B>, Error> {
        self.add(layouter, p, p)
    }
}
