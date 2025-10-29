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
#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::ConstraintSystem;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::Error,
};
#[cfg(any(test, feature = "testing"))]
use {crate::testing_utils::Sampleable, rand::RngCore};

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;
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
        ArithInstructions, AssertionInstructions, AssignmentInstructions,
        DecompositionInstructions, EccInstructions, NativeInstructions, PublicInputInstructions,
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

impl<F, C, B, S, N> AssertionInstructions<F, AssignedForeignEdwardsPoint<F, C, B>>
    for ForeignEdwardsEccChip<F, C, B, S, N>
where
    F: PrimeField,
    C: EdwardsCurve,
    B: FieldEmulationParams<F, C::Base>,
    S: ScalarFieldInstructions<F>,
    S::Scalar: InnerValue<Element = C::Scalar>,
    N: NativeInstructions<F>,
{
    fn assert_equal(
        &self,
        _layouter: &mut impl Layouter<F>,
        _x: &AssignedForeignEdwardsPoint<F, C, B>,
        _y: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn assert_equal_to_fixed(
        &self,
        _layouter: &mut impl Layouter<F>,
        _x: &AssignedForeignEdwardsPoint<F, C, B>,
        _constant: <AssignedForeignEdwardsPoint<F, C, B> as InnerValue>::Element,
    ) -> Result<(), Error> {
        todo!()
    }

    fn assert_not_equal(
        &self,
        _layouter: &mut impl Layouter<F>,
        _x: &AssignedForeignEdwardsPoint<F, C, B>,
        _y: &AssignedForeignEdwardsPoint<F, C, B>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn assert_not_equal_to_fixed(
        &self,
        _layouter: &mut impl Layouter<F>,
        _x: &AssignedForeignEdwardsPoint<F, C, B>,
        _constant: <AssignedForeignEdwardsPoint<F, C, B> as InnerValue>::Element,
    ) -> Result<(), Error> {
        todo!()
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

    fn negate(
        &self,
        _layouter: &mut impl Layouter<F>,
        _p: &Self::Point,
    ) -> Result<Self::Point, Error> {
        todo!()
    }

    fn msm(
        &self,
        _layouter: &mut impl Layouter<F>,
        _scalars: &[Self::Scalar],
        _bases: &[Self::Point],
    ) -> Result<Self::Point, Error> {
        todo!()
    }

    fn mul_by_constant(
        &self,
        _layouter: &mut impl Layouter<F>,
        _scalar: <C>::Scalar,
        _base: &Self::Point,
    ) -> Result<Self::Point, Error> {
        todo!()
    }

    fn point_from_coordinates(
        &self,
        _layouter: &mut impl Layouter<F>,
        _x: &Self::Coordinate,
        _y: &Self::Coordinate,
    ) -> Result<Self::Point, Error> {
        todo!()
    }

    fn x_coordinate(&self, _point: &Self::Point) -> Self::Coordinate {
        todo!()
    }

    fn y_coordinate(&self, _point: &Self::Point) -> Self::Coordinate {
        todo!()
    }

    fn base_field(&self) -> &impl DecompositionInstructions<F, Self::Coordinate> {
        self.base_field_chip()
    }
}

#[derive(Clone, Debug)]
#[cfg(any(test, feature = "testing"))]
/// Configuration used to implement `FromScratch` for the ForeignEcc chip. This
/// should only be used for testing.
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

    //  config: ForeignEdwardsEccConfig<C>,
    //     native_gadget: N,
    //     base_field_chip: FieldChip<F, C::Base, B, N>,
    //     scalar_field_chip: S,

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
        let native_gadget_config =
            <N as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let scalar_field_config =
            <S as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let nb_advice_cols = nb_foreign_ecc_chip_columns::<F, C, B, S>();
        let advice_columns = (0..nb_advice_cols).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let base_field_config = FieldChip::<F, C::Base, B, N>::configure(meta, &advice_columns);
        let ff_ecc_config = ForeignWeierstrassEccChip::<F, C, B, S, N>::configure(
            meta,
            &base_field_config,
            &advice_columns,
        );
        ForeignEccTestConfig {
            native_gadget_config,
            scalar_field_config,
            ff_ecc_config,
        }
    }
}

#[cfg(test)]
mod tests {
    use group::Group;
    use halo2curves::{
        pasta::{vesta::Point as VestaCurve, Fp as VestaScalar, Fq as PallasScalar},
        secp256k1::Secp256k1,
    };
    use midnight_curves::{Fq as BlsScalar, G1Projective as BlsG1, JubjubExtended, JubjubSubgroup};

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
                test_generic!($mod, $op, BlsScalar, JubjubExtended, EmulatedField<BlsScalar, JubjubExtended>, "foreign_ecc_secp");
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
                ForeignWeierstrassEccChip<
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
