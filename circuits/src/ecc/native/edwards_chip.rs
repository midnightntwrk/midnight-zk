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

//! Generic Chip implementation for the ECC Instructions over twisted Edwards
//! curves. Indeed, this chip only implements partially generic twisted Edwards
//! curve, i.e. with a = -1, which is the case of Jubjub.

use ecc::EccInstructions;
use ff::{Field, PrimeField};
use group::Group;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};
#[cfg(any(test, feature = "testing"))]
use {
    crate::field::decomposition::chip::P2RDecompositionConfig,
    crate::testing_utils::{FromScratch, Sampleable},
    midnight_proofs::plonk::Instance,
    rand::RngCore,
};

use crate::{
    ecc::curves::{CircuitCurve, EdwardsCurve},
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    instructions::*,
    types::{AssignedBit, AssignedNative, InnerConstants, InnerValue, Instantiable},
    utils::{
        util::{fe_to_le_bits, le_bits_to_field_elem},
        ComposableChip,
    },
};

/// The number of advice columns used by the EccChip.
pub const NB_EDWARDS_COLS: usize = 9;

/// A twisted Edwards curve point represented in affine (x, y) coordinates, the
/// identity represented as (0, 1).
#[derive(Clone, Debug)]
pub struct AssignedNativePoint<C: CircuitCurve> {
    x: AssignedNative<C::Base>,
    y: AssignedNative<C::Base>,
}

impl<C: CircuitCurve> InnerValue for AssignedNativePoint<C> {
    type Element = C::CryptographicGroup;

    fn value(&self) -> Value<Self::Element> {
        self.x
            .value()
            .zip(self.y.value())
            .map(|(x, y)| C::from_xy(*x, *y).expect("non-id").into_subgroup())
    }
}

impl<C: CircuitCurve> AssignedNativePoint<C> {
    // To ensure type safety, we expect all assigned values to belong to the
    // subgroup. However, for Multi-Table Commitment (MTC), we may be working with
    // points on the full curve rather than strictly within the subgroup.
    //
    // As a result, we cannot generically treat the inner type of the curve using
    // the `InnerValue` trait, as this trait assumes subgroup membership by directly
    // unwrapping the `into_subgroup` function.
    //
    // Certain internal functions, such as `assign_double_add` and
    // `assign_cond_add`, operate on points that may lie on the full curve (not
    // only the subgroup). To handle these cases safely, we use this auxiliary
    // closure to avoid unintentional assumptions about subgroup membership.
    /// Return the value of the assigned point
    fn curve_value(&self) -> Value<C> {
        self.x
            .value()
            .zip(self.y.value())
            .map(|(x, y)| C::from_xy(*x, *y).expect("Valid coordinates."))
    }
}

impl<C: CircuitCurve> Instantiable<C::Base> for AssignedNativePoint<C> {
    fn as_public_input(p: &C::CryptographicGroup) -> Vec<C::Base> {
        let point: C = (*p).into();
        let coordinates = point.coordinates().expect("non-id");
        vec![coordinates.0, coordinates.1]
    }
}

impl<C: EdwardsCurve> InnerConstants for AssignedNativePoint<C> {
    fn inner_zero() -> C::CryptographicGroup {
        C::CryptographicGroup::identity()
    }

    fn inner_one() -> Self::Element {
        C::CryptographicGroup::generator()
    }
}

/// Scalars are represented as a vector of assigned bits in little endian.
#[derive(Clone, Debug)]
pub struct ScalarVar<C: CircuitCurve>(Vec<AssignedBit<C::Base>>);

impl<C: CircuitCurve> InnerValue for ScalarVar<C> {
    type Element = C::Scalar;

    fn value(&self) -> Value<Self::Element> {
        let bools = self.0.iter().map(|b| b.value());
        let value_bools: Value<Vec<bool>> = Value::from_iter(bools);
        value_bools.map(|le_bits| le_bits_to_field_elem::<C::Scalar>(&le_bits))
    }
}

impl<C: EdwardsCurve> Instantiable<C::Base> for ScalarVar<C> {
    fn as_public_input(element: &C::Scalar) -> Vec<C::Base> {
        // We aggregate the bits while they fit in a single `C::Base` value.
        let nb_bits_per_batch = C::Base::NUM_BITS as usize - 1;
        fe_to_le_bits(element, Some(C::Base::NUM_BITS as usize))
            .chunks(nb_bits_per_batch)
            .map(le_bits_to_field_elem)
            .collect()
    }
}

impl<C: EdwardsCurve> InnerConstants for ScalarVar<C> {
    fn inner_zero() -> C::Scalar {
        C::Scalar::ZERO
    }
    fn inner_one() -> C::Scalar {
        C::Scalar::ONE
    }
}

#[cfg(any(test, feature = "testing"))]
impl<C: EdwardsCurve> Sampleable for ScalarVar<C> {
    fn sample_inner(rng: impl RngCore) -> C::Scalar {
        C::Scalar::random(rng)
    }
}

/// [`EccConfig`], which uses [`NB_EDWARDS_COLS`] advice columns.
#[derive(Clone, Debug)]
pub struct EccConfig {
    pub(crate) q_double: Selector,
    pub(crate) q_cond_add: Selector,
    pub(crate) q_mem: Selector,
    pub(crate) advice_cols: [Column<Advice>; NB_EDWARDS_COLS],
}

impl EccConfig {
    /// Enforce `Q = 2 * P`, using columns:
    ///
    /// ```text
    ///    0      1      2      3       4      5      6       7      8     
    /// ------------------------------------------------------------------
    /// |      |      |      |      |      |  xp  |  yp  | xp_xp |       |
    /// |  xq  |  yq  |      |      |      |      |      |       |       |
    /// ------------------------------------------------------------------
    /// ```
    ///
    /// The curve equation is `-x^2 + y^2 = 1 + d * x^2 * y^2`.
    /// The result of doubling, the point `Q = (xq, yq)`, can be computed as:
    /// * `xq = (2 * xp * yp) / (1 + d * xp * xp * yp * yp)`
    /// * `yq = (yp * yp + xp * xp) / (1 - d * xp * xp * yp * yp)`
    ///
    /// Equivalently, the above can be computed as:
    /// * `xq * (1 + d * xp * xp * yp * yp) = 2 * xp * yp`
    /// * `yq * (1 - d * xp * xp * yp * yp) = yp * yp + xp * xp`
    ///
    /// Note, that `d * xp * xp * yp * yp != 1,-1` if `P` satisfies the
    /// curve equation (since `-1` is a square and `d` is not a square
    /// in the base field).
    /// See <https://eprint.iacr.org/2008/013.pdf>.
    ///
    /// Enforce the constraints:
    /// * `xq * (1 + d * xp_xp * yp * yp) = 2 * xp * yp`
    /// * `yq * (1 - d * xp_xp * yp * yp) = yp * yp + xp * xp`
    /// * `xp_xp = xp * xp`
    fn create_double_gate<C: EdwardsCurve>(
        &self,
        meta: &mut ConstraintSystem<C::Base>,
        q_double: &Selector,
    ) {
        meta.create_gate("double", |meta| {
            let xp = meta.query_advice(self.advice_cols[5], Rotation::cur());
            let yp = meta.query_advice(self.advice_cols[6], Rotation::cur());
            let xq = meta.query_advice(self.advice_cols[0], Rotation::next());
            let yq = meta.query_advice(self.advice_cols[1], Rotation::next());

            let xp_xp = meta.query_advice(self.advice_cols[7], Rotation::cur());

            let one = Expression::Constant(C::Base::ONE);
            let edwards_d = Expression::Constant(C::D);
            let xp_yp = xp.clone() * yp.clone();
            let yp_yp = yp.square();
            let d_xp_xp_yp_yp = edwards_d * xp_xp.clone() * yp_yp.clone();

            let id1 = xq * (one.clone() + d_xp_xp_yp_yp.clone()) - (xp_yp.clone() + xp_yp);

            let id2 = yq * (one - d_xp_xp_yp_yp) - (yp_yp + xp_xp.clone());

            let id3 = xp.clone() * xp - xp_xp;

            Constraints::with_selector(
                *q_double,
                vec![
                    ("qx constraint for q = 2 * p", id1),
                    ("qy constraint for q = 2 * p", id2),
                    ("constraint for xp_xp = xp * xp", id3),
                ],
            )
        })
    }

    /// Enforce `R = Q + b * S`, using columns:
    ///
    /// ```text
    ///    0      1      2      3       4      5      6      7         8
    /// -----------------------------------------------------------------------
    /// |  xq  |  yq  |  xs  |  ys  |   b   |  xr  |  yr  |     | xq_yq_xs_ys |
    /// -----------------------------------------------------------------------
    /// ```
    ///
    /// The curve equation is `-x^2 + y^2 = 1 + d * x^2 * y^2`.
    /// The result, `R = (xr, yr)`, can be computed as:
    /// * `xr = (xq + b * (xq*ys + xs*yq - xq)) / (1 + b*d * xq*xs*yq*ys)`
    /// * `yr = (yq + b * (yq*ys + xq*xs - yq)) / (1 - b*d * xq*xs*yq*ys)`
    ///
    /// Equivalently, the above can be computed as:
    /// * `xr * (1 + b * d * xq * xs * yq * ys) = xq + b * (xq*ys + xs*yq - xq)`
    /// * `yr * (1 - b * d * xq * xs * yq * ys) = yq + b * (yq*ys + xq*xs - yq)`
    ///
    /// Note, that `b * d * xq * xs * yq * ys != 1,-1` if `Q`, `S` satisfy the
    /// curve equation (since `-1` is a square and `d` is not a square
    /// in the base field).
    /// See <https://eprint.iacr.org/2008/013.pdf>.
    ///
    /// Enforce the constraints:
    /// * `xr * (1 + b * d * xq_yq_xs_ys) = xq + b * (xq*ys + xs*yq - xq)`
    /// * `yr * (1 - b * d * xq_yq_xs_ys) = yq + b * (yq*ys + xq*xs - yq)`
    /// * `xq_yq_xs_ys = xq * yq * xs * ys`
    fn create_cond_add_gate<C: EdwardsCurve>(
        &self,
        meta: &mut ConstraintSystem<C::Base>,
        q_cond_add: &Selector,
    ) {
        meta.create_gate("conditional add", |meta| {
            let xq = meta.query_advice(self.advice_cols[0], Rotation::cur());
            let yq = meta.query_advice(self.advice_cols[1], Rotation::cur());
            let xs = meta.query_advice(self.advice_cols[2], Rotation::cur());
            let ys = meta.query_advice(self.advice_cols[3], Rotation::cur());
            let xr = meta.query_advice(self.advice_cols[5], Rotation::cur());
            let yr = meta.query_advice(self.advice_cols[6], Rotation::cur());
            let b = meta.query_advice(self.advice_cols[4], Rotation::cur());

            let one = Expression::Constant(C::Base::ONE);
            let edwards_d = Expression::Constant(C::D);

            let xq_yq_xs_ys = meta.query_advice(self.advice_cols[8], Rotation::cur());

            let xq_xs = xq.clone() * xs.clone();
            let yq_ys = yq.clone() * ys.clone();
            let xq_ys = xq.clone() * ys.clone();
            let xs_yq = xs.clone() * yq.clone();
            let b_d_xq_xs_yq_ys = b.clone() * edwards_d * xq_yq_xs_ys.clone();

            let id1 = xr * (one.clone() + b_d_xq_xs_yq_ys.clone())
                - (xq.clone() + b.clone() * (xq_ys + xs_yq - xq.clone()));

            let id2 =
                yr * (one - b_d_xq_xs_yq_ys) - (yq.clone() + b * (yq_ys + xq_xs - yq.clone()));

            let id3 = xq_yq_xs_ys - xq * yq * xs * ys;

            Constraints::with_selector(
                *q_cond_add,
                vec![
                    ("rx constraint for r = q + b * s", id1),
                    ("ry constraint for r = q + b * s", id2),
                    ("constraint for xq_yq_xs_ys = xq * yq * xs * ys", id3),
                ],
            )
        })
    }

    /// Enforce `P = (x, y)` is on the curve, using columns:
    ///
    /// ```text
    /// -------------
    /// |  x  |  y  |
    /// -------------
    /// ```
    ///
    /// Enforce the constraint:
    /// * `-x^2 + y^2 = 1 + d * x^2 * y^2`
    fn create_membership_gate<C: EdwardsCurve>(
        &self,
        meta: &mut ConstraintSystem<C::Base>,
        q_point: &Selector,
    ) {
        meta.create_gate("witness point", |meta| {
            let x = meta.query_advice(self.advice_cols[0], Rotation::cur());
            let y = meta.query_advice(self.advice_cols[1], Rotation::cur());

            let one = Expression::Constant(C::Base::ONE);
            let edwards_d = Expression::Constant(C::D);

            let x2 = x.square();
            let y2 = y.square();

            let id = y2.clone() - x2.clone() - (one + edwards_d * x2 * y2);

            Constraints::with_selector(*q_point, vec![("curve equation", id)])
        })
    }
}

type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

/// A native  [`EccInstructions`] chip.
/// Since the chip is native, it only supports the embedded curve Jubjub.
#[derive(Clone, Debug)]
pub struct EccChip<C: EdwardsCurve> {
    config: EccConfig,
    native_gadget: NG<C::Base>,
}

impl<C: EdwardsCurve> Chip<C::Base> for EccChip<C> {
    type Config = EccConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<C: EdwardsCurve> ComposableChip<C::Base> for EccChip<C> {
    type SharedResources = [Column<Advice>; NB_EDWARDS_COLS];
    type InstructionDeps = NG<C::Base>;

    fn new(config: &Self::Config, sub_chips: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: sub_chips.clone(),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<C::Base>,
        advice_cols: &Self::SharedResources,
    ) -> Self::Config {
        assert_eq!(C::A, -C::Base::ONE);
        for col in advice_cols.iter() {
            meta.enable_equality(*col)
        }

        let q_double = meta.selector();
        let q_cond_add = meta.selector();
        let q_mem = meta.selector();

        let config = EccConfig {
            q_double,
            q_cond_add,
            q_mem,
            advice_cols: *advice_cols,
        };

        config.create_double_gate::<C>(meta, &q_double);
        config.create_cond_add_gate::<C>(meta, &q_cond_add);
        config.create_membership_gate::<C>(meta, &q_mem);

        config
    }

    fn load(&self, _layouter: &mut impl Layouter<C::Base>) -> Result<(), Error> {
        Ok(())
    }
}

impl<C: EdwardsCurve> EccChip<C> {
    /// Given `Q`, `S`, and bit `b`, supposedly already assigned in the
    /// current row, this function assigns `R` in the same row and
    /// enforces that `R = Q + b * S`.
    //
    // We use the following layout.
    //
    // ```text
    //    0      1      2      3       4     5      6      7         8
    // ----------------------------------------------------------------------
    // |  xq  |  yq  |  xs  |  ys  |   b   | xr  |  yr  |     | xq_yq_xs_ys |
    // ----------------------------------------------------------------------
    // ```
    fn assign_cond_add(
        &self,
        region: &mut Region<C::Base>,
        offset: usize,
        q: Value<C>,
        s: Value<C>,
        b: Value<bool>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let config = self.config();
        config.q_cond_add.enable(region, offset)?;

        let (xr_val, yr_val) = Self::p_plus_b_q(q, s, b);
        let xr = region.assign_advice(|| "xr", config.advice_cols[5], offset, || xr_val)?;
        let yr = region.assign_advice(|| "yr", config.advice_cols[6], offset, || yr_val)?;

        let (xq, yq) = q.map(|q| q.coordinates().expect("non-id")).unzip();
        let (xs, ys) = s.map(|s| s.coordinates().expect("non-id")).unzip();
        let prod_val = xq * yq * xs * ys;
        region.assign_advice(|| "xq_yq_xs_ys", config.advice_cols[8], offset, || prod_val)?;

        Ok(AssignedNativePoint { x: xr, y: yr })
    }

    /// Given `P`, `Q`, and bit `b`, supposedly already assigned in the
    /// current row, this function assigns `R` in the next row and
    /// enforces that `R = 2 * (P + b * Q)`.
    //
    // We use the following layout.
    //
    // ```text
    // ------------------------------------------------------------------------
    // |  xp  |  yp  |  xq  |  yq  |  b   |  xs  |  ys  | xs_xs | xp_yp_xq_yq |
    // |  xr  |  yr  |      |      |      |      |      |       |             |
    // ------------------------------------------------------------------------
    // ```
    fn assign_add_then_double(
        &self,
        region: &mut Region<C::Base>,
        offset: usize,
        p_val: Value<C>,
        q_val: Value<C>,
        b_val: Value<bool>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let config = self.config();

        config.q_cond_add.enable(region, offset)?;
        config.q_double.enable(region, offset)?;

        let (xs_val, ys_val) = Self::p_plus_b_q(p_val, q_val, b_val);

        region.assign_advice(|| "xs", config.advice_cols[5], offset, || xs_val)?;
        region.assign_advice(|| "ys", config.advice_cols[6], offset, || ys_val)?;

        let s_val = xs_val
            .zip(ys_val)
            .map(|(xs, ys)| C::from_xy(xs, ys).unwrap());
        let r_val = s_val.map(|s| s + s);

        let xr_val = r_val.map(|r: C| r.coordinates().expect("non-id").0);
        let yr_val = r_val.map(|r: C| r.coordinates().expect("non-id").1);

        let xr = region.assign_advice(|| "xr", config.advice_cols[0], offset + 1, || xr_val)?;
        let yr = region.assign_advice(|| "yr", config.advice_cols[1], offset + 1, || yr_val)?;

        region.assign_advice(
            || "xs_xs",
            config.advice_cols[7],
            offset,
            || xs_val * xs_val,
        )?;

        let (xp, yp) = p_val.map(|c| c.coordinates().expect("non-id")).unzip();
        let (xq, yq) = q_val.map(|c| c.coordinates().expect("non-id")).unzip();
        let prod_val = xp * yp * xq * yq;
        region.assign_advice(|| "xp_yp_xq_yq", config.advice_cols[8], offset, || prod_val)?;

        Ok(AssignedNativePoint { x: xr, y: yr })
    }

    /// Given the scalar in little-endian, double and add for each bit.
    pub fn mul(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        scalar: &ScalarVar<C>,
        base: &AssignedNativePoint<C>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let config = &self.config();

        // Convert to big-endian.
        let scalar_be_bits = &mut scalar.0.clone();
        scalar_be_bits.reverse();

        let base_val = base.curve_value();
        let id_point: AssignedNativePoint<C> =
            self.assign_fixed(layouter, C::CryptographicGroup::identity())?;

        layouter.assign_region(
            || "assign mul",
            |mut region: Region<'_, C::Base>| {
                (id_point.x).copy_advice(|| "id.x", &mut region, config.advice_cols[0], 0)?;
                (id_point.y).copy_advice(|| "id.y", &mut region, config.advice_cols[1], 0)?;

                let mut acc = id_point.clone();

                for (i, bit) in scalar_be_bits.iter().enumerate() {
                    (base.x).copy_advice(|| "base.x", &mut region, config.advice_cols[2], i)?;
                    (base.y).copy_advice(|| "base.y", &mut region, config.advice_cols[3], i)?;
                    (bit.0).copy_advice(|| "b cond_add", &mut region, config.advice_cols[4], i)?;

                    if i < scalar_be_bits.len() - 1 {
                        acc = self.assign_add_then_double(
                            &mut region,
                            i,
                            acc.curve_value(),
                            base_val,
                            bit.value(),
                        )?;
                    }
                    // In the last iteration, add but do not double.
                    else {
                        acc = self.assign_cond_add(
                            &mut region,
                            i,
                            acc.curve_value(),
                            base_val,
                            bit.value(),
                        )?;
                    }
                }

                Ok(acc)
            },
        )
    }

    /// Given values of P, Q and b, computes the value of P + b * Q.
    fn p_plus_b_q(p: Value<C>, q: Value<C>, b: Value<bool>) -> (Value<C::Base>, Value<C::Base>) {
        p.zip(q)
            .zip(b)
            .map(|((p, q), b)| if b { p + q } else { p })
            .map(|r| r.coordinates().expect("non-id"))
            .unzip()
    }

    /// The native gadget carried by this chip.
    pub fn native_gadget(&self) -> &impl NativeInstructions<C::Base> {
        &self.native_gadget
    }
}

impl<C: EdwardsCurve> EccInstructions<C::Base, C> for EccChip<C> {
    type Point = AssignedNativePoint<C>;
    type Coordinate = AssignedNative<C::Base>;
    type Scalar = ScalarVar<C>;

    fn add(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &Self::Point,
        q: &Self::Point,
    ) -> Result<Self::Point, Error> {
        let config = self.config();
        let b: AssignedBit<C::Base> = self.native_gadget.assign_fixed(layouter, true)?;

        layouter.assign_region(
            || "assign add",
            |mut region: Region<'_, C::Base>| {
                p.x.copy_advice(|| "px", &mut region, config.advice_cols[0], 0)?;
                p.y.copy_advice(|| "py", &mut region, config.advice_cols[1], 0)?;
                q.x.copy_advice(|| "qx", &mut region, config.advice_cols[2], 0)?;
                q.y.copy_advice(|| "qy", &mut region, config.advice_cols[3], 0)?;
                b.0.copy_advice(|| "b", &mut region, config.advice_cols[4], 0)?;

                self.assign_cond_add(&mut region, 0, p.curve_value(), q.curve_value(), b.value())
            },
        )
    }

    fn double(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &Self::Point,
    ) -> Result<Self::Point, Error> {
        self.add(layouter, p, p)
    }

    fn negate(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &Self::Point,
    ) -> Result<Self::Point, Error> {
        Ok(AssignedNativePoint {
            x: self.native_gadget.neg(layouter, &p.x)?,
            y: p.y.clone(),
        })
    }

    fn msm(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        scalars: &[Self::Scalar],
        bases: &[Self::Point],
    ) -> Result<Self::Point, Error> {
        let scaled_points = scalars
            .iter()
            .zip(bases.iter())
            .map(|(scalar, point)| self.mul(layouter, scalar, point))
            .collect::<Result<Vec<Self::Point>, Error>>()?;

        scaled_points[1..]
            .iter()
            .try_fold(scaled_points[0].clone(), |acc, e| {
                self.add(layouter, &acc, e)
            })
    }

    fn mul_by_constant(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        scalar: C::Scalar,
        base: &Self::Point,
    ) -> Result<Self::Point, Error> {
        if scalar == C::Scalar::ZERO {
            return self.assign_fixed(layouter, C::CryptographicGroup::identity());
        }

        if scalar == C::Scalar::ONE {
            return Ok(base.clone());
        }

        let s = self.assign_fixed(layouter, scalar)?;
        self.msm(layouter, &[s], &[base.clone()])
    }

    fn point_from_coordinates(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        x: &Self::Coordinate,
        y: &Self::Coordinate,
    ) -> Result<Self::Point, Error> {
        layouter.assign_region(
            || "assign new point",
            |mut region: Region<'_, C::Base>| {
                x.copy_advice(|| "x", &mut region, self.config.advice_cols[0], 0)?;
                y.copy_advice(|| "y", &mut region, self.config.advice_cols[1], 0)?;
                self.config.q_mem.enable(&mut region, 0)
            },
        )?;
        Ok(AssignedNativePoint {
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

    fn base_field(&self) -> &impl DecompositionInstructions<C::Base, Self::Coordinate> {
        &self.native_gadget
    }
}

impl<C: EdwardsCurve> AssignmentInstructions<C::Base, AssignedNativePoint<C>> for EccChip<C> {
    fn assign(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        value: Value<C::CryptographicGroup>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let config = self.config();

        // Ensure the point lies in the correct subgroup.
        // To achieve this, we first assign the point multiplied by the inverse of the
        // cofactor. Then, we return the assigned point after multiplying it by
        // the cofactor.
        let cofactor = C::Scalar::from_u128(C::COFACTOR);
        let (x_val, y_val) = value
            .map(|p| {
                let p = p * cofactor.invert().expect("cofactor should not be 0");
                p.into().coordinates().expect("non-id")
            })
            .unzip();

        let cf_root = layouter.assign_region(
            || "assign point",
            |mut region: Region<'_, C::Base>| {
                config.q_mem.enable(&mut region, 0)?;
                let x = region.assign_advice(|| "x", config.advice_cols[0], 0, || x_val)?;
                let y = region.assign_advice(|| "y", config.advice_cols[1], 0, || y_val)?;
                Ok(AssignedNativePoint { x, y })
            },
        )?;

        self.mul_by_constant(layouter, cofactor, &cf_root)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let coords = constant.into().coordinates().expect("non-id");
        let x = self.native_gadget.assign_fixed(layouter, coords.0)?;
        let y = self.native_gadget.assign_fixed(layouter, coords.1)?;
        Ok(AssignedNativePoint { x, y })
    }
}

impl<C: EdwardsCurve> AssignmentInstructions<C::Base, ScalarVar<C>> for EccChip<C> {
    fn assign(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        value: Value<C::Scalar>,
    ) -> Result<ScalarVar<C>, Error> {
        let bits = value
            .map(|s| fe_to_le_bits(&s, Some(C::Scalar::NUM_BITS as usize)))
            .transpose_vec(<C::Scalar as PrimeField>::NUM_BITS as usize);
        self.native_gadget
            .assign_many(layouter, &bits)
            .map(ScalarVar)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        constant: C::Scalar,
    ) -> Result<ScalarVar<C>, Error> {
        self.native_gadget
            .assign_many_fixed(layouter, &fe_to_le_bits(&constant, None))
            .map(ScalarVar)
    }
}

impl<C: EdwardsCurve> AssertionInstructions<C::Base, AssignedNativePoint<C>> for EccChip<C> {
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        q: &AssignedNativePoint<C>,
    ) -> Result<(), Error> {
        self.native_gadget.assert_equal(layouter, &p.x, &q.x)?;
        self.native_gadget.assert_equal(layouter, &p.y, &q.y)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        q: &AssignedNativePoint<C>,
    ) -> Result<(), Error> {
        let is_eq = self.is_equal(layouter, p, q)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &is_eq, false)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        constant: C::CryptographicGroup,
    ) -> Result<(), Error> {
        let (cx, cy) = constant.into().coordinates().expect("non-id");
        self.native_gadget
            .assert_equal_to_fixed(layouter, &p.x, cx)?;
        self.native_gadget.assert_equal_to_fixed(layouter, &p.y, cy)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        constant: C::CryptographicGroup,
    ) -> Result<(), Error> {
        let is_eq = self.is_equal_to_fixed(layouter, p, constant)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &is_eq, false)
    }
}

impl<C: EdwardsCurve> PublicInputInstructions<C::Base, AssignedNativePoint<C>> for EccChip<C> {
    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
    ) -> Result<Vec<AssignedNative<C::Base>>, Error> {
        Ok(vec![p.x.clone(), p.y.clone()])
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
    ) -> Result<(), Error> {
        self.as_public_input(layouter, p)?
            .iter()
            .try_for_each(|c| self.native_gadget.constrain_as_public_input(layouter, c))
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: Value<C::CryptographicGroup>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        // We can skip the curve equation check in this case.
        let (x, y) = p.map(|p| p.into().coordinates().expect("non-id")).unzip();
        let x = self.native_gadget.assign_as_public_input(layouter, x)?;
        let y = self.native_gadget.assign_as_public_input(layouter, y)?;
        Ok(AssignedNativePoint { x, y })
    }
}

impl<C: EdwardsCurve> PublicInputInstructions<C::Base, ScalarVar<C>> for EccChip<C> {
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        assigned: &ScalarVar<C>,
    ) -> Result<Vec<AssignedNative<C::Base>>, Error> {
        // We aggregate the bits while they fit in a single `AssignedNative`.
        let nb_bits_per_batch = C::Base::NUM_BITS as usize - 1;
        assigned
            .0
            .chunks(nb_bits_per_batch)
            .map(|chunk| self.native_gadget.assigned_from_le_bits(layouter, chunk))
            .collect()
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        assigned: &ScalarVar<C>,
    ) -> Result<(), Error> {
        self.as_public_input(layouter, assigned)?
            .iter()
            .try_for_each(|c| self.native_gadget.constrain_as_public_input(layouter, c))
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        value: Value<C::Scalar>,
    ) -> Result<ScalarVar<C>, Error> {
        let assigned: ScalarVar<C> = self.assign(layouter, value)?;
        self.constrain_as_public_input(layouter, &assigned)?;
        Ok(assigned)
    }
}

impl<C: EdwardsCurve> EqualityInstructions<C::Base, AssignedNativePoint<C>> for EccChip<C> {
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        q: &AssignedNativePoint<C>,
    ) -> Result<AssignedBit<C::Base>, Error> {
        let eq_x = self.native_gadget.is_equal(layouter, &p.x, &q.x)?;
        let eq_y = self.native_gadget.is_equal(layouter, &p.y, &q.y)?;
        self.native_gadget.and(layouter, &[eq_x, eq_y])
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedBit<C::Base>, Error> {
        let (cx, cy) = constant.into().coordinates().expect("non-id");
        let eq_x = self.native_gadget.is_equal_to_fixed(layouter, &p.x, cx)?;
        let eq_y = self.native_gadget.is_equal_to_fixed(layouter, &p.y, cy)?;
        self.native_gadget.and(layouter, &[eq_x, eq_y])
    }
}

impl<C: EdwardsCurve> ZeroInstructions<C::Base, AssignedNativePoint<C>> for EccChip<C> {}

impl<C: EdwardsCurve> ControlFlowInstructions<C::Base, AssignedNativePoint<C>> for EccChip<C> {
    fn select(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        cond: &AssignedBit<C::Base>,
        a: &AssignedNativePoint<C>,
        b: &AssignedNativePoint<C>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let x = self.native_gadget.select(layouter, cond, &a.x, &b.x)?;
        let y = self.native_gadget.select(layouter, cond, &a.y, &b.y)?;
        Ok(AssignedNativePoint { x, y })
    }
}

#[cfg(any(test, feature = "testing"))]
impl<C: EdwardsCurve> FromScratch<C::Base> for EccChip<C> {
    type Config = (EccConfig, P2RDecompositionConfig);

    fn new_from_scratch(config: &Self::Config) -> Self {
        let p2r_decomp_config = &config.1;
        let max_bit_len = 8;
        let native_chip = NativeChip::new_from_scratch(&p2r_decomp_config.native_config);
        let core_decomposition_chip = P2RDecompositionChip::new(p2r_decomp_config, &max_bit_len);
        let native_gadget = NativeGadget::new(core_decomposition_chip, native_chip);
        Self {
            native_gadget,
            config: config.0.clone(),
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<C::Base>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let native_gadget_config =
            <NG<C::Base> as FromScratch<C::Base>>::configure_from_scratch(meta, instance_columns);
        let advice_cols: [Column<Advice>; NB_EDWARDS_COLS] =
            core::array::from_fn(|_| meta.advice_column());
        let ecc_config = EccChip::<C>::configure(meta, &advice_cols);

        (ecc_config, native_gadget_config)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<C::Base>, config: &Self::Config) {
        NativeGadget::load_from_scratch(layouter, &config.1)
    }
}

#[cfg(any(test, feature = "testing"))]
impl<C: EdwardsCurve> Sampleable for AssignedNativePoint<C> {
    fn sample_inner(rng: impl RngCore) -> C::CryptographicGroup {
        C::CryptographicGroup::random(rng)
    }
}

/// This conversion should not exist for Base -> Scalar. It is a tech debt. We
/// should fix this as soon as compact supports types (other than assigned
/// native) <https://github.com/midnightntwrk/midnight-circuits/issues/433>
impl<C: EdwardsCurve> ConversionInstructions<C::Base, AssignedNative<C::Base>, ScalarVar<C>>
    for EccChip<C>
{
    fn convert_value(
        &self,
        _x: &<AssignedNative<C::Base> as InnerValue>::Element,
    ) -> Option<<ScalarVar<C> as InnerValue>::Element> {
        unimplemented!("The caller should decide how to convert the value off-circuit, i.e., what to do with overflows.");
    }

    fn convert(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        x: &AssignedNative<C::Base>,
    ) -> Result<ScalarVar<C>, Error> {
        Ok(ScalarVar(
            self.native_gadget
                .assigned_to_le_bits(layouter, x, None, true)?,
        ))
    }
}

#[cfg(test)]
mod tests {
    use midnight_curves::{Fq as JubjubBase, JubjubExtended};

    use super::*;
    use crate::{
        ecc::hash_to_curve::HashToCurveGadget,
        hash::poseidon::PoseidonChip,
        instructions::{ecc, hash_to_curve::tests::test_hash_to_curve},
    };

    macro_rules! test_generic {
        ($mod:ident, $op:ident, $native:ty, $curve:ty, $name:expr) => {
            $mod::tests::$op::<$native, AssignedNativePoint<$curve>, EccChip<$curve>>($name);
        };
    }

    macro_rules! test {
        ($mod:ident, $op:ident) => {
            #[test]
            fn $op() {
                test_generic!($mod, $op, JubjubBase, JubjubExtended, "native_ecc");
            }
        };
    }

    test!(assertions, test_assertions);

    test!(public_input, test_public_inputs);

    #[test]
    fn test_scalarvar_public_inputs() {
        public_input::tests::test_public_inputs::<
            JubjubBase,
            ScalarVar<JubjubExtended>,
            EccChip<JubjubExtended>,
        >("public_inputs_scalar_var");
    }

    test!(equality, test_is_equal);

    test!(zero, test_zero_assertions);
    test!(zero, test_is_zero);

    test!(control_flow, test_select);
    test!(control_flow, test_cond_assert_equal);

    macro_rules! ecc_tests {
        ($op:ident) => {
            #[test]
            fn $op() {
                ecc::tests::$op::<JubjubBase, JubjubExtended, EccChip<JubjubExtended>>(
                    "native_ecc",
                );
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

    #[test]
    fn test_htc() {
        test_hash_to_curve::<
            JubjubBase,
            JubjubExtended,
            AssignedNative<JubjubBase>,
            EccChip<JubjubExtended>,
            NativeChip<JubjubBase>,
            HashToCurveGadget<_, _, _, PoseidonChip<JubjubBase>, _>,
        >("native_ecc")
    }
}
