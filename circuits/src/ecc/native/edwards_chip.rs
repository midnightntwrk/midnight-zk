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
    types::{AssignedBit, AssignedByte, AssignedNative, InnerConstants, InnerValue, Instantiable},
    utils::ComposableChip,
    CircuitField,
};

/// The number of advice columns used by the EccChip.
pub const NB_EDWARDS_COLS: usize = 9;

/// A twisted Edwards curve point represented in affine (x, y) coordinates, the
/// identity represented as (0, 1).
/// The represented point may or may not lie in the prime order subgroup. If
/// `in_subgroup` is true, then the point has been constrained to be in the
/// prime order subgroup.
/// Since in most use cases we want to ensure the point is in the subgroup,
/// the implementation of `InnerValue` and `AssignmentInstructions` require
/// subgroup membership. To use arbitrary points of the curve there are
/// equivalent functions that explicitly state the absence of this subgroup
/// membership check.
#[derive(Clone, Debug)]
pub struct AssignedNativePoint<C: CircuitCurve> {
    x: AssignedNative<C::Base>,
    y: AssignedNative<C::Base>,
    in_subgroup: bool,
}

impl<C: CircuitCurve> InnerValue for AssignedNativePoint<C> {
    type Element = C::CryptographicGroup;

    fn value(&self) -> Value<Self::Element> {
        assert!(self.in_subgroup);
        self.x
            .value()
            .zip(self.y.value())
            .map(|(x, y)| C::from_xy(*x, *y).expect("Valid coordinates.").into_subgroup())
    }
}

impl<C: CircuitCurve> AssignedNativePoint<C> {
    /// Return the value of the assigned point, possibly not in the subgroup.
    /// If the point is known to be in the subgroup, consider using `value()`
    /// instead.
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
        let coordinates = point.coordinates().unwrap();
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
pub struct AssignedScalarOfNativeCurve<C: CircuitCurve>(Vec<AssignedBit<C::Base>>);

impl<C: CircuitCurve> InnerValue for AssignedScalarOfNativeCurve<C> {
    type Element = C::ScalarExt;

    fn value(&self) -> Value<Self::Element> {
        let bools = self.0.iter().map(|b| b.value());
        let value_bools: Value<Vec<bool>> = Value::from_iter(bools);
        value_bools.map(|le_bits| C::ScalarExt::from_le_bits(&le_bits))
    }
}

impl<C: EdwardsCurve> Instantiable<C::Base> for AssignedScalarOfNativeCurve<C> {
    fn as_public_input(element: &C::ScalarExt) -> Vec<C::Base> {
        // We aggregate the bits while they fit in a single `C::Base` value.
        let nb_bits_per_batch = C::Base::NUM_BITS as usize - 1;
        element
            .to_le_bits(Some(C::NUM_BITS_SUBGROUP as usize))
            .chunks(nb_bits_per_batch)
            .map(|bits| C::Base::from_le_bits(bits))
            .collect()
    }
}

impl<C: EdwardsCurve> InnerConstants for AssignedScalarOfNativeCurve<C> {
    fn inner_zero() -> C::ScalarExt {
        C::ScalarExt::ZERO
    }
    fn inner_one() -> C::ScalarExt {
        C::ScalarExt::ONE
    }
}

#[cfg(any(test, feature = "testing"))]
impl<C: EdwardsCurve> Sampleable for AssignedScalarOfNativeCurve<C> {
    fn sample_inner(rng: impl RngCore) -> C::ScalarExt {
        C::ScalarExt::random(rng)
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

            let one = Expression::from(1);
            let edwards_d = Expression::Constant(C::D);
            let xp_yp = &xp * &yp;
            let yp_yp = yp.square();
            let d_xp_xp_yp_yp = edwards_d * &xp_xp * &yp_yp;

            let id1 = xq * (&one + &d_xp_xp_yp_yp) - (xp_yp.clone() + xp_yp);
            let id2 = yq * (one - d_xp_xp_yp_yp) - (yp_yp + &xp_xp);
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

            let one = Expression::from(1);
            let edwards_d = Expression::Constant(C::D);

            let xq_yq_xs_ys = meta.query_advice(self.advice_cols[8], Rotation::cur());

            let xq_xs = &xq * &xs;
            let yq_ys = &yq * &ys;
            let xq_ys = &xq * &ys;
            let xs_yq = &xs * &yq;
            let b_d_xq_xs_yq_ys = &b * edwards_d * &xq_yq_xs_ys;

            let id1 = xr * (&one + &b_d_xq_xs_yq_ys) - (&xq + &b * (xq_ys + xs_yq - &xq));
            let id2 = yr * (one - b_d_xq_xs_yq_ys) - (&yq + b * (yq_ys + xq_xs - &yq));
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

            let one = Expression::from(1);
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

        // Only the first 7 need to be copy-enabled.
        for col in advice_cols.iter().take(7) {
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
    /// Given points Q, S and bit `b`, computes R = Q + b * S.
    /// This function requires the inputs to be already assigned in the current
    /// row. The result R will be asigned by this function in the same row,
    /// following the layout:
    ///
    ///
    /// ```text
    ///    0      1      2      3       4     5      6      7         8
    /// ----------------------------------------------------------------------
    /// |  xq  |  yq  |  xs  |  ys  |   b   | xr  |  yr  |     | xq_yq_xs_ys |
    /// ----------------------------------------------------------------------
    /// ```
    fn cond_add(
        &self,
        region: &mut Region<C::Base>,
        offset: usize,
        q: &AssignedNativePoint<C>,
        s: &AssignedNativePoint<C>,
        b: &AssignedBit<C::Base>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let config = self.config();
        config.q_cond_add.enable(region, offset)?;

        let (q_val, s_val) = (q.curve_value(), s.curve_value());
        let in_subgroup = q.in_subgroup && s.in_subgroup;

        let (xr_val, yr_val) = Self::p_plus_b_q(q_val, s_val, b.value());
        let xr = region.assign_advice(|| "xr", config.advice_cols[5], offset, || xr_val)?;
        let yr = region.assign_advice(|| "yr", config.advice_cols[6], offset, || yr_val)?;

        let (xq, yq) = q_val.map(|q| q.coordinates().unwrap()).unzip();
        let (xs, ys) = s_val.map(|s| s.coordinates().unwrap()).unzip();
        let prod_val = xq * yq * xs * ys;
        region.assign_advice(|| "xq_yq_xs_ys", config.advice_cols[8], offset, || prod_val)?;

        Ok(AssignedNativePoint {
            x: xr,
            y: yr,
            in_subgroup,
        })
    }

    /// Given points P, Q and bit `b`, computes R = 2 * (P + b * Q).
    /// This function requires the inputs to be already assigned in the current
    /// row. The result R will be asigned by this function in the next row,
    /// following the layout:
    ///
    ///
    /// ```text
    /// ------------------------------------------------------------------------
    /// |  xp  |  yp  |  xq  |  yq  |  b   |  xs  |  ys  | xs_xs | xp_yp_xq_yq |
    /// |  xr  |  yr  |      |      |      |      |      |       |             |
    /// ------------------------------------------------------------------------
    /// ```
    fn add_then_double(
        &self,
        region: &mut Region<C::Base>,
        offset: usize,
        p: &AssignedNativePoint<C>,
        q: &AssignedNativePoint<C>,
        b: &AssignedBit<C::Base>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let config = self.config();

        config.q_cond_add.enable(region, offset)?;
        config.q_double.enable(region, offset)?;

        let (q_val, p_val) = (q.curve_value(), p.curve_value());
        let in_subgroup = q.in_subgroup && p.in_subgroup;

        let (xs_val, ys_val) = Self::p_plus_b_q(p_val, q_val, b.value());

        region.assign_advice(|| "xs", config.advice_cols[5], offset, || xs_val)?;
        region.assign_advice(|| "ys", config.advice_cols[6], offset, || ys_val)?;

        let s_val = xs_val.zip(ys_val).map(|(xs, ys)| C::from_xy(xs, ys).unwrap());
        let r_val = s_val.map(|s| s + s);

        let xr_val = r_val.map(|r: C| r.coordinates().unwrap().0);
        let yr_val = r_val.map(|r: C| r.coordinates().unwrap().1);

        let xr = region.assign_advice(|| "xr", config.advice_cols[0], offset + 1, || xr_val)?;
        let yr = region.assign_advice(|| "yr", config.advice_cols[1], offset + 1, || yr_val)?;

        region.assign_advice(
            || "xs_xs",
            config.advice_cols[7],
            offset,
            || xs_val * xs_val,
        )?;

        let (xp, yp) = p_val.map(|c| c.coordinates().unwrap()).unzip();
        let (xq, yq) = q_val.map(|c| c.coordinates().unwrap()).unzip();
        let prod_val = xp * yp * xq * yq;
        region.assign_advice(|| "xp_yp_xq_yq", config.advice_cols[8], offset, || prod_val)?;

        Ok(AssignedNativePoint {
            x: xr,
            y: yr,
            in_subgroup,
        })
    }

    /// Given the scalar in little-endian, double and add for each bit.
    pub fn mul(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        scalar: &AssignedScalarOfNativeCurve<C>,
        base: &AssignedNativePoint<C>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let config = &self.config();

        // Convert to big-endian.
        let scalar_be_bits = &mut scalar.0.clone();
        scalar_be_bits.reverse();

        let id_point: AssignedNativePoint<C> =
            self.assign_fixed(layouter, C::CryptographicGroup::identity())?;

        layouter.assign_region(
            || "assign mul",
            |mut region: Region<'_, C::Base>| {
                id_point.x.copy_advice(|| "id.x", &mut region, config.advice_cols[0], 0)?;
                id_point.y.copy_advice(|| "id.y", &mut region, config.advice_cols[1], 0)?;

                let mut acc = id_point.clone();

                for (i, bit) in scalar_be_bits.iter().enumerate() {
                    base.x.copy_advice(|| "base.x", &mut region, config.advice_cols[2], i)?;
                    base.y.copy_advice(|| "base.y", &mut region, config.advice_cols[3], i)?;
                    bit.0.copy_advice(|| "b cond_add", &mut region, config.advice_cols[4], i)?;

                    if i < scalar_be_bits.len() - 1 {
                        acc = self.add_then_double(&mut region, i, &acc, base, bit)?;
                    }
                    // In the last iteration, add but do not double.
                    else {
                        acc = self.cond_add(&mut region, i, &acc, base, bit)?;
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
            .map(|r| r.coordinates().unwrap())
            .unzip()
    }

    /// The native gadget carried by this chip.
    pub fn native_gadget(&self) -> &impl NativeInstructions<C::Base> {
        &self.native_gadget
    }
}

impl<C: EdwardsCurve> EccChip<C> {
    /// Multiplies by the cofactor, ensuring the result lies in the prime order
    /// subgroup.
    pub(crate) fn clear_cofactor(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        point: &AssignedNativePoint<C>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        if point.in_subgroup {
            return Err(Error::Synthesis("clear_cofactor() should not be called in a point that is already guaranteed to be in the prime-order subgroup.".to_owned()));
        }
        let r = self.mul_by_constant(layouter, C::ScalarExt::from_u128(C::COFACTOR), point)?;
        Ok(AssignedNativePoint {
            x: r.x,
            y: r.y,
            in_subgroup: true,
        })
    }

    /// Assigns a point given its affine coordinates, checking the curve
    /// equation and *not* checking subgroup membership.
    pub(crate) fn point_from_coordinates_unsafe(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        x: &AssignedNative<C::Base>,
        y: &AssignedNative<C::Base>,
    ) -> Result<AssignedNativePoint<C>, Error> {
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
            in_subgroup: false,
        })
    }
}

impl<C: EdwardsCurve> EccInstructions<C::Base, C> for EccChip<C> {
    type Point = AssignedNativePoint<C>;
    type Coordinate = AssignedNative<C::Base>;
    type Scalar = AssignedScalarOfNativeCurve<C>;

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

                self.cond_add(&mut region, 0, p, q, &b)
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
            in_subgroup: p.in_subgroup,
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

        scaled_points[1..].iter().try_fold(scaled_points[0].clone(), |acc, e| {
            self.add(layouter, &acc, e)
        })
    }

    fn mul_by_constant(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        scalar: C::ScalarExt,
        base: &Self::Point,
    ) -> Result<Self::Point, Error> {
        if scalar == C::ScalarExt::ZERO {
            return self.assign_fixed(layouter, C::CryptographicGroup::identity());
        }

        if scalar == C::ScalarExt::ONE {
            return Ok(base.clone());
        }

        let s = self.assign_fixed(layouter, scalar)?;
        self.msm(layouter, &[s], std::slice::from_ref(base))
    }

    fn point_from_coordinates(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        x: &Self::Coordinate,
        y: &Self::Coordinate,
    ) -> Result<Self::Point, Error> {
        let point_val = x.value().zip(y.value()).map(|(x, y)| {
            C::from_xy(*x, *y)
                .expect("Affine coordinates must satisfy Jubjub equation.")
                .into_subgroup()
        });
        let point: Self::Point = self.assign(layouter, point_val)?;
        self.native_gadget.assert_equal(layouter, x, &point.x)?;
        self.native_gadget.assert_equal(layouter, y, &point.y)?;
        Ok(point)
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
        let cofactor = C::ScalarExt::from_u128(C::COFACTOR);
        let (x_val, y_val) = value
            .map(|p| {
                let p = p * cofactor.invert().expect("Cofactor should not be 0");
                p.into().coordinates().unwrap()
            })
            .unzip();

        let cf_root = layouter.assign_region(
            || "assign point",
            |mut region: Region<'_, C::Base>| {
                config.q_mem.enable(&mut region, 0)?;
                let x = region.assign_advice(|| "x", config.advice_cols[0], 0, || x_val)?;
                let y = region.assign_advice(|| "y", config.advice_cols[1], 0, || y_val)?;
                Ok(AssignedNativePoint {
                    x,
                    y,
                    in_subgroup: false,
                })
            },
        )?;

        self.clear_cofactor(layouter, &cf_root)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let coords = constant.into().coordinates().unwrap();
        let x = self.native_gadget.assign_fixed(layouter, coords.0)?;
        let y = self.native_gadget.assign_fixed(layouter, coords.1)?;
        Ok(AssignedNativePoint {
            x,
            y,
            in_subgroup: true,
        })
    }
}

impl<C: EdwardsCurve> AssignmentInstructions<C::Base, AssignedScalarOfNativeCurve<C>>
    for EccChip<C>
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        value: Value<C::ScalarExt>,
    ) -> Result<AssignedScalarOfNativeCurve<C>, Error> {
        let bits = value
            .map(|s| s.to_le_bits(Some(C::ScalarExt::NUM_BITS as usize)))
            .transpose_vec(<C::ScalarExt as PrimeField>::NUM_BITS as usize);
        self.native_gadget.assign_many(layouter, &bits).map(AssignedScalarOfNativeCurve)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        constant: C::ScalarExt,
    ) -> Result<AssignedScalarOfNativeCurve<C>, Error> {
        self.native_gadget
            .assign_many_fixed(layouter, &constant.to_le_bits(None))
            .map(AssignedScalarOfNativeCurve)
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
        self.native_gadget.assert_equal_to_fixed(layouter, &is_eq, false)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        constant: C::CryptographicGroup,
    ) -> Result<(), Error> {
        let (cx, cy) = constant.into().coordinates().unwrap();
        self.native_gadget.assert_equal_to_fixed(layouter, &p.x, cx)?;
        self.native_gadget.assert_equal_to_fixed(layouter, &p.y, cy)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        constant: C::CryptographicGroup,
    ) -> Result<(), Error> {
        let is_eq = self.is_equal_to_fixed(layouter, p, constant)?;
        self.native_gadget.assert_equal_to_fixed(layouter, &is_eq, false)
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
        let (x, y) = p.map(|p| p.into().coordinates().unwrap()).unzip();
        let x = self.native_gadget.assign_as_public_input(layouter, x)?;
        let y = self.native_gadget.assign_as_public_input(layouter, y)?;

        // Since the input value will be constrained to be equal to a PI,
        // the verifier will check the validity of the point out-of-circuit,
        // so the checks can be skipped.
        Ok(AssignedNativePoint {
            x,
            y,
            in_subgroup: true,
        })
    }
}

impl<C: EdwardsCurve> PublicInputInstructions<C::Base, AssignedScalarOfNativeCurve<C>>
    for EccChip<C>
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        assigned: &AssignedScalarOfNativeCurve<C>,
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
        assigned: &AssignedScalarOfNativeCurve<C>,
    ) -> Result<(), Error> {
        self.as_public_input(layouter, assigned)?
            .iter()
            .try_for_each(|c| self.native_gadget.constrain_as_public_input(layouter, c))
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        value: Value<C::ScalarExt>,
    ) -> Result<AssignedScalarOfNativeCurve<C>, Error> {
        let assigned: AssignedScalarOfNativeCurve<C> = self.assign(layouter, value)?;
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

    fn is_not_equal(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        q: &AssignedNativePoint<C>,
    ) -> Result<AssignedBit<C::Base>, Error> {
        let not_eq_x = self.native_gadget.is_not_equal(layouter, &p.x, &q.x)?;
        let not_eq_y = self.native_gadget.is_not_equal(layouter, &p.y, &q.y)?;
        self.native_gadget.or(layouter, &[not_eq_x, not_eq_y])
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedBit<C::Base>, Error> {
        let (cx, cy) = constant.into().coordinates().unwrap();
        let eq_x = self.native_gadget.is_equal_to_fixed(layouter, &p.x, cx)?;
        let eq_y = self.native_gadget.is_equal_to_fixed(layouter, &p.y, cy)?;
        self.native_gadget.and(layouter, &[eq_x, eq_y])
    }

    fn is_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        p: &AssignedNativePoint<C>,
        constant: C::CryptographicGroup,
    ) -> Result<AssignedBit<C::Base>, Error> {
        let (cx, cy) = constant.into().coordinates().unwrap();
        let not_eq_x = self.native_gadget.is_not_equal_to_fixed(layouter, &p.x, cx)?;
        let not_eq_y = self.native_gadget.is_not_equal_to_fixed(layouter, &p.y, cy)?;
        self.native_gadget.or(layouter, &[not_eq_x, not_eq_y])
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
        let in_subgroup = a.in_subgroup && b.in_subgroup;
        Ok(AssignedNativePoint { x, y, in_subgroup })
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

    fn load_from_scratch(&self, layouter: &mut impl Layouter<C::Base>) -> Result<(), Error> {
        self.native_gadget.load_from_scratch(layouter)
    }
}

#[cfg(any(test, feature = "testing"))]
impl<C: EdwardsCurve> Sampleable for AssignedNativePoint<C> {
    fn sample_inner(rng: impl RngCore) -> C::CryptographicGroup {
        C::CryptographicGroup::random(rng)
    }
}

impl<C: EdwardsCurve> EccChip<C> {
    /// Creates an assigned Jubjub scalar from an integer represented as a
    /// sequence of little-endian bytes.
    pub fn scalar_from_le_bytes(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        bytes: &[AssignedByte<C::Base>],
    ) -> Result<AssignedScalarOfNativeCurve<C>, Error> {
        let mut bits = Vec::with_capacity(bytes.len() * 8);
        for byte in bytes {
            let byte_as_f: AssignedNative<C::Base> = self.native_gadget.convert(layouter, byte)?;
            bits.extend(self.native_gadget.assigned_to_le_bits(
                layouter,
                &byte_as_f,
                Some(8),
                true,
            )?)
        }
        Ok(AssignedScalarOfNativeCurve(bits))
    }
}

/// This conversion should not exist for Base -> Scalar. It is a tech debt. We
/// should fix this as soon as compact supports types (other than assigned
/// native) <https://github.com/midnightntwrk/midnight-circuits/issues/433>
impl<C: EdwardsCurve>
    ConversionInstructions<C::Base, AssignedNative<C::Base>, AssignedScalarOfNativeCurve<C>>
    for EccChip<C>
{
    fn convert_value(&self, _x: &C::Base) -> Option<C::ScalarExt> {
        unimplemented!("The caller should decide how to convert the value off-circuit, i.e., what to do with overflows.");
    }

    fn convert(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        x: &AssignedNative<C::Base>,
    ) -> Result<AssignedScalarOfNativeCurve<C>, Error> {
        Ok(AssignedScalarOfNativeCurve(
            self.native_gadget.assigned_to_le_bits(layouter, x, None, true)?,
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
            AssignedScalarOfNativeCurve<JubjubExtended>,
            EccChip<JubjubExtended>,
        >("public_inputs_scalar_var");
    }

    test!(equality, test_is_equal);

    test!(zero, test_zero_assertions);
    test!(zero, test_is_zero);

    test!(control_flow, test_select);
    test!(control_flow, test_cond_assert_equal);
    test!(control_flow, test_cond_swap);

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
