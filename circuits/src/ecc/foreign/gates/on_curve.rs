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

use core::marker::PhantomData;
use std::ops::Rem;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};
use num_bigint::{BigInt as BI, ToBigInt};
use num_traits::{One, Signed};

use crate::{
    ecc::curves::WeierstrassCurve,
    field::foreign::{
        field_chip::{FieldChip, FieldChipConfig},
        params::FieldEmulationParams,
        util::{
            compute_u, compute_vj, get_advice_vec, get_identity_auxiliary_bounds, pair_wise_prod,
            sum_bigints, sum_exprs, urem,
        },
    },
    instructions::{ArithInstructions, NativeInstructions},
    types::{AssignedBit, AssignedField, InnerValue},
    utils::util::{bigint_to_fe, fe_to_bigint, modulus},
};

/// Foreign ECC OnCurve configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OnCurveConfig<C: WeierstrassCurve> {
    q_on_curve: Selector,
    u_bounds: (BI, BI),
    vs_bounds: Vec<(BI, BI)>,
    cond_col: Column<Advice>,
    _marker: PhantomData<C>,
}

impl<C: WeierstrassCurve> OnCurveConfig<C> {
    /// Checks that the FieldEmulationParams are sound for implementing the
    /// assertion that a point satisfies the curve equation.
    /// Returns (k_min, u_max), {(lj_min, vj_max)}_j,
    /// which are parameters involved in the identities enforced by the ModArith
    /// custom gate. We refer to the implementation of this function for
    /// explanations on what such values represent.
    pub fn bounds<F, P>() -> ((BI, BI), Vec<(BI, BI)>)
    where
        F: PrimeField,
        P: FieldEmulationParams<F, C::Base>,
    {
        let base = BI::from(2).pow(P::LOG2_BASE);
        let nb_limbs = P::NB_LIMBS;
        let moduli = P::moduli();
        let bs = P::base_powers();
        let bs2 = P::double_base_powers();

        let b = fe_to_bigint::<C::Base>(&C::B);

        // Recall that limbs x_i represent emulated field element 1 + sum_i base^i x_i.
        // Let x := 1 + sum_i base^i x_i
        //     y := 1 + sum_i base^i y_i
        //     z := 1 + sum_i base^i z_i
        //
        // We will have a custom gate enforcing equation:
        //   y^2 - (x * z + b) = 0  (mod m)
        //
        // So if z equals to x^2 (mod m), this is asserting that (x, y) satisfies the
        // curve equation.
        //
        // Define:
        //   sum_x := sum_i (base^i % m) * x_i
        //   sum_y := sum_i (base^i % m) * y_i
        //   sum_z := sum_i (base^i % m) * z_i
        //  sum_xz := sum_i (sum_j (base^{i+j} % m) * x_i * z_j)
        //  sum_y2 := sum_i (sum_j (base^{i+j} % m) * y_i * y_j)
        //
        // We enforce y^2 = x * z + b (mod m) with equation:
        //   2 * sum_y + sum_y2 - (sum_xz + sum_z + sum_x + b) = k * m

        let limbs_max = vec![&base - BI::one(); nb_limbs as usize];
        let limbs_max2 = vec![(&base - BI::one()).pow(2); (nb_limbs * nb_limbs) as usize];
        let max_sum_x = sum_bigints(&bs, &limbs_max);
        let max_sum_y = max_sum_x.clone();
        let max_sum_z = max_sum_x.clone();
        let max_sum_xz = sum_bigints(&bs2, &limbs_max2);
        let max_sum_y2 = max_sum_xz.clone();
        let expr_min = -(&max_sum_xz + max_sum_z + max_sum_x + &b);
        let expr_max = BI::from(2) * max_sum_y + max_sum_y2;
        let expr_bounds = (expr_min, expr_max);

        let expr_mj_bounds: Vec<_> = moduli
            .iter()
            .map(|mj| {
                let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let max_sum_x_mj = sum_bigints(&bs_mj, &limbs_max);
                let max_sum_y_mj = max_sum_x_mj.clone();
                let max_sum_z_mj = max_sum_x_mj.clone();
                let max_sum_xz_mj = sum_bigints(&bs2_mj, &limbs_max2);
                let max_sum_y2_mj = max_sum_xz_mj.clone();
                let expr_mj_min = -(&max_sum_xz_mj + max_sum_z_mj + max_sum_x_mj + urem(&b, mj));
                let expr_mj_max = BI::from(2) * max_sum_y_mj + max_sum_y2_mj;
                (expr_mj_min, expr_mj_max)
            })
            .collect();
        get_identity_auxiliary_bounds::<F, C::Base>(
            "on_curve",
            &moduli,
            expr_bounds,
            &expr_mj_bounds,
        )
    }

    /// Configures the foreign on_curve gate
    pub fn configure<F, P>(
        meta: &mut ConstraintSystem<F>,
        field_chip_config: &FieldChipConfig,
        cond_col: &Column<Advice>,
    ) -> OnCurveConfig<C>
    where
        F: PrimeField,
        P: FieldEmulationParams<F, C::Base>,
    {
        let m = &modulus::<C::Base>().to_bigint().unwrap();
        let moduli = P::moduli();
        let bs = P::base_powers();
        let bs2 = P::double_base_powers();

        let ((k_min, u_max), vs_bounds) = Self::bounds::<F, P>();

        let b = fe_to_bigint::<C::Base>(&C::B);

        let q_on_curve = meta.selector();

        // The layout is in two rows:
        // | x0 ... xk | z0 ... zk        |
        // | y0 ... yk | u v0 ... vl cond |
        // For this, we require that x_cols and z_cols be disjoint and the same for
        // y_cols, u_col, vs_cols and cond_col.

        meta.create_gate("Foreign-field EC is_on_curve", |meta| {
            let cond = meta.query_advice(*cond_col, Rotation::next());
            let xs = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::cur());
            let ys = get_advice_vec(meta, &field_chip_config.y_cols, Rotation::next());
            let zs = get_advice_vec(meta, &field_chip_config.z_cols, Rotation::cur());
            let u = meta.query_advice(field_chip_config.u_col, Rotation::next());
            let vs = get_advice_vec(meta, &field_chip_config.v_cols, Rotation::next());

            let xzs = pair_wise_prod(&xs, &zs);
            let y2s = pair_wise_prod(&ys, &ys);

            let const_b = Expression::Constant(bigint_to_fe::<F>(&b));

            // 2 * sum_y + sum_y2 - (sum_xz + sum_z + (a+1) * sum_x + b) = (u + k_min) * m
            let native_id = &cond
                * (Expression::Constant(F::from(2)) * sum_exprs::<F>(&bs, &ys)
                    + sum_exprs::<F>(&bs2, &y2s)
                    - (sum_exprs::<F>(&bs2, &xzs)
                        + sum_exprs::<F>(&bs, &zs)
                        + sum_exprs::<F>(&bs, &xs)
                        + const_b)
                    - (&u + Expression::Constant(bigint_to_fe::<F>(&k_min)))
                        * Expression::Constant(bigint_to_fe::<F>(m)));
            let mut moduli_ids = moduli
                .iter()
                .zip(vs)
                .zip(vs_bounds.iter())
                .map(|((mj, vj), vj_bounds)| {
                    let (lj_min, _vj_max) = vj_bounds;
                    let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let const_b_mj = Expression::Constant(bigint_to_fe::<F>(&urem(&b, mj)));

                    // 2 * sum_y_mj + sum_y2_mj - (sum_xz_mj + sum_z_mj
                    //  + ((a+1) % mj) * sum_x_mj + b % mj)
                    //  - u * (m % mj) - (k_min * m) % mj - (vj + lj_min) * mj = 0
                    &cond
                        * (Expression::Constant(F::ONE + F::ONE) * sum_exprs::<F>(&bs_mj, &ys)
                            + sum_exprs::<F>(&bs2_mj, &y2s)
                            - (sum_exprs::<F>(&bs2_mj, &xzs)
                                + sum_exprs::<F>(&bs_mj, &zs)
                                + sum_exprs::<F>(&bs_mj, &xs)
                                + const_b_mj)
                            - &u * Expression::Constant(bigint_to_fe::<F>(&urem(m, mj)))
                            - Expression::Constant(bigint_to_fe::<F>(&urem(&(&k_min * m), mj)))
                            - (vj + Expression::Constant(bigint_to_fe::<F>(lj_min)))
                                * Expression::Constant(bigint_to_fe::<F>(mj)))
                })
                .collect::<Vec<_>>();
            moduli_ids.push(native_id);

            Constraints::with_selector(q_on_curve, moduli_ids)
        });

        OnCurveConfig {
            q_on_curve,
            u_bounds: (k_min, u_max),
            vs_bounds,
            cond_col: *cond_col,
            _marker: PhantomData,
        }
    }
}

/// If `cond = 1`, it asserts that `(x, y)` satisfy the curve `C` equation:
///   `y^2 = x^3 + b`.
///
/// If `cond = 0`, it asserts nothing.
pub fn assert_is_on_curve<F, C, P, N>(
    layouter: &mut impl Layouter<F>,
    cond: &AssignedBit<F>,
    x: &AssignedField<F, C::Base, P>,
    y: &AssignedField<F, C::Base, P>,
    base_chip: &FieldChip<F, C::Base, P, N>,
    on_curve_config: &OnCurveConfig<C>,
) -> Result<(), Error>
where
    F: PrimeField,
    C: WeierstrassCurve,
    P: FieldEmulationParams<F, C::Base>,
    N: NativeInstructions<F>,
{
    let m = &modulus::<C::Base>().to_bigint().unwrap();
    let moduli = P::moduli();
    let bs = P::base_powers();
    let bs2 = P::double_base_powers();
    let field_chip_config = base_chip.config();

    let b = fe_to_bigint::<C::Base>(&C::B);
    assert!(!BI::is_negative(&b));

    let x = base_chip.normalize(layouter, x)?;
    let y = base_chip.normalize(layouter, y)?;
    let z = base_chip.mul(layouter, &x, &x, None)?;

    let range_checks = layouter.assign_region(
        || "assert is on curve",
        |mut region| {
            let mut offset = 0;

            let xs = x.bigint_limbs();
            let ys = y.bigint_limbs();
            let zs = z.bigint_limbs();

            let xzs = xs
                .clone()
                .zip(zs.clone())
                .map(|(xs, zs)| pair_wise_prod(&xs, &zs));
            let y2s = ys.clone().map(|ys| pair_wise_prod(&ys, &ys));

            let (k_min, u_max) = on_curve_config.u_bounds.clone();

            // 2 * sum_y + sum_y2 - (sum_xz + sum_z + (a+1) * sum_x + b) = (u + k_min) * m
            let expr = ys.clone().map(|v| BI::from(2) * sum_bigints(&bs, &v) - &b)
                + y2s.clone().map(|v| sum_bigints(&bs2, &v))
                - xzs.clone().map(|v| sum_bigints(&bs2, &v))
                - zs.clone().map(|v| sum_bigints(&bs, &v))
                - xs.clone().map(|v| sum_bigints(&bs, &v));
            let u = expr.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

            let vs_values =
                moduli
                    .iter()
                    .zip(on_curve_config.vs_bounds.iter())
                    .map(|(mj, vj_bounds)| {
                        let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                        let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                        let (lj_min, vj_max) = vj_bounds.clone();

                        // 2 * sum_y_mj + sum_y2_mj
                        //  - (sum_xz_mj + sum_z_mj + (a+1) * sum_x_mj + b)
                        //  - u * (m % mj) - (k_min * m) % mj = (vj + lj_min) * mj
                        let expr_mj = ys
                            .clone()
                            .map(|v| BI::from(2) * sum_bigints(&bs_mj, &v) - &b)
                            + y2s.clone().map(|v| sum_bigints(&bs2_mj, &v))
                            - xzs.clone().map(|v| sum_bigints(&bs2_mj, &v))
                            - zs.clone().map(|v| sum_bigints(&bs_mj, &v))
                            - xs.clone().map(|v| sum_bigints(&bs_mj, &v));
                        expr_mj.zip(u.clone()).map(|(e, u)| {
                            compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value())
                        })
                    });

            on_curve_config.q_on_curve.enable(&mut region, offset)?;

            let x_limbs = x.limb_values();
            let y_limbs = y.limb_values();
            let z_limbs = z.limb_values();

            let x_iter = x_limbs.iter().zip(field_chip_config.x_cols.iter());
            let z_iter = z_limbs.iter().zip(field_chip_config.z_cols.iter());
            x_iter
                .chain(z_iter)
                .map(|(cell, &col)| cell.copy_advice(|| "ECC.mem input", &mut region, col, offset))
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            y_limbs
                .iter()
                .zip(field_chip_config.y_cols.iter())
                .map(|(cell, &col)| cell.copy_advice(|| "ECC.mem input", &mut region, col, offset))
                .collect::<Result<Vec<_>, _>>()?;

            let u_value = u.clone().map(|u| bigint_to_fe::<F>(&u));
            let u_cell = region.assign_advice(
                || "ECC.mem u",
                field_chip_config.u_col,
                offset,
                || u_value,
            )?;

            let vs_cells = vs_values
                .zip(field_chip_config.v_cols.iter())
                .map(|(vj, &vj_col)| {
                    let vj_value = vj.map(|vj| bigint_to_fe::<F>(&vj));
                    region.assign_advice(|| "ECC.mem vj", vj_col, offset, || vj_value)
                })
                .collect::<Result<Vec<_>, _>>()?;

            cond.0.copy_advice(
                || "ECC.mem cond",
                &mut region,
                on_curve_config.cond_col,
                offset,
            )?;

            // u_cell will be range-checked in [0, u_max)
            let u_range_check = (u_cell, u_max);

            // Every vj_cell will be range-checked in [0, vj_max)
            let vs_max = on_curve_config
                .vs_bounds
                .clone()
                .into_iter()
                .map(|(_, vj_max)| vj_max);
            let vs_range_checks = vs_cells
                .into_iter()
                .zip(vs_max.collect::<Vec<_>>())
                .collect::<Vec<_>>();

            // We return an iterator over values that need to be range-checked
            Ok([u_range_check]
                .into_iter()
                .chain(vs_range_checks.into_iter())
                .collect::<Vec<_>>())
        },
    )?;

    // Assert all range-checks
    range_checks.into_iter().try_for_each(|(cell, ubound)| {
        base_chip
            .native_gadget
            .assert_lower_than_fixed(layouter, &cell, ubound.magnitude())
    })?;

    Ok(())
}
