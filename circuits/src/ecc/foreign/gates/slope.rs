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

use std::{marker::PhantomData, ops::Rem};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};
use num_bigint::{BigInt as BI, ToBigInt};
use num_traits::One;

use crate::{
    ecc::curves::CircuitCurve,
    field::foreign::{
        field_chip::FieldChipConfig,
        params::FieldEmulationParams,
        util::{
            compute_u, compute_vj, get_advice_vec, get_identity_auxiliary_bounds, pair_wise_prod,
            sum_bigints, sum_exprs, urem,
        },
        FieldChip,
    },
    instructions::NativeInstructions,
    types::{AssignedBit, AssignedField, InnerValue},
    utils::util::{bigint_to_fe, fe_to_bigint, modulus},
};

/// Foreign ECC Slope configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SlopeConfig<C: CircuitCurve> {
    q_slope: Selector,
    u_bounds: (BI, BI),
    vs_bounds: Vec<(BI, BI)>,
    cond_col: Column<Advice>,
    _marker: PhantomData<C>,
}

impl<C: CircuitCurve> SlopeConfig<C> {
    /// Checks that the FieldEmulationParams are sound for implementing the
    /// modular assertion on the slope between two points.
    /// Returns (k_min, u_max), {(lj_min, vj_max)}_j, which are parameters
    /// involved in the identities enforced by the ModArith custom gate.
    /// We refer to the implementation of this function for explanations on
    /// what such values represent.
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

        // Recall that limbs x_i represent emulated field element 1 + sum_i base^i x_i.
        // Let px := 1 + sum_i base^i px_i
        //     py := 1 + sum_i base^i py_i
        //     qx := 1 + sum_i base^i qx_i
        //     qy := 1 + sum_i base^i qy_i
        // lambda := 1 + sum_i base^i lambda_i
        //
        // We will have a custom gate enforcing equation:
        //  ± qy - py = lambda * (qx - px)   (mod m)
        //
        // This asserts that the slope between points (qx, ±qy) and (px, py) is lambda.
        // If the two points are equal, this condition becomes trivial.

        // Define:
        //      sum_px := sum_i (base^i % m) * px_i
        //      sum_py := sum_i (base^i % m) * py_i
        //      sum_qx := sum_i (base^i % m) * qx_i
        //      sum_qy := sum_i (base^i % m) * qy_i
        //  sum_lambda := sum_i (base^i % m) * lambda_i
        //     sum_lpx := sum_i (sum_j (base^{i+j} % m) * lambda_i * px_j)
        //     sum_lqx := sum_i (sum_j (base^{i+j} % m) * lambda_i * qx_j)
        //        sign in {-1, 1}

        // We enforce:
        //  sign * (1 + sum_qy) - (1 + sum_py)
        //   - (1 + sum_lambda) * ((1 + sum_qx) - (1 + sum_px)) = k * m
        //
        // Which can be simplified to:
        //  sign - 1 + sign * sum_qy - sum_py
        //    - sum_qx + sum_px - sum_lqx + sum_lpx = k * m

        let limbs_max = vec![&base - BI::one(); nb_limbs as usize];
        let limbs_max2 = vec![(&base - BI::one()).pow(2); (nb_limbs * nb_limbs) as usize];
        let max_sum_px = sum_bigints(&bs, &limbs_max);
        let max_sum_py = max_sum_px.clone();
        let max_sum_qx = max_sum_px.clone();
        let max_sum_qy = max_sum_px.clone();
        let max_sum_lpx = sum_bigints(&bs2, &limbs_max2);
        let max_sum_lqx = max_sum_lpx.clone();
        let expr_min = -(BI::from(2) + &max_sum_qy + max_sum_py + max_sum_qx + max_sum_lqx);
        let expr_max = max_sum_qy + max_sum_px + max_sum_lpx;
        let expr_bounds = (expr_min, expr_max);

        let expr_mj_bounds: Vec<_> = moduli
            .iter()
            .map(|mj| {
                let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let max_sum_px_mj = sum_bigints(&bs_mj, &limbs_max);
                let max_sum_py_mj = max_sum_px_mj.clone();
                let max_sum_qx_mj = max_sum_px_mj.clone();
                let max_sum_qy_mj = max_sum_px_mj.clone();
                let max_sum_lpx_mj = sum_bigints(&bs2_mj, &limbs_max2);
                let max_sum_lqx_mj = max_sum_lpx_mj.clone();
                let expr_mj_min = -(BI::from(2)
                    + &max_sum_qy_mj
                    + max_sum_py_mj
                    + max_sum_qx_mj
                    + max_sum_lqx_mj);
                let expr_mj_max = max_sum_qy_mj + max_sum_px_mj + max_sum_lpx_mj;
                (expr_mj_min, expr_mj_max)
            })
            .collect();
        get_identity_auxiliary_bounds::<F, C::Base>("slope", &moduli, expr_bounds, &expr_mj_bounds)
    }

    /// Configures the  foreign slope gate
    pub fn configure<F, P>(
        meta: &mut ConstraintSystem<F>,
        field_chip_config: &FieldChipConfig,
        cond_col: &Column<Advice>,
    ) -> SlopeConfig<C>
    where
        F: PrimeField,
        P: FieldEmulationParams<F, C::Base>,
    {
        let m = &modulus::<C::Base>().to_bigint().unwrap();
        let moduli = P::moduli();
        let bs = P::base_powers();
        let bs2 = P::double_base_powers();

        let ((k_min, u_max), vs_bounds) = Self::bounds::<F, P>();

        let q_slope = meta.selector();

        // The layout is in three rows:
        // | px_0 ... px_k | qx_0 ... qx_k    |
        // | py_0 ... py_k | qy_0 ... qy_k    |  <- selector enabled here
        // |  λ_0 ...  λ_k | u v0 ... vl cond |

        meta.create_gate("Foreign-field EC lambda slope", |meta| {
            let cond = meta.query_advice(*cond_col, Rotation::next());
            // We store the sign in the same place as `cond`. This is no problem, as
            // when `cond = 0` the gate will be disabled, and when it is enabled,
            // we will have `cond = ±1`, which is fine.
            // It is the responsibility of the caller to make sure that `cond = ±1`,
            // when enabled, this is not asserted with constraints.
            let sign = cond.clone();
            let pxs = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::prev());
            let pys = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::cur());
            let qxs = get_advice_vec(meta, &field_chip_config.z_cols, Rotation::prev());
            let qys = get_advice_vec(meta, &field_chip_config.z_cols, Rotation::cur());
            let lambdas = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::next());
            let u = meta.query_advice(field_chip_config.u_col, Rotation::next());
            let vs = get_advice_vec(meta, &field_chip_config.v_cols, Rotation::next());

            let lpxs = pair_wise_prod(&lambdas, &pxs);
            let lqxs = pair_wise_prod(&lambdas, &qxs);

            // sign - 1 + sign * sum_qy - sum_py - sum_qx + sum_px - sum_lqx + sum_lpx
            //  = (u + k_min) * m

            let native_id = cond.clone()
                * (sign.clone() - Expression::Constant(F::ONE)
                    + sign.clone() * sum_exprs::<F>(&bs, &qys)
                    - sum_exprs::<F>(&bs, &pys)
                    - sum_exprs::<F>(&bs, &qxs)
                    + sum_exprs::<F>(&bs, &pxs)
                    - sum_exprs::<F>(&bs2, &lqxs)
                    + sum_exprs::<F>(&bs2, &lpxs)
                    - (u.clone() + Expression::Constant(bigint_to_fe::<F>(&k_min)))
                        * Expression::Constant(bigint_to_fe::<F>(m)));
            let mut moduli_ids = moduli
                .iter()
                .zip(vs.iter())
                .zip(vs_bounds.iter())
                .map(|((mj, vj), vj_bounds)| {
                    let (lj_min, _vj_max) = vj_bounds;
                    let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    // sign - 1 + sign * sum_qy_mj - sum_py_mj
                    //  - sum_qx_mj + sum_px_mj - sum_lqx_mj + sum_lpx_mj
                    //  - u * (m % mj) - (k_min * m) % mj - (vj + lj_min) * mj = 0
                    cond.clone()
                        * (sign.clone() - Expression::Constant(F::ONE)
                            + sign.clone() * sum_exprs::<F>(&bs_mj, &qys)
                            - sum_exprs::<F>(&bs_mj, &pys)
                            - sum_exprs::<F>(&bs_mj, &qxs)
                            + sum_exprs::<F>(&bs_mj, &pxs)
                            - sum_exprs::<F>(&bs2_mj, &lqxs)
                            + sum_exprs::<F>(&bs2_mj, &lpxs)
                            - u.clone() * Expression::Constant(bigint_to_fe::<F>(&urem(m, mj)))
                            - Expression::Constant(bigint_to_fe::<F>(&urem(&(&k_min * m), mj)))
                            - (vj.clone() + Expression::Constant(bigint_to_fe::<F>(lj_min)))
                                * Expression::Constant(bigint_to_fe::<F>(mj)))
                })
                .collect::<Vec<_>>();
            moduli_ids.push(native_id);

            Constraints::with_selector(q_slope, moduli_ids)
        });

        SlopeConfig {
            q_slope,
            u_bounds: (k_min, u_max),
            vs_bounds,
            cond_col: *cond_col,
            _marker: PhantomData,
        }
    }
}

/// If `cond = 1`, it asserts that `lambda * (q.0 - p.0) = (sign * q.1 - p.1)`,
/// where `sign := q.2 ? -1 : +1`.
///
/// If `cond = 0`, it asserts nothing.
#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
pub fn assert_slope<F, C, P, N>(
    layouter: &mut impl Layouter<F>,
    cond: &AssignedBit<F>,
    p: (&AssignedField<F, C::Base, P>, &AssignedField<F, C::Base, P>),
    q: (
        &AssignedField<F, C::Base, P>,
        &AssignedField<F, C::Base, P>,
        bool,
    ),
    lambda: &AssignedField<F, C::Base, P>,
    base_chip: &FieldChip<F, C::Base, P, N>,
    slope_config: &SlopeConfig<C>,
) -> Result<(), Error>
where
    F: PrimeField,
    C: CircuitCurve,
    P: FieldEmulationParams<F, C::Base>,
    N: NativeInstructions<F>,
{
    let m = &modulus::<C::Base>().to_bigint().unwrap();
    let moduli = P::moduli();
    let bs = P::base_powers();
    let bs2 = P::double_base_powers();
    let base_chip_config = base_chip.config();

    let px = &base_chip.normalize(layouter, p.0)?;
    let py = &base_chip.normalize(layouter, p.1)?;
    let qx = &base_chip.normalize(layouter, q.0)?;
    let qy = &base_chip.normalize(layouter, q.1)?;
    let lambda = &base_chip.normalize(layouter, lambda)?;
    let negate_q = q.2;

    // If `negate_q = true`, we negate `cond` so that the sign becomes `-1`.
    // In case `cond` was `0`, it will remain `0`.
    let mut cond_as_assigned_value = cond.clone().into();
    if negate_q {
        cond_as_assigned_value = base_chip
            .native_gadget
            .neg(layouter, &cond_as_assigned_value)?;
    };

    let mut range_checks = layouter.assign_region(
        || "Slope",
        |mut region| {
            let mut offset = 0;

            let pxs = px.bigint_limbs();
            let pys = py.bigint_limbs();
            let qxs = qx.bigint_limbs();
            let qys = qy.bigint_limbs();
            let lambdas = lambda.bigint_limbs();

            let lpxs = lambdas
                .clone()
                .zip(pxs.clone())
                .map(|(ls, pxs)| pair_wise_prod(&ls, &pxs));
            let lqxs = lambdas
                .clone()
                .zip(qxs.clone())
                .map(|(ls, qxs)| pair_wise_prod(&ls, &qxs));

            let (k_min, u_max) = slope_config.u_bounds.clone();

            let sign = cond_as_assigned_value
                .value()
                .map(|v| fe_to_bigint::<F>(&(*v + F::ONE)) - BI::one());

            // sign - 1 + sign * sum_qy - sum_py - sum_qx + sum_px - sum_lqx + sum_lpx
            //  = (u + k_min) * m
            let expr = sign.clone()
                + sign
                    .clone()
                    .zip(qys.clone())
                    .map(|(s, qys)| s * sum_bigints(&bs, &qys) - BI::one())
                - pys.clone().map(|v| sum_bigints(&bs, &v))
                - qxs.clone().map(|v| sum_bigints(&bs, &v))
                + pxs.clone().map(|v| sum_bigints(&bs, &v))
                - lqxs.clone().map(|v| sum_bigints(&bs2, &v))
                + lpxs.clone().map(|v| sum_bigints(&bs2, &v));
            let u = expr.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

            let vs_values =
                moduli
                    .iter()
                    .zip(slope_config.vs_bounds.iter())
                    .map(|(mj, vj_bounds)| {
                        let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                        let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                        let (lj_min, vj_max) = vj_bounds.clone();

                        // sign - 1 + sign * sum_qy_mj - sum_py_mj
                        //  - sum_qx_mj + sum_px_mj - sum_lqx_mj + sum_lpx_mj
                        //  - u * (m % mj) - (k_min * m) % mj = (vj + lj_min) * mj
                        let expr_mj = sign.clone()
                            + sign
                                .clone()
                                .zip(qys.clone())
                                .map(|(s, qys)| s * sum_bigints(&bs_mj, &qys) - BI::one())
                            - pys.clone().map(|v| sum_bigints(&bs_mj, &v))
                            - qxs.clone().map(|v| sum_bigints(&bs_mj, &v))
                            + pxs.clone().map(|v| sum_bigints(&bs_mj, &v))
                            - lqxs.clone().map(|v| sum_bigints(&bs2_mj, &v))
                            + lpxs.clone().map(|v| sum_bigints(&bs2_mj, &v));
                        expr_mj.zip(u.clone()).map(|(e, u)| {
                            compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value())
                        })
                    });

            let px_limbs = px.limb_values();
            let qx_limbs = qx.limb_values();
            let lambda_limbs = lambda.limb_values();
            let px_iter = px_limbs.iter().zip(base_chip_config.x_cols.iter());
            let qx_iter = qx_limbs.iter().zip(base_chip_config.z_cols.iter());

            px_iter
                .chain(qx_iter)
                .map(|(cell, &col)| cell.copy_advice(|| "ECC.slope x", &mut region, col, offset))
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            slope_config.q_slope.enable(&mut region, offset)?;

            let py_limbs = py.limb_values();
            let qy_limbs = qy.limb_values();
            let py_iter = py_limbs.iter().zip(base_chip_config.x_cols.iter());
            let qy_iter = qy_limbs.iter().zip(base_chip_config.z_cols.iter());
            py_iter
                .chain(qy_iter)
                .map(|(cell, &col)| cell.copy_advice(|| "ECC.slope y", &mut region, col, offset))
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            lambda_limbs
                .iter()
                .zip(base_chip_config.x_cols.iter())
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "ECC.slope lambda", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            let u_value = u.clone().map(|u| bigint_to_fe::<F>(&u));
            let u_cell = region.assign_advice(
                || "ECC.slope u",
                base_chip_config.u_col,
                offset,
                || u_value,
            )?;

            let vs_cells = vs_values
                .zip(base_chip_config.v_cols.iter())
                .map(|(vj, &vj_col)| {
                    let vj_value = vj.map(|vj| bigint_to_fe::<F>(&vj));
                    region.assign_advice(|| "ECC.slope vj", vj_col, offset, || vj_value)
                })
                .collect::<Result<Vec<_>, _>>()?;

            cond_as_assigned_value.copy_advice(
                || "ECC.slope cond",
                &mut region,
                slope_config.cond_col,
                offset,
            )?;

            // u_cell will be range-checked in [0, u_max)
            let u_range_check = (u_cell, u_max);

            // Every vj_cell will be range-checked in [0, vj_max)
            let vs_max = slope_config
                .vs_bounds
                .clone()
                .into_iter()
                .map(|(_, vj_max)| vj_max);
            let vs_range_checks = vs_cells
                .into_iter()
                .zip(vs_max.collect::<Vec<_>>())
                .collect::<Vec<_>>();

            // Assert all range-checks
            Ok([u_range_check]
                .into_iter()
                .chain(vs_range_checks.into_iter()))
        },
    )?;

    range_checks.try_for_each(|(cell, ubound)| {
        base_chip
            .native_gadget
            .assert_lower_than_fixed(layouter, &cell, ubound.magnitude())
    })
}
