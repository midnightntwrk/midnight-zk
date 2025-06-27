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
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use num_bigint::{BigInt as BI, ToBigInt};
use num_traits::One;

use crate::{
    ecc::curves::CircuitCurve,
    field::foreign::{
        params::FieldEmulationParams,
        util::{
            compute_u, compute_vj, get_advice_vec, get_identity_auxiliary_bounds, pair_wise_prod,
            sum_bigints, sum_exprs, urem,
        },
        FieldChip, FieldChipConfig,
    },
    instructions::NativeInstructions,
    types::{AssignedBit, AssignedField, InnerValue},
    utils::util::{bigint_to_fe, modulus},
};

/// Foreign-Field ECC Lambda-Squared configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LambdaSquaredConfig<C: CircuitCurve> {
    q_lambda_squared: Selector,
    u_bounds: (BI, BI),
    vs_bounds: Vec<(BI, BI)>,
    cond_col: Column<Advice>,
    _marker: PhantomData<C>,
}

impl<C: CircuitCurve> LambdaSquaredConfig<C> {
    /// Checks that the FieldEmulationParams are sound for implementing the
    /// assertion that the x-coordinate of three points add up to
    /// lambda squared. Returns (k_min, u_max), {(lj_min, vj_max)}_j, which
    /// are parameters involved in the identities enforced by the ModArith
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

        // Recall that limbs x_i represent emulated field element 1 + sum_i base^i x_i.
        // Let px := 1 + sum_i base^i px_i
        //     qx := 1 + sum_i base^i qx_i
        //     rx := 1 + sum_i base^i rx_i
        //  lamda := 1 + sum_i base^i lambda_i
        //
        // We will have a custom gate enforcing equation:
        //  px + qx + rx = lambda^2   (mod m)

        // Define:
        //      sum_px := sum_i (base^i % m) * px_i
        //      sum_qx := sum_i (base^i % m) * qx_i
        //      sum_rx := sum_i (base^i % m) * rx_i
        //  sum_lambda := sum_i (base^i % m) * lambda_i
        // sum_lambda2 := sum_i (sum_j (base^{i+j} % m) * lambda_i * lambda_j)

        // We enforce:
        //  (1 + sum_px) + (1 + sum_qx) + (1 + sum_rx)
        //    - (1 + 2 sum_lambda + sum_lambda2) = k * m
        //
        // Which can be simplified to:
        //  2 + sum_px + sum_qx + sum_rx - (2 sum_lambda + sum_lambda2) = k * m

        let limbs_max = vec![&base - BI::one(); nb_limbs as usize];
        let limbs_max2 = vec![(&base - BI::one()).pow(2); (nb_limbs * nb_limbs) as usize];
        let max_sum_px = sum_bigints(&bs, &limbs_max);
        let max_sum_qx = max_sum_px.clone();
        let max_sum_rx = max_sum_px.clone();
        let max_sum_lambda = max_sum_px.clone();
        let max_sum_lambda2 = sum_bigints(&bs2, &limbs_max2);
        let expr_min = BI::from(2) - (BI::from(2) * max_sum_lambda + max_sum_lambda2);
        let expr_max = BI::from(2) + max_sum_px + max_sum_qx + max_sum_rx;
        let expr_bounds = (expr_min, expr_max);

        let expr_mj_bounds: Vec<_> = moduli
            .iter()
            .map(|mj| {
                let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let max_sum_px_mj = sum_bigints(&bs_mj, &limbs_max);
                let max_sum_qx_mj = max_sum_px_mj.clone();
                let max_sum_rx_mj = max_sum_px_mj.clone();
                let max_sum_lambda_mj = max_sum_px_mj.clone();
                let max_sum_lambda2_mj = sum_bigints(&bs2_mj, &limbs_max2);
                let expr_min_mj =
                    BI::from(2) - (BI::from(2) * max_sum_lambda_mj + max_sum_lambda2_mj);
                let expr_max_mj = BI::from(2) + max_sum_px_mj + max_sum_qx_mj + max_sum_rx_mj;
                (expr_min_mj, expr_max_mj)
            })
            .collect();
        get_identity_auxiliary_bounds::<F, C::Base>(
            "lambda_squared",
            &moduli,
            expr_bounds,
            &expr_mj_bounds,
        )
    }

    /// Configures the foreign lambda_squared gate
    pub fn configure<F, P>(
        meta: &mut ConstraintSystem<F>,
        field_chip_config: &FieldChipConfig,
        cond_col: &Column<Advice>,
    ) -> LambdaSquaredConfig<C>
    where
        F: PrimeField,
        P: FieldEmulationParams<F, C::Base>,
    {
        let m = &modulus::<C::Base>().to_bigint().unwrap();
        let moduli = P::moduli();
        let bs = P::base_powers();
        let bs2 = P::double_base_powers();

        let ((k_min, u_max), vs_bounds) = Self::bounds::<F, P>();

        let q_lambda_squared = meta.selector();

        // The layout is in three rows:
        // | px_0 ... px_k |                  |
        // | qx_0 ... qx_k | rx_0 ... rx_k    |  <- selector enabled here
        // |  λ_0 ...  λ_k | u v0 ... vl cond |

        meta.create_gate("Foreign-field EC assert_lambda_squared", |meta| {
            let q = meta.query_selector(q_lambda_squared);
            let cond = meta.query_advice(*cond_col, Rotation::next());
            let pxs = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::prev());
            let qxs = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::cur());
            let rxs = get_advice_vec(meta, &field_chip_config.z_cols, Rotation::cur());
            let lambdas = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::next());
            let u = meta.query_advice(field_chip_config.u_col, Rotation::next());
            let vs = get_advice_vec(meta, &field_chip_config.v_cols, Rotation::next());

            let lambdas2 = pair_wise_prod(&lambdas, &lambdas);

            // 2 + sum_px + sum_qx + sum_rx - (2 sum_lambda + sum_lambda2)
            //   = (u + k_min) * m

            let two = Expression::Constant(F::from(2));
            let native_id = q.clone()
                * cond.clone()
                * (two.clone()
                    + sum_exprs::<F>(&bs, &pxs)
                    + sum_exprs::<F>(&bs, &qxs)
                    + sum_exprs::<F>(&bs, &rxs)
                    - two.clone() * sum_exprs::<F>(&bs, &lambdas)
                    - sum_exprs::<F>(&bs2, &lambdas2)
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
                    // 2 + sum_px_mj + sum_qx_mj + sum_rx_mj - (2 sum_lambda_mj + sum_lambda2_mj)
                    // - u * (m % mj) - (k_min * m) % mj - (vj + lj_min) * mj = 0
                    q.clone()
                        * cond.clone()
                        * (two.clone()
                            + sum_exprs::<F>(&bs_mj, &pxs)
                            + sum_exprs::<F>(&bs_mj, &qxs)
                            + sum_exprs::<F>(&bs_mj, &rxs)
                            - two.clone() * sum_exprs::<F>(&bs_mj, &lambdas)
                            - sum_exprs::<F>(&bs2_mj, &lambdas2)
                            - u.clone() * Expression::Constant(bigint_to_fe::<F>(&urem(m, mj)))
                            - Expression::Constant(bigint_to_fe::<F>(&urem(&(&k_min * m), mj)))
                            - (vj.clone() + Expression::Constant(bigint_to_fe::<F>(lj_min)))
                                * Expression::Constant(bigint_to_fe::<F>(mj)))
                })
                .collect::<Vec<_>>();
            moduli_ids.push(native_id);
            moduli_ids
        });

        LambdaSquaredConfig {
            q_lambda_squared,
            u_bounds: (k_min, u_max),
            vs_bounds,
            cond_col: *cond_col,
            _marker: PhantomData,
        }
    }
}

/// If `cond = 1`, it asserts that `xs.0 + xs.1 + xs.2 = lambda^2`.
///
/// If `cond = 0`, it asserts nothing.
#[allow(clippy::type_complexity)]
pub fn assert_lambda_squared<F, C, P, N>(
    layouter: &mut impl Layouter<F>,
    cond: &AssignedBit<F>,
    xs: (
        &AssignedField<F, C::Base, P>,
        &AssignedField<F, C::Base, P>,
        &AssignedField<F, C::Base, P>,
    ),
    lambda: &AssignedField<F, C::Base, P>,
    base_chip: &FieldChip<F, C::Base, P, N>,
    lambda_squared_config: &LambdaSquaredConfig<C>,
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
    let field_chip_config = base_chip.config();

    let px = &base_chip.normalize(layouter, xs.0)?;
    let qx = &base_chip.normalize(layouter, xs.1)?;
    let rx = &base_chip.normalize(layouter, xs.2)?;
    let lambda = &base_chip.normalize(layouter, lambda)?;

    let range_checks = layouter.assign_region(
        || "Lambda squared",
        |mut region| {
            let mut offset = 0;

            let pxs = px.bigint_limbs();
            let qxs = qx.bigint_limbs();
            let rxs = rx.bigint_limbs();
            let lambdas = lambda.bigint_limbs();

            let lambdas2 = lambdas.clone().map(|v| pair_wise_prod(&v, &v));

            let (k_min, u_max) = lambda_squared_config.u_bounds.clone();

            // 2 + sum_px + sum_qx + sum_rx - (2 sum_lambda + sum_lambda2)
            //   = (u + k_min) * m
            let expr = pxs.clone().map(|v| BI::from(2) + sum_bigints(&bs, &v))
                + qxs.clone().map(|v| sum_bigints(&bs, &v))
                + rxs.clone().map(|v| sum_bigints(&bs, &v))
                - lambdas.clone().map(|v| BI::from(2) * sum_bigints(&bs, &v))
                - lambdas2.clone().map(|v| sum_bigints(&bs2, &v));
            let u = expr.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

            let vs_values = moduli
                .iter()
                .zip(lambda_squared_config.vs_bounds.iter())
                .map(|(mj, vj_bounds)| {
                    let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let (lj_min, vj_max) = vj_bounds.clone();

                    // 2 + sum_px + sum_qx + sum_rx - (2 sum_lambda + sum_lambda2)
                    //  - u * (m % mj) - (k_min * m) % mj = (vj + lj_min) * mj
                    let expr_mj = pxs.clone().map(|v| BI::from(2) + sum_bigints(&bs_mj, &v))
                        + qxs.clone().map(|v| sum_bigints(&bs_mj, &v))
                        + rxs.clone().map(|v| sum_bigints(&bs_mj, &v))
                        - lambdas
                            .clone()
                            .map(|v| BI::from(2) * sum_bigints(&bs_mj, &v))
                        - lambdas2.clone().map(|v| sum_bigints(&bs2_mj, &v));
                    expr_mj.zip(u.clone()).map(|(e, u)| {
                        compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value())
                    })
                });

            let px_limbs = px.limb_values();
            let qx_limbs = qx.limb_values();
            let rx_limbs = rx.limb_values();

            px_limbs
                .iter()
                .zip(field_chip_config.x_cols.iter())
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "ECC.lambda_squared x", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            lambda_squared_config
                .q_lambda_squared
                .enable(&mut region, offset)?;

            let qx_iter = qx_limbs.iter().zip(field_chip_config.x_cols.iter());
            let rx_iter = rx_limbs.iter().zip(field_chip_config.z_cols.iter());
            qx_iter
                .chain(rx_iter)
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "ECC.lambda_squared x", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            lambda
                .limb_values()
                .iter()
                .zip(field_chip_config.x_cols.iter())
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "ECC.aligned lambda", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            let u_value = u.clone().map(|u| bigint_to_fe::<F>(&u));
            let u_cell = region.assign_advice(
                || "ECC.lambda_squared u",
                field_chip_config.u_col,
                offset,
                || u_value,
            )?;

            let vs_cells = vs_values
                .zip(field_chip_config.v_cols.iter())
                .map(|(vj, &vj_col)| {
                    let vj_value = vj.map(|vj| bigint_to_fe::<F>(&vj));
                    region.assign_advice(|| "ECC.lambda_squared vj", vj_col, offset, || vj_value)
                })
                .collect::<Result<Vec<_>, _>>()?;

            cond.0.copy_advice(
                || "ECC.lambda_squared cond",
                &mut region,
                lambda_squared_config.cond_col,
                offset,
            )?;

            // u_cell will be range-checked in [0, u_max)
            let u_range_check = (u_cell, u_max);

            // Every vj_cell will be range-checked in [0, vj_max)
            let vs_max = lambda_squared_config
                .clone()
                .vs_bounds
                .into_iter()
                .map(|(_, vj_max)| vj_max);
            let vs_range_checks = vs_cells
                .into_iter()
                .zip(vs_max.collect::<Vec<_>>())
                .collect::<Vec<_>>();

            // Assert all range-checks
            Ok([u_range_check]
                .into_iter()
                .chain(vs_range_checks.into_iter())
                .collect::<Vec<_>>())
        },
    )?;

    range_checks.iter().try_for_each(|(cell, ubound)| {
        base_chip
            .native_gadget
            .assert_lower_than_fixed(layouter, cell, ubound.magnitude())
    })
}
