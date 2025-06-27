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

use std::ops::Rem;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use num_bigint::{BigInt as BI, ToBigInt};
use num_traits::One;

use crate::{
    field::foreign::{
        params::FieldEmulationParams,
        util::{
            compute_u, compute_vj, get_advice_vec, get_identity_auxiliary_bounds, pair_wise_prod,
            sum_bigints, sum_exprs, urem,
        },
    },
    instructions::RangeCheckInstructions,
    types::{AssignedField, AssignedNative},
    utils::util::{bigint_to_fe, modulus},
};

/// Foreign-Field Mul configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MulConfig {
    q_mul: Selector,
    u_bounds: (BI, BI),
    vs_bounds: Vec<(BI, BI)>,
    xy_cols: Vec<Column<Advice>>,
    z_cols: Vec<Column<Advice>>,
}

impl MulConfig {
    /// Checks that the FieldEmulationParams are sound for implementing the
    /// emulated multiplication gate. Returns (k_min, u_max), {(lj_min,
    /// vj_max)}_j, which are parameters involved in the identities enforced
    /// by the ModArith custom gate. We refer to the implementation of this
    /// function for explanations on what such values represent.
    pub fn bounds<F, K, P>() -> ((BI, BI), Vec<(BI, BI)>)
    where
        F: PrimeField,
        K: PrimeField,
        P: FieldEmulationParams<F, K>,
    {
        let base = BI::from(2).pow(P::LOG2_BASE);
        let nb_limbs = P::NB_LIMBS;
        let moduli = P::moduli();
        let base_powers = P::base_powers();
        let double_base_powers = P::double_base_powers();

        // Note that x := 1 + sum_i base^i x_i, and that y, z are defined analogously.
        //
        // We enforce z - x * y = 0 (mod m) with the equation:
        //  sum_xy + sum_x + sum_y - sum_z = k * m
        //
        // where
        //  sum_xy := sum_i (sum_j (base^{i+j} % m) * x_i * y_j),
        //   sum_x := sum_i (base^i % m) * x_i ,
        //   sum_y := sum_i (base^i % m) * y_i ,
        //   sum_z := sum_i (base^i % m) * z_i .

        let limbs_max = vec![&base - BI::one(); nb_limbs as usize];
        let limbs_max2 = vec![(&base - BI::one()).pow(2); (nb_limbs * nb_limbs) as usize];
        let max_sum_xy = sum_bigints(&double_base_powers, &limbs_max2);
        let max_sum_z = sum_bigints(&base_powers, &limbs_max);
        let max_sum_x = max_sum_z.clone();
        let max_sum_y = max_sum_z.clone();
        let expr_min = -max_sum_z;
        let expr_max = &max_sum_xy + &max_sum_x + &max_sum_y;
        let expr_bounds = (expr_min, expr_max);

        let expr_mj_bounds: Vec<_> = moduli
            .iter()
            .map(|mj| {
                let base_powers_mj = base_powers.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let double_base_powers_mj = double_base_powers
                    .iter()
                    .map(|b| b.rem(mj))
                    .collect::<Vec<_>>();
                let max_sum_xy_mj = sum_bigints(&double_base_powers_mj, &limbs_max2);
                let max_sum_z_mj = sum_bigints(&base_powers_mj, &limbs_max);
                let max_sum_x_mj = max_sum_z_mj.clone();
                let max_sum_y_mj = max_sum_z_mj.clone();
                let expr_mj_min = -max_sum_z_mj;
                let expr_mj_max = &max_sum_xy_mj + &max_sum_x_mj + &max_sum_y_mj;
                (expr_mj_min, expr_mj_max)
            })
            .collect();
        get_identity_auxiliary_bounds::<F, K>("mul", &moduli, expr_bounds, &expr_mj_bounds)
    }

    /// Configures the foreign multiplication chip
    pub fn configure<F, K, P>(
        meta: &mut ConstraintSystem<F>,
        xy_cols: &[Column<Advice>],
        z_cols: &[Column<Advice>],
    ) -> Self
    where
        F: PrimeField,
        K: PrimeField,
        P: FieldEmulationParams<F, K>,
    {
        let m = &modulus::<K>().to_bigint().unwrap();
        let base_powers = P::base_powers();
        let double_base_powers = P::double_base_powers();
        let moduli = P::moduli();

        let ((k_min, u_max), vs_bounds) = Self::bounds::<F, K, P>();

        let q_mul = meta.selector();

        // The layout is in two rows:
        // | x0 ... xk | z0 ... zk   |  <- selector enabled here
        // | y0 ... yk | u v0 ... vl |

        meta.create_gate("Foreign-field multiplication", |meta| {
            let q = meta.query_selector(q_mul);
            let xs = get_advice_vec(meta, xy_cols, Rotation::cur());
            let ys = get_advice_vec(meta, xy_cols, Rotation::next());
            let zs = get_advice_vec(meta, z_cols, Rotation::cur());
            let u = meta.query_advice(z_cols[0], Rotation::next());
            let vs = get_advice_vec(meta, &z_cols[1..=vs_bounds.len()], Rotation::next());

            let xys = pair_wise_prod(&xs, &ys);

            //  sum_xy + sum_x + sum_y - sum_z - (u + k_min) * m = 0
            let native_id = q.clone()
                * (sum_exprs::<F>(&double_base_powers, &xys)
                    + sum_exprs::<F>(&base_powers, &xs)
                    + sum_exprs::<F>(&base_powers, &ys)
                    - sum_exprs::<F>(&base_powers, &zs)
                    - (u.clone() + Expression::Constant(bigint_to_fe::<F>(&k_min)))
                        * Expression::Constant(bigint_to_fe::<F>(m)));
            let mut moduli_ids = moduli
                .iter()
                .zip(vs.iter())
                .zip(vs_bounds.iter())
                .map(|((mj, vj), vj_bounds)| {
                    let (lj_min, _vj_max) = vj_bounds;
                    let bij_powers_mj = double_base_powers
                        .iter()
                        .map(|b| b.rem(mj))
                        .collect::<Vec<_>>();
                    let bi_powers_mj = base_powers.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    //  sum_xy_mj + sum_x_mj + sum_y_mj - sum_z_mj - u * (m % mj) - (k_min * m) % mj
                    //    - (vj + lj_min) * mj = 0
                    q.clone()
                        * (sum_exprs::<F>(&bij_powers_mj, &xys)
                            + sum_exprs::<F>(&bi_powers_mj, &xs)
                            + sum_exprs::<F>(&bi_powers_mj, &ys)
                            - sum_exprs::<F>(&bi_powers_mj, &zs)
                            - u.clone() * Expression::Constant(bigint_to_fe::<F>(&urem(m, mj)))
                            - Expression::Constant(bigint_to_fe::<F>(&urem(&(&k_min * m), mj)))
                            - (vj.clone() + Expression::Constant(bigint_to_fe::<F>(lj_min)))
                                * Expression::Constant(bigint_to_fe::<F>(mj)))
                })
                .collect::<Vec<_>>();
            moduli_ids.push(native_id);
            moduli_ids
        });

        MulConfig {
            q_mul,
            u_bounds: (k_min, u_max),
            vs_bounds,
            xy_cols: xy_cols.to_vec(),
            z_cols: z_cols.to_vec(),
        }
    }
}

/// Asserts that the given AssignedField x, y, z are in a multiplicative
/// relation: x * y = z.
///
/// # Precondition
///
/// x, y and z are assumed to be well-formed.
pub fn assert_mul<F, K, P, RangeGadget>(
    layouter: &mut impl Layouter<F>,
    x: &AssignedField<F, K, P>,
    y: &AssignedField<F, K, P>,
    z: &AssignedField<F, K, P>,
    mul_config: &MulConfig,
    range_gadget: &RangeGadget,
) -> Result<(), Error>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    RangeGadget: RangeCheckInstructions<F, AssignedNative<F>>,
{
    let mut range_checks = layouter.assign_region(
        || "Foreign multiplication",
        |mut region| {
            let mut offset = 0;

            let m = &modulus::<K>().to_bigint().unwrap();
            let moduli = P::moduli();
            let base_powers = P::base_powers();
            let double_base_powers = P::double_base_powers();

            let xs = x.bigint_limbs();
            let ys = y.bigint_limbs();
            let zs = z.bigint_limbs();

            let xys = xs
                .clone()
                .zip(ys.clone())
                .map(|(xs, ys)| pair_wise_prod(&xs, &ys));
            let (k_min, u_max) = mul_config.u_bounds.clone();

            let expr = xys.clone().map(|v| sum_bigints(&double_base_powers, &v))
                + xs.clone().map(|v| sum_bigints(&base_powers, &v))
                + ys.clone().map(|v| sum_bigints(&base_powers, &v))
                - zs.clone().map(|v| sum_bigints(&base_powers, &v));
            let u = expr.map(|e| compute_u(m, &e, (&k_min, &u_max), Value::known(true)));

            let vs_values =
                moduli
                    .iter()
                    .zip(mul_config.vs_bounds.iter())
                    .map(|(mj, vj_bounds)| {
                        let base_powers_mj =
                            base_powers.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                        let double_base_powers_mj = double_base_powers
                            .iter()
                            .map(|b| b.rem(mj))
                            .collect::<Vec<_>>();
                        let (lj_min, vj_max) = vj_bounds.clone();

                        let expr_mj = xys.clone().map(|v| sum_bigints(&double_base_powers_mj, &v))
                            + xs.clone().map(|v| sum_bigints(&base_powers_mj, &v))
                            + ys.clone().map(|v| sum_bigints(&base_powers_mj, &v))
                            - zs.clone().map(|v| sum_bigints(&base_powers_mj, &v));
                        expr_mj.zip(u.clone()).map(|(e, u)| {
                            compute_vj(
                                m,
                                mj,
                                &e,
                                &u,
                                &k_min,
                                (&lj_min, &vj_max),
                                Value::known(true),
                            )
                        })
                    });

            mul_config.q_mul.enable(&mut region, offset)?;

            x.limb_values()
                .iter()
                .zip(mul_config.xy_cols.iter())
                .map(|(cell, &col)| cell.copy_advice(|| "assert_mul x", &mut region, col, offset))
                .collect::<Result<Vec<_>, _>>()?;

            z.limb_values()
                .iter()
                .zip(mul_config.z_cols.iter())
                .map(|(cell, &col)| cell.copy_advice(|| "assert_mul z", &mut region, col, offset))
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            y.limb_values()
                .iter()
                .zip(mul_config.xy_cols.iter())
                .map(|(cell, &col)| cell.copy_advice(|| "assert_mul y", &mut region, col, offset))
                .collect::<Result<Vec<_>, _>>()?;

            let u_value = u.clone().map(|u| bigint_to_fe::<F>(&u));
            let u_cell = region.assign_advice(
                || "assert_mul u",
                mul_config.z_cols[0],
                offset,
                || u_value,
            )?;

            let vs_cells = vs_values
                .zip(mul_config.z_cols[1..=mul_config.vs_bounds.len()].iter())
                .map(|(vj, &vj_col)| {
                    let vj_value = vj.map(|vj| bigint_to_fe::<F>(&vj));
                    region.assign_advice(|| "assert_mul vj", vj_col, offset, || vj_value)
                })
                .collect::<Result<Vec<_>, _>>()?;

            // u_cell will be range-checked in [0, u_max)
            let u_range_check = (u_cell, u_max);

            // Every vj_cell will be range-checked in [0, vj_max)
            let vs_max = mul_config
                .vs_bounds
                .clone()
                .into_iter()
                .map(|(_, vj_max)| vj_max.clone());
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
        range_gadget.assert_lower_than_fixed(layouter, &cell, ubound.magnitude())
    })
}
