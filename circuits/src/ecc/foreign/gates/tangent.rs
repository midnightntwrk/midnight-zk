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
    utils::util::{bigint_to_fe, modulus},
};

/// Foreign ECC tangent configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TangentConfig<C: CircuitCurve> {
    q_tangent: Selector,
    u_bounds: (BI, BI),
    vs_bounds: Vec<(BI, BI)>,
    cond_col: Column<Advice>,
    _marker: PhantomData<C>,
}

impl<C: CircuitCurve> TangentConfig<C> {
    /// Checks that the FieldEmulationParams are sound for implementing the
    /// assertion that lambda is the slope of the tangent to the
    /// curve at a given point. Returns (k_min, u_max), {(lj_min,
    /// vj_max)}_j, which are parameters involved in the identities enforced
    /// by the FFA custom gate. We refer to the implementation of this
    /// function for explanations on what such values represent.
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

        // Recall that limbs x_i represent integer 1 + sum_i base^i x_i.
        // Let px := 1 + sum_i base^i px_i
        //     py := 1 + sum_i base^i py_i
        // lambda := 1 + sum_i base^i lambda_i
        //
        // We will have a custom gate enforcing equation:
        //   3 * px^2 + a = 2 * py * lambda  (mod m)
        //
        // Define:
        //      sum_px := sum_i (base^i % m) * px_i
        //      sum_py := sum_i (base^i % m) * py_i
        //  sum_lambda := sum_i (base^i % m) * lambda_i
        //   sum_px2 := sum_i (sum_j (base^{i+j} % m) * px_i * px_j)
        //   sum_lpy := sum_i (sum_j (base^{i+j} % m) * lambda_i * py_j)

        // We enforce relation (from now on we assume a = 0):
        //    3 * (1 + sum_px) * (1 + sum_px)
        //  = 2 * (1 + sum_py) * (1 + sum_lambda)  (mod m)

        // with equation:
        //   3 * (2 * sum_px + sum_px2) + 1
        // - 2 * (sum_py + sum_lambda + sum_lpy) = k * m

        let limbs_max = vec![&base - BI::one(); nb_limbs as usize];
        let limbs_max2 = vec![(&base - BI::one()).pow(2); (nb_limbs * nb_limbs) as usize];
        let max_sum_px = sum_bigints(&bs, &limbs_max);
        let max_sum_py = max_sum_px.clone();
        let max_sum_lambda = max_sum_px.clone();
        let max_sum_px2 = sum_bigints(&bs2, &limbs_max2);
        let max_sum_lpy = max_sum_px2.clone();
        let expr_min = -BI::from(2) * (max_sum_py + max_sum_lambda + max_sum_lpy) + BI::one();
        let expr_max = BI::from(3) * (&max_sum_px + &max_sum_px + max_sum_px2) + BI::one();
        let expr_bounds = (expr_min, expr_max);

        let expr_mj_bounds: Vec<_> = moduli
            .iter()
            .map(|mj| {
                let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let max_sum_px_mj = sum_bigints(&bs_mj, &limbs_max);
                let max_sum_py_mj = max_sum_px_mj.clone();
                let max_sum_lambda_mj = max_sum_px_mj.clone();
                let max_sum_px2_mj = sum_bigints(&bs2_mj, &limbs_max2);
                let max_sum_lpy_mj = max_sum_px2_mj.clone();
                let expr_mj_min =
                    -BI::from(2) * (max_sum_py_mj + max_sum_lambda_mj + max_sum_lpy_mj) + BI::one();
                let expr_mj_max =
                    BI::from(3) * (&max_sum_px_mj + &max_sum_px_mj + max_sum_px2_mj) + BI::one();
                (expr_mj_min, expr_mj_max)
            })
            .collect();
        get_identity_auxiliary_bounds::<F, C::Base>(
            "tangent",
            &moduli,
            expr_bounds,
            &expr_mj_bounds,
        )
    }

    /// Configures the foreign tangent check gate
    pub fn configure<F, P>(
        meta: &mut ConstraintSystem<F>,
        field_chip_config: &FieldChipConfig,
        cond_col: &Column<Advice>,
    ) -> TangentConfig<C>
    where
        F: PrimeField,
        P: FieldEmulationParams<F, C::Base>,
    {
        let m = &modulus::<C::Base>().to_bigint().unwrap();
        let bs = P::base_powers();
        let bs2 = P::double_base_powers();
        let moduli = P::moduli();

        let ((k_min, u_max), vs_bounds) = Self::bounds::<F, P>();

        let q_tangent = meta.selector();

        // The layout is in two rows:
        // | px_0 ... px_k | py_0 ... py_k    | <- selector enabled here
        // |  λ_0 ...  λ_k | u v0 ... vl cond |

        meta.create_gate("Foreign-field EC assert_tangent", |meta| {
            let cond = meta.query_advice(*cond_col, Rotation::next());
            let pxs = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::cur());
            let pys = get_advice_vec(meta, &field_chip_config.z_cols, Rotation::cur());
            let lambdas = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::next());
            let u = meta.query_advice(field_chip_config.u_col, Rotation::next());
            let vs = get_advice_vec(meta, &field_chip_config.v_cols, Rotation::next());

            let px2s = pair_wise_prod(&pxs, &pxs);
            let lpys = pair_wise_prod(&lambdas, &pys);

            //   3 * (2 * sum_px + sum_px2) + 1
            // - 2 * (sum_py + sum_lambda + sum_lpy) = (u + k_min) * m
            let native_id = &cond
                * (Expression::Constant(F::from(3))
                    * (Expression::Constant(F::from(2)) * sum_exprs::<F>(&bs, &pxs)
                        + sum_exprs::<F>(&bs2, &px2s))
                    + Expression::Constant(F::ONE)
                    - Expression::Constant(F::from(2))
                        * (sum_exprs::<F>(&bs, &pys)
                            + sum_exprs::<F>(&bs, &lambdas)
                            + sum_exprs::<F>(&bs2, &lpys))
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

                    //   3 * (2 * sum_px_mj + sum_px2_mj) + 1
                    // - 2 * (sum_py_mj + sum_lambda_mj + sum_lpy_mj)
                    // - u * (m % mj) - (k_min * m) % mj - (vj + lj_min) * mj = 0
                    &cond
                        * (Expression::Constant(F::from(3))
                            * (Expression::Constant(F::from(2)) * sum_exprs::<F>(&bs_mj, &pxs)
                                + sum_exprs::<F>(&bs2_mj, &px2s))
                            + Expression::Constant(F::ONE)
                            - Expression::Constant(F::from(2))
                                * (sum_exprs::<F>(&bs_mj, &pys)
                                    + sum_exprs::<F>(&bs_mj, &lambdas)
                                    + sum_exprs::<F>(&bs2_mj, &lpys))
                            - &u * Expression::Constant(bigint_to_fe::<F>(&urem(m, mj)))
                            - Expression::Constant(bigint_to_fe::<F>(&urem(&(&k_min * m), mj)))
                            - (vj + Expression::Constant(bigint_to_fe::<F>(lj_min)))
                                * Expression::Constant(bigint_to_fe::<F>(mj)))
                })
                .collect::<Vec<_>>();
            moduli_ids.push(native_id);

            Constraints::with_selector(q_tangent, moduli_ids)
        });

        TangentConfig {
            q_tangent,
            u_bounds: (k_min, u_max),
            vs_bounds,
            cond_col: *cond_col,
            _marker: PhantomData,
        }
    }
}

/// If `cond = 1`, it asserts that `3 * p.0 * p.0 = 2 * p.1 * lambda`.
///
/// If `cond = 0`, it asserts nothing.
#[allow(clippy::type_complexity)]
pub fn assert_tangent<F, C, P, N>(
    layouter: &mut impl Layouter<F>,
    cond: &AssignedBit<F>,
    p: (&AssignedField<F, C::Base, P>, &AssignedField<F, C::Base, P>),
    lambda: &AssignedField<F, C::Base, P>,
    base_chip: &FieldChip<F, C::Base, P, N>,
    tangent_config: &TangentConfig<C>,
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
    let lambda = &base_chip.normalize(layouter, lambda)?;

    let mut range_checks = layouter.assign_region(
        || "Tangent",
        |mut region| {
            let mut offset = 0;

            let pxs = px.bigint_limbs();
            let pys = py.bigint_limbs();
            let lambdas = lambda.bigint_limbs();

            let px2s = pxs.clone().map(|pxs| pair_wise_prod(&pxs, &pxs));
            let lpys = lambdas
                .clone()
                .zip(pys.clone())
                .map(|(ls, pys)| pair_wise_prod(&ls, &pys));

            let (k_min, u_max) = tangent_config.u_bounds.clone();

            //   3 * (2 * sum_px + sum_px2) + 1
            // - 2 * (sum_py + sum_lambda + sum_lpy) = (u + k_min) * m
            let expr = pxs.clone().map(|v| BI::from(6) * sum_bigints(&bs, &v))
                + px2s
                    .clone()
                    .map(|v| BI::from(3) * sum_bigints(&bs2, &v) + BI::one())
                - (pys.clone().map(|v| sum_bigints(&bs, &v))
                    + lambdas.clone().map(|v| sum_bigints(&bs, &v))
                    + lpys.clone().map(|v| sum_bigints(&bs2, &v)))
                .map(|v| BI::from(2) * v);
            let u = expr.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

            let vs_values =
                moduli
                    .iter()
                    .zip(tangent_config.vs_bounds.iter())
                    .map(|(mj, vj_bounds)| {
                        let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                        let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();

                        let (lj_min, vj_max) = vj_bounds.clone();

                        //    3 * (2 * sum_px_mj + sum_px2_mj) + 1
                        //  - 2 * (sum_py_mj + sum_lambda_mj + sum_lpy_mj)
                        //  - u * (m % mj) - (k_min * m) % mj = (vj + lj_min) * mj
                        let expr_mj = pxs.clone().map(|v| BI::from(6) * sum_bigints(&bs_mj, &v))
                            + px2s
                                .clone()
                                .map(|v| BI::from(3) * sum_bigints(&bs2_mj, &v) + BI::from(1))
                            - (pys.clone().map(|v| sum_bigints(&bs_mj, &v))
                                + lambdas.clone().map(|v| sum_bigints(&bs_mj, &v))
                                + lpys.clone().map(|v| sum_bigints(&bs2_mj, &v)))
                            .map(|v| BI::from(2) * v);
                        expr_mj.zip(u.clone()).map(|(e, u)| {
                            compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value())
                        })
                    });

            tangent_config.q_tangent.enable(&mut region, offset)?;

            let px_limbs = px.limb_values();
            let py_limbs = py.limb_values();
            let lambda_limbs = lambda.limb_values();

            let px_iter = px_limbs.iter().zip(base_chip_config.x_cols.iter());
            let py_iter = py_limbs.iter().zip(base_chip_config.z_cols.iter());
            px_iter
                .chain(py_iter)
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "ECC.tangent input", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            lambda_limbs
                .iter()
                .zip(base_chip_config.x_cols.iter())
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "ECC.tangent lambda", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            let u_value = u.clone().map(|u| bigint_to_fe::<F>(&u));
            let u_cell = region.assign_advice(
                || "ECC.tangent u",
                base_chip_config.u_col,
                offset,
                || u_value,
            )?;

            let vs_cells = vs_values
                .zip(base_chip_config.v_cols.iter())
                .map(|(vj, &vj_col)| {
                    let vj_value = vj.map(|vj| bigint_to_fe::<F>(&vj));
                    region.assign_advice(|| "ECC.tangent vj", vj_col, offset, || vj_value)
                })
                .collect::<Result<Vec<_>, _>>()?;

            cond.0.copy_advice(
                || "ECC.tangent cond",
                &mut region,
                tangent_config.cond_col,
                offset,
            )?;

            // u_cell will be range-checked in [0, u_max)
            let u_range_check = (u_cell, u_max);

            // Every vj_cell will be range-checked in [0, vj_max)
            let vs_max = tangent_config
                .vs_bounds
                .clone()
                .into_iter()
                .map(|(_, vj_max)| vj_max);
            let vs_range_checks = vs_cells
                .into_iter()
                .zip(vs_max.collect::<Vec<_>>())
                .collect::<Vec<_>>();

            Ok([u_range_check]
                .into_iter()
                .chain(vs_range_checks.into_iter()))
        },
    )?;

    // Assert all range-checks
    range_checks.try_for_each(|(cell, ubound)| {
        base_chip
            .native_gadget
            .assert_lower_than_fixed(layouter, &cell, ubound.magnitude())
    })
}
