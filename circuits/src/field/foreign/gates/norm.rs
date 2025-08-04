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
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};
use num_bigint::{BigInt as BI, ToBigInt};
use num_traits::One;

use crate::{
    field::foreign::{
        params::FieldEmulationParams,
        util::{
            bi_to_limbs, compute_u, compute_vj, get_advice_vec, get_identity_auxiliary_bounds,
            sum_bigints, sum_exprs, urem,
        },
        well_formed_log2_bounds,
    },
    instructions::RangeCheckInstructions,
    types::{AssignedField, AssignedNative},
    utils::util::{bigint_to_fe, modulus},
};

/// Foreign-Field Normalization configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NormConfig {
    q_norm: Selector,
    u_bounds: (BI, BI),
    vs_bounds: Vec<(BI, BI)>,
    x_cols: Vec<Column<Advice>>,
    z_cols: Vec<Column<Advice>>,
}

impl NormConfig {
    /// Checks that the FieldEmulationParams are sound for implementing the
    /// normalization procedure, a mechanism that makes a emulated field element
    /// well-formed as long as their limb bounds have a moderate size, i.e.
    /// they are smaller (in absolute value) than P::max_limb_bound().
    /// (A emulated field element is well-formed if its limbs are in the range
    /// [0, base).) Returns (k_min, u_max), {(lj_min, vj_max)}_j, which are
    /// parameters involved in the identities enforced by the ModArith
    /// normalization custom gate. We refer to the implementation of this
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
        let max_limb_bound = P::max_limb_bound();
        let base_powers = P::base_powers();

        // Let x be the possibly non-well-formed emulated field element to be normalized
        // and let z be its normal form.
        //
        // Note that x := 1 + sum_i base^i x_i, and that z is defined analogously.
        //
        // The limbs of x are guaranteed to be within the range [-max_limb_bound,
        // max_limb_bound]. On the other hand, the limbs of z will be asserted to be
        // in the range [0, base). We enforce x - z = 0 (mod m) with equation:
        //  sum_shifted_x - sum_z - sum_shifts = k * m
        //
        // where
        //   sum_shifted_x := sum_i base_power_i * (x_i + max_limb_bound) .
        //           sum_z := sum_i base_power_i * z_i .
        //      sum_shifts := sum_i base_power_i * max_limb_bound
        //
        // The shifts of max_limb_bound are introduced to correct any wrap-arounds over
        // the native modulus due to negative vaues of x_i.
        // Note that (x_i + max_limb_bound) is guaranteed to be in the range
        // [0, 2 * max_limb_bound].

        let shifts = vec![max_limb_bound; nb_limbs as usize];
        let sum_shifts = sum_bigints(&base_powers, &shifts);
        let max_sum_shifted_x = &sum_shifts + &sum_shifts;
        let z_limbs_max = vec![&base - BI::one(); nb_limbs as usize];
        let max_sum_z = sum_bigints(&base_powers, &z_limbs_max);
        let expr_min = -&max_sum_z - &sum_shifts;
        let expr_max = &max_sum_shifted_x - &sum_shifts;
        let expr_bounds = (expr_min, expr_max);

        let expr_mj_bounds: Vec<_> = moduli
            .iter()
            .map(|mj| {
                let base_powers_mj = base_powers.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let sum_shifts_mj = sum_bigints(&base_powers_mj, &shifts);
                let max_sum_shifted_x_mj = &sum_shifts_mj + &sum_shifts_mj;
                let max_sum_z_mj = sum_bigints(&base_powers_mj, &z_limbs_max);
                let expr_mj_min = -&max_sum_z_mj - urem(&sum_shifts, mj);
                let expr_mj_max = &max_sum_shifted_x_mj - urem(&sum_shifts, mj);
                (expr_mj_min, expr_mj_max)
            })
            .collect();
        get_identity_auxiliary_bounds::<F, K>(
            "normalization",
            &moduli,
            expr_bounds,
            &expr_mj_bounds,
        )
    }

    /// Configures the foreign normalization chip
    pub fn configure<F, K, P>(
        meta: &mut ConstraintSystem<F>,
        x_cols: &[Column<Advice>],
        z_cols: &[Column<Advice>],
    ) -> NormConfig
    where
        F: PrimeField,
        K: PrimeField,
        P: FieldEmulationParams<F, K>,
    {
        let m = &modulus::<K>().to_bigint().unwrap();
        let nb_limbs = P::NB_LIMBS;
        let base_powers = P::base_powers();
        let moduli = P::moduli();
        let max_limb_bound = P::max_limb_bound();

        let ((k_min, u_max), vs_bounds) = Self::bounds::<F, K, P>();

        let q_norm = meta.selector();

        // The layout is in two rows:
        // | x0 ... xk | z0 ... zk   |  <- selector enabled here
        // |           | u v0 ... vl |

        meta.create_gate("Foreign-field normalization", |meta| {
            let xs = get_advice_vec(meta, x_cols, Rotation::cur());
            let zs = get_advice_vec(meta, z_cols, Rotation::cur());
            let u = meta.query_advice(z_cols[0], Rotation::next());
            let vs = get_advice_vec(meta, &z_cols[1..=vs_bounds.len()], Rotation::next());

            let shift = Expression::Constant(bigint_to_fe::<F>(&max_limb_bound));
            let shifted_x = xs
                .iter()
                .map(|x| x.clone() + shift.clone())
                .collect::<Vec<_>>();
            let shifts = vec![max_limb_bound; nb_limbs as usize];
            let sum_shifts = sum_bigints(&base_powers, &shifts);

            //  sum_shifted_x - sum_z - sum_shifts - (u + k_min) * m = 0
            let native_id = sum_exprs::<F>(&base_powers, &shifted_x)
                - sum_exprs::<F>(&base_powers, &zs)
                - Expression::Constant(bigint_to_fe::<F>(&sum_shifts))
                - (u.clone() + Expression::Constant(bigint_to_fe::<F>(&k_min)))
                    * Expression::Constant(bigint_to_fe::<F>(m));

            //  vs_norm_bounds may be shorter than moduli
            let mut moduli_ids = moduli
                .iter()
                .zip(vs.iter())
                .zip(vs_bounds.iter())
                .map(|((mj, vj), vj_bounds)| {
                    let (lj_min, _vj_max) = vj_bounds;
                    let base_powers_mj = base_powers.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    //  sum_shifted_x_mj - sum_z_mj - sum_shifts % mj - u * (m % mj) - (k_min * m) %
                    // mj - (vj + lj_min) * mj = 0
                    sum_exprs::<F>(&base_powers_mj, &shifted_x)
                        - sum_exprs::<F>(&base_powers_mj, &zs)
                        - Expression::Constant(bigint_to_fe::<F>(&urem(&sum_shifts, mj)))
                        - u.clone() * Expression::Constant(bigint_to_fe::<F>(&urem(m, mj)))
                        - Expression::Constant(bigint_to_fe::<F>(&urem(&(&k_min * m), mj)))
                        - (vj.clone() + Expression::Constant(bigint_to_fe::<F>(lj_min)))
                            * Expression::Constant(bigint_to_fe::<F>(mj))
                })
                .collect::<Vec<_>>();
            moduli_ids.push(native_id);

            Constraints::with_selector(q_norm, moduli_ids)
        });

        NormConfig {
            q_norm,
            u_bounds: (k_min, u_max),
            vs_bounds,
            x_cols: x_cols.to_vec(),
            z_cols: z_cols.to_vec(),
        }
    }
}

/// Normalizes AssignedField x, returning the limbs of a well-formed equivalent
/// integer.
pub fn normalize<F, K, P, RangeGadget>(
    layouter: &mut impl Layouter<F>,
    x: &AssignedField<F, K, P>,
    norm_config: &NormConfig,
    range_gadget: &RangeGadget,
) -> Result<Vec<AssignedNative<F>>, Error>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    RangeGadget: RangeCheckInstructions<F, AssignedNative<F>>,
{
    let (mut range_checks, z_cells) = layouter.assign_region(
        || "Foreign norm",
        |mut region| {
            let mut offset = 0;

            let m = &modulus::<K>().to_bigint().unwrap();
            let base = BI::from(2).pow(P::LOG2_BASE);
            let nb_limbs = P::NB_LIMBS;
            let moduli = P::moduli();
            let base_powers = P::base_powers();
            let max_limb_bound = P::max_limb_bound();

            let shift = max_limb_bound.clone();
            let xs_shifted = x.bigint_limbs().map(|limbs| {
                limbs
                    .iter()
                    .map(|xi| shift.clone() + xi)
                    .collect::<Vec<_>>()
            });
            // Convert to BigInt in order to normalize, then back to limbs
            let shifts = vec![max_limb_bound; nb_limbs as usize];
            let sum_shifted_x = xs_shifted.clone().map(|v| sum_bigints(&base_powers, &v));
            let sum_shifts = sum_bigints(&base_powers, &shifts);
            // The shift of +1 on x (for the unique representation of 0) has not been added,
            // but this will cancel out if we do not shift zv either in the call to
            // `bi_to_libms`.
            let zv = sum_shifted_x.clone().map(|v| urem(&(&v - &sum_shifts), m));
            let zs = zv.map(|v| bi_to_limbs(nb_limbs, &base, &v));
            let z_values =
                (0..nb_limbs).map(|i| zs.clone().map(|zs| bigint_to_fe::<F>(&zs[i as usize])));

            let sum_z = zs.clone().map(|v| sum_bigints(&base_powers, &v));

            let (k_min, u_max) = norm_config.u_bounds.clone();
            let expr = &sum_shifted_x.clone() - &sum_z - Value::known(sum_shifts.clone());

            let u = expr.map(|e| compute_u(m, &e, (&k_min, &u_max), Value::known(true)));

            // norm_config.vs_bounds may be shorter than moduli, this is intended.
            let vs_values = moduli
                .iter()
                .zip(norm_config.vs_bounds.iter())
                .map(|(mj, vj_bounds)| {
                    let base_powers_mj = base_powers.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let sum_shifted_x_mj =
                        xs_shifted.clone().map(|v| sum_bigints(&base_powers_mj, &v));
                    let sum_z_mj = zs.clone().map(|v| sum_bigints(&base_powers_mj, &v));
                    let (lj_min, vj_max) = vj_bounds.clone();

                    let expr_mj =
                        &sum_shifted_x_mj - &sum_z_mj - Value::known(urem(&sum_shifts.clone(), mj));
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
                })
                .collect::<Vec<_>>();

            norm_config.q_norm.enable(&mut region, offset)?;

            let x_limb_values = x.limb_values();
            let x_iter = x_limb_values.iter().zip(norm_config.x_cols.iter());
            x_iter
                .map(|(cell, &col)| cell.copy_advice(|| "norm input", &mut region, col, offset))
                .collect::<Result<Vec<_>, _>>()?;

            let z_cells = z_values
                .zip(norm_config.z_cols.iter())
                .map(|(z, &z_col)| region.assign_advice(|| "norm output", z_col, offset, || z))
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            let u_value = u.clone().map(|u| bigint_to_fe::<F>(&u));
            let u_cell =
                region.assign_advice(|| "norm u", norm_config.z_cols[0], offset, || u_value)?;

            let vs_cells = vs_values
                .iter()
                .zip(norm_config.z_cols[1..=norm_config.vs_bounds.len()].iter())
                .map(|(vj, &vj_col)| {
                    let vj_value = vj.clone().map(|vj| bigint_to_fe::<F>(&vj));
                    region.assign_advice(|| "norm vj", vj_col, offset, || vj_value)
                })
                .collect::<Result<Vec<_>, _>>()?;

            // Every z_cell will be range-checked in [0, base)
            let z_range_checks = z_cells
                .clone()
                .into_iter()
                .zip(well_formed_log2_bounds::<F, K, P>().iter())
                .map(|(cell, log2_bound)| (cell, BI::from(2).pow(*log2_bound)))
                .collect::<Vec<_>>();

            // u_cell will be range-checked in [0, u_max)
            let u_range_check = (u_cell, u_max);

            // Every vj_cell will be range-checked in [0, vj_max)
            let vs_max = norm_config
                .vs_bounds
                .clone()
                .into_iter()
                .map(|(_, vj_max)| vj_max.clone());
            let vs_range_checks = vs_cells
                .into_iter()
                .zip(vs_max.collect::<Vec<_>>())
                .collect::<Vec<_>>();

            // Assert all range-checks
            Ok((
                z_range_checks
                    .into_iter()
                    .chain([u_range_check].into_iter())
                    .chain(vs_range_checks.into_iter()),
                z_cells,
            ))
        },
    )?;

    range_checks.try_for_each(|(cell, ubound)| {
        range_gadget.assert_lower_than_fixed(layouter, &cell, ubound.magnitude())
    })?;

    Ok(z_cells)
}
