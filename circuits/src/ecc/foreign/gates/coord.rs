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
    circuit::{Chip, Layouter, Value},
    plonk::{ConstraintSystem, Constraints, Error, Expression, Selector},
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
    types::AssignedField,
    utils::util::{bigint_to_fe, modulus},
};

/// Foreign-Field twisted Edwards configuration for asserting the
/// coordinates of point addition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoordConfig<C: CircuitCurve> {
    q: Selector,
    u_bounds: (BI, BI),
    vs_bounds: Vec<(BI, BI)>,
    _marker: PhantomData<C>,
}

impl<C: CircuitCurve> CoordConfig<C> {
    /// Checks that the FieldEmulationParams are sound for implementing the
    /// addition assertion. Returns (k_min, u_max), {(lj_min, vj_max)}_j, which
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
        let bs_sqrd = P::double_base_powers();

        // Let a := 1 + sum_i B^i * a_i
        //     b := 1 + sum_i B^i * b_i
        //     c := 1 + sum_i B^i * c_i
        //     z := 1 + sum_i B^i * z_i
        //
        // Let m denote the foreign modulus. Define:
        //      sum_a := sum_i (B^i % m) * a_i
        //      sum_b := sum_i (B^i % m) * b_i
        //      sum_c := sum_i (B^i % m) * c_i
        //      sum_z := sum_i (B^i % m) * z_i
        //      sum_az := sum_i sum_j (B^{i+j} % m) * a_i * z_j
        //
        // This custom gate enforces the constraint:
        //
        // a * (1 + z) = b + c   (mod m)
        // <=>
        // 2 * sum_a + sum_z + sum_az - sum_b - sum_c  = k * m   (over the integers)
        // <=>
        // LHS = k * m   (over the integers)
        //
        // This equation over the integers can be enforced modulo the native modulus p
        // with the following constraints:
        //
        // LHS  = (u + k_min) * m   (mod p),
        // LHS  = u * (m % mj) + (k_min * m) % mj + (vj + lj_min) * mj   (mod p), ∀.mj

        let limbs_max = vec![&base - BI::one(); nb_limbs as usize];
        let limbs_max_sqrd_val = (&base - BI::one()).pow(2);
        let limbs_max_sqrd = vec![limbs_max_sqrd_val.clone(); (nb_limbs * nb_limbs) as usize];

        let max_sum = sum_bigints(&bs, &limbs_max);
        let max_sum_sqrd = sum_bigints(&bs_sqrd, &limbs_max_sqrd);

        // 2 * sum_a + sum_z + sum_az - sum_b - sum_c >= -sum_b - sum_c >= -2 * sum_max
        let expr_min = -(BI::from(2) * max_sum.clone());
        let expr_max = BI::from(3) * max_sum + max_sum_sqrd;
        let expr_bounds = (expr_min, expr_max);

        let expr_mj_bounds: Vec<_> = moduli
            .iter()
            .map(|mj| {
                let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let bs_sqrd_mj = bs_sqrd.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();

                let max_sum_mj = sum_bigints(&bs_mj, &limbs_max);
                let max_sum_sqrd_mj = sum_bigints(&bs_sqrd_mj, &limbs_max_sqrd);

                let expr_min_mj = -(BI::from(2) * max_sum_mj.clone());
                let expr_max_mj = BI::from(3) * max_sum_mj + max_sum_sqrd_mj;
                (expr_min_mj, expr_max_mj)
            })
            .collect();

        get_identity_auxiliary_bounds::<F, C::Base>("coord", &moduli, expr_bounds, &expr_mj_bounds)
    }

    /// Configures the custom gate
    pub fn configure<F, P>(
        meta: &mut ConstraintSystem<F>,
        field_chip_config: &FieldChipConfig,
    ) -> CoordConfig<C>
    where
        F: PrimeField,
        P: FieldEmulationParams<F, C::Base>,
    {
        let m = &modulus::<C::Base>().to_bigint().unwrap();
        let moduli = P::moduli();
        let bs = P::base_powers();
        let bs_sqrd = P::double_base_powers();

        let ((k_min, u_max), vs_bounds) = Self::bounds::<F, P>();

        let q = meta.selector();

        // The layout is in three rows:
        // | a_0 ... a_k | z_0    ... z_k |
        // | b_0 ... b_k |                |  <-- selector enabled here
        // | c_0 ... c_k | u v_0  ... v_l |

        meta.create_gate("Foreign-Edwards coord", |meta| {
            let a_limbs = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::prev());
            let b_limbs = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::cur());
            let c_limbs = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::next());
            let z_limbs = get_advice_vec(meta, &field_chip_config.z_cols, Rotation::prev());
            let u = meta.query_advice(field_chip_config.u_col, Rotation::next());
            let vs = get_advice_vec(meta, &field_chip_config.v_cols, Rotation::next());

            let az_limbs = pair_wise_prod(&a_limbs, &z_limbs);

            // 2 * sum_a + sum_z + sum_az - sum_b - sum_c  = (u + k_min) * m
            let two = Expression::from(2);
            let native_id = &two * sum_exprs::<F>(&bs, &a_limbs)
                + sum_exprs::<F>(&bs, &z_limbs)
                + sum_exprs::<F>(&bs_sqrd, &az_limbs)
                - sum_exprs::<F>(&bs, &b_limbs)
                - sum_exprs::<F>(&bs, &c_limbs)
                - (&u + Expression::Constant(bigint_to_fe::<F>(&k_min)))
                    * Expression::Constant(bigint_to_fe::<F>(m));

            let mut moduli_ids = moduli
                .iter()
                .zip(vs)
                .zip(vs_bounds.iter())
                .map(|((mj, vj), vj_bounds)| {
                    let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let bs_sqrd_mj = bs_sqrd.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let (lj_min, _) = vj_bounds;

                    // 2 * sum_a_mj + sum_z_mj + sum_az_mj - sum_b_mj - sum_c_mj
                    // - u * (m % mj) - (k_min * m) % mj - (vj + lj_min) * mj = 0
                    &two * sum_exprs::<F>(&bs_mj, &a_limbs)
                        + sum_exprs::<F>(&bs_mj, &z_limbs)
                        + sum_exprs::<F>(&bs_sqrd_mj, &az_limbs)
                        - sum_exprs::<F>(&bs_mj, &b_limbs)
                        - sum_exprs::<F>(&bs_mj, &c_limbs)
                        - &u * Expression::Constant(bigint_to_fe::<F>(&urem(m, mj)))
                        - Expression::Constant(bigint_to_fe::<F>(&urem(&(&k_min * m), mj)))
                        - (vj + Expression::Constant(bigint_to_fe::<F>(lj_min)))
                            * Expression::Constant(bigint_to_fe::<F>(mj))
                })
                .collect::<Vec<_>>();

            moduli_ids.push(native_id);

            Constraints::with_selector(q, moduli_ids)
        });

        CoordConfig {
            q,
            u_bounds: (k_min, u_max),
            vs_bounds,
            _marker: PhantomData,
        }
    }
}

/// Assert that `a * (1 - z) = b - c`.
#[allow(clippy::type_complexity)]
pub fn assert_coord<F, C, P, N>(
    layouter: &mut impl Layouter<F>,
    a: &AssignedField<F, C::Base, P>,
    b: &AssignedField<F, C::Base, P>,
    c: &AssignedField<F, C::Base, P>,
    z: &AssignedField<F, C::Base, P>,
    base_chip: &FieldChip<F, C::Base, P, N>,
    coord_config: &CoordConfig<C>,
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
    let bs_sqrd = P::double_base_powers();
    let field_chip_config = base_chip.config();

    let a_norm = &base_chip.normalize(layouter, a)?;
    let b_norm = &base_chip.normalize(layouter, b)?;
    let c_norm = &base_chip.normalize(layouter, c)?;
    let z_norm = &base_chip.normalize(layouter, z)?;

    let range_checks = layouter.assign_region(
        || "Foreign-Edwards coord",
        |mut region| {
            let a_s = a_norm.bigint_limbs();
            let b_s = b_norm.bigint_limbs();
            let c_s = c_norm.bigint_limbs();
            let z_s = z_norm.bigint_limbs();
            let az_s = a_s.clone().zip(z_s.clone()).map(|(a, z)| pair_wise_prod(&a, &z));

            let (k_min, u_max) = coord_config.u_bounds.clone();

            // 2 * sum_a + sum_z + sum_az - sum_b - sum_c  = (u + k_min) * m
            let expr = a_s.clone().map(|v| BI::from(2) * sum_bigints(&bs, &v))
                + z_s.clone().map(|v| sum_bigints(&bs, &v))
                + az_s.clone().map(|v| sum_bigints(&bs_sqrd, &v))
                - b_s.clone().map(|v| sum_bigints(&bs, &v))
                - c_s.clone().map(|v| sum_bigints(&bs, &v));

            let u = expr.map(|e| compute_u(m, &e, (&k_min, &u_max), Value::unknown()));

            let vs_values =
                moduli.iter().zip(coord_config.vs_bounds.iter()).map(|(mj, vj_bounds)| {
                    let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let bs_sqrd_mj = bs_sqrd.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let (lj_min, vj_max) = vj_bounds.clone();

                    // 2 * sum_a_mj + sum_z_mj + sum_az_mj - sum_b_mj - sum_c_mj
                    // - u * (m % mj) - (k_min * m) % mj - (vj + lj_min) * mj = 0
                    let expr_mj = a_s.clone().map(|v| BI::from(2) * sum_bigints(&bs_mj, &v))
                        + z_s.clone().map(|v| sum_bigints(&bs_mj, &v))
                        + az_s.clone().map(|v| sum_bigints(&bs_sqrd_mj, &v))
                        - b_s.clone().map(|v| sum_bigints(&bs_mj, &v))
                        - c_s.clone().map(|v| sum_bigints(&bs_mj, &v));

                    expr_mj.zip(u.clone()).map(|(e, u)| {
                        compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), Value::unknown())
                    })
                });

            let a_limbs = a_norm.limb_values();
            let b_limbs = b_norm.limb_values();
            let c_limbs = c_norm.limb_values();
            let z_limbs = z_norm.limb_values();

            // The layout is in three rows:
            // | a_0 ... a_k | z_0    ... z_k |
            // | b_0 ... b_k |                |  <-- selector enabled here
            // | c_0 ... c_k | u v_0  ... v_l |

            let mut offset = 0;

            // 1st row
            a_limbs
                .iter()
                .zip(field_chip_config.x_cols.iter())
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "Edwards.coord a", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            z_limbs
                .iter()
                .zip(field_chip_config.z_cols.iter())
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "Edwards.coord z", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            // 2nd row
            // Activate selector on middle row of this region
            coord_config.q.enable(&mut region, offset)?;

            b_limbs
                .iter()
                .zip(field_chip_config.x_cols.iter())
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "Edwards.coord b", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            offset += 1;

            // 3rd row
            c_limbs
                .iter()
                .zip(field_chip_config.x_cols.iter())
                .map(|(cell, &col)| {
                    cell.copy_advice(|| "Edwards.coord c", &mut region, col, offset)
                })
                .collect::<Result<Vec<_>, _>>()?;

            let u_value = u.clone().map(|u| bigint_to_fe::<F>(&u));
            let u_cell = region.assign_advice(
                || "Edwards.coord u",
                field_chip_config.u_col,
                offset,
                || u_value,
            )?;

            let vs_cells = vs_values
                .zip(field_chip_config.v_cols.iter())
                .map(|(vj, &col)| {
                    let vj_value = vj.map(|vj| bigint_to_fe::<F>(&vj));
                    region.assign_advice(|| "Edwards.coord vj", col, offset, || vj_value)
                })
                .collect::<Result<Vec<_>, _>>()?;

            // u_cell will be range-checked in [0, u_max)
            let u_range_check = (u_cell, u_max);

            // Every vj_cell will be range-checked in [0, vj_max)
            let vs_max = coord_config
                .clone()
                .vs_bounds
                .into_iter()
                .map(|(_, vj_max)| vj_max)
                .collect::<Vec<_>>();
            let vs_range_checks = vs_cells.into_iter().zip(vs_max);

            // Assert all range-checks
            Ok([u_range_check].into_iter().chain(vs_range_checks).collect::<Vec<_>>())
        },
    )?;

    range_checks.iter().try_for_each(|(cell, ubound)| {
        base_chip
            .native_gadget
            .assert_lower_than_fixed(layouter, cell, ubound.magnitude())
    })
}
