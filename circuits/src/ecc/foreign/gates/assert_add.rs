// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

//! Foreign-field elliptic-curve addition assertion built on the unified gate.
//!
//! Proves `p + q = r` via three instantiations of the unified gate in a
//! **single region**, sharing one row between the two slope gates:
//!
//! ```text
//! Row 0: x=qx, z=qy    [slope(p,q): A, B]
//! Row 1: x=λ,  aux=u_A [slope(p,q): C + selector]
//! Row 2: x=px, z=py    [slope(p,q): D,E  =  slope(p,r): A,B  ← shared]
//! Row 3: x=λ,  aux=u_C [slope(p,r): C + selector]
//! Row 4: x=rx, z=ry    [slope(p,r): D, E]
//! Row 5: x=λ,  z=rx    [lambda_sq: A, B  ← data row]
//! Row 6: x=−,  aux=u_B [lambda_sq: C(unused) + selector]
//! Row 7: x=px, z=qx    [lambda_sq: D, E]
//! ```
//!
//! The slope(p,r) gate swaps A↔D slots (A=px, D=rx).  The lambda-squared gate
//! uses `a=1, A=λ` and `b=−1, B=rx` from the dedicated data row (Row 5).

use std::ops::Rem;

use midnight_proofs::{
    circuit::{Chip, Layouter},
    plonk::Error,
};
use num_bigint::{BigInt as BI, ToBigInt};
use num_traits::{One, Zero};

use crate::{
    ecc::curves::CircuitCurve,
    field::foreign::{
        params::FieldEmulationParams,
        util::{compute_u, compute_vj, pair_wise_prod, sum_bigints},
        FieldChip,
    },
    instructions::NativeInstructions,
    types::{AssignedBit, AssignedField, InnerValue},
    utils::util::bigint_to_fe,
    CircuitField,
};

use super::{
    unified::UnifiedConfig,
    utils::{assign_coeffs, copy_limbs},
};

/// If `cond = 1`, asserts that `p + q = r` over the foreign field.
///
/// If `cond = 0`, asserts nothing.
#[allow(clippy::type_complexity)]
pub fn assert_add<F, C, P, N>(
    layouter: &mut impl Layouter<F>,
    cond: &AssignedBit<F>,
    p: (&AssignedField<F, C::Base, P>, &AssignedField<F, C::Base, P>),
    q: (&AssignedField<F, C::Base, P>, &AssignedField<F, C::Base, P>),
    r: (&AssignedField<F, C::Base, P>, &AssignedField<F, C::Base, P>),
    lambda: &AssignedField<F, C::Base, P>,
    base_chip: &FieldChip<F, C::Base, P, N>,
    config: &UnifiedConfig<C>,
) -> Result<(), Error>
where
    F: CircuitField,
    C: CircuitCurve,
    P: FieldEmulationParams<F, C::Base>,
    N: NativeInstructions<F>,
{
    let m = &C::Base::modulus().to_bigint().unwrap();
    let moduli = P::moduli();
    let bs = P::base_powers();
    let bs2 = P::double_base_powers();
    let fcc = base_chip.config();

    let (px, py) = p;
    let (qx, qy) = q;
    let (rx, ry) = r;

    // Normalize each field element once; the three gates share the results.
    let px = &base_chip.normalize(layouter, px)?;
    let py = &base_chip.normalize(layouter, py)?;
    let qx = &base_chip.normalize(layouter, qx)?;
    let qy = &base_chip.normalize(layouter, qy)?;
    let rx = &base_chip.normalize(layouter, rx)?;
    let ry = &base_chip.normalize(layouter, ry)?;
    let lambda = &base_chip.normalize(layouter, lambda)?;

    // ---------------------------------------------------------------------------
    // Gate A — slope(p, q, negate=false)
    //   a=0, b=−1, d=0, e=1, ca=1, cd=−1
    //   A=qx, B=qy, C=λ, D=px, E=py
    // ---------------------------------------------------------------------------
    let (a_a, b_a, d_a, e_a, ca_a, cd_a) =
        (BI::zero(), -BI::one(), BI::zero(), BI::one(), BI::one(), -BI::one());
    let const_a = &a_a + &b_a + &d_a + &e_a + &ca_a + &cd_a; // = 0
    let csa_a = BI::from(2) * &a_a + &ca_a; // coef of ΣA = 1
    let csd_a = &d_a + &cd_a; // coef of ΣD = -1

    // ---------------------------------------------------------------------------
    // Gate C — slope(p, r, negate=true) with swapped A↔D
    //   A=px, B=py, C=λ, D=rx, E=ry
    //   a=0, b=−1, d=0, e=−1, ca=1, cd=−1
    //
    //   Verify: λ·px − λ·rx − py − ry = λ(px−rx) − (py+ry) = 0
    //         ↔ λ(rx−px) = −py − ry ✓
    // ---------------------------------------------------------------------------
    let (a_c, b_c, d_c, e_c, ca_c, cd_c) =
        (BI::zero(), -BI::one(), BI::zero(), -BI::one(), BI::one(), -BI::one());
    let const_c = &a_c + &b_c + &d_c + &e_c + &ca_c + &cd_c; // = -2
    let csa_c = BI::from(2) * &a_c + &ca_c; // = 1
    let csd_c = &d_c + &cd_c; // = -1

    // ---------------------------------------------------------------------------
    // Gate B — lambda_squared
    //   a=1, b=−1, d=−1, e=−1, ca=0, cd=0
    //   A=λ (prev x-slot = Row 3), B=rx (prev z-slot = Row 3), D=px, E=qx
    //   Enforces: λ² − rx − px − qx = 0  (mod m)
    // ---------------------------------------------------------------------------
    let (a_b, b_b, d_b, e_b, ca_b, cd_b) = (
        BI::one(), -BI::one(), -BI::one(), -BI::one(),
        BI::zero(), BI::zero(),
    );

    // ---------------------------------------------------------------------------
    // Precompute limb representations (shared across gates).
    // ---------------------------------------------------------------------------
    let lmb = lambda.bigint_limbs();
    let pxl = px.bigint_limbs();
    let pyl = py.bigint_limbs();
    let qxl = qx.bigint_limbs();
    let qyl = qy.bigint_limbs();
    let rxl = rx.bigint_limbs();
    let ryl = ry.bigint_limbs();

    // Bilinear products needed by the gates.
    let lmb_qx = lmb.clone().zip(qxl.clone()).map(|(l, q)| pair_wise_prod(&l, &q)); // λ·qx (gate A)
    let lmb_px_ca = lmb.clone().zip(pxl.clone()).map(|(l, p)| pair_wise_prod(&l, &p)); // λ·px (gates A cd, C ca)
    let lmb_rx = lmb.clone().zip(rxl.clone()).map(|(l, r)| pair_wise_prod(&l, &r)); // λ·rx (gate C cd)
    let lmb2 = lmb.clone().map(|l| pair_wise_prod(&l, &l)); // λ² (gate B)

    let (k_min, u_max) = config.u_bounds.clone();

    // ---------------------------------------------------------------------------
    // Witness: u and vj for gate A.
    // ---------------------------------------------------------------------------
    let expr_a = qxl.clone().map(|v| &csa_a * sum_bigints(&bs, &v) + &const_a)
        + qyl.clone().map(|v| &b_a * sum_bigints(&bs, &v))
        + pxl.clone().map(|v| &csd_a * sum_bigints(&bs, &v))
        + pyl.clone().map(|v| &e_a * sum_bigints(&bs, &v))
        + lmb_qx.clone().map(|v| &ca_a * sum_bigints(&bs2, &v))
        + lmb_px_ca.clone().map(|v| &cd_a * sum_bigints(&bs2, &v));
    let u_a = expr_a.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

    let vs_a: Vec<_> = moduli
        .iter()
        .zip(config.vs_bounds.iter())
        .map(|(mj, vj_bounds)| {
            let bs_mj: Vec<_> = bs.iter().map(|b| b.rem(mj)).collect();
            let bs2_mj: Vec<_> = bs2.iter().map(|b| b.rem(mj)).collect();
            let (lj_min, vj_max) = vj_bounds.clone();
            let expr_mj = qxl.clone().map(|v| &csa_a * sum_bigints(&bs_mj, &v) + &const_a)
                + qyl.clone().map(|v| &b_a * sum_bigints(&bs_mj, &v))
                + pxl.clone().map(|v| &csd_a * sum_bigints(&bs_mj, &v))
                + pyl.clone().map(|v| &e_a * sum_bigints(&bs_mj, &v))
                + lmb_qx.clone().map(|v| &ca_a * sum_bigints(&bs2_mj, &v))
                + lmb_px_ca.clone().map(|v| &cd_a * sum_bigints(&bs2_mj, &v));
            expr_mj
                .zip(u_a.clone())
                .map(|(e, u)| compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value()))
        })
        .collect();

    // ---------------------------------------------------------------------------
    // Witness: u and vj for gate C (swapped slope p,r).
    // ---------------------------------------------------------------------------
    let expr_c = pxl.clone().map(|v| &csa_c * sum_bigints(&bs, &v) + &const_c)
        + pyl.clone().map(|v| &b_c * sum_bigints(&bs, &v))
        + rxl.clone().map(|v| &csd_c * sum_bigints(&bs, &v))
        + ryl.clone().map(|v| &e_c * sum_bigints(&bs, &v))
        + lmb_px_ca.clone().map(|v| &ca_c * sum_bigints(&bs2, &v))
        + lmb_rx.clone().map(|v| &cd_c * sum_bigints(&bs2, &v));
    let u_c = expr_c.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

    let vs_c: Vec<_> = moduli
        .iter()
        .zip(config.vs_bounds.iter())
        .map(|(mj, vj_bounds)| {
            let bs_mj: Vec<_> = bs.iter().map(|b| b.rem(mj)).collect();
            let bs2_mj: Vec<_> = bs2.iter().map(|b| b.rem(mj)).collect();
            let (lj_min, vj_max) = vj_bounds.clone();
            let expr_mj = pxl.clone().map(|v| &csa_c * sum_bigints(&bs_mj, &v) + &const_c)
                + pyl.clone().map(|v| &b_c * sum_bigints(&bs_mj, &v))
                + rxl.clone().map(|v| &csd_c * sum_bigints(&bs_mj, &v))
                + ryl.clone().map(|v| &e_c * sum_bigints(&bs_mj, &v))
                + lmb_px_ca.clone().map(|v| &ca_c * sum_bigints(&bs2_mj, &v))
                + lmb_rx.clone().map(|v| &cd_c * sum_bigints(&bs2_mj, &v));
            expr_mj
                .zip(u_c.clone())
                .map(|(e, u)| compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value()))
        })
        .collect();

    // ---------------------------------------------------------------------------
    // Witness: u and vj for gate B (lambda_squared).
    // expr = 2·Σλ + Σλ² − Σpx − Σqx − Σrx − 2
    // ---------------------------------------------------------------------------
    let expr_b = lmb.clone().map(|v| BI::from(2) * sum_bigints(&bs, &v) - BI::from(2))
        + lmb2.clone().map(|v| sum_bigints(&bs2, &v))
        - pxl.clone().map(|v| sum_bigints(&bs, &v))
        - qxl.clone().map(|v| sum_bigints(&bs, &v))
        - rxl.clone().map(|v| sum_bigints(&bs, &v));
    let u_b = expr_b.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

    let vs_b: Vec<_> = moduli
        .iter()
        .zip(config.vs_bounds.iter())
        .map(|(mj, vj_bounds)| {
            let bs_mj: Vec<_> = bs.iter().map(|b| b.rem(mj)).collect();
            let bs2_mj: Vec<_> = bs2.iter().map(|b| b.rem(mj)).collect();
            let (lj_min, vj_max) = vj_bounds.clone();
            let expr_mj =
                lmb.clone().map(|v| BI::from(2) * sum_bigints(&bs_mj, &v) - BI::from(2))
                    + lmb2.clone().map(|v| sum_bigints(&bs2_mj, &v))
                    - pxl.clone().map(|v| sum_bigints(&bs_mj, &v))
                    - qxl.clone().map(|v| sum_bigints(&bs_mj, &v))
                    - rxl.clone().map(|v| sum_bigints(&bs_mj, &v));
            expr_mj
                .zip(u_b.clone())
                .map(|(e, u)| compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value()))
        })
        .collect();

    // ---------------------------------------------------------------------------
    // Lay out the 7-row region.
    // ---------------------------------------------------------------------------
    let range_checks = layouter.assign_region(
        || "Add",
        |mut region| {
            // --- Row 0: gate A prev (A=qx, B=qy) ---
            copy_limbs(&mut region, qx, &fcc.x_cols, 0, "qx")?;
            copy_limbs(&mut region, qy, &fcc.z_cols, 0, "qy")?;

            // --- Row 1: gate A cur (C=λ, selector, u_A, vj_A, cond, fixed coeffs) ---
            config.q_unified.enable(&mut region, 1)?;
            copy_limbs(&mut region, lambda, &fcc.x_cols, 1, "lambda")?;
            assign_coeffs(
                &mut region, 1, &config.coeff_cols, &config.coeff_bounds,
                &a_a, &b_a, &d_a, &e_a, &ca_a, &cd_a,
            )?;
            let u_a_cell = region.assign_advice(
                || "u_A", fcc.u_col, 1, || u_a.clone().map(|u| bigint_to_fe::<F>(&u)),
            )?;
            let vs_a_cells = vs_a
                .iter()
                .zip(fcc.v_cols.iter())
                .map(|(vj, &col)| {
                    let val = vj.clone().map(|v| bigint_to_fe::<F>(&v));
                    region.assign_advice(|| "vj_A", col, 1, || val)
                })
                .collect::<Result<Vec<_>, _>>()?;
            cond.0.copy_advice(|| "cond", &mut region, config.cond_col, 1)?;

            // --- Row 2: shared (gate A next D,E = gate C prev A,B) ---
            copy_limbs(&mut region, px, &fcc.x_cols, 2, "px")?;
            copy_limbs(&mut region, py, &fcc.z_cols, 2, "py")?;

            // --- Row 3: gate C cur (C=λ, selector, u_C, vj_C, cond, fixed coeffs) ---
            config.q_unified.enable(&mut region, 3)?;
            copy_limbs(&mut region, lambda, &fcc.x_cols, 3, "lambda")?;
            assign_coeffs(
                &mut region, 3, &config.coeff_cols, &config.coeff_bounds,
                &a_c, &b_c, &d_c, &e_c, &ca_c, &cd_c,
            )?;
            let u_c_cell = region.assign_advice(
                || "u_C", fcc.u_col, 3, || u_c.clone().map(|u| bigint_to_fe::<F>(&u)),
            )?;
            let vs_c_cells = vs_c
                .iter()
                .zip(fcc.v_cols.iter())
                .map(|(vj, &col)| {
                    let val = vj.clone().map(|v| bigint_to_fe::<F>(&v));
                    region.assign_advice(|| "vj_C", col, 3, || val)
                })
                .collect::<Result<Vec<_>, _>>()?;
            cond.0.copy_advice(|| "cond", &mut region, config.cond_col, 3)?;

            // --- Row 4: gate C next (D=rx, E=ry) ---
            copy_limbs(&mut region, rx, &fcc.x_cols, 4, "rx")?;
            copy_limbs(&mut region, ry, &fcc.z_cols, 4, "ry")?;

            // --- Row 5: gate B prev (A=λ, B=rx) ---
            copy_limbs(&mut region, lambda, &fcc.x_cols, 5, "lambda")?;
            copy_limbs(&mut region, rx, &fcc.z_cols, 5, "rx")?;

            // --- Row 6: gate B cur (C=unused, selector, u_B, vj_B, cond, fixed coeffs) ---
            config.q_unified.enable(&mut region, 6)?;
            assign_coeffs(
                &mut region, 6, &config.coeff_cols, &config.coeff_bounds,
                &a_b, &b_b, &d_b, &e_b, &ca_b, &cd_b,
            )?;
            let u_b_cell = region.assign_advice(
                || "u_B", fcc.u_col, 6, || u_b.clone().map(|u| bigint_to_fe::<F>(&u)),
            )?;
            let vs_b_cells = vs_b
                .iter()
                .zip(fcc.v_cols.iter())
                .map(|(vj, &col)| {
                    let val = vj.clone().map(|v| bigint_to_fe::<F>(&v));
                    region.assign_advice(|| "vj_B", col, 6, || val)
                })
                .collect::<Result<Vec<_>, _>>()?;
            cond.0.copy_advice(|| "cond", &mut region, config.cond_col, 6)?;

            // --- Row 7: gate B next (D=px, E=qx) ---
            copy_limbs(&mut region, px, &fcc.x_cols, 7, "px")?;
            copy_limbs(&mut region, qx, &fcc.z_cols, 7, "qx")?;

            // Collect range checks for all three gates.
            let checks_a = std::iter::once((u_a_cell, u_max.clone()))
                .chain(vs_a_cells.into_iter().zip(
                    config.vs_bounds.iter().map(|(_, vj_max)| vj_max.clone()),
                ));
            let checks_c = std::iter::once((u_c_cell, u_max.clone()))
                .chain(vs_c_cells.into_iter().zip(
                    config.vs_bounds.iter().map(|(_, vj_max)| vj_max.clone()),
                ));
            let checks_b = std::iter::once((u_b_cell, u_max.clone()))
                .chain(vs_b_cells.into_iter().zip(
                    config.vs_bounds.iter().map(|(_, vj_max)| vj_max.clone()),
                ));

            Ok(checks_a.chain(checks_c).chain(checks_b).collect::<Vec<_>>())
        },
    )?;

    range_checks.iter().try_for_each(|(cell, ubound)| {
        base_chip
            .native_gadget
            .assert_lower_than_fixed(layouter, cell, ubound.magnitude())
    })
}
