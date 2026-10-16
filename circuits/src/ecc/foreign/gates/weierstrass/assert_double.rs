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

//! Foreign-field elliptic-curve point-doubling assertion built on the unified
//! gate.
//!
//! Proves `[2]p = r` via three instantiations of the unified gate in a
//! **single region**, sharing two rows between consecutive gates:
//!
//! ```text
//! Row 0: x=rx, z=ry          [slope(p,r):  A, B]
//! Row 1: x=λ,  aux=u_W       [slope(p,r):  C + selector]
//! Row 2: x=px, z=py          [slope(p,r):  D, E  =  tangent: A, B(unused)  ← shared]
//! Row 3: x=py, aux=u_T       [tangent:     C + selector]
//! Row 4: x=λ,  z=px          [tangent:     D, E(unused)  =  lambda_sq: A, B  ← shared]
//! Row 5: x=0,  aux=u_S       [lambda_sq:   C(zeroed) + selector]
//! Row 6: x=px, z=rx          [lambda_sq:   D, E]
//! ```
//!
//! **Row-sharing trick**: the tangent gate is instantiated with C=py and D=λ
//! instead of the usual C=λ and D=py.  Both assignments produce the same
//! constraint `3·px² + α − 2·λ·py = 0 (mod m)` because `cd·(C·D) = −2·py·λ` is
//! symmetric.  With C=py the tangent's prev-row holds (x=px, z=py), matching
//! the slope's next-row; with D=λ the tangent's next-row holds (x=λ, z=px),
//! matching the lambda-squared prev-row.

use std::collections::BTreeMap;

use midnight_proofs::{
    circuit::{Chip, Layouter},
    plonk::Error,
};
use num_bigint::{BigInt as BI, BigUint, ToBigInt};
use num_traits::{One, Zero};

use super::{
    unified::{UnifiedConfig, curve_alpha},
    utils::{assign_coeffs, copy_limbs},
};
use crate::{
    CircuitField,
    ecc::curves::WeierstrassCurve,
    field::foreign::{
        FieldChip,
        params::FieldEmulationParams,
        util::{compute_u, compute_vj, pair_wise_prod, signed_mod, sum_bigints},
    },
    instructions::NativeInstructions,
    types::{AssignedBit, AssignedField, InnerValue},
};

/// If `cond = 1`, asserts that `[2]p = r` over the foreign field.
///
/// If `cond = 0`, asserts nothing.
#[allow(clippy::type_complexity)]
pub fn assert_double<F, C, P, N>(
    layouter: &mut impl Layouter<F>,
    cond: &AssignedBit<F>,
    p: (&AssignedField<F, C::Base, P>, &AssignedField<F, C::Base, P>),
    r: (&AssignedField<F, C::Base, P>, &AssignedField<F, C::Base, P>),
    lambda: &AssignedField<F, C::Base, P>,
    base_chip: &FieldChip<F, C::Base, P, N>,
    config: &UnifiedConfig<C>,
) -> Result<(), Error>
where
    F: CircuitField,
    C: WeierstrassCurve,
    P: FieldEmulationParams<F, C::Base>,
    N: NativeInstructions<F>,
{
    let m = &C::Base::modulus().to_bigint().unwrap();
    let moduli = P::moduli();
    let powers = &base_chip.config().witness_powers;
    let (bs, bs2) = (&powers.bs, &powers.bs2);
    let fcc = base_chip.config();

    let (px, py) = p;
    let (rx, ry) = r;

    // Normalize each field element once; the three gates share the results.
    let px = &base_chip.normalize(layouter, px)?;
    let py = &base_chip.normalize(layouter, py)?;
    let rx = &base_chip.normalize(layouter, rx)?;
    let ry = &base_chip.normalize(layouter, ry)?;
    let lambda = &base_chip.normalize(layouter, lambda)?;

    // ---------------------------------------------------------------------------
    // Gate W — slope(p, r, negate=true), standard slot assignment
    //   a=0, b=1, d=0, e=1, ca=1, cd=−1
    //   A=rx, B=ry, C=λ, D=px, E=py
    //   Enforces: λ·(rx − px) = −(ry + py)  (mod m)
    // ---------------------------------------------------------------------------
    let (a_w, b_w, d_w, e_w, ca_w, cd_w) = (
        BI::zero(),
        BI::one(),
        BI::zero(),
        BI::one(),
        BI::one(),
        -BI::one(),
    );
    let const_w = &a_w + &b_w + &d_w + &e_w + &ca_w + &cd_w; // = 2
    let csa_w = BI::from(2) * &a_w + &ca_w; // coef of ΣA = 1
    let csd_w = &d_w + &cd_w; // coef of ΣD = -1

    // ---------------------------------------------------------------------------
    // Gate T — tangent, with C=py and D=λ (swapped from the usual C=λ, D=py)
    //   a=3, b=0, d=0, e=0, ca=0, cd=−2, k=1
    //   A=px, B=py(unused), C=py, D=λ, E=px(unused)
    //   Enforces: 3·px² + α − 2·py·λ = 0  (mod m) — same as 3·px² + α = 2·λ·py,
    //   for α the coefficient `a` of the curve equation
    //
    //   The slot swap is what enables both row sharings:
    //     prev-row (A=px, B=py) matches slope's next-row (D=px, E=py)
    //     next-row (D=λ, E=px) matches lambda_sq's prev-row (A=λ, B=px)
    // ---------------------------------------------------------------------------
    let (a_t, b_t, d_t, e_t, ca_t, cd_t) = (
        BI::from(3),
        BI::zero(),
        BI::zero(),
        BI::zero(),
        BI::zero(),
        -BI::from(2),
    );

    // ---------------------------------------------------------------------------
    // Gate LS — lambda-squared: λ² = 2·px + rx  (mod m)
    //   a=1, b=−2, d=−1, e=0, ca=0, cd=0
    //   A=λ (prev x-slot = Row 4), B=px, D=rx, E=unused
    //   Using b=−2 collapses the two px terms into one coefficient.
    // ---------------------------------------------------------------------------
    let (a_ls, b_ls, d_ls, e_ls, ca_ls, cd_ls) = (
        BI::one(),
        -BI::from(2),
        -BI::one(),
        BI::zero(),
        BI::zero(),
        BI::zero(),
    );

    // ---------------------------------------------------------------------------
    // Precompute limb representations (shared across gates).
    // ---------------------------------------------------------------------------
    let lmb = lambda.bigint_limbs();
    let pxl = px.bigint_limbs();
    let pyl = py.bigint_limbs();
    let rxl = rx.bigint_limbs();
    let ryl = ry.bigint_limbs();

    // Bilinear products needed by the gates.
    let lmb_rx = lmb.clone().zip(rxl.clone()).map(|(l, r)| pair_wise_prod(&l, &r)); // λ·rx (gate W ca)
    let lmb_px = lmb.clone().zip(pxl.clone()).map(|(l, p)| pair_wise_prod(&l, &p)); // λ·px (gate W cd)
    let pxl2 = pxl.clone().map(|v| pair_wise_prod(&v, &v)); // px²  (gate T A²)
    let lmb_py = lmb.clone().zip(pyl.clone()).map(|(l, p)| pair_wise_prod(&l, &p)); // λ·py (gate T cd, via C·D=py·λ)
    let lmb2 = lmb.clone().map(|l| pair_wise_prod(&l, &l)); // λ²   (gate LS A²)

    let (k_min, u_max) = config.u_bounds.clone();

    // ---------------------------------------------------------------------------
    // Witness: u and vj for gate W (slope).
    // expr = 2 + Σrx + Σry − Σpx + Σpy + Σλrx − Σλpx
    // ---------------------------------------------------------------------------
    let expr_w = rxl.clone().map(|v| &csa_w * sum_bigints(bs, &v) + &const_w)
        + ryl.clone().map(|v| &b_w * sum_bigints(bs, &v))
        + pxl.clone().map(|v| &csd_w * sum_bigints(bs, &v))
        + pyl.clone().map(|v| &e_w * sum_bigints(bs, &v))
        + lmb_rx.clone().map(|v| &ca_w * sum_bigints(bs2, &v))
        + lmb_px.clone().map(|v| &cd_w * sum_bigints(bs2, &v));
    let u_w = expr_w.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

    let vs_w: Vec<_> = moduli
        .iter()
        .zip(config.vs_bounds.iter())
        .enumerate()
        .map(|(j, (mj, vj_bounds))| {
            let bs_mj = &powers.bs_mj[j];
            let bs2_mj = &powers.bs2_mj[j];
            let (lj_min, vj_max) = vj_bounds.clone();
            let expr_mj = rxl.clone().map(|v| &csa_w * sum_bigints(bs_mj, &v) + &const_w)
                + ryl.clone().map(|v| &b_w * sum_bigints(bs_mj, &v))
                + pxl.clone().map(|v| &csd_w * sum_bigints(bs_mj, &v))
                + pyl.clone().map(|v| &e_w * sum_bigints(bs_mj, &v))
                + lmb_rx.clone().map(|v| &ca_w * sum_bigints(bs2_mj, &v))
                + lmb_px.clone().map(|v| &cd_w * sum_bigints(bs2_mj, &v));
            expr_mj
                .zip(u_w.clone())
                .map(|(e, u)| compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value()))
        })
        .collect();

    // ---------------------------------------------------------------------------
    // Witness: u and vj for gate T (tangent with C=py, D=λ).
    // expr = 1 + α + 6·Σpx + 3·Σpx² − 2·Σpy − 2·Σλ − 2·Σλpy
    // ---------------------------------------------------------------------------
    let alpha = curve_alpha::<C>();
    let expr_t = pxl.clone().map(|v| BI::from(6) * sum_bigints(bs, &v) + BI::one() + &alpha)
        + pxl2.clone().map(|v| BI::from(3) * sum_bigints(bs2, &v))
        - pyl.clone().map(|v| BI::from(2) * sum_bigints(bs, &v))
        - lmb.clone().map(|v| BI::from(2) * sum_bigints(bs, &v))
        - lmb_py.clone().map(|v| BI::from(2) * sum_bigints(bs2, &v));
    let u_t = expr_t.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

    let vs_t: Vec<_> = moduli
        .iter()
        .zip(config.vs_bounds.iter())
        .enumerate()
        .map(|(j, (mj, vj_bounds))| {
            let bs_mj = &powers.bs_mj[j];
            let bs2_mj = &powers.bs2_mj[j];
            let (lj_min, vj_max) = vj_bounds.clone();
            let alpha_mj = signed_mod(&alpha, mj);
            let expr_mj = pxl
                .clone()
                .map(|v| BI::from(6) * sum_bigints(bs_mj, &v) + BI::one() + &alpha_mj)
                + pxl2.clone().map(|v| BI::from(3) * sum_bigints(bs2_mj, &v))
                - pyl.clone().map(|v| BI::from(2) * sum_bigints(bs_mj, &v))
                - lmb.clone().map(|v| BI::from(2) * sum_bigints(bs_mj, &v))
                - lmb_py.clone().map(|v| BI::from(2) * sum_bigints(bs2_mj, &v));
            expr_mj
                .zip(u_t.clone())
                .map(|(e, u)| compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value()))
        })
        .collect();

    // ---------------------------------------------------------------------------
    // Witness: u and vj for gate LS (lambda-squared).
    // expr = −2 + 2·Σλ + Σλ² − 2·Σpx − Σrx
    // ---------------------------------------------------------------------------
    let expr_ls = lmb.clone().map(|v| BI::from(2) * sum_bigints(bs, &v) - BI::from(2))
        + lmb2.clone().map(|v| sum_bigints(bs2, &v))
        - pxl.clone().map(|v| BI::from(2) * sum_bigints(bs, &v))
        - rxl.clone().map(|v| sum_bigints(bs, &v));
    let u_ls = expr_ls.map(|e| compute_u(m, &e, (&k_min, &u_max), cond.value()));

    let vs_ls: Vec<_> = moduli
        .iter()
        .zip(config.vs_bounds.iter())
        .enumerate()
        .map(|(j, (mj, vj_bounds))| {
            let bs_mj = &powers.bs_mj[j];
            let bs2_mj = &powers.bs2_mj[j];
            let (lj_min, vj_max) = vj_bounds.clone();
            let expr_mj = lmb.clone().map(|v| BI::from(2) * sum_bigints(bs_mj, &v) - BI::from(2))
                + lmb2.clone().map(|v| sum_bigints(bs2_mj, &v))
                - pxl.clone().map(|v| BI::from(2) * sum_bigints(bs_mj, &v))
                - rxl.clone().map(|v| sum_bigints(bs_mj, &v));
            expr_mj
                .zip(u_ls.clone())
                .map(|(e, u)| compute_vj(m, mj, &e, &u, &k_min, (&lj_min, &vj_max), cond.value()))
        })
        .collect();

    // ---------------------------------------------------------------------------
    // Lay out the 7-row region.
    // ---------------------------------------------------------------------------
    let range_checks = layouter.assign_region(
        || "Double",
        |mut region| {
            // --- Row 0: gate W prev (A=rx, B=ry) ---
            copy_limbs(&mut region, rx, &fcc.x_cols, 0, "rx")?;
            copy_limbs(&mut region, ry, &fcc.z_cols, 0, "ry")?;

            // --- Row 1: gate W cur (C=λ, selector, u_W, vj_W, cond, fixed coeffs) ---
            config.q_unified.enable(&mut region, 1)?;
            copy_limbs(&mut region, lambda, &fcc.x_cols, 1, "lambda")?;
            assign_coeffs(
                &mut region,
                1,
                &config.coeff_cols,
                &config.coeff_bounds,
                [&a_w, &b_w, &d_w, &e_w, &ca_w, &cd_w, &BI::zero()],
            )?;
            let checks_w = config.assign_carries(&mut region, fcc, 1, &u_w, &vs_w)?;
            cond.0.copy_advice(|| "cond", &mut region, config.cond_col, 1)?;

            // --- Row 2: shared (gate W next D=px/E=py; gate T prev A=px/B=py) ---
            copy_limbs(&mut region, px, &fcc.x_cols, 2, "px")?;
            copy_limbs(&mut region, py, &fcc.z_cols, 2, "py")?;

            // --- Row 3: gate T cur (C=py, selector, u_T, vj_T, cond, fixed coeffs) ---
            config.q_unified.enable(&mut region, 3)?;
            copy_limbs(&mut region, py, &fcc.x_cols, 3, "py")?;
            assign_coeffs(
                &mut region,
                3,
                &config.coeff_cols,
                &config.coeff_bounds,
                [&a_t, &b_t, &d_t, &e_t, &ca_t, &cd_t, &BI::one()],
            )?;
            let checks_t = config.assign_carries(&mut region, fcc, 3, &u_t, &vs_t)?;
            cond.0.copy_advice(|| "cond", &mut region, config.cond_col, 3)?;

            // --- Row 4: shared (gate T next D=λ/E=px; gate LS prev A=λ/B=px) ---
            copy_limbs(&mut region, lambda, &fcc.x_cols, 4, "lambda")?;
            copy_limbs(&mut region, px, &fcc.z_cols, 4, "px")?;

            // --- Row 5: gate LS cur (C=unused, selector, u_LS, vj_LS, cond, fixed coeffs)
            // ---
            config.q_unified.enable(&mut region, 5)?;
            assign_coeffs(
                &mut region,
                5,
                &config.coeff_cols,
                &config.coeff_bounds,
                [&a_ls, &b_ls, &d_ls, &e_ls, &ca_ls, &cd_ls, &BI::zero()],
            )?;
            let checks_ls = config.assign_carries(&mut region, fcc, 5, &u_ls, &vs_ls)?;
            cond.0.copy_advice(|| "cond", &mut region, config.cond_col, 5)?;

            // --- Row 6: gate LS next (D=rx, E=unused) ---
            copy_limbs(&mut region, rx, &fcc.x_cols, 6, "rx")?;

            Ok([checks_w, checks_t, checks_ls].concat())
        },
    )?;

    let mut by_bound = BTreeMap::<BigUint, Vec<_>>::new();
    for (cell, bound) in range_checks {
        by_bound.entry(bound.magnitude().clone()).or_default().push(cell);
    }
    (by_bound.iter()).try_for_each(|(bound, cells)| {
        base_chip.native_gadget.assert_many_lower_than_fixed(layouter, cells, bound)
    })
}
