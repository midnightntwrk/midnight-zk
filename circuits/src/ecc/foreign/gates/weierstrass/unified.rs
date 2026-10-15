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

//! Unified foreign-field custom gate for degree-2 modular identities.
//!
//! The gate enforces
//!
//! ```text
//! cond · [a·A² + b·B + d·D + e·E + ca·(C·A) + cd·(C·D) + k·α − (u + k_min)·m] = 0
//! ```
//!
//! where
//!   - `A`, `B`, `C`, `D`, `E` are foreign-field elements (multi-limb) laid out
//!     across three consecutive rows,
//!   - `(a, b, d, e, ca, cd, k)` are fixed coefficients stored in seven
//!     dedicated fixed columns at the selector row,
//!   - `α` is the coefficient `a` of the curve equation `y² = x³ + αx + β`,
//!   - `u` and `vj` are auxiliary carry witnesses,
//!   - `m` is the foreign-field modulus,
//!   - `k_min` is a constant chosen so that `u` stays non-negative.
//!
//! Note: there is no `C²` or linear-`A` term; any quadratic `X²` identity
//! should place `X` in the `A` slot and use `a=1`.
//!
//! Layout (three rows):
//!
//! ```text
//! | A_0 … A_k  | B_0 … B_k  |   ← row S−1  (x_cols, z_cols)
//! | C_0 … C_k  | u  vj  cond |   ← row S    (x_cols, aux; selector here)
//! | D_0 … D_k  | E_0 … E_k  |   ← row S+1  (x_cols, z_cols)
//! ```
//!
//! Coefficient ranges are declared by the caller via [`CoeffBounds`]. The
//! ranges drive the worst-case bounds on `u` and `vj`, and therefore the
//! bit-lengths of the range checks at every use site.
//!
//! A carry wider than one row of range checks (`nb_parallel_range_checks ·
//! max_bit_len` bits) is split as `lo + 2^L · hi`, for `L` that row width,
//! with `hi` in one of the free columns of the selector row. Its `lo` then
//! takes exactly one row of range checks, and its short `hi` shares a row
//! with other short values.
//!
//! # Purpose
//!
//! This gate is the shared backend for several foreign-field ECC identities
//! (e.g. the tangent check `3·px² + α = 2·λ·py`, the λ-squared check
//! `λ² = px + qx + rx`, and the slope check `λ·(qx − px) = ±qy − py`).
//! Merging them into one custom gate amortises the range-checked carry row
//! `(u, vj)` across all instantiations, reducing proving cost relative to a
//! separate gate per identity. The module itself is agnostic to these
//! particular instantiations and exposes only the generic equation above.

use std::{cmp, marker::PhantomData, ops::Rem};

use midnight_proofs::{
    circuit::{Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Constraints, Error, Expression, Fixed, Selector,
        VirtualCells,
    },
    poly::Rotation,
};
use num_bigint::{BigInt as BI, ToBigInt};
use num_traits::{One, Zero};

use crate::{
    CircuitField,
    ecc::curves::WeierstrassCurve,
    field::foreign::{
        field_chip::FieldChipConfig,
        params::FieldEmulationParams,
        util::{
            get_advice_vec, get_identity_auxiliary_bounds, karatsuba_bilinear_sum, signed_mod,
            signed_repr, sum_bigints, sum_exprs, urem,
        },
    },
    types::AssignedNative,
    utils::util::bigint_to_fe,
};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Inclusive `(min, max)` range for each of the seven gate coefficients.
/// Declared by the caller when configuring the gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffBounds {
    pub a: (BI, BI),
    pub b: (BI, BI),
    pub d: (BI, BI),
    pub e: (BI, BI),
    pub ca: (BI, BI),
    pub cd: (BI, BI),
    pub k: (BI, BI),
}

/// Unified foreign-field gate configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnifiedConfig<C: WeierstrassCurve> {
    pub(super) q_unified: Selector,
    /// Fixed coefficient columns `[a, b, d, e, ca, cd, k]`, queried at
    /// selector offset.
    pub(super) coeff_cols: [Column<Fixed>; 7],
    pub(super) u_bounds: (BI, BI),
    pub(super) vs_bounds: Vec<(BI, BI)>,
    pub(super) cond_col: Column<Advice>,
    /// Declared coefficient ranges; enforced at every call site.
    pub(super) coeff_bounds: CoeffBounds,
    /// The bit length `L` of the low part of split carries, and the column of
    /// the high part of every carry `[u, v_1, ...]` that is split.
    carry_split: (u32, Vec<Option<Column<Advice>>>),
    _marker: PhantomData<C>,
}

impl<C: WeierstrassCurve> UnifiedConfig<C> {
    /// Computes worst-case auxiliary-variable bounds for the gate, given the
    /// declared coefficient ranges and the limb decomposition parameters.
    pub fn bounds<F, P>(
        coeff_bounds: &CoeffBounds,
        nb_parallel_range_checks: usize,
        max_bit_len: u32,
    ) -> ((BI, BI), Vec<(BI, BI)>)
    where
        F: CircuitField,
        P: FieldEmulationParams<F, C::Base>,
    {
        let base = BI::from(2).pow(P::LOG2_BASE);
        let nb_limbs = P::NB_LIMBS;
        let moduli = P::moduli();
        let bs = P::base_powers();
        let bs2 = P::double_base_powers();

        let limbs_max = vec![&base - BI::one(); nb_limbs as usize];
        let limbs_max2 = vec![(&base - BI::one()).pow(2); (nb_limbs * nb_limbs) as usize];
        let max_sum = sum_bigints(&bs, &limbs_max);
        let max_sum2 = sum_bigints(&bs2, &limbs_max2);
        let alpha = curve_alpha::<C>();

        let expr_bounds = expr_bounds_for_weights(coeff_bounds, &alpha, &max_sum, &max_sum2);

        let expr_mj_bounds: Vec<_> = moduli
            .iter()
            .map(|mj| {
                let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                let max_sum_mj = sum_bigints(&bs_mj, &limbs_max);
                let max_sum2_mj = sum_bigints(&bs2_mj, &limbs_max2);
                let alpha_mj = signed_mod(&alpha, mj);
                expr_bounds_for_weights(coeff_bounds, &alpha_mj, &max_sum_mj, &max_sum2_mj)
            })
            .collect();

        get_identity_auxiliary_bounds::<F, C::Base>(
            "unified_ffa",
            &moduli,
            expr_bounds,
            &expr_mj_bounds,
            nb_parallel_range_checks,
            max_bit_len,
        )
    }

    /// Configures the gate. Allocates seven fresh fixed columns for the
    /// per-row coefficients and installs the constraint polynomial. The high
    /// parts of split carries take `free_cols`, which must be unused at the
    /// selector row; a carry is not split if they are not enough.
    pub fn configure<F, P>(
        meta: &mut ConstraintSystem<F>,
        field_chip_config: &FieldChipConfig,
        cond_col: &Column<Advice>,
        free_cols: &[Column<Advice>],
        coeff_bounds: &CoeffBounds,
        nb_parallel_range_checks: usize,
        max_bit_len: u32,
    ) -> UnifiedConfig<C>
    where
        F: CircuitField,
        P: FieldEmulationParams<F, C::Base>,
    {
        let m = &C::Base::modulus().to_bigint().unwrap();
        let moduli = P::moduli();
        let bs = P::base_powers();
        let bs2 = P::double_base_powers();

        let ((k_min, u_max), vs_bounds) =
            Self::bounds::<F, P>(coeff_bounds, nb_parallel_range_checks, max_bit_len);

        let lo_bits = nb_parallel_range_checks as u32 * max_bit_len;
        let carry_bounds =
            std::iter::once(&u_max).chain(vs_bounds.iter().map(|(_, vj_max)| vj_max));
        let mut free_cols = free_cols.iter();
        let hi_cols: Vec<_> = carry_bounds
            .map(|bound| (bound.bits() > lo_bits as u64 + 1).then(|| free_cols.next()).flatten())
            .map(|col| col.inspect(|col| meta.enable_equality(**col)).copied())
            .collect();
        let two_pow_lo = Expression::Constant(bigint_to_fe::<F>(&(BI::one() << lo_bits)));
        let carry = |meta: &mut VirtualCells<'_, F>, col: Column<Advice>, i: usize| {
            let lo = meta.query_advice(col, Rotation::cur());
            match hi_cols[i] {
                Some(hi_col) => {
                    lo + two_pow_lo.clone() * meta.query_advice(hi_col, Rotation::cur())
                }
                None => lo,
            }
        };

        let alpha = curve_alpha::<C>();
        let q_unified = meta.selector();
        let coeff_cols: [Column<Fixed>; 7] = core::array::from_fn(|_| meta.fixed_column());

        meta.create_gate("Foreign-field unified", |meta| {
            let cond = meta.query_advice(*cond_col, Rotation::cur());
            let u = carry(meta, field_chip_config.u_col, 0);
            let vs: Vec<_> = (field_chip_config.v_cols.iter().enumerate())
                .map(|(j, col)| carry(meta, *col, j + 1))
                .collect();

            let a_s = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::prev());
            let b_s = get_advice_vec(meta, &field_chip_config.z_cols, Rotation::prev());
            let c_s = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::cur());
            let d_s = get_advice_vec(meta, &field_chip_config.x_cols, Rotation::next());
            let e_s = get_advice_vec(meta, &field_chip_config.z_cols, Rotation::next());

            let a_c = meta.query_fixed(coeff_cols[0], Rotation::cur());
            let b_c = meta.query_fixed(coeff_cols[1], Rotation::cur());
            let d_c = meta.query_fixed(coeff_cols[2], Rotation::cur());
            let e_c = meta.query_fixed(coeff_cols[3], Rotation::cur());
            let ca_c = meta.query_fixed(coeff_cols[4], Rotation::cur());
            let cd_c = meta.query_fixed(coeff_cols[5], Rotation::cur());
            let k_c = meta.query_fixed(coeff_cols[6], Rotation::cur());

            let k_min_fe = Expression::Constant(bigint_to_fe::<F>(&k_min));
            let m_fe = Expression::Constant(bigint_to_fe::<F>(m));

            // Gate polynomial expanded from
            //   a·(1+ΣA)² + b·(1+ΣB) + d·(1+ΣD) + e·(1+ΣE)
            //     + ca·(1+ΣC)·(1+ΣA) + cd·(1+ΣC)·(1+ΣD)
            // into per-summation coefficients:
            //   (a+b+d+e+ca+cd)
            //   + (2a+ca)·ΣA + a·ΣA²
            //   + b·ΣB
            //   + (ca+cd)·ΣC
            //   + (d+cd)·ΣD + e·ΣE
            //   + ca·ΣCA + cd·ΣCD
            // plus the constant k·α.
            let native_id = {
                let sum_a = sum_exprs::<F>(&bs, &a_s);
                let sum_b = sum_exprs::<F>(&bs, &b_s);
                let sum_c = sum_exprs::<F>(&bs, &c_s);
                let sum_d = sum_exprs::<F>(&bs, &d_s);
                let sum_e = sum_exprs::<F>(&bs, &e_s);
                let sum_a2 = karatsuba_bilinear_sum::<F>(&bs2, &a_s, &a_s);
                let sum_ca = karatsuba_bilinear_sum::<F>(&bs2, &c_s, &a_s);
                let sum_cd = karatsuba_bilinear_sum::<F>(&bs2, &c_s, &d_s);

                let expr = (&a_c + &b_c + &d_c + &e_c + &ca_c + &cd_c)
                    + (Expression::from(2) * &a_c + &ca_c) * sum_a
                    + &a_c * sum_a2
                    + &b_c * sum_b
                    + (&ca_c + &cd_c) * sum_c
                    + (&d_c + &cd_c) * sum_d
                    + &e_c * sum_e
                    + &ca_c * sum_ca
                    + &cd_c * sum_cd
                    + &k_c * Expression::Constant(bigint_to_fe::<F>(&alpha));
                &cond * (expr - (&u + k_min_fe) * m_fe)
            };

            let mut moduli_ids = moduli
                .iter()
                .zip(vs)
                .zip(vs_bounds.iter())
                .map(|((mj, vj), vj_bounds)| {
                    let (lj_min, _) = vj_bounds;
                    let bs_mj = bs.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();
                    let bs2_mj = bs2.iter().map(|b| b.rem(mj)).collect::<Vec<_>>();

                    let sum_a = sum_exprs::<F>(&bs_mj, &a_s);
                    let sum_b = sum_exprs::<F>(&bs_mj, &b_s);
                    let sum_c = sum_exprs::<F>(&bs_mj, &c_s);
                    let sum_d = sum_exprs::<F>(&bs_mj, &d_s);
                    let sum_e = sum_exprs::<F>(&bs_mj, &e_s);
                    let sum_a2 = karatsuba_bilinear_sum::<F>(&bs2_mj, &a_s, &a_s);
                    let sum_ca = karatsuba_bilinear_sum::<F>(&bs2_mj, &c_s, &a_s);
                    let sum_cd = karatsuba_bilinear_sum::<F>(&bs2_mj, &c_s, &d_s);

                    let expr_mj = (&a_c + &b_c + &d_c + &e_c + &ca_c + &cd_c)
                        + (Expression::from(2) * &a_c + &ca_c) * sum_a
                        + &a_c * sum_a2
                        + &b_c * sum_b
                        + (&ca_c + &cd_c) * sum_c
                        + (&d_c + &cd_c) * sum_d
                        + &e_c * sum_e
                        + &ca_c * sum_ca
                        + &cd_c * sum_cd
                        + &k_c * Expression::Constant(bigint_to_fe::<F>(&signed_mod(&alpha, mj)));
                    &cond
                        * (expr_mj
                            - &u * Expression::Constant(bigint_to_fe::<F>(&urem(m, mj)))
                            - Expression::Constant(bigint_to_fe::<F>(&urem(&(&k_min * m), mj)))
                            - (vj + Expression::Constant(bigint_to_fe::<F>(lj_min)))
                                * Expression::Constant(bigint_to_fe::<F>(mj)))
                })
                .collect::<Vec<_>>();
            moduli_ids.push(native_id);

            Constraints::with_selector(q_unified, moduli_ids)
        });

        UnifiedConfig {
            q_unified,
            coeff_cols,
            u_bounds: (k_min, u_max),
            vs_bounds,
            cond_col: *cond_col,
            coeff_bounds: coeff_bounds.clone(),
            carry_split: (lo_bits, hi_cols),
            _marker: PhantomData,
        }
    }

    /// Assigns the carries `u` and `vs` of the gate instance at `offset`,
    /// returning the cells to range-check with their (power-of-two) bounds.
    pub(super) fn assign_carries<F: CircuitField>(
        &self,
        region: &mut Region<'_, F>,
        field_chip_config: &FieldChipConfig,
        offset: usize,
        u: &Value<BI>,
        vs: &[Value<BI>],
    ) -> Result<Vec<(AssignedNative<F>, BI)>, Error> {
        let (lo_bits, hi_cols) = &self.carry_split;
        let cols = std::iter::once(&field_chip_config.u_col).chain(&field_chip_config.v_cols);
        let bounds = std::iter::once(&self.u_bounds.1).chain(self.vs_bounds.iter().map(|(_, b)| b));
        let mut checks = vec![];
        for (((col, hi_col), carry), bound) in
            cols.zip(hi_cols).zip(std::iter::once(u).chain(vs)).zip(bounds)
        {
            let assign = |region: &mut Region<'_, F>, col: Column<Advice>, value: Value<BI>| {
                region.assign_advice(
                    || "carry",
                    col,
                    offset,
                    || value.as_ref().map(bigint_to_fe::<F>),
                )
            };
            match hi_col {
                None => checks.push((assign(region, *col, carry.clone())?, bound.clone())),
                Some(hi_col) => {
                    let lo = carry.clone().map(|c| c & ((BI::one() << lo_bits) - 1));
                    let hi = carry.clone().map(|c| c >> lo_bits);
                    checks.push((assign(region, *col, lo)?, BI::one() << lo_bits));
                    checks.push((assign(region, *hi_col, hi)?, bound >> lo_bits));
                }
            }
        }
        Ok(checks)
    }
}

// ---------------------------------------------------------------------------
// Bounds helper
// ---------------------------------------------------------------------------

/// The coefficient `α` of the curve equation `y² = x³ + αx + β`, as its signed
/// representative.
pub(super) fn curve_alpha<C: WeierstrassCurve>() -> BI {
    signed_repr::<C::Base>()(C::A.to_biguint().into())
}

/// Worst-case `(min, max)` of the gate polynomial over the declared coefficient
/// ranges and limb values in `[0, base−1]`.
///
/// Each per-summation term is `coeff · Σ` with `Σ ∈ [0, Σ_max]` and `coeff` in
/// some range `[c_min, c_max]`. Since `Σ ≥ 0`, the term's contribution to the
/// overall `max` is `max(0, c_max·Σ_max)`, and to the overall `min` is
/// `min(0, c_min·Σ_max)`.
fn expr_bounds_for_weights(cb: &CoeffBounds, alpha: &BI, max_sum: &BI, max_sum2: &BI) -> (BI, BI) {
    // Compound coefficient ranges, the constant including k·α.
    let (k_alpha_lo, k_alpha_hi) = {
        let (x, y) = (&cb.k.0 * alpha, &cb.k.1 * alpha);
        (cmp::min(x.clone(), y.clone()), cmp::max(x, y))
    };
    let const_lo = &cb.a.0 + &cb.b.0 + &cb.d.0 + &cb.e.0 + &cb.ca.0 + &cb.cd.0 + k_alpha_lo;
    let const_hi = &cb.a.1 + &cb.b.1 + &cb.d.1 + &cb.e.1 + &cb.ca.1 + &cb.cd.1 + k_alpha_hi;

    let sa_lo = BI::from(2) * &cb.a.0 + &cb.ca.0;
    let sa_hi = BI::from(2) * &cb.a.1 + &cb.ca.1;
    let sc_lo = &cb.ca.0 + &cb.cd.0;
    let sc_hi = &cb.ca.1 + &cb.cd.1;
    let sd_lo = &cb.d.0 + &cb.cd.0;
    let sd_hi = &cb.d.1 + &cb.cd.1;

    let zero = BI::zero();
    let pos = |c: BI, w: &BI| cmp::max(zero.clone(), c * w);
    let neg = |c: BI, w: &BI| cmp::min(zero.clone(), c * w);

    let hi = const_hi
        + pos(sa_hi, max_sum)
        + pos(cb.a.1.clone(), max_sum2)
        + pos(cb.b.1.clone(), max_sum)
        + pos(sc_hi, max_sum)
        + pos(sd_hi, max_sum)
        + pos(cb.e.1.clone(), max_sum)
        + pos(cb.ca.1.clone(), max_sum2)
        + pos(cb.cd.1.clone(), max_sum2);

    let lo = const_lo
        + neg(sa_lo, max_sum)
        + neg(cb.a.0.clone(), max_sum2)
        + neg(cb.b.0.clone(), max_sum)
        + neg(sc_lo, max_sum)
        + neg(sd_lo, max_sum)
        + neg(cb.e.0.clone(), max_sum)
        + neg(cb.ca.0.clone(), max_sum2)
        + neg(cb.cd.0.clone(), max_sum2);

    (lo, hi)
}
