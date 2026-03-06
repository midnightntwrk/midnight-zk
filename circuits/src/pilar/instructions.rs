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

//! Instruction trait implementations for [`PilarChip`].
//!
//! Implements [`AssignmentInstructions`], [`AssertionInstructions`],
//! [`ArithInstructions`], and [`EqualityInstructions`] for
//! [`AssignedNative`] using the single Pilar gate identity.

use std::ops::Neg;

use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::Error,
};

use crate::{
    field::{native::AssignedBit, AssignedNative},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, EqualityInstructions,
        ZeroInstructions,
    },
    CircuitField,
};

use super::PilarChip;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

impl<F: CircuitField> PilarChip<F> {
    /// Assign all five fixed columns at the given offset to encode a gate:
    /// `q_a · a_prev + q_b · a_cur + q_c · a_next + q_m · a_prev · a_cur + q_k = 0`.
    fn set_gate(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        q_a: F,
        q_b: F,
        q_c: F,
        q_m: F,
        q_k: F,
    ) -> Result<(), Error> {
        let cfg = self.config();
        region.assign_fixed(|| "q_a", cfg.q_a, offset, || Value::known(q_a))?;
        region.assign_fixed(|| "q_b", cfg.q_b, offset, || Value::known(q_b))?;
        region.assign_fixed(|| "q_c", cfg.q_c, offset, || Value::known(q_c))?;
        region.assign_fixed(|| "q_m", cfg.q_m, offset, || Value::known(q_m))?;
        region.assign_fixed(|| "q_k", cfg.q_k, offset, || Value::known(q_k))?;
        Ok(())
    }

    /// Copy `src` into the advice column at `offset` and constrain equality.
    fn copy_to(
        &self,
        region: &mut Region<'_, F>,
        src: &AssignedNative<F>,
        offset: usize,
    ) -> Result<AssignedNative<F>, Error> {
        let dst = region.assign_advice(
            || "copy",
            self.config().advice,
            offset,
            || src.value().copied(),
        )?;
        region.constrain_equal(src.cell(), dst.cell())?;
        Ok(dst)
    }
}

// ---------------------------------------------------------------------------
// AssignmentInstructions
// ---------------------------------------------------------------------------

impl<F: CircuitField> AssignmentInstructions<F, AssignedNative<F>> for PilarChip<F> {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedNative<F>, Error> {
        layouter.assign_region(
            || "pilar assign",
            |mut region| region.assign_advice(|| "val", self.config().advice, 0, || value),
        )
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        // Assign the constant and constrain it via the gate:
        // q_b · a_cur + q_k = 0  ⟹  1 · a_cur + (-constant) = 0  ⟹  a_cur = constant.
        layouter.assign_region(
            || "pilar assign_fixed",
            |mut region| {
                let cell = region.assign_advice(
                    || "const",
                    self.config().advice,
                    1,
                    || Value::known(constant),
                )?;
                // Padding rows 0 and 2 with zeros (they are accessed by rotations).
                region.assign_advice(|| "pad0", self.config().advice, 0, || Value::known(F::ZERO))?;
                region.assign_advice(|| "pad2", self.config().advice, 2, || Value::known(F::ZERO))?;
                self.set_gate(&mut region, 1, F::ZERO, F::ONE, F::ZERO, F::ZERO, -constant)?;
                Ok(cell)
            },
        )
    }
}

// ---------------------------------------------------------------------------
// AssertionInstructions
// ---------------------------------------------------------------------------

impl<F: CircuitField> AssertionInstructions<F, AssignedNative<F>> for PilarChip<F> {
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "pilar assert_equal",
            |mut region| region.constrain_equal(x.cell(), y.cell()),
        )
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<(), Error> {
        // Witness r = (x - y)^{-1} and constrain q_m · r · x - q_m · r · y - 1 = 0.
        // Encoded as: row layout [r, x, y] at offsets [0, 1, 2].
        // Gate at offset 1: q_a · a_prev + q_b · a_cur + q_m · a_prev · a_cur + q_k = 0.
        //   ⟹ (-1)·y + 0·x + 0 + 0 + 0 = ...
        // We need r·x - r·y = 1. The gate has a_prev = r, a_cur = x, a_next = y.
        // q_m · r · x + q_c · y + q_k = 0  ⟹  1·r·x + (-1)·y_via_lc ... hmm.
        //
        // Actually, let's use two gates. Gate at offset 1:
        //   q_a·r + q_b·x + q_m·r·x + q_k = 0  where a_prev=r, a_cur=x.
        //   Set q_m=1, others zero except q_k=-1 won't work because r·x != 1.
        //
        // Simpler: witness d = x - y and r = d^{-1}, constrain d·r = 1 and d = x - y.
        //
        // Gate 1 (offset 1): a_prev - a_cur + a_next = 0  ⟹  x - d + y... no.
        //
        // Let me use the approach: layout [x, d, y, r, -, dr] across rows.
        // Gate at offset 1: q_a·x + q_b·d + q_c·y = 0 with q_a=1, q_b=-1, q_c=-1.
        //   ⟹ x - d - y = 0  ⟹  d = x - y. ✓
        // Gate at offset 4: a_prev=r, a_cur=_, a_next=dr.
        //   Actually this uses too many rows. Let me think more carefully.
        //
        // Two separate regions:
        // Region 1: constrain d = x - y: [x, d, y] at [0,1,2], gate at 1: q_a·x - q_b·d - q_c·y = 0.
        //   ⟹ q_a=1, q_b=-1, q_c=-1: 1·x + (-1)·d + (-1)·y = 0  ⟹  d = x - y ✓
        // Region 2: constrain d·r = 1: [d, r, _] at [0,1,2], gate at 1: q_m·d·r + q_k = 0.
        //   ⟹ q_m=1, q_k=-1: d·r - 1 = 0  ⟹  d·r = 1 ✓

        let d_val = x.value().zip(y.value()).map(|(x, y)| *x - *y);
        let r_val = d_val.map(|d| d.invert().unwrap_or(F::ZERO));

        // Region 1: d = x - y.
        let d = layouter.assign_region(
            || "pilar assert_neq: d=x-y",
            |mut region| {
                self.copy_to(&mut region, x, 0)?;
                let d =
                    region.assign_advice(|| "d", self.config().advice, 1, || d_val)?;
                self.copy_to(&mut region, y, 2)?;
                // q_a·a_prev + q_b·a_cur + q_c·a_next = 0 ⟹ 1·x + (-1)·d + (-1)·y = 0.
                self.set_gate(&mut region, 1, F::ONE, -F::ONE, -F::ONE, F::ZERO, F::ZERO)?;
                Ok(d)
            },
        )?;

        // Region 2: d * r = 1.
        layouter.assign_region(
            || "pilar assert_neq: d*r=1",
            |mut region| {
                self.copy_to(&mut region, &d, 0)?;
                region.assign_advice(|| "r", self.config().advice, 1, || r_val)?;
                region.assign_advice(
                    || "pad",
                    self.config().advice,
                    2,
                    || Value::known(F::ZERO),
                )?;
                // q_m · a_prev · a_cur + q_k = 0  ⟹  1·d·r + (-1) = 0.
                self.set_gate(&mut region, 1, F::ZERO, F::ZERO, F::ZERO, F::ONE, -F::ONE)?;
                Ok(())
            },
        )
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        constant: F,
    ) -> Result<(), Error> {
        let c = self.assign_fixed(layouter, constant)?;
        self.assert_equal(layouter, x, &c)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        constant: F,
    ) -> Result<(), Error> {
        // Witness r = (x - constant)^{-1}, constrain r·x + (-constant)·r - 1 = 0.
        // Layout: [_, r, _] with gate at 1. But we need x in the gate.
        // Use: [x, r, _], gate at 1: q_m · x · r + q_k = 0 with q_m = 1, q_k = -1 doesn't
        // work because we need r*(x - c) = 1, i.e. r*x - c*r - 1 = 0.
        // Gate: q_a · a_prev + q_m · a_prev · a_cur + q_k = 0 with a_prev=x, a_cur=r.
        //   q_a = 0, q_b = -constant (coeff of r), q_m = 1, q_k = -1.
        //   ⟹ (-c)·r + 1·x·r + (-1) = 0  ⟹  r·(x - c) = 1  ✓

        let r_val = x.value().map(|x| (*x - constant).invert().unwrap_or(F::ZERO));

        layouter.assign_region(
            || "pilar assert_neq_fixed",
            |mut region| {
                self.copy_to(&mut region, x, 0)?;
                region.assign_advice(|| "r", self.config().advice, 1, || r_val)?;
                region.assign_advice(
                    || "pad",
                    self.config().advice,
                    2,
                    || Value::known(F::ZERO),
                )?;
                // q_a·x + q_b·r + q_m·x·r + q_k = 0 with q_a=0, q_b=-c, q_m=1, q_k=-1.
                self.set_gate(
                    &mut region,
                    1,
                    F::ZERO,
                    -constant,
                    F::ZERO,
                    F::ONE,
                    -F::ONE,
                )?;
                Ok(())
            },
        )
    }
}

// ---------------------------------------------------------------------------
// ArithInstructions
// ---------------------------------------------------------------------------

impl<F: CircuitField> ArithInstructions<F, AssignedNative<F>> for PilarChip<F> {
    fn linear_combination(
        &self,
        layouter: &mut impl Layouter<F>,
        terms: &[(F, AssignedNative<F>)],
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        // Filter out zero-coefficient terms.
        let terms: Vec<_> = terms.iter().filter(|(c, _)| !F::is_zero_vartime(c)).cloned().collect();

        if terms.is_empty() {
            return self.assign_fixed(layouter, constant);
        }

        // The Pilar gate can handle up to 2 terms per gate application
        // (using a_prev and a_cur with coefficients q_a and q_b), with a_next
        // holding the running accumulator. We chain gates to handle longer sums.
        //
        // For n terms, we process 2 at a time:
        //   Gate at offset 1: q_a·t0 + q_b·t1 + q_c·(-acc) + q_k = constant_part.
        //   Then the accumulator is copied forward.
        //
        // Actually the simplest approach: process terms in pairs.
        // Each gate: q_a · a_prev + q_b · a_cur + q_c · a_next + q_k = 0
        //   a_prev = term_i, a_cur = term_{i+1}, a_next = partial_sum, q_c = -1.
        //
        // For a single term: q_a · term + q_c · result + q_k = 0.

        let result_val = terms
            .iter()
            .fold(Value::known(constant), |acc, (coeff, x)| {
                acc.zip(x.value()).map(|(acc, val)| acc + *coeff * val)
            });

        if terms.len() == 1 {
            // Single term: result = c0 * t0 + constant.
            // Layout: [t0, result, _], gate at 1:
            //   q_a · t0 + q_b · result + q_k = 0
            //   q_a = c0, q_b = -1, q_k = constant.
            return layouter.assign_region(
                || "pilar lc (1 term)",
                |mut region| {
                    self.copy_to(&mut region, &terms[0].1, 0)?;
                    let result = region.assign_advice(
                        || "lc_result",
                        self.config().advice,
                        1,
                        || result_val,
                    )?;
                    region.assign_advice(
                        || "pad",
                        self.config().advice,
                        2,
                        || Value::known(F::ZERO),
                    )?;
                    self.set_gate(
                        &mut region,
                        1,
                        terms[0].0,
                        -F::ONE,
                        F::ZERO,
                        F::ZERO,
                        constant,
                    )?;
                    Ok(result)
                },
            );
        }

        if terms.len() == 2 {
            // Two terms: result = c0*t0 + c1*t1 + constant.
            // Layout: [t0, t1, result], gate at 1:
            //   q_a·t0 + q_b·t1 + q_c·result + q_k = 0
            //   q_a=c0, q_b=c1, q_c=-1, q_k=constant.
            return layouter.assign_region(
                || "pilar lc (2 terms)",
                |mut region| {
                    self.copy_to(&mut region, &terms[0].1, 0)?;
                    self.copy_to(&mut region, &terms[1].1, 1)?;
                    let result = region.assign_advice(
                        || "lc_result",
                        self.config().advice,
                        2,
                        || result_val,
                    )?;
                    self.set_gate(
                        &mut region,
                        1,
                        terms[0].0,
                        terms[1].0,
                        -F::ONE,
                        F::ZERO,
                        constant,
                    )?;
                    Ok(result)
                },
            );
        }

        // General case: chain gates to accumulate.
        // Process first 2 terms to get partial_sum, then one term at a time
        // (using a_prev = term_i, a_cur = old_acc, a_next = new_acc).
        let mut partial_val = Value::known(constant)
            .zip(terms[0].1.value())
            .map(|(acc, v)| acc + terms[0].0 * v);
        partial_val = partial_val
            .zip(terms[1].1.value())
            .map(|(acc, v)| acc + terms[1].0 * v);

        // First gate: [t0, t1, partial] at [0,1,2].
        let mut acc = layouter.assign_region(
            || "pilar lc (first pair)",
            |mut region| {
                self.copy_to(&mut region, &terms[0].1, 0)?;
                self.copy_to(&mut region, &terms[1].1, 1)?;
                let partial = region.assign_advice(
                    || "partial",
                    self.config().advice,
                    2,
                    || partial_val,
                )?;
                self.set_gate(
                    &mut region,
                    1,
                    terms[0].0,
                    terms[1].0,
                    -F::ONE,
                    F::ZERO,
                    constant,
                )?;
                Ok(partial)
            },
        )?;

        // Remaining terms: one per gate.
        for i in 2..terms.len() {
            let new_val = acc
                .value()
                .zip(terms[i].1.value())
                .map(|(a, v)| *a + terms[i].0 * v);

            let is_last = i == terms.len() - 1;
            let label = if is_last { "pilar lc (final)" } else { "pilar lc (chain)" };

            acc = layouter.assign_region(
                || label,
                |mut region| {
                    self.copy_to(&mut region, &terms[i].1, 0)?;
                    self.copy_to(&mut region, &acc, 1)?;
                    let new_acc = region.assign_advice(
                        || "acc",
                        self.config().advice,
                        2,
                        || new_val,
                    )?;
                    // q_a · term_i + q_b · old_acc + q_c · new_acc = 0.
                    // q_a = c_i, q_b = 1, q_c = -1.
                    self.set_gate(
                        &mut region,
                        1,
                        terms[i].0,
                        F::ONE,
                        -F::ONE,
                        F::ZERO,
                        F::ZERO,
                    )?;
                    Ok(new_acc)
                },
            )?;
        }

        Ok(acc)
    }

    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
        multiplying_constant: Option<F>,
    ) -> Result<AssignedNative<F>, Error> {
        if multiplying_constant == Some(F::ZERO) {
            return self.assign_fixed(layouter, F::ZERO);
        }

        let m = multiplying_constant.unwrap_or(F::ONE);

        // Layout: [x, y, result], gate at 1:
        //   q_m · x · y + q_c · result = 0  ⟹  m·x·y - result = 0.
        let result_val = x
            .value()
            .zip(y.value())
            .map(|(x, y)| m * *x * *y);

        layouter.assign_region(
            || "pilar mul",
            |mut region| {
                self.copy_to(&mut region, x, 0)?;
                self.copy_to(&mut region, y, 1)?;
                let result = region.assign_advice(
                    || "product",
                    self.config().advice,
                    2,
                    || result_val,
                )?;
                self.set_gate(&mut region, 1, F::ZERO, F::ZERO, -F::ONE, m, F::ZERO)?;
                Ok(result)
            },
        )
    }

    fn div(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let y_inv = self.inv(layouter, y)?;
        self.mul(layouter, x, &y_inv, None)
    }

    fn inv(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        // Witness r = x^{-1}, constrain x · r = 1.
        // Layout: [x, r, _], gate at 1: q_m · x · r + q_k = 0 with q_m=1, q_k=-1.
        let r_val = x.value().map(|x| x.invert().unwrap_or(F::ZERO));

        layouter.assign_region(
            || "pilar inv",
            |mut region| {
                self.copy_to(&mut region, x, 0)?;
                let r =
                    region.assign_advice(|| "inv", self.config().advice, 1, || r_val)?;
                region.assign_advice(
                    || "pad",
                    self.config().advice,
                    2,
                    || Value::known(F::ZERO),
                )?;
                self.set_gate(&mut region, 1, F::ZERO, F::ZERO, F::ZERO, F::ONE, -F::ONE)?;
                Ok(r)
            },
        )
    }

    fn inv0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        // If x = 0 return 0, else return x^{-1}.
        let is_zero = self.is_zero(layouter, x)?;
        let zero = self.assign_fixed(layouter, F::ZERO)?;
        let one = self.assign_fixed(layouter, F::ONE)?;

        // invertible = is_zero ? 1 : x  (so it is always non-zero).
        let invertible = self.select(layouter, &is_zero, &one, x)?;
        let inverse = self.inv(layouter, &invertible)?;

        // result = is_zero ? 0 : inverse.
        self.select(layouter, &is_zero, &zero, &inverse)
    }

    fn add_and_mul(
        &self,
        layouter: &mut impl Layouter<F>,
        (a, x): (F, &AssignedNative<F>),
        (b, y): (F, &AssignedNative<F>),
        (c, z): (F, &AssignedNative<F>),
        k: F,
        m: F,
    ) -> Result<AssignedNative<F>, Error> {
        // Compute a*x + b*y + c*z + k + m*x*y.
        // First compute p = x * y, then linear_combination of a*x + b*y + c*z + m*p + k.
        let p = self.mul(layouter, x, y, None)?;
        self.linear_combination(
            layouter,
            &[
                (a, x.clone()),
                (b, y.clone()),
                (c, z.clone()),
                (m, p),
            ],
            k,
        )
    }
}

// ---------------------------------------------------------------------------
// EqualityInstructions
// ---------------------------------------------------------------------------

impl<F: CircuitField + From<u64> + Neg<Output = F>> EqualityInstructions<F, AssignedNative<F>>
    for PilarChip<F>
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        // Enforce (i) (x - y) · aux = 1 - res  and  (ii) (x - y) · res = 0.
        //
        // Step 1: compute d = x - y.
        let d = self.sub(layouter, x, y)?;

        let res_val = x.value().zip(y.value()).map(|(x, y)| F::from((x == y) as u64));
        let aux_val = x
            .value()
            .zip(y.value())
            .map(|(x, y)| (*x - *y).invert().unwrap_or(F::ONE));

        // Step 2: (i) d · aux + res - 1 = 0.
        // Layout: [d, aux, _], gate at 1: q_m·d·aux + q_k = 0.
        // But we also need res. We need a second gate for res.
        // Actually, let's use: d·aux = 1 - res  ⟹  d·aux + res - 1 = 0.
        // Layout: [d, aux, res], gate at 1:
        //   q_m·d·aux + q_c·res + q_k = 0 with q_m=1, q_c=1, q_k=-1.
        let res = layouter.assign_region(
            || "pilar is_equal (i)",
            |mut region| {
                self.copy_to(&mut region, &d, 0)?;
                region.assign_advice(|| "aux", self.config().advice, 1, || aux_val)?;
                let res = region.assign_advice(
                    || "res",
                    self.config().advice,
                    2,
                    || res_val,
                )?;
                // q_m·d·aux + q_c·res + q_k = 0 ⟹ d·aux + res - 1 = 0.
                self.set_gate(&mut region, 1, F::ZERO, F::ZERO, F::ONE, F::ONE, -F::ONE)?;
                Ok(res)
            },
        )?;

        // Step 3: (ii) d · res = 0.
        // Layout: [d, res, _], gate at 1: q_m·d·res = 0.
        layouter.assign_region(
            || "pilar is_equal (ii)",
            |mut region| {
                self.copy_to(&mut region, &d, 0)?;
                self.copy_to(&mut region, &res, 1)?;
                region.assign_advice(
                    || "pad",
                    self.config().advice,
                    2,
                    || Value::known(F::ZERO),
                )?;
                self.set_gate(&mut region, 1, F::ZERO, F::ZERO, F::ZERO, F::ONE, F::ZERO)?;
                Ok(())
            },
        )?;

        Ok(AssignedBit(res))
    }

    fn is_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        // Enforce (i) (x - y) · aux = res  and  (ii) (x - y) · (1 - res) = 0.
        let d = self.sub(layouter, x, y)?;

        let res_val = x.value().zip(y.value()).map(|(x, y)| F::from((x != y) as u64));
        let aux_val = x
            .value()
            .zip(y.value())
            .map(|(x, y)| (*x - *y).invert().unwrap_or(F::ONE));

        // (i) d · aux - res = 0.
        // Layout: [d, aux, res], gate at 1: q_m·d·aux + q_c·res = 0.
        //   q_m=1, q_c=-1.
        let res = layouter.assign_region(
            || "pilar is_not_equal (i)",
            |mut region| {
                self.copy_to(&mut region, &d, 0)?;
                region.assign_advice(|| "aux", self.config().advice, 1, || aux_val)?;
                let res = region.assign_advice(
                    || "res",
                    self.config().advice,
                    2,
                    || res_val,
                )?;
                self.set_gate(
                    &mut region,
                    1,
                    F::ZERO,
                    F::ZERO,
                    -F::ONE,
                    F::ONE,
                    F::ZERO,
                )?;
                Ok(res)
            },
        )?;

        // (ii) d · (1 - res) = 0.
        // Gate at offset 1: a_prev = d (row 0), a_cur = res (row 1).
        // q_a · d + q_m · d · res = 0  with q_a = 1, q_m = -1.
        layouter.assign_region(
            || "pilar is_not_equal (ii)",
            |mut region| {
                self.copy_to(&mut region, &d, 0)?;
                self.copy_to(&mut region, &res, 1)?;
                region.assign_advice(
                    || "pad",
                    self.config().advice,
                    2,
                    || Value::known(F::ZERO),
                )?;
                self.set_gate(
                    &mut region,
                    1,
                    F::ONE,
                    F::ZERO,
                    F::ZERO,
                    -F::ONE,
                    F::ZERO,
                )?;
                Ok(())
            },
        )?;

        Ok(AssignedBit(res))
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        c: F,
    ) -> Result<AssignedBit<F>, Error> {
        let y = self.assign_fixed(layouter, c)?;
        self.is_equal(layouter, x, &y)
    }

    fn is_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        c: F,
    ) -> Result<AssignedBit<F>, Error> {
        let y = self.assign_fixed(layouter, c)?;
        self.is_not_equal(layouter, x, &y)
    }
}

// ---------------------------------------------------------------------------
// ZeroInstructions (blanket, uses defaults from the trait).
// ---------------------------------------------------------------------------

impl<F: CircuitField + From<u64> + Neg<Output = F>> ZeroInstructions<F, AssignedNative<F>>
    for PilarChip<F>
{
}

// ---------------------------------------------------------------------------
// Helper: select (needed by inv0).
// ---------------------------------------------------------------------------

impl<F: CircuitField + From<u64> + Neg<Output = F>> PilarChip<F> {
    /// `select(cond, a, b)` returns `a` if `cond = 1`, else `b`.
    /// Constrains `result = cond · a + (1 - cond) · b = cond · (a - b) + b`.
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        if_true: &AssignedNative<F>,
        if_false: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let diff = self.sub(layouter, if_true, if_false)?;
        let cond_native: AssignedNative<F> = cond.clone().into();
        let cond_times_diff = self.mul(layouter, &cond_native, &diff, None)?;
        self.linear_combination(
            layouter,
            &[
                (F::ONE, cond_times_diff),
                (F::ONE, if_false.clone()),
            ],
            F::ZERO,
        )
    }
}

// ---------------------------------------------------------------------------
// FromScratch (test infrastructure).
// ---------------------------------------------------------------------------

#[cfg(any(test, feature = "testing"))]
impl<F: CircuitField> crate::testing_utils::FromScratch<F> for PilarChip<F> {
    type Config = super::PilarConfig;

    fn new_from_scratch(config: &Self::Config) -> Self {
        use crate::utils::ComposableChip;
        PilarChip::new(config, &())
    }

    fn configure_from_scratch(
        meta: &mut midnight_proofs::plonk::ConstraintSystem<F>,
        instance_columns: &[midnight_proofs::plonk::Column<midnight_proofs::plonk::Instance>; 2],
    ) -> Self::Config {
        use crate::utils::ComposableChip;
        use midnight_proofs::plonk::Fixed;

        let advice = meta.advice_column();
        let fixed_cols: [midnight_proofs::plonk::Column<Fixed>; super::NB_PILAR_FIXED_COLS] =
            core::array::from_fn(|_| meta.fixed_column());
        // PilarChip only uses one instance column; pick the second one
        // (matching existing convention where index 1 is the "normal" instance).
        let instance = instance_columns[1];
        PilarChip::<F>::configure(meta, &(advice, fixed_cols, instance))
    }

    fn load_from_scratch(
        &self,
        _layouter: &mut impl midnight_proofs::circuit::Layouter<F>,
    ) -> Result<(), midnight_proofs::plonk::Error> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use midnight_curves::Fq as BlsScalar;

    use super::super::PilarChip;
    use crate::{
        field::AssignedNative,
        instructions::{arithmetic, assertions, equality, zero},
    };

    macro_rules! test {
        ($mod:ident, $op:ident) => {
            #[test]
            fn $op() {
                $mod::tests::$op::<BlsScalar, AssignedNative<BlsScalar>, PilarChip<BlsScalar>>(
                    "pilar_chip",
                );
            }
        };
    }

    test!(assertions, test_assertions);

    test!(arithmetic, test_add);
    test!(arithmetic, test_sub);
    test!(arithmetic, test_mul);
    test!(arithmetic, test_div);
    test!(arithmetic, test_neg);
    test!(arithmetic, test_inv);
    test!(arithmetic, test_pow);
    test!(arithmetic, test_linear_combination);
    test!(arithmetic, test_add_and_mul);

    test!(equality, test_is_equal);

    test!(zero, test_zero_assertions);
    test!(zero, test_is_zero);
}
