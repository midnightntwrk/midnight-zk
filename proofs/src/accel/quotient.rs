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

//! The quotient job: everything an accelerator needs to compute the quotient
//! polynomial `h(X)` of one proof, with the constraint system's evaluators
//! lowered to per-row programs.
//!
//! Each program is the proving key's `FlatGraphEvaluator` lowered to a
//! [`DeviceProgram`]: the same operations in the same order, with only the
//! storage of intermediate values renamed. [`QuotientJob::numerator_reference`]
//! and [`QuotientJob::divide_reference`] interpret a job on the CPU; tests
//! check them against the stock prover.

use ff::PrimeField;

use crate::{
    plonk::{
        Any, Expression, ProvingKey,
        evaluation::{FlatGraphEvaluator, FlatOpKind},
        traces::ProverTrace,
    },
    poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme},
};

/// Operand tag of a uniform value: `DeviceProgram::uniforms[index]`.
pub const TAG_UNIFORM: u32 = 0;
/// Operand tag of a column read: `DeviceProgram::reads[index]`, read at the
/// current row.
pub const TAG_READ: u32 = 1;
/// Operand tag of a scratch slot of the current row.
pub const TAG_SLOT: u32 = 2;
/// The bits of an operand that hold its index; the two bits above hold the
/// tag.
pub const INDEX_MASK: u32 = (1 << 30) - 1;

/// An operand of a [`DeviceOp`]: `(tag << 30) | index`.
#[inline]
pub const fn operand(tag: u32, index: u32) -> u32 {
    (tag << 30) | index
}

/// `dst = a + b`.
pub const OP_ADD: u32 = 0;
/// `dst = a - b`.
pub const OP_SUB: u32 = 1;
/// `dst = a * b`.
pub const OP_MUL: u32 = 2;
/// `dst = a * a`.
pub const OP_SQUARE: u32 = 3;
/// `dst = a + a`.
pub const OP_DOUBLE: u32 = 4;
/// `dst = -a`.
pub const OP_NEGATE: u32 = 5;
/// `dst = a * b + c`.
pub const OP_MUL_ADD: u32 = 6;

/// Column kind of a [`DeviceRead`]: a fixed column.
pub const COLUMN_FIXED: u32 = 0;
/// Column kind of a [`DeviceRead`]: an advice column.
pub const COLUMN_ADVICE: u32 = 1;
/// Column kind of a [`DeviceRead`]: an instance column.
pub const COLUMN_INSTANCE: u32 = 2;

/// One operation of a [`DeviceProgram`]. `dst` is a slot index; `a`, `b`,
/// `c` are operands (see [`operand`]); unused operands are uniform 0.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeviceOp {
    /// One of the `OP_*` constants.
    pub kind: u32,
    /// The slot written.
    pub dst: u32,
    /// First operand.
    pub a: u32,
    /// Second operand.
    pub b: u32,
    /// Third operand (`OP_MUL_ADD` only).
    pub c: u32,
}

/// A column read of a [`DeviceProgram`]: column `column` of kind `kind` at
/// the current row rotated by `rotation` rows of the base domain.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeviceRead {
    /// One of the `COLUMN_*` constants.
    pub kind: u32,
    /// Column index within its kind.
    pub column: u32,
    /// Rotation, in rows of the base domain.
    pub rotation: i32,
}

/// A `FlatGraphEvaluator` in a form an accelerator can run per row.
///
/// The operations are the evaluator's operations, in its order, with the
/// same kinds. Constants and challenges become uniforms (the evaluator's
/// values buffer before its column reads, with the previous value 0, as the
/// prover passes it); column reads keep their order; intermediate values get
/// scratch slots by live interval, so a slot is reused once the value in it
/// is dead.
#[derive(Clone, Debug)]
pub struct DeviceProgram<F> {
    /// Values that are the same for every row.
    pub uniforms: Vec<F>,
    /// Column reads.
    pub reads: Vec<DeviceRead>,
    /// Operations.
    pub ops: Vec<DeviceOp>,
    /// Scratch slots per row.
    pub nslots: u32,
    /// Operands of the program's outputs after the last operation.
    pub outputs: Vec<u32>,
}

/// Number of named slots after the constants in a flat evaluator's buffer.
const NUM_CHALLENGE_SLOTS: usize = 5;

impl<F: PrimeField> DeviceProgram<F> {
    /// Lowers `flat` with outputs at the buffer indices `outputs`. The
    /// uniforms take `beta`, `theta`, `trash_challenge` and `y`. `None` when
    /// the evaluator has a shape this lowering does not take (the job then
    /// declines).
    pub(crate) fn lower(
        flat: &FlatGraphEvaluator<F>,
        outputs: &[usize],
        beta: F,
        theta: F,
        trash_challenge: F,
        y: F,
    ) -> Option<Self> {
        let nconst = flat.constants.len();
        let read_off = nconst + NUM_CHALLENGE_SLOTS;
        if flat.beta_idx as usize != nconst
            || flat.theta_idx as usize != nconst + 1
            || flat.trash_challenge_idx as usize != nconst + 2
            || flat.y_idx as usize != nconst + 3
            || flat.previous_value_idx as usize != nconst + 4
        {
            return None;
        }
        let mut reads = Vec::with_capacity(flat.column_reads.len());
        for (j, cr) in flat.column_reads.iter().enumerate() {
            if cr.dst as usize != read_off + j {
                return None;
            }
            reads.push(DeviceRead {
                kind: cr.col_type as u32,
                column: cr.col_idx as u32,
                rotation: *flat.rotations.get(cr.rot_idx as usize)?,
            });
        }
        let var_off = read_off + reads.len();
        if flat.values_len < var_off {
            return None;
        }
        let nvars = flat.values_len - var_off;

        // The operands an op reads, as buffer indices.
        let reads_of = |op: &crate::plonk::evaluation::FlatOp| -> Vec<u32> {
            match op.kind {
                FlatOpKind::Add | FlatOpKind::Sub | FlatOpKind::Mul => vec![op.a, op.b],
                FlatOpKind::Square | FlatOpKind::Double | FlatOpKind::Negate => vec![op.a],
                FlatOpKind::MulAdd => vec![op.a, op.b, op.c],
            }
        };

        // Live intervals of the intermediate values: [first write, last use].
        const NONE: usize = usize::MAX;
        let mut first = vec![NONE; nvars];
        let mut end = vec![0usize; nvars];
        for (p, op) in flat.ops.iter().enumerate() {
            for i in reads_of(op) {
                let i = i as usize;
                if i >= flat.values_len {
                    return None;
                }
                if i >= var_off {
                    let v = i - var_off;
                    // A read before any write would see the previous row's
                    // value in the flat evaluator: not taken.
                    if first[v] == NONE || first[v] > p {
                        return None;
                    }
                    end[v] = end[v].max(p);
                }
            }
            let d = op.dst as usize;
            if d < var_off || d >= flat.values_len {
                return None;
            }
            let v = d - var_off;
            if first[v] == NONE {
                first[v] = p;
            }
            end[v] = end[v].max(p);
        }
        for &o in outputs {
            if o >= flat.values_len {
                return None;
            }
            if o >= var_off {
                let v = o - var_off;
                if first[v] == NONE {
                    return None;
                }
                end[v] = usize::MAX;
            }
        }

        // Slots by interval. At op p a new value may take the slot of a
        // value whose last use is p (operands are read before the write).
        let mut slot = vec![u32::MAX; nvars];
        let mut free: Vec<u32> = Vec::new();
        let mut live: Vec<usize> = Vec::new();
        let mut nslots = 0u32;
        let mut ops = Vec::with_capacity(flat.ops.len());
        let map = |i: u32, slot: &[u32]| -> u32 {
            let i = i as usize;
            if i < read_off {
                operand(TAG_UNIFORM, i as u32)
            } else if i < var_off {
                operand(TAG_READ, (i - read_off) as u32)
            } else {
                operand(TAG_SLOT, slot[i - var_off])
            }
        };
        for (p, op) in flat.ops.iter().enumerate() {
            let v = op.dst as usize - var_off;
            if first[v] == p {
                live.retain(|&w| {
                    if end[w] < p || (end[w] == p && w != v) {
                        free.push(slot[w]);
                        false
                    } else {
                        true
                    }
                });
                free.sort_unstable_by(|a, b| b.cmp(a));
                slot[v] = free.pop().unwrap_or_else(|| {
                    nslots += 1;
                    nslots - 1
                });
                live.push(v);
            }
            let u0 = operand(TAG_UNIFORM, 0);
            let (kind, a, b, c) = match op.kind {
                FlatOpKind::Add => (OP_ADD, map(op.a, &slot), map(op.b, &slot), u0),
                FlatOpKind::Sub => (OP_SUB, map(op.a, &slot), map(op.b, &slot), u0),
                FlatOpKind::Mul => (OP_MUL, map(op.a, &slot), map(op.b, &slot), u0),
                FlatOpKind::Square => (OP_SQUARE, map(op.a, &slot), u0, u0),
                FlatOpKind::Double => (OP_DOUBLE, map(op.a, &slot), u0, u0),
                FlatOpKind::Negate => (OP_NEGATE, map(op.a, &slot), u0, u0),
                FlatOpKind::MulAdd => (
                    OP_MUL_ADD,
                    map(op.a, &slot),
                    map(op.b, &slot),
                    map(op.c, &slot),
                ),
            };
            ops.push(DeviceOp {
                kind,
                dst: slot[v],
                a,
                b,
                c,
            });
        }
        if nslots > INDEX_MASK || reads.len() > INDEX_MASK as usize {
            return None;
        }
        let outputs = outputs.iter().map(|&o| map(o as u32, &slot)).collect();

        let mut uniforms = flat.constants.clone();
        uniforms.extend([beta, theta, trash_challenge, y, F::ZERO]);
        Some(DeviceProgram {
            uniforms,
            reads,
            ops,
            nslots,
            outputs,
        })
    }

    /// Runs the program for one row: `read(r)` gives the value of the column
    /// read `r`; `slots` holds at least `nslots` values; the outputs are
    /// written to `out`.
    pub fn eval(&self, read: impl Fn(&DeviceRead) -> F, slots: &mut [F], out: &mut [F]) {
        let get = |o: u32, slots: &[F]| -> F {
            let i = (o & INDEX_MASK) as usize;
            match o >> 30 {
                TAG_UNIFORM => self.uniforms[i],
                TAG_READ => read(&self.reads[i]),
                _ => slots[i],
            }
        };
        for op in &self.ops {
            let a = get(op.a, slots);
            let v = match op.kind {
                OP_ADD => a + get(op.b, slots),
                OP_SUB => a - get(op.b, slots),
                OP_MUL => a * get(op.b, slots),
                OP_SQUARE => a.square(),
                OP_DOUBLE => a.double(),
                OP_NEGATE => -a,
                _ => a * get(op.b, slots) + get(op.c, slots),
            };
            slots[op.dst as usize] = v;
        }
        for (o, d) in self.outputs.iter().zip(out.iter_mut()) {
            *d = get(*o, slots);
        }
    }
}

// ------------------------------------------------------------------ the job

/// The permutation part of a [`QuotientJob`].
#[derive(Clone)]
pub struct PermutationJob<'a, F> {
    /// Columns per set (`cs.degree() - 2`).
    pub chunk_len: u32,
    /// The permuted columns: (`COLUMN_*` kind, index).
    pub columns: Vec<(u32, u32)>,
    /// The permutation polynomials of the key, extended cosets, one per
    /// column.
    pub sigma: Vec<&'a [F]>,
    /// The accumulator of each set, coefficients (`2^k`).
    pub products: Vec<&'a [F]>,
    /// The rotation of the last active row, `-(blinding_factors + 1)`.
    pub last_rotation: i32,
}

/// One flattened lookup argument (LogUp) of a [`QuotientJob`].
#[derive(Clone)]
pub struct LookupJob<'a, F> {
    /// The aggregator, coefficients.
    pub aggregator: &'a [F],
    /// The multiplicities, coefficients.
    pub multiplicities: &'a [F],
    /// One helper per input chunk, coefficients.
    pub helpers: Vec<&'a [F]>,
    /// One program per input chunk, with the outputs (sum of partial
    /// products, product, table, selector). Table and selector are taken
    /// from the first chunk.
    pub programs: Vec<DeviceProgram<F>>,
}

/// One trash argument of a [`QuotientJob`].
#[derive(Clone)]
pub struct TrashJob<'a, F> {
    /// The trash polynomial, coefficients.
    pub trash: &'a [F],
    /// The fixed column of the selector.
    pub selector_column: u32,
    /// The compressed constraints, one output.
    pub program: DeviceProgram<F>,
}

/// The division of the numerator by `t(X) = X^n - 1` on the extended coset
/// and the inverse transform of `EvaluationDomain::extended_to_coeff`:
/// `h[i] = nu[i] * t_inv[i mod t_inv.len()]`; the inverse FFT of size
/// `2^ext_k` at `omega_inv`, each value times `divisor`; then
/// `h[i] *= zeta_out[(i mod 3) - 1]` for `i mod 3 != 0`; then the first `len`
/// coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuotientDivide<F> {
    /// `1 / t(zeta * extended_omega^i)` for `i < 2^(ext_k - k)`.
    pub t_inv: Vec<F>,
    /// The inverse extended root.
    pub omega_inv: F,
    /// `1 / 2^ext_k`.
    pub divisor: F,
    /// `[g_coset_inv, g_coset]`.
    pub zeta_out: [F; 2],
    /// `(n - 1) * quotient_poly_degree`.
    pub len: usize,
}

/// The `Debug` of the job types prints shapes only: the polynomials of a
/// proof are witness data and never reach a log.
struct Len(usize);

impl std::fmt::Debug for Len {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{} values>", self.0)
    }
}

fn lens<T: AsRef<[U]>, U>(v: &[T]) -> Vec<Len> {
    v.iter().map(|p| Len(p.as_ref().len())).collect()
}

impl<F> std::fmt::Debug for PermutationJob<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PermutationJob")
            .field("chunk_len", &self.chunk_len)
            .field("columns", &self.columns)
            .field("sigma", &lens(&self.sigma))
            .field("products", &lens(&self.products))
            .field("last_rotation", &self.last_rotation)
            .finish()
    }
}

impl<F> std::fmt::Debug for LookupJob<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LookupJob")
            .field("aggregator", &Len(self.aggregator.len()))
            .field("multiplicities", &Len(self.multiplicities.len()))
            .field("helpers", &lens(&self.helpers))
            .field("programs", &self.programs.len())
            .finish()
    }
}

impl<F> std::fmt::Debug for TrashJob<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TrashJob")
            .field("trash", &Len(self.trash.len()))
            .field("selector_column", &self.selector_column)
            .finish_non_exhaustive()
    }
}

impl<F> std::fmt::Debug for QuotientJob<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("QuotientJob")
            .field("k", &self.k)
            .field("ext_k", &self.ext_k)
            .field("advice", &lens(&self.advice))
            .field("instance", &lens(&self.instance))
            .field("fixed", &self.fixed.iter().filter(|p| p.is_some()).count())
            .field("gates_ops", &self.gates.ops.len())
            .field("permutation", &self.permutation)
            .field("lookups", &self.lookups)
            .field("trash", &self.trash)
            .field("len", &self.divide.len)
            .finish_non_exhaustive()
    }
}

/// The quotient of one proof. Polynomials of the proof are given in
/// coefficient form (`2^k` values); the accelerator computes their extended
/// cosets. Polynomials of the proving key are given as extended cosets
/// (`2^ext_k` values).
///
/// The numerator at row `i` of the extended coset is the chain of the stock
/// evaluator: the gates program; the permutation terms; for each lookup the
/// LogUp terms; for each trash argument its term; each step
/// `value = value * y + term`.
#[derive(Clone)]
pub struct QuotientJob<'a, F> {
    /// log2 of the domain.
    pub k: u32,
    /// log2 of the extended domain.
    pub ext_k: u32,
    /// `[g_coset, g_coset_inv]`: the factors into the coset.
    pub zeta: [F; 2],
    /// The extended root.
    pub extended_omega: F,
    /// The advice columns, coefficients.
    pub advice: Vec<&'a [F]>,
    /// The instance columns, coefficients.
    pub instance: Vec<&'a [F]>,
    /// The fixed columns the job reads, extended cosets; `None` for a column
    /// it does not read.
    pub fixed: Vec<Option<&'a [F]>>,
    /// `l_0`, `l_last`, `l_active_row`, extended cosets.
    pub l0: &'a [F],
    /// See `l0`.
    pub l_last: &'a [F],
    /// See `l0`.
    pub l_active: &'a [F],
    /// Challenge `y`.
    pub y: F,
    /// Challenge `beta`.
    pub beta: F,
    /// Challenge `gamma`.
    pub gamma: F,
    /// `beta * g_coset`.
    pub delta_start: F,
    /// `F::DELTA`.
    pub delta: F,
    /// The custom gates, one output.
    pub gates: DeviceProgram<F>,
    /// The permutation argument, if it has columns.
    pub permutation: Option<PermutationJob<'a, F>>,
    /// The flattened lookup arguments, in the prover's order.
    pub lookups: Vec<LookupJob<'a, F>>,
    /// The trash arguments, in the prover's order.
    pub trash: Vec<TrashJob<'a, F>>,
    /// Division and inverse transform.
    pub divide: QuotientDivide<F>,
}

impl<F: PrimeField> QuotientJob<'_, F> {
    /// The scratch slots one row needs: the largest program.
    pub fn nslots(&self) -> u32 {
        std::iter::once(&self.gates)
            .chain(self.lookups.iter().flat_map(|l| l.programs.iter()))
            .chain(self.trash.iter().map(|t| &t.program))
            .map(|p| p.nslots)
            .max()
            .unwrap_or(0)
    }

    /// The polynomials of the proof the job transforms to the extended
    /// coset: advice, instance, permutation accumulators, then per lookup
    /// the aggregator, the multiplicities and the helpers, then the trash
    /// polynomials.
    pub fn proof_polys(&self) -> Vec<&[F]> {
        let mut v: Vec<&[F]> = Vec::new();
        v.extend(self.advice.iter().copied());
        v.extend(self.instance.iter().copied());
        if let Some(p) = &self.permutation {
            v.extend(p.products.iter().copied());
        }
        for l in &self.lookups {
            v.push(l.aggregator);
            v.push(l.multiplicities);
            v.extend(l.helpers.iter().copied());
        }
        v.extend(self.trash.iter().map(|t| t.trash));
        v
    }

    /// The numerator `nu` on the extended coset, on the CPU, by the job's own
    /// definition: the reference for accelerators, and (in tests) the proof
    /// that the job equals the stock evaluator.
    #[allow(clippy::type_complexity)]
    pub fn numerator_reference(&self) -> Vec<F> {
        let n = 1usize << self.ext_k;
        let log_scale = self.ext_k - self.k;
        let coset = |c: &[F]| -> Vec<F> {
            let mut a = vec![F::ZERO; n];
            a[..c.len()].copy_from_slice(c);
            for (i, x) in a[..c.len()].iter_mut().enumerate() {
                match i % 3 {
                    1 => *x *= self.zeta[0],
                    2 => *x *= self.zeta[1],
                    _ => {}
                }
            }
            midnight_curves::fft::best_fft(&mut a, self.extended_omega, self.ext_k);
            a
        };
        let advice: Vec<Vec<F>> = self.advice.iter().map(|c| coset(c)).collect();
        let instance: Vec<Vec<F>> = self.instance.iter().map(|c| coset(c)).collect();
        let products: Vec<Vec<F>> = self
            .permutation
            .iter()
            .flat_map(|p| p.products.iter())
            .map(|c| coset(c))
            .collect();
        let lookups: Vec<(Vec<F>, Vec<F>, Vec<Vec<F>>)> = self
            .lookups
            .iter()
            .map(|l| {
                (
                    coset(l.aggregator),
                    coset(l.multiplicities),
                    l.helpers.iter().map(|h| coset(h)).collect(),
                )
            })
            .collect();
        let trash: Vec<Vec<F>> = self.trash.iter().map(|t| coset(t.trash)).collect();

        let rot = |idx: usize, r: i32| -> usize {
            idx.wrapping_add(((r as isize) << log_scale) as usize) & (n - 1)
        };
        let col = |kind: u32, c: u32, i: usize| -> F {
            match kind {
                COLUMN_FIXED => self.fixed[c as usize].expect("a fixed column the job reads")[i],
                COLUMN_ADVICE => advice[c as usize][i],
                _ => instance[c as usize][i],
            }
        };
        let mut slots = vec![F::ZERO; self.nslots() as usize];
        let mut out = vec![F::ZERO; 4];
        let mut omega_i = F::ONE;
        let mut values = vec![F::ZERO; n];
        for (idx, value) in values.iter_mut().enumerate() {
            let read = |r: &DeviceRead| col(r.kind, r.column, rot(idx, r.rotation));
            self.gates.eval(read, &mut slots, &mut out);
            let mut v = out[0];
            let (l0, l_last, l_active) = (self.l0[idx], self.l_last[idx], self.l_active[idx]);
            if let Some(p) = &self.permutation {
                let (r_next, r_last) = (rot(idx, 1), rot(idx, p.last_rotation));
                let first = &products[0];
                let last = &products[products.len() - 1];
                v = v * self.y + (F::ONE - first[idx]) * l0;
                v = v * self.y + (last[idx] * last[idx] - last[idx]) * l_last;
                for s in 1..products.len() {
                    v = v * self.y + (products[s][idx] - products[s - 1][r_last]) * l0;
                }
                let mut current_delta = self.delta_start * omega_i;
                for (s, z) in products.iter().enumerate() {
                    let lo = s * p.chunk_len as usize;
                    let hi = (lo + p.chunk_len as usize).min(p.columns.len());
                    let mut left = z[r_next];
                    for c in lo..hi {
                        let (kd, ci) = p.columns[c];
                        left *= col(kd, ci, idx) + self.beta * p.sigma[c][idx] + self.gamma;
                    }
                    let mut right = z[idx];
                    for c in lo..hi {
                        let (kd, ci) = p.columns[c];
                        right *= col(kd, ci, idx) + current_delta + self.gamma;
                        current_delta *= self.delta;
                    }
                    v = v * self.y + (left - right) * l_active;
                }
            }
            for (l, (agg, mult, helpers)) in self.lookups.iter().zip(&lookups) {
                v = v * self.y + agg[idx] * (l0 + l_last);
                let (mut sum_helpers, mut table, mut selector) = (F::ZERO, F::ZERO, F::ZERO);
                for (fi, prog) in l.programs.iter().enumerate() {
                    prog.eval(read, &mut slots, &mut out);
                    if fi == 0 {
                        table = out[2];
                        selector = out[3];
                    }
                    v = v * self.y + helpers[fi][idx] * out[1] - out[0];
                    sum_helpers += helpers[fi][idx];
                }
                let r_next = rot(idx, 1);
                v = v * self.y
                    + l_active
                        * ((agg[r_next] - agg[idx] - selector * sum_helpers) * table + mult[idx]);
            }
            for (t, tc) in self.trash.iter().zip(&trash) {
                t.program.eval(read, &mut slots, &mut out);
                let q = col(COLUMN_FIXED, t.selector_column, idx);
                v = v * self.y + (out[0] - (F::ONE - q) * tc[idx]);
            }
            *value = v;
            omega_i *= self.extended_omega;
        }
        values
    }

    /// [`QuotientDivide`] of a numerator on the CPU: the coefficients of
    /// `h(X)`, computed in place.
    pub fn divide_reference(&self, mut nu: Vec<F>) -> Vec<F> {
        let d = &self.divide;
        for (i, h) in nu.iter_mut().enumerate() {
            *h *= d.t_inv[i & (d.t_inv.len() - 1)];
        }
        midnight_curves::fft::best_fft(&mut nu, d.omega_inv, self.ext_k);
        for (i, h) in nu.iter_mut().enumerate() {
            *h *= d.divisor;
            match i % 3 {
                1 => *h *= d.zeta_out[0],
                2 => *h *= d.zeta_out[1],
                _ => {}
            }
        }
        nu.truncate(d.len);
        nu
    }
}

/// The fixed columns a set of programs reads.
fn mark_fixed<F>(used: &mut [bool], p: &DeviceProgram<F>) {
    for r in &p.reads {
        if r.kind == COLUMN_FIXED
            && let Some(u) = used.get_mut(r.column as usize)
        {
            *u = true;
        }
    }
}

/// The shape of the quotient job of a proving key, for admission and
/// memory planning before a proof (see [`quotient_shape`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuotientShape {
    /// log2 of the domain.
    pub k: u32,
    /// log2 of the extended domain.
    pub ext_k: u32,
    /// Scratch slots per row (largest program).
    pub nslots: u32,
    /// Polynomials of the proof moved to the extended coset (each `2^ext_k`
    /// values on the device).
    pub proof_polys: usize,
    /// Proving-key polynomials the job reads (extended cosets).
    pub key_polys: usize,
    /// Flattened lookup arguments and their chunks.
    pub lookup_chunks: Vec<usize>,
    /// Trash arguments.
    pub trash: usize,
    /// Coefficients of `h(X)` the hook returns.
    pub len: usize,
}

/// The shape of the quotient job of `pk`, or `None` when the job would
/// decline for this key (the quotient then runs on the CPU).
pub fn quotient_shape<F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, PCS>,
) -> Option<QuotientShape> {
    let p = plan(pk, [F::ONE; 4])?;
    let cs = pk.vk.cs();
    let domain = pk.vk.get_domain();
    let nslots = std::iter::once(&p.gates)
        .chain(p.lookups.iter().flatten())
        .chain(p.trash.iter().map(|t| &t.1))
        .map(|g| g.nslots)
        .max()
        .unwrap_or(0);
    let nsets = if p.columns.is_empty() {
        0
    } else {
        cs.permutation().num_sets(cs.degree())
    };
    let lookup_chunks: Vec<usize> = p.lookups.iter().map(|l| l.len()).collect();
    let proof_polys = cs.num_advice_columns
        + cs.num_instance_columns
        + nsets
        + lookup_chunks.iter().map(|c| c + 2).sum::<usize>()
        + p.trash.len();
    Some(QuotientShape {
        k: domain.k(),
        ext_k: domain.extended_k(),
        nslots,
        proof_polys,
        key_polys: resident_key_polys(pk)?.len(),
        lookup_chunks,
        trash: p.trash.len(),
        len: (domain.n as usize - 1) * domain.get_quotient_poly_degree(),
    })
}

struct Plan<F> {
    gates: DeviceProgram<F>,
    lookups: Vec<Vec<DeviceProgram<F>>>,
    trash: Vec<(u32, DeviceProgram<F>)>,
    columns: Vec<(u32, u32)>,
    used: Vec<bool>,
}

fn plan<F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, CS>,
    challenges: [F; 4],
) -> Option<Plan<F>> {
    let [beta, theta, trash_challenge, y] = challenges;
    let ev = &pk.ev;
    let cs = pk.vk.cs();
    let lower = |flat: &FlatGraphEvaluator<F>, outputs: &[usize]| {
        DeviceProgram::lower(flat, outputs, beta, theta, trash_challenge, y)
    };
    let gates = lower(
        &ev.custom_gates_flat,
        &[ev.custom_gates_flat.result_idx as usize],
    )?;
    if ev.lookups.len() != ev.lookups_flat.len() || ev.lookups.len() != cs.lookups.len() {
        return None;
    }
    let mut lookups = Vec::with_capacity(ev.lookups.len());
    for (batch, flats) in ev.lookups.iter().zip(&ev.lookups_flat) {
        if batch.len() != flats.len() || batch.is_empty() {
            return None;
        }
        let mut progs = Vec::with_capacity(batch.len());
        for (le, flat) in batch.iter().zip(flats) {
            let idx = |vs| match vs {
                crate::plonk::evaluation::ValueSource::Intermediate(_) => {
                    Some(flat.resolve_idx(vs))
                }
                _ => None,
            };
            let outs = [
                idx(le.sum_partial_products)?,
                idx(le.product)?,
                idx(le.table)?,
                idx(le.selector)?,
            ];
            progs.push(lower(flat, &outs)?);
        }
        lookups.push(progs);
    }
    if ev.trashcans_flat.len() != cs.trashcans.len() {
        return None;
    }
    let mut trash = Vec::with_capacity(cs.trashcans.len());
    for (arg, flat) in cs.trashcans.iter().zip(&ev.trashcans_flat) {
        let Expression::Fixed(q) = arg.selector() else {
            return None;
        };
        trash.push((
            q.column_index() as u32,
            lower(flat, &[flat.result_idx as usize])?,
        ));
    }
    let columns: Vec<(u32, u32)> = cs
        .permutation
        .columns
        .iter()
        .map(|c| {
            let kind = match c.column_type() {
                Any::Fixed => COLUMN_FIXED,
                Any::Advice => COLUMN_ADVICE,
                Any::Instance => COLUMN_INSTANCE,
            };
            (kind, c.index() as u32)
        })
        .collect();
    let mut used = vec![false; pk.fixed_cosets.len()];
    mark_fixed(&mut used, &gates);
    for p in lookups.iter().flatten() {
        mark_fixed(&mut used, p);
    }
    for (sel, p) in &trash {
        mark_fixed(&mut used, p);
        *used.get_mut(*sel as usize)? = true;
    }
    for (kind, c) in &columns {
        if *kind == COLUMN_FIXED {
            *used.get_mut(*c as usize)? = true;
        }
    }
    Some(Plan {
        gates,
        lookups,
        trash,
        columns,
        used,
    })
}

/// The proving-key polynomials the quotient job of `pk` reads: the fixed
/// cosets it reads, then the permutation cosets, then `l_0`, `l_last` and
/// `l_active_row`. An accelerator can keep copies of them across proofs.
/// Public key material only. `None` when the quotient job declines for this
/// key.
pub fn resident_key_polys<F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, PCS>,
) -> Option<Vec<&[F]>> {
    let z = F::ZERO;
    let p = plan(pk, [z, z, z, z])?;
    let mut v: Vec<&[F]> = Vec::new();
    for (c, u) in pk.fixed_cosets.iter().zip(&p.used) {
        if *u {
            v.push(&c.values);
        }
    }
    if !p.columns.is_empty() {
        v.extend(pk.sigmas.cosets.iter().map(|c| c.values.as_slice()));
    }
    v.extend([&pk.l0, &pk.l_last, &pk.l_active_row].map(|c| c.values.as_slice()));
    Some(v)
}

/// Builds the quotient job of `pk` and `trace`. `None`: the job declines.
pub(crate) fn job<'a, F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    pk: &'a ProvingKey<F, PCS>,
    trace: &'a ProverTrace<'_, F>,
) -> Option<QuotientJob<'a, F>> {
    let cs = pk.vk.cs();
    let domain = pk.vk.get_domain();
    let Plan {
        gates,
        lookups: lprogs,
        trash: tprogs,
        columns,
        used,
    } = plan(
        pk,
        [trace.beta, trace.theta, trace.trash_challenge, trace.y],
    )?;

    let n = domain.n as usize;
    fn coeffs<F>(c: &crate::poly::Polynomial<F, crate::poly::Coeff>, n: usize) -> Option<&[F]> {
        (c.values.len() == n).then_some(&c.values[..])
    }
    let phase1 = &trace.phase1_committed;
    let phase2 = &trace.phase2_committed;
    let mut advice = Vec::with_capacity(cs.num_advice_columns);
    for p in phase1.polys_of(&cs.advice_labels()) {
        advice.push(coeffs(p, n)?);
    }
    let mut instance = Vec::with_capacity(trace.instance_polys.len());
    for p in &trace.instance_polys {
        instance.push(coeffs(p, n)?);
    }
    let ext_len = domain.extended_len();
    let fixed: Vec<Option<&[F]>> = pk
        .fixed_cosets
        .iter()
        .zip(&used)
        .map(|(c, u)| u.then_some(&c.values[..]))
        .collect();
    if fixed.iter().flatten().any(|c| c.len() != ext_len) {
        return None;
    }

    let permutation = if columns.is_empty() {
        None
    } else {
        let nsets = cs.permutation().num_sets(cs.degree());
        let chunk_len = cs.degree() - 2;
        if nsets == 0 || pk.sigmas.cosets.len() != columns.len() {
            return None;
        }
        let mut products = Vec::with_capacity(nsets);
        for i in 0..nsets {
            products.push(coeffs(
                phase2.poly(&PolynomialLabel::PermutationAccumulator(i))?,
                n,
            )?);
        }
        Some(PermutationJob {
            chunk_len: chunk_len as u32,
            columns,
            sigma: pk.sigmas.cosets.iter().map(|c| &c.values[..]).collect(),
            products,
            last_rotation: -((cs.blinding_factors() + 1) as i32),
        })
    };

    let mut lookups = Vec::with_capacity(lprogs.len());
    for (i, (programs, arg)) in lprogs.into_iter().zip(&cs.lookups).enumerate() {
        let chunks = arg.chunk_by_degree(cs.degree()).input_expression_chunks.len();
        if chunks != programs.len() {
            return None;
        }
        let mut helpers = Vec::with_capacity(chunks);
        for j in 0..chunks {
            helpers.push(coeffs(
                phase2.poly(&PolynomialLabel::LogupHelper(i, j))?,
                n,
            )?);
        }
        lookups.push(LookupJob {
            aggregator: coeffs(phase2.poly(&PolynomialLabel::LogupAggregator(i))?, n)?,
            multiplicities: coeffs(phase1.poly(&PolynomialLabel::LogupMultiplicities(i))?, n)?,
            helpers,
            programs,
        });
    }
    let mut trash = Vec::with_capacity(tprogs.len());
    for (i, (selector_column, program)) in tprogs.into_iter().enumerate() {
        trash.push(TrashJob {
            trash: coeffs(phase2.poly(&PolynomialLabel::Trash(i))?, n)?,
            selector_column,
            program,
        });
    }
    let key_polys = [&pk.l0, &pk.l_last, &pk.l_active_row];
    if key_polys.iter().any(|p| p.values.len() != ext_len)
        || pk.sigmas.cosets.iter().any(|p| p.values.len() != ext_len)
    {
        return None;
    }
    Some(QuotientJob {
        k: domain.k(),
        ext_k: domain.extended_k(),
        zeta: domain.coset_zetas(),
        extended_omega: domain.get_extended_omega(),
        advice,
        instance,
        fixed,
        l0: &pk.l0.values,
        l_last: &pk.l_last.values,
        l_active: &pk.l_active_row.values,
        y: trace.y,
        beta: trace.beta,
        gamma: trace.gamma,
        delta_start: trace.beta * domain.g_coset,
        delta: F::DELTA,
        gates,
        permutation,
        lookups,
        trash,
        divide: domain.quotient_divide(),
    })
}
