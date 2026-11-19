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

//! Accelerator hooks of the prover (cargo feature `gpu`).
//!
//! A process can install one set of [`GpuHooks`] with [`install`]. The prover
//! offers these operations to the hooks before it runs its own code:
//!
//! - the G1 MSM of the KZG commitments and of
//!   [`msm_specific`](crate::poly::kzg::msm::msm_specific) over BLS12-381
//!   ([`GpuHooks::msm_g1`]);
//! - the forward and inverse FFT of
//!   [`EvaluationDomain`](crate::poly::EvaluationDomain) over the BLS12-381
//!   scalar field on the base domain ([`GpuHooks::fft`], [`GpuHooks::ifft`]);
//!   extended-domain transforms are not offered: the extended cosets exist only
//!   inside the quotient hook, so no extended vector crosses back;
//! - the quotient polynomial `h(X)`: its numerator, the division by `X^n - 1`
//!   and the inverse transform of the extended domain ([`GpuHooks::quotient`]),
//!   described by a [`QuotientJob`].
//!
//! Each hook either returns the exact value of the stock code or declines.
//! When a hook declines, the stock code runs on the unchanged input. With no
//! hooks installed the prover runs only the stock code, so its proofs are
//! the proofs of a build without the feature. The hooks add, remove or move
//! no random draw and no transcript operation.
//!
//! Only the BLS12-381 scalar field [`Fq`] and its G1 group reach a hook. The
//! hook layer is pure Rust; an accelerator crate (for example a CUDA backend)
//! provides the functions.
//!
//! The quotient job is built from the evaluator of the proving key: each
//! graph is the key's `FlatGraphEvaluator` lowered to a [`DeviceProgram`],
//! which runs the same operations in the same order and only renames the
//! storage of intermediate values. [`QuotientJob::numerator_reference`] is a
//! CPU interpreter of the job, tested against the stock evaluator.
#![allow(unsafe_code)]

use std::{
    any::TypeId,
    sync::{
        OnceLock,
        atomic::{AtomicU64, Ordering},
    },
};

use ff::PrimeField;
use midnight_curves::{Fq, G1Affine, G1Projective};

use crate::{
    plonk::{
        Any, Expression, ProvingKey,
        evaluation::{FlatGraphEvaluator, FlatOpKind},
        traces::ProverTrace,
    },
    poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme},
};

pub mod abi;
pub mod adapter;
pub mod batch;
pub mod erasing;

use adapter::{G1AffineLimbs, G1JacobianLimbs, Scalar};
use erasing::ErasingVec;

/// The MSM hook: `sum scalars[i] * bases[i]`.
pub type MsmFn = fn(&[Scalar], &[G1AffineLimbs]) -> Option<G1JacobianLimbs>;
/// The FFT hook: `(a, omega, log_n)`.
pub type FftFn = fn(&mut [Scalar], Scalar, u32) -> bool;
/// The inverse FFT hook: `(a, omega_inv, log_n, divisor)`.
pub type IfftFn = fn(&mut [Scalar], Scalar, u32, Scalar) -> bool;
/// The quotient hook: `(job, out)`, `job` a [`abi::QuotientJobAbi`].
pub type QuotientFn = unsafe fn(*const std::ffi::c_void, &mut [Scalar]) -> bool;

/// The accelerator functions. Each one is optional, and each one may decline.
/// The types are the plain limb arrays of [`adapter`].
#[derive(Default, Clone, Copy, Debug)]
pub struct GpuHooks {
    /// `sum scalars[i] * bases[i]` (equal lengths). `None`: declined.
    pub msm_g1: Option<MsmFn>,
    /// The FFT of `a` (length `2^log_n`) at the root `omega`, in natural
    /// order, in place. `false`: declined, and `a` is unchanged.
    pub fft: Option<FftFn>,
    /// The FFT of `a` at `omega_inv`, then each element times `divisor`, in
    /// place. `false`: declined, and `a` is unchanged.
    pub ifft: Option<IfftFn>,
    /// The quotient `h(X)` of a job ([`abi::QuotientJobAbi`]): the first
    /// `out.len()` coefficients of `extended_to_coeff(
    /// divide_by_vanishing_poly(nu))`. `false`: declined, and the prover
    /// computes the quotient on the CPU.
    ///
    /// # Safety
    /// The prover passes a valid job whose pointers live for the call.
    pub quotient: Option<QuotientFn>,
}

static HOOKS: OnceLock<GpuHooks> = OnceLock::new();

/// Installs the hooks of this process. Returns `false`, and changes nothing,
/// when hooks are installed already.
pub fn install(hooks: GpuHooks) -> bool {
    HOOKS.set(hooks).is_ok()
}

/// The hooks for this caller, if any: the scoped hooks on a batch pool
/// worker ([`batch`]), else the installed hooks. While a batch runs, a
/// caller outside its pool gets `None` (every hook declines, the stock
/// code runs), so no ordinary device call interleaves with the batch.
pub fn hooks() -> Option<&'static GpuHooks> {
    if test_switches::suspended() {
        return None;
    }
    match scoped_hooks() {
        Some(scoped) => scoped,
        None if batch_active() => None,
        None => HOOKS.get(),
    }
}

std::thread_local! {
    /// The scoped hooks of a batch pool worker (see [`batch`]): the outer
    /// `None` inherits the installed hooks; `Some(None)` is a job admitted
    /// to the CPU only.
    static SCOPED: std::cell::Cell<Option<Option<&'static GpuHooks>>> =
        const { std::cell::Cell::new(None) };
}

/// The scoped hooks of this thread, if it is a batch pool worker.
pub(crate) fn scoped_hooks() -> Option<Option<&'static GpuHooks>> {
    SCOPED.get()
}

/// Sets the scoped hooks of this thread ([`batch`] pool workers only).
pub(crate) fn set_scoped_hooks(hooks: Option<Option<&'static GpuHooks>>) {
    SCOPED.set(hooks);
}

static BATCH_ACTIVE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Whether a batch is running in this process (see [`batch`]).
pub(crate) fn batch_active() -> bool {
    BATCH_ACTIVE.load(std::sync::atomic::Ordering::Acquire)
}

/// Marks a batch running or finished ([`batch`] only, under its lock).
pub(crate) fn set_batch_active(active: bool) {
    BATCH_ACTIVE.store(active, std::sync::atomic::Ordering::Release);
}

#[inline]
fn is_fq<F: 'static>() -> bool {
    TypeId::of::<F>() == TypeId::of::<Fq>()
}

#[inline]
fn as_fq_mut<F: 'static>(a: &mut [F]) -> &mut [Fq] {
    assert!(is_fq::<F>());
    // SAFETY: `F` is `Fq` (checked above), so the slices have the same type.
    unsafe { &mut *(a as *mut [F] as *mut [Fq]) }
}

#[inline]
fn limb<F: 'static + Copy>(a: F) -> Scalar {
    assert!(is_fq::<F>());
    // SAFETY: `F` is `Fq` (checked above).
    adapter::scalar(unsafe { std::mem::transmute_copy::<F, Fq>(&a) })
}

/// The MSM hook, for the KZG commitments and `msm_specific`. `None`: not
/// taken.
pub(crate) fn msm<C: 'static, S: 'static, R: 'static>(scalars: &[S], bases: &[C]) -> Option<R> {
    let f = hooks()?.msm_g1?;
    if TypeId::of::<C>() != TypeId::of::<G1Affine>()
        || TypeId::of::<S>() != TypeId::of::<Fq>()
        || TypeId::of::<R>() != TypeId::of::<G1Projective>()
    {
        return hook_decline("msm", "field-type");
    }
    if scalars.len() != bases.len() {
        return hook_decline("msm", "length-mismatch");
    }
    // SAFETY: the types are the BLS12-381 types (checked above).
    let s = unsafe { &*(scalars as *const [S] as *const [Fq]) };
    let b = unsafe { &*(bases as *const [C] as *const [G1Affine]) };
    let Some(r) = f(adapter::scalars(s), adapter::affine(b)) else {
        return hook_decline("msm", "hook");
    };
    let r = adapter::from_jacobian(r);
    // SAFETY: `R` is `G1Projective` (checked above).
    Some(unsafe { std::mem::transmute_copy::<G1Projective, R>(&r) })
}

/// The FFT hook, for the domain's transforms. `twiddles` are `[1, w, ...]`.
pub(crate) fn fft<F: 'static + Copy>(a: &mut [F], twiddles: &[F], log_n: u32) -> bool {
    let Some(f) = hooks().and_then(|h| h.fft) else {
        return false;
    };
    if !is_fq::<F>() {
        return declined_bool("fft", "field-type");
    }
    if twiddles.len() < 2 || a.len() as u64 != 1u64 << log_n {
        return declined_bool("fft", "length-mismatch");
    }
    f(adapter::scalars_mut(as_fq_mut(a)), limb(twiddles[1]), log_n) || declined_bool("fft", "hook")
}

/// The inverse FFT hook (transform at the inverse root, then scale).
pub(crate) fn ifft<F: 'static + Copy>(a: &mut [F], twiddles: &[F], log_n: u32, divisor: F) -> bool {
    let Some(f) = hooks().and_then(|h| h.ifft) else {
        return false;
    };
    if !is_fq::<F>() {
        return declined_bool("ifft", "field-type");
    }
    if twiddles.len() < 2 || a.len() as u64 != 1u64 << log_n {
        return declined_bool("ifft", "length-mismatch");
    }
    f(
        adapter::scalars_mut(as_fq_mut(a)),
        limb(twiddles[1]),
        log_n,
        limb(divisor),
    ) || declined_bool("ifft", "hook")
}

static HOOK_DECLINES: std::sync::Mutex<Vec<(&str, &str, u64)>> = std::sync::Mutex::new(Vec::new());

/// Counts a decline of an installed hook at this layer and returns `None`.
fn hook_decline<T>(class: &'static str, reason: &'static str) -> Option<T> {
    let mut v = HOOK_DECLINES.lock().unwrap_or_else(|e| e.into_inner());
    match v.iter_mut().find(|e| e.0 == class && e.1 == reason) {
        Some(e) => e.2 += 1,
        None => v.push((class, reason, 1)),
    }
    None
}

/// [`hook_decline`] for a hook that returns `bool`: counts it, `false`.
fn declined_bool(class: &'static str, reason: &'static str) -> bool {
    hook_decline::<()>(class, reason);
    false
}

/// Declines of the installed hooks since process start or the last
/// [`reset_hook_declines`], as `(class, reason, count)`. Classes: `msm`,
/// `fft`, `ifft`, `quotient`. Reasons: `field-type` (the prover's types are
/// not the BLS12-381 types), `length-mismatch` (scalars and bases, or a
/// transform length and its `log_n`), `job-shape` (the key or trace has a
/// shape the quotient job does not take), `forced` (a test switch), `hook`
/// (the hook itself declined; the accelerator counts its own reason). A call
/// with no hook installed is not counted.
pub fn hook_declines() -> Vec<(&'static str, &'static str, u64)> {
    HOOK_DECLINES.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

/// Resets [`hook_declines`] and [`quotient_declines`].
pub fn reset_hook_declines() {
    HOOK_DECLINES.lock().unwrap_or_else(|e| e.into_inner()).clear();
    QUOTIENT_DECLINES.store(0, Ordering::Relaxed);
}

// ------------------------------------------------------------------ programs

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

    /// The numerator on the CPU, by the job's own definition (a reference
    /// for accelerators and the guard that the job equals the stock
    /// evaluator). The numerator is witness-dependent, so it and every
    /// coset and scratch buffer of this reference live in an
    /// [`erasing::ErasingVec`]: fixed capacity, zeroed on drop.
    #[allow(clippy::type_complexity)]
    pub fn numerator_reference(&self) -> ErasingVec<F> {
        let n = 1usize << self.ext_k;
        let log_scale = self.ext_k - self.k;
        let coset = |c: &[F]| -> ErasingVec<F> {
            // One fixed allocation of the extended length: the
            // coefficients are copied in and the rest is already zero,
            // where a growing `Vec` would reallocate and leave an
            // unzeroed copy of the shorter buffer behind.
            let mut a = ErasingVec::zeroed(n);
            a[..c.len()].copy_from_slice(c);
            for (i, x) in a[..c.len()].iter_mut().enumerate() {
                match i % 3 {
                    1 => *x *= self.zeta[0],
                    2 => *x *= self.zeta[1],
                    _ => {}
                }
            }
            midnight_curves::fft::best_fft(a.as_mut_slice(), self.extended_omega, self.ext_k);
            a
        };
        let advice: Vec<ErasingVec<F>> = self.advice.iter().map(|c| coset(c)).collect();
        let instance: Vec<ErasingVec<F>> = self.instance.iter().map(|c| coset(c)).collect();
        let products: Vec<ErasingVec<F>> = self
            .permutation
            .iter()
            .flat_map(|p| p.products.iter())
            .map(|c| coset(c))
            .collect();
        let lookups: Vec<(ErasingVec<F>, ErasingVec<F>, Vec<ErasingVec<F>>)> = self
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
        let trash: Vec<ErasingVec<F>> = self.trash.iter().map(|t| coset(t.trash)).collect();

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
        let mut slots = ErasingVec::zeroed(self.nslots() as usize);
        let mut out = ErasingVec::zeroed(4);
        let mut omega_i = F::ONE;
        let mut values = ErasingVec::zeroed(n);
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

    /// [`QuotientDivide`] of a numerator on the CPU. The numerator is
    /// taken as an [`erasing::ErasingVec`] (a stock `Vec` is adopted
    /// without copying) and the quotient is returned in the same fixed
    /// allocation: the transform is in place and the truncation only
    /// shortens the length, so nothing reallocates.
    pub fn divide_reference(&self, nu: impl Into<ErasingVec<F>>) -> ErasingVec<F> {
        let mut nu = nu.into();
        let d = &self.divide;
        for (i, h) in nu.iter_mut().enumerate() {
            *h *= d.t_inv[i & (d.t_inv.len() - 1)];
        }
        midnight_curves::fft::best_fft(nu.as_mut_slice(), d.omega_inv, self.ext_k);
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

/// The key-dependent part of the job, from the proving key alone.
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
    /// Operations of the job's programs by kind (index `OP_*`): the node
    /// coverage of a fuzz run.
    pub op_kinds: [usize; 7],
    /// Column reads of the job's programs by kind (index `COLUMN_*`), and
    /// reads at a non-zero rotation.
    pub read_kinds: [usize; 4],
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
    let (mut op_kinds, mut read_kinds) = ([0usize; 7], [0usize; 4]);
    for g in std::iter::once(&p.gates)
        .chain(p.lookups.iter().flatten())
        .chain(p.trash.iter().map(|t| &t.1))
    {
        for op in &g.ops {
            op_kinds[op.kind as usize] += 1;
        }
        for r in &g.reads {
            read_kinds[r.kind as usize] += 1;
            read_kinds[3] += usize::from(r.rotation != 0);
        }
    }
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
        key_polys: pk.gpu_resident_polys()?.len(),
        lookup_chunks,
        trash: p.trash.len(),
        len: (domain.n as usize - 1) * domain.get_quotient_poly_degree(),
        op_kinds,
        read_kinds,
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

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> ProvingKey<F, PCS> {
    /// The proving-key polynomials the quotient job reads (feature `gpu`):
    /// the fixed cosets it reads, then the permutation cosets, then `l_0`,
    /// `l_last` and `l_active_row`. An accelerator can keep device copies
    /// of them across proofs. Public key material only. `None` when the
    /// quotient job declines for this key.
    pub fn gpu_resident_polys(&self) -> Option<Vec<&[F]>> {
        let z = F::ZERO;
        let p = plan(self, [z, z, z, z])?;
        let mut v: Vec<&[F]> = Vec::new();
        for (c, u) in self.fixed_cosets.iter().zip(&p.used) {
            if *u {
                v.push(&c.values);
            }
        }
        if !p.columns.is_empty() {
            v.extend(self.sigmas.cosets.iter().map(|c| c.values.as_slice()));
        }
        v.extend([&self.l0, &self.l_last, &self.l_active_row].map(|c| c.values.as_slice()));
        Some(v)
    }
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

/// The quotient coefficients from the accelerator, or `None` (the prover
/// then computes them on the CPU).
///
/// `stock` computes the stock quotient coefficients (check mode only).
/// The read-back buffer and, in check mode, the stock reference live in
/// an [`erasing::ErasingVec`]: fixed capacity, zeroed on drop.
pub(crate) fn quotient_coeffs<F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, PCS>,
    trace: &ProverTrace<'_, F>,
    stock: impl FnOnce() -> Vec<F>,
) -> Option<ErasingVec<F>> {
    let f = hooks()?.quotient?;
    quotient_coeffs_with(f, pk, trace, stock, test_switches::quotient_check())
}

/// [`quotient_coeffs`] with the hook and the check mode given, so a test
/// can run the real path without the process-wide install.
fn quotient_coeffs_with<F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    f: QuotientFn,
    pk: &ProvingKey<F, PCS>,
    trace: &ProverTrace<'_, F>,
    stock: impl FnOnce() -> Vec<F>,
    check: bool,
) -> Option<ErasingVec<F>> {
    let declined = |reason| {
        QUOTIENT_DECLINES.fetch_add(1, Ordering::Relaxed);
        hook_decline("quotient", reason)
    };
    if !is_fq::<F>() {
        return declined("field-type");
    }
    if test_switches::force_quotient_decline() {
        return declined("forced");
    }
    let Some(job) = job(pk, trace) else {
        return declined("job-shape");
    };
    let mut out = ErasingVec::zeroed(job.divide.len);
    // SAFETY: `F` is `Fq` (checked above), so the job types are the same.
    let job_fq = unsafe { &*(&job as *const QuotientJob<'_, F>).cast::<QuotientJob<'_, Fq>>() };
    let packed = abi::PackedJob::new(job_fq);
    // SAFETY: the packed job and the tables it points to live until the end
    // of this function.
    let ok = unsafe {
        f(
            packed.as_ptr(),
            adapter::scalars_mut(as_fq_mut(out.as_mut_slice())),
        )
    };
    drop(packed);
    if !ok {
        // `out` is dropped here: its whole capacity is zeroed by the owner.
        return hook_decline("quotient", "hook");
    }
    if check {
        // The stock reference offers no hook (the coset transforms and the
        // extended inverse transform of the quotient are never offered), so
        // no process-wide switch is needed and a concurrent proof is not
        // touched. Pass or fail only: no index, count or value of the
        // private quotient is kept.
        //
        // The stock closure hands over a stock `Vec`; adopt its
        // allocation at once, without copying, so it is zeroed on drop
        // from here on. The allocation's history inside the stock code
        // is stock behaviour and cannot be changed at this layer.
        let mut stock = ErasingVec::from_vec(stock());
        stock.truncate(job.divide.len);
        QUOTIENT_CHECKS.fetch_add(1, Ordering::Relaxed);
        if out.as_slice() != stock.as_slice() {
            QUOTIENT_CHECK_DIFFS.fetch_add(1, Ordering::Relaxed);
        }
        // The device result is not used: the owner's drop zeroes it.
        drop(out);
        return Some(stock);
    }
    Some(out)
}

static QUOTIENT_DECLINES: AtomicU64 = AtomicU64::new(0);
static QUOTIENT_CHECK_DIFFS: AtomicU64 = AtomicU64::new(0);
static QUOTIENT_CHECKS: AtomicU64 = AtomicU64::new(0);

/// Quotient jobs that declined before the hook ran, since process start or
/// the last [`reset_hook_declines`] (see [`hook_declines`] for the reasons).
pub fn quotient_declines() -> u64 {
    QUOTIENT_DECLINES.load(Ordering::Relaxed)
}

/// Quotient checks (feature `gpu-test`) that failed since process start: the
/// accelerator's quotient differed from the stock quotient. A pass or fail
/// per check; nothing about the private values is kept.
pub fn quotient_check_diffs() -> u64 {
    QUOTIENT_CHECK_DIFFS.load(Ordering::Relaxed)
}

/// Quotient checks that ran since process start: a zero
/// [`quotient_check_diffs`] is a pass only when this is not zero.
pub fn quotient_checks() -> u64 {
    QUOTIENT_CHECKS.load(Ordering::Relaxed)
}

/// Test-only switches (feature `gpu-test`). Without the feature none of them
/// exists, and the functions the prover calls are constants.
#[cfg(feature = "gpu-test")]
pub mod test_switches {
    use std::sync::atomic::{AtomicBool, Ordering};

    /// Run the prover's custom gate evaluator on supplied extended columns and
    /// lower those same gates for a quotient hook. Oracle numerator fixtures
    /// supply the columns directly, without a proving key or witness.
    #[cfg(feature = "test-fault")]
    pub fn custom_gate_numerator<F: ff::PrimeField>(
        cs: &crate::plonk::ConstraintSystem<F>,
        columns: [&[crate::poly::Polynomial<F, crate::poly::ExtendedLagrangeCoeff>]; 3],
        log_n: u32,
        log_scale: u32,
        y: F,
    ) -> (Vec<F>, super::DeviceProgram<F>) {
        let flat = crate::plonk::evaluation::Evaluator::new(cs).custom_gates_flat;
        let [fixed, advice, instance] = columns;
        let template = flat.new_values_buffer(&F::ZERO, &F::ZERO, &F::ZERO, &y);
        let mut values = vec![F::ZERO; 1 << log_n];
        flat.evaluate_chunk::<4, _>(
            &template,
            &mut values,
            0,
            fixed,
            advice,
            instance,
            log_scale,
            log_n,
        );
        let program = super::DeviceProgram::lower(
            &flat,
            &[flat.result_idx as usize],
            F::ZERO,
            F::ZERO,
            F::ZERO,
            y,
        )
        .expect("lower the custom gates of the vector");
        (values, program)
    }

    static SUSPENDED: AtomicBool = AtomicBool::new(false);
    /// When set, the quotient job declines before the hook runs.
    pub static FORCE_QUOTIENT_DECLINE: AtomicBool = AtomicBool::new(false);
    /// When set, the prover also computes the stock quotient with every hook
    /// suspended, counts the differing coefficients
    /// ([`super::quotient_check_diffs`]) and proves with the stock values.
    pub static QUOTIENT_CHECK: AtomicBool = AtomicBool::new(false);

    pub(crate) fn suspended() -> bool {
        SUSPENDED.load(Ordering::Acquire)
    }

    pub(crate) fn force_quotient_decline() -> bool {
        FORCE_QUOTIENT_DECLINE.load(Ordering::Relaxed)
    }

    pub(crate) fn quotient_check() -> bool {
        QUOTIENT_CHECK.load(Ordering::Relaxed)
    }

    /// Runs `f` with every hook suspended (process wide), then restores
    /// them, also when `f` panics.
    pub fn without_hooks<R>(f: impl FnOnce() -> R) -> R {
        struct Restore(bool);
        impl Drop for Restore {
            fn drop(&mut self) {
                SUSPENDED.store(self.0, Ordering::Release);
            }
        }
        let _r = Restore(SUSPENDED.swap(true, Ordering::AcqRel));
        f()
    }

    /// Sets the seed of the quotient limb blinding (`None`: the stock
    /// `OsRng`). A seed makes proof bytes a function of the key, the
    /// witness, the prover's RNG and this seed.
    pub fn set_quotient_blinding_seed(seed: Option<u64>) {
        crate::plonk::prover::test_blinding::set(seed)
    }

    /// A seeded random circuit (random gates, a batched LogUp lookup, a
    /// copy constraint, a trash argument) of shape `seed` at `2^k` rows,
    /// for accelerator tests.
    #[derive(Debug)]
    pub struct RandomCircuit {
        seed: u64,
        satisfied: bool,
        params: crate::poly::kzg::params::ParamsKZG<midnight_curves::Bls12>,
        pk: crate::plonk::ProvingKey<midnight_curves::Fq, crate::test_circuit::Scheme>,
    }

    impl RandomCircuit {
        /// Proves using the caller's generator and the current quotient
        /// blinding source. Concurrent jobs can share one fixed test
        /// blinding seed.
        pub fn prove_with_rng<R: rand_core::RngCore + rand_core::CryptoRng>(
            &self,
            rng: R,
        ) -> (Vec<u8>, bool) {
            super::prove_direct(&self.params, &self.pk, self.seed, self.satisfied, rng)
        }

        /// Keys for shape `seed`. Unsatisfied: the gates and the trash
        /// argument do not hold (proofs do not verify, the quotient is still
        /// computed); satisfied: proofs verify.
        pub fn new(seed: u64, satisfied: bool, k: u32) -> Self {
            let (params, pk) = crate::test_circuit::with_shape(seed, satisfied, || {
                crate::test_circuit::setup(seed, satisfied, k)
            });
            RandomCircuit {
                seed,
                satisfied,
                params,
                pk,
            }
        }

        /// The proving key of this random constraint system (KZG over
        /// BLS12-381), for accelerator tests in other crates: key
        /// registration, residency, shapes.
        pub fn pk(
            &self,
        ) -> &crate::plonk::ProvingKey<
            midnight_curves::Fq,
            crate::poly::kzg::KZGCommitmentScheme<midnight_curves::Bls12>,
        > {
            &self.pk
        }

        /// The KZG parameters the key was built with.
        pub fn params(&self) -> &crate::poly::kzg::params::ParamsKZG<midnight_curves::Bls12> {
            &self.params
        }

        /// The quotient job size of this circuit's key
        /// ([`super::quotient_shape`]).
        pub fn shape(&self) -> Option<super::QuotientShape> {
            super::quotient_shape(&self.pk)
        }

        /// A proof with every random draw seeded (the quotient blinding
        /// included) and whether it verifies.
        pub fn prove(&self) -> (Vec<u8>, bool) {
            crate::test_circuit::prove(&self.params, &self.pk, self.seed, self.satisfied)
        }
    }
}

#[cfg(not(feature = "gpu-test"))]
mod test_switches {
    #[inline(always)]
    pub(crate) fn suspended() -> bool {
        false
    }

    #[inline(always)]
    pub(crate) fn force_quotient_decline() -> bool {
        false
    }

    #[inline(always)]
    pub(crate) fn quotient_check() -> bool {
        false
    }

    #[cfg(test)]
    pub(crate) fn without_hooks<R>(f: impl FnOnce() -> R) -> R {
        f()
    }
}

/// One job of a real proof, with its randomness taken as it comes.
#[cfg(any(test, feature = "gpu-test"))]
fn prove_direct<R: rand_core::RngCore + rand_core::CryptoRng>(
    params: &crate::poly::kzg::params::ParamsKZG<midnight_curves::Bls12>,
    pk: &crate::plonk::ProvingKey<midnight_curves::Fq, crate::test_circuit::Scheme>,
    seed: u64,
    satisfied: bool,
    rng: R,
) -> (Vec<u8>, bool) {
    use crate::{
        plonk::{create_proof, prepare},
        poly::commitment::Guard,
        test_circuit::{ConfiguredCircuit, instance},
        transcript::{CircuitTranscript, Transcript},
    };
    let inst = instance(seed);
    let mut transcript = CircuitTranscript::<blake2b_simd::State>::init();
    create_proof(
        params,
        pk,
        &ConfiguredCircuit::new(seed, satisfied),
        #[cfg(feature = "committed-instances")]
        0,
        &[&inst],
        &mut transcript,
        rng,
    )
    .unwrap_or_else(|_| panic!("test circuit proving failed"));
    let proof = transcript.finalize();
    let mut transcript = CircuitTranscript::<blake2b_simd::State>::init_from_bytes(&proof);
    let ok = prepare(
        pk.get_vk(),
        #[cfg(feature = "committed-instances")]
        &[],
        &[&inst],
        &mut transcript,
    )
    .is_ok_and(|g| g.verify(&params.verifier_params()).is_ok());
    (proof, ok)
}

#[cfg(test)]
mod tests;
