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

//! Prover accelerator hooks (cargo feature `accel`).
//!
//! A process may [`install`] one [`Accelerator`]. The prover then offers it
//! the following operations before running its own code:
//!
//! - every KZG commitment MSM over BLS12-381 G1 ([`Accelerator::msm_g1`]), and
//!   the commitments of a group of same-length polynomials as one batch
//!   ([`Accelerator::msm_g1_batch`]);
//! - the base-domain FFT and inverse FFT of
//!   [`EvaluationDomain`](crate::poly::EvaluationDomain) over the BLS12-381
//!   scalar field ([`Accelerator::fft`], [`Accelerator::ifft`]);
//! - the quotient polynomial `h(X)` in coefficient form
//!   ([`Accelerator::quotient`]), described by a [`QuotientJob`]. This covers
//!   the extended-coset transforms, the numerator, the division by `X^n - 1`
//!   and the inverse extended transform, so no extended-domain vector has to
//!   cross between host and accelerator.
//!
//! Every method either returns exactly the value of the stock code or
//! declines, in which case the stock code runs on the unchanged input. The
//! hooks add, remove or reorder no random draw and no transcript operation,
//! so with no accelerator installed (or one that declines everything) a proof
//! is byte-identical to a proof from a build without the feature.
//!
//! Only the BLS12-381 types ([`Fq`], [`G1Affine`]) reach an accelerator;
//! calls over other fields and curves always run the stock code.
//!
//! [`reference::CpuReference`] implements every method with the stock CPU
//! code and is the conformance reference for accelerator backends.

use std::{
    any::TypeId,
    sync::{
        Arc, RwLock,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
};

use ff::PrimeField;
use midnight_curves::{Fq, G1Affine, G1Projective};

use crate::{
    plonk::{ProvingKey, traces::ProverTrace},
    poly::commitment::PolynomialCommitmentScheme,
};

mod quotient;
pub mod reference;
#[cfg(test)]
mod test_circuit;
#[cfg(test)]
mod tests;

pub use quotient::{
    COLUMN_ADVICE, COLUMN_FIXED, COLUMN_INSTANCE, DeviceOp, DeviceProgram, DeviceRead, INDEX_MASK,
    LookupJob, OP_ADD, OP_DOUBLE, OP_MUL, OP_MUL_ADD, OP_NEGATE, OP_SQUARE, OP_SUB, PermutationJob,
    QuotientDivide, QuotientJob, QuotientShape, TAG_READ, TAG_SLOT, TAG_UNIFORM, TrashJob, operand,
    quotient_shape, resident_key_polys,
};

/// An accelerator for the prover's heavy operations over BLS12-381.
///
/// Every method has a declining default, so an accelerator implements only
/// what it serves. A method may decline any call (input too small, device
/// busy or failed, ...); the prover then runs its stock code. A method that
/// serves a call must return exactly the value of the stock code.
pub trait Accelerator: Send + Sync {
    /// `sum_i scalars[i] * bases[i]`. Both slices have the same length.
    /// `None`: declined.
    fn msm_g1(&self, scalars: &[Fq], bases: &[G1Affine]) -> Option<G1Projective> {
        let _ = (scalars, bases);
        None
    }

    /// `sum_i scalars[j][i] * bases[i]` for every `j`. Every `scalars[j]` has
    /// the length of `bases`, and there are at least two. `None`: declined,
    /// and each MSM is then offered to [`Accelerator::msm_g1`] on its own.
    fn msm_g1_batch(&self, scalars: &[&[Fq]], bases: &[G1Affine]) -> Option<Vec<G1Projective>> {
        let _ = (scalars, bases);
        None
    }

    /// The FFT of `a` (length `2^log_n`) at the root `omega`, in natural
    /// order, in place. `false`: declined, and `a` must be unchanged.
    fn fft(&self, a: &mut [Fq], omega: Fq, log_n: u32) -> bool {
        let _ = (a, omega, log_n);
        false
    }

    /// The FFT of `a` (length `2^log_n`) at `omega_inv`, then every element
    /// times `divisor`, in place. `false`: declined, and `a` must be
    /// unchanged.
    fn ifft(&self, a: &mut [Fq], omega_inv: Fq, log_n: u32, divisor: Fq) -> bool {
        let _ = (a, omega_inv, log_n, divisor);
        false
    }

    /// A proof starts on this thread. Every hook call of the proof comes
    /// after it, on this thread or on Rayon workers it spawns.
    fn begin_proof(&self) {}

    /// The proof started by the matching [`Accelerator::begin_proof`] has
    /// ended, also when it failed or panicked: the backend may release or
    /// wipe what it kept for the proof (scratch that held witness values).
    fn end_proof(&self) {}

    /// Writes the coefficients of the quotient `h(X)` of `job` to `out`
    /// (`out.len() == job.divide.len`). See [`QuotientJob`] for the exact
    /// definition, and [`QuotientJob::numerator_reference`] and
    /// [`QuotientJob::divide_reference`] for a CPU implementation.
    /// `false`: declined, and the prover computes the quotient itself.
    fn quotient(&self, job: &QuotientJob<'_, Fq>, out: &mut [Fq]) -> bool {
        let _ = (job, out);
        false
    }
}

static INSTALLED: AtomicBool = AtomicBool::new(false);
static ACCELERATOR: RwLock<Option<Arc<dyn Accelerator>>> = RwLock::new(None);

/// Installs the accelerator of this process and returns the one it
/// replaces. Proofs already running may finish with either one.
pub fn install(accel: Arc<dyn Accelerator>) -> Option<Arc<dyn Accelerator>> {
    let mut slot = ACCELERATOR.write().unwrap_or_else(|e| e.into_inner());
    INSTALLED.store(true, Ordering::Release);
    slot.replace(accel)
}

/// Removes the installed accelerator, if any, and returns it. From then on
/// the prover runs only its stock code.
pub fn uninstall() -> Option<Arc<dyn Accelerator>> {
    let mut slot = ACCELERATOR.write().unwrap_or_else(|e| e.into_inner());
    INSTALLED.store(false, Ordering::Release);
    slot.take()
}

/// The installed accelerator. With none installed this is one atomic load.
fn installed() -> Option<Arc<dyn Accelerator>> {
    if !INSTALLED.load(Ordering::Acquire) {
        return None;
    }
    ACCELERATOR.read().unwrap_or_else(|e| e.into_inner()).clone()
}

// ------------------------------------------------------------------ stats

/// The operations the prover offers to an accelerator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    /// [`Accelerator::msm_g1`].
    Msm,
    /// [`Accelerator::msm_g1_batch`] (one count per batch).
    MsmBatch,
    /// [`Accelerator::fft`].
    Fft,
    /// [`Accelerator::ifft`].
    Ifft,
    /// [`Accelerator::quotient`].
    Quotient,
}

const NOPS: usize = 5;
static SERVED: [AtomicU64; NOPS] = [const { AtomicU64::new(0) }; NOPS];
static DECLINED: [AtomicU64; NOPS] = [const { AtomicU64::new(0) }; NOPS];

/// Calls offered to the installed accelerator since process start (or the
/// last [`reset_stats`]), as `(served, declined)` for `op`. Calls made with
/// no accelerator installed, or over non-BLS12-381 types, are not counted.
pub fn stats(op: Op) -> (u64, u64) {
    let i = op as usize;
    (
        SERVED[i].load(Ordering::Relaxed),
        DECLINED[i].load(Ordering::Relaxed),
    )
}

/// Resets [`stats`].
pub fn reset_stats() {
    for c in SERVED.iter().chain(&DECLINED) {
        c.store(0, Ordering::Relaxed);
    }
}

fn count(op: Op, served: bool) -> bool {
    let c = if served { &SERVED } else { &DECLINED };
    c[op as usize].fetch_add(1, Ordering::Relaxed);
    served
}

/// Brackets one proof for the installed accelerator: begins it, and ends it
/// when dropped, so the end also comes after an error or a panic.
pub(crate) struct ProofScope(Option<Arc<dyn Accelerator>>);

impl ProofScope {
    pub(crate) fn begin() -> Self {
        let accel = installed();
        if let Some(a) = &accel {
            a.begin_proof();
        }
        ProofScope(accel)
    }
}

impl Drop for ProofScope {
    fn drop(&mut self) {
        if let Some(a) = &self.0 {
            a.end_proof();
        }
    }
}

// ------------------------------------------------------------------ casts
//
// The prover is generic over its field and curve; the accelerator takes the
// BLS12-381 types. These are the only conversions between the two, and they
// are the identity: each checks with `TypeId` that the generic type *is* the
// concrete one before reinterpreting a reference.

#[inline]
fn same<T: 'static, U: 'static>() -> bool {
    TypeId::of::<T>() == TypeId::of::<U>()
}

#[allow(unsafe_code)]
fn cast_slice<T: 'static, U: 'static>(s: &[T]) -> Option<&[U]> {
    // SAFETY: `T` and `U` are the same type.
    same::<T, U>().then(|| unsafe { &*(s as *const [T] as *const [U]) })
}

#[allow(unsafe_code)]
fn cast_slice_mut<T: 'static, U: 'static>(s: &mut [T]) -> Option<&mut [U]> {
    // SAFETY: `T` and `U` are the same type.
    same::<T, U>().then(|| unsafe { &mut *(s as *mut [T] as *mut [U]) })
}

fn cast<T: 'static + Copy, U: 'static + Copy>(t: T) -> Option<U> {
    cast_slice::<T, U>(std::slice::from_ref(&t)).map(|u| u[0])
}

// ------------------------------------------------------------------ dispatch

/// Offers the MSM `sum scalars[i] * bases[i]` to the accelerator.
pub(crate) fn msm<C: 'static + Copy, S: 'static, R: 'static + Copy>(
    scalars: &[S],
    bases: &[C],
) -> Option<R> {
    let accel = installed()?;
    let s = cast_slice::<S, Fq>(scalars)?;
    let b = cast_slice::<C, G1Affine>(bases)?;
    if !same::<R, G1Projective>() || s.len() != b.len() {
        return None;
    }
    let r = accel.msm_g1(s, b);
    count(Op::Msm, r.is_some());
    cast::<G1Projective, R>(r?)
}

/// Offers the MSMs `sum scalars[j][i] * bases[i]` to the accelerator as one
/// batch.
pub(crate) fn msm_batch<C: 'static + Copy, S: 'static, R: 'static + Copy>(
    scalars: &[&[S]],
    bases: &[C],
) -> Option<Vec<R>> {
    let accel = installed()?;
    let b = cast_slice::<C, G1Affine>(bases)?;
    let s: Vec<&[Fq]> = scalars.iter().map(|s| cast_slice::<S, Fq>(s)).collect::<Option<_>>()?;
    if !same::<R, G1Projective>() || s.len() < 2 || s.iter().any(|s| s.len() != b.len()) {
        return None;
    }
    let r = accel.msm_g1_batch(&s, b).filter(|r| r.len() == s.len());
    count(Op::MsmBatch, r.is_some());
    r?.into_iter().map(cast::<G1Projective, R>).collect()
}

/// Offers the FFT of `a` at `omega` to the accelerator.
pub(crate) fn fft<F: 'static + Copy>(a: &mut [F], omega: F, log_n: u32) -> bool {
    let Some(accel) = installed() else {
        return false;
    };
    let (Some(a), Some(omega)) = (cast_slice_mut::<F, Fq>(a), cast::<F, Fq>(omega)) else {
        return false;
    };
    count(Op::Fft, accel.fft(a, omega, log_n))
}

/// Offers the scaled inverse FFT of `a` at `omega_inv` to the accelerator.
pub(crate) fn ifft<F: 'static + Copy>(a: &mut [F], omega_inv: F, log_n: u32, divisor: F) -> bool {
    let Some(accel) = installed() else {
        return false;
    };
    let (Some(a), Some(omega_inv), Some(divisor)) = (
        cast_slice_mut::<F, Fq>(a),
        cast::<F, Fq>(omega_inv),
        cast::<F, Fq>(divisor),
    ) else {
        return false;
    };
    count(Op::Ifft, accel.ifft(a, omega_inv, log_n, divisor))
}

/// Offers the quotient of a proof to the accelerator: the first
/// `(n - 1) * quotient_poly_degree` coefficients of `h(X)`, or `None`.
pub(crate) fn quotient<F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, PCS>,
    trace: &ProverTrace<'_, F>,
) -> Option<Vec<F>> {
    let accel = installed()?;
    if !same::<F, Fq>() {
        return None;
    }
    let Some(job) = quotient::job(pk, trace) else {
        count(Op::Quotient, false);
        return None;
    };
    // SAFETY: `F` is `Fq` (checked above), so `QuotientJob<'_, F>` is
    // `QuotientJob<'_, Fq>`.
    #[allow(unsafe_code)]
    let job_fq = unsafe { &*(&job as *const QuotientJob<'_, F>).cast::<QuotientJob<'_, Fq>>() };
    let mut out = vec![F::ZERO; job.divide.len];
    let served = accel.quotient(job_fq, cast_slice_mut::<F, Fq>(&mut out)?);
    count(Op::Quotient, served).then_some(out)
}
