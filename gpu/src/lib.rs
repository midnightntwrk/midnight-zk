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

//! # midnight_gpu
//!
//! CUDA kernels for the accelerator hooks of `midnight-proofs` (feature
//! `gpu`): BLS12-381 G1 MSM and scalar-field NTT through the sppark templates,
//! and the quotient (coset transforms, numerator, division by the vanishing
//! polynomial, extended inverse transform), whose extended values stay on the
//! device: only the quotient coefficients come back.
//!
//! Every device function returns the exact value of the stock CPU code or
//! declines (`None` / `false`); on a decline the caller's buffers are
//! unchanged and the caller runs the CPU code. The device is never a
//! correctness dependency. Declines: the build has no CUDA core (feature
//! `cuda` off, or `nvcc` missing at build time), no usable device or
//! `MIDNIGHT_GPU=off`, a size below `2^min_k`, a root of unity other than
//! the standard one, a scalar that is not reduced, a job shape this crate
//! does not take, a device error, or an armed test fault.
//!
//! This crate does not depend on midnight-curves or midnight-proofs. Its
//! functions have the signatures of the hook fields of
//! `midnight_proofs::gpu::GpuHooks`, so a process installs them as they are:
//!
//! ```ignore
//! midnight_proofs::gpu::install(midnight_proofs::gpu::GpuHooks {
//!     msm_g1: Some(midnight_gpu::msm_g1),
//!     fft: Some(midnight_gpu::fft),
//!     ifft: Some(midnight_gpu::ifft),
//!     quotient: Some(midnight_gpu::quotient),
//! });
//! ```
//!
//! Data layout (the in-memory form of the `midnight-curves` types, through
//! the zero-copy adapter `midnight_proofs::gpu::adapter`):
//! - [`Scalar`]: `blst_fr`, four little-endian `u64` limbs of the Montgomery
//!   form (`R = 2^256`), reduced modulo `r` ([`field::MODULUS`]).
//! - [`G1AffineLimbs`]: `blst_p1_affine`, `x` and `y` as six limbs each,
//!   Montgomery (`R = 2^384`); the point at infinity is all zero.
//! - [`G1JacobianLimbs`]: `blst_p1`, Jacobian `X`, `Y`, `Z`.
//!
//! Run-time environment:
//! - `MIDNIGHT_GPU=off`: use no device.
//! - `MIDNIGHT_GPU_MIN_K` (default 14): the smallest log2 size sent to the
//!   device (MSM length, transform size, extended quotient size); see
//!   [`set_min_k`].
//! - `MIDNIGHT_GPU_MAX_BYTES`: the device memory one quotient may use (default:
//!   90% of the free device memory at the call).
//! - `MIDNIGHT_GPU_QUOTIENT_THREADS`: grid threads of the quotient kernel
//!   (default 512 per multiprocessor; see [`quotient::grid_threads`]).
//! - `MIDNIGHT_GPU_STAGE=off`, `MIDNIGHT_GPU_STAGE_THREADS`: the page-locked
//!   staging of large copies ([`xfer`]).
//! - `MIDNIGHT_GPU_WIPE_CHECK=1`: check every zeroed region ([`wipe`]), the
//!   CUDA core's frees of sppark's blocks included; device regions are checked
//!   on the device.
//! - `MIDNIGHT_GPU_KEEP_KEYS=1`: keep the device copies of registered
//!   proving-key polynomials between requests (default: freed at
//!   [`end_request`]; see [`quotient::set_keep_resident`]).
//! - `MIDNIGHT_GPU_FAULT`: armed test faults (feature `test-fault` only, module
//!   `fault`). Set in a build without that feature, it is refused and the
//!   device is not used.
//!
//! Detection ([`device_count`], [`present`]) makes no CUDA context; the first
//! device call ([`device`]) makes it.
//!
//! Build-time environment (feature `cuda`, see `build.rs`): `CUDA_PATH`,
//! `CUDA_HOME`, `MIDNIGHT_GPU_ARCHS`, `MIDNIGHT_GPU_REQUIRE_CUDA`.
//!
//! A dedicated thread owns device 0 and executes one device request at a time.
//! Call [`end_request`] between proofs to zero and free buffers that held
//! witness values.

#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
// The stub build (no CUDA core) keeps the host-side code it does not call.
#![cfg_attr(not(midnight_gpu_cuda), allow(dead_code, unused_imports))]

use std::{
    collections::BTreeMap,
    sync::{
        Mutex, OnceLock,
        atomic::{AtomicU32, AtomicU64, Ordering::Relaxed},
    },
};

/// A diagnostic line on stderr from the device-owner thread or from inside
/// a device operation. It is best effort: a line that cannot be written at
/// once is dropped, because the device owner must neither unwind nor wait
/// on a diagnostic (a caller may hold the standard stderr lock, or drain a
/// stderr pipe only after its device call returns, while it waits for the
/// owner). On Linux the line is appended through a fresh non-blocking
/// descriptor of the process's stderr, without the standard library's
/// stderr lock; a closed stderr or a full pipe drops the line. A stderr
/// that cannot be reopened (a socket, as under a service manager that
/// logs to a journal) and every other system use the standard stderr,
/// which can wait for that lock.
#[cfg_attr(not(midnight_gpu_cuda), allow(unused_macros))]
macro_rules! diag {
    ($($arg:tt)*) => {
        $crate::diag_write(format_args!($($arg)*))
    };
}
#[cfg_attr(not(midnight_gpu_cuda), allow(unused_imports))]
pub(crate) use diag;

#[cfg_attr(not(midnight_gpu_cuda), allow(dead_code))]
pub(crate) fn diag_write(args: std::fmt::Arguments<'_>) {
    let mut line = String::new();
    if std::fmt::write(&mut line, args).is_err() {
        return;
    }
    line.push('\n');
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    {
        use std::{io::Write as _, os::unix::fs::OpenOptionsExt as _};
        // O_NONBLOCK of these two Linux targets.
        const O_NONBLOCK: i32 = 0o4000;
        // Append: a reopened regular file starts at offset 0 and must not
        // be written over.
        match std::fs::OpenOptions::new()
            .append(true)
            .custom_flags(O_NONBLOCK)
            .open("/proc/self/fd/2")
        {
            Ok(mut err) => {
                let _ = err.write_all(line.as_bytes());
            }
            // no descriptor 2: nothing to write to
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            // a stderr that cannot be reopened (a socket)
            Err(_) => {
                let _ = std::io::stderr().write_all(line.as_bytes());
            }
        }
    }
    #[cfg(not(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    )))]
    {
        use std::io::Write as _;
        let _ = std::io::stderr().write_all(line.as_bytes());
    }
}

pub mod abi;
pub mod actor;
pub mod batch;
pub mod field;
pub mod ident;
pub mod msm;
pub mod quotient;
pub mod teardown;
pub mod wipe;
pub mod xfer;

#[cfg(feature = "test-fault")]
pub mod fault;

/// Without `test-fault` no fault can be armed.
#[cfg(not(feature = "test-fault"))]
#[allow(dead_code)]
pub(crate) mod fault {
    #[derive(Clone, Copy)]
    pub(crate) enum Class {
        Msm,
        Ntt,
        Quotient,
        Erase,
    }
    #[derive(Clone, Copy)]
    pub(crate) enum Point {
        Upload,
        Launch,
        Divide,
        Readback,
        Corrupt,
        Check,
    }
    #[inline(always)]
    pub(crate) fn hit(_: Class, _: Point) -> bool {
        false
    }
}

#[cfg(midnight_gpu_cuda)]
mod ffi;
#[cfg(midnight_gpu_cuda)]
mod ntt;

pub use msm::{SrsHandle, register_srs};
pub use quotient::{KeyHandle, quotient, register_key};
pub use teardown::{
    declined_after_teardown, device_disabled, erasure_failed, teardown_context, teardown_ntt_tables,
};

/// A scalar: `blst_fr` limbs, Montgomery form (see the crate text).
pub type Scalar = [u64; 4];
/// An affine G1 point: `blst_p1_affine` limbs.
pub type G1AffineLimbs = [u64; 12];
/// A Jacobian G1 point: `blst_p1` limbs.
pub type G1JacobianLimbs = [u64; 18];

/// The largest log2 size of the device transforms.
pub const MAX_EXT_K: u32 = 28;

/// The largest log2 length of a device MSM; a longer one declines (`shape`).
pub const MAX_MSM_LOG: u32 = 28;

/// The admission of an MSM on its lengths alone, in the order the device
/// path applies it (before the device-presence check, so the stub declines
/// the same way): an empty input, unequal lengths or a length above
/// `2^max_log` is `shape`; a length below `2^min_k()` is `below-min-k`.
/// [`msm_g1`] uses it with `max_log = MAX_MSM_LOG`.
pub fn msm_admission(scalars: usize, bases: usize, max_log: u32) -> Result<(), &'static str> {
    if scalars == 0 || scalars != bases || scalars > (1usize << max_log.min(62)) {
        return Err("shape");
    }
    if scalars < (1usize << min_k().min(40)) {
        return Err("below-min-k");
    }
    Ok(())
}

/// Device 0 as its properties describe it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GpuInfo {
    /// Device name.
    pub name: String,
    /// Usable devices (only device 0 is used).
    pub devices: u32,
    /// Multiprocessors.
    pub sm_count: u32,
    /// Compute capability (major, minor).
    pub compute_capability: (u32, u32),
    /// An integrated part (memory shared with the host).
    pub integrated: bool,
    /// Device memory in bytes.
    pub total_bytes: u64,
    /// CUDA runtime version the core links (`1000 * major + 10 * minor`,
    /// e.g. 12080 for 12.8).
    pub runtime_version: u32,
    /// Latest CUDA version the installed driver supports (same encoding).
    pub driver_version: u32,
}

/// Whether the CUDA core is compiled in.
pub const fn cuda_built() -> bool {
    cfg!(midnight_gpu_cuda)
}

/// The `-gencode` arguments the CUDA core was compiled with.
pub fn build_archs() -> Option<&'static str> {
    #[cfg(midnight_gpu_cuda)]
    {
        Some(env!("MIDNIGHT_GPU_BUILD_ARCHS"))
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

fn disabled() -> bool {
    static OFF: OnceLock<bool> = OnceLock::new();
    *OFF.get_or_init(|| {
        if std::env::var("MIDNIGHT_GPU").as_deref() == Ok("off") {
            return true;
        }
        // a test switch in a build without the test feature: refused, and the
        // device is not used (every call declines as `no-device`)
        if !cfg!(feature = "test-fault") && std::env::var_os("MIDNIGHT_GPU_FAULT").is_some() {
            eprintln!(
                "midnight-gpu: MIDNIGHT_GPU_FAULT is set in a build without the feature \
                 `test-fault`; the device is not used"
            );
            return true;
        }
        false
    })
}

/// Devices the CUDA runtime sees (`cudaGetDeviceCount` only): no CUDA
/// context is made and no device memory is touched. 0 in a stub build, with
/// no driver, or with `MIDNIGHT_GPU=off`.
pub fn device_count() -> u32 {
    if disabled() || teardown::device_disabled() {
        return 0;
    }
    #[cfg(midnight_gpu_cuda)]
    {
        // SAFETY: no argument.
        unsafe { ffi::mgpu_device_count_only() }.max(0) as u32
    }
    #[cfg(not(midnight_gpu_cuda))]
    0
}

/// Whether the primary CUDA context of device 0 is active: `Some(false)`
/// until this crate's first device call (`device()`), `None` when unknown (a
/// stub build or no driver). Detection ([`device_count`], [`present`]) never
/// makes the context.
pub fn context_active() -> Option<bool> {
    #[cfg(midnight_gpu_cuda)]
    {
        // SAFETY: no argument.
        match unsafe { ffi::mgpu_primary_ctx_active() } {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

/// Device 0 from its properties, without a CUDA context: `Some` when the
/// CUDA core is compiled in, the device has compute capability 7.0 or more
/// and cooperative launch, and `MIDNIGHT_GPU` is not `off`.
pub fn present() -> Option<&'static GpuInfo> {
    if disabled() || teardown::device_disabled() {
        return None;
    }
    #[cfg(midnight_gpu_cuda)]
    {
        ffi::probe()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

/// Whether device calls can run: [`present`], and the CUDA context is made
/// (the first call makes it). Returns false during an exclusive session.
pub fn device() -> bool {
    let Some(_gate) = batch::admit_ordinary("query") else {
        return false;
    };
    device_admitted()
}

fn device_admitted() -> bool {
    if present().is_none() {
        return false;
    }
    #[cfg(midnight_gpu_cuda)]
    {
        ffi::context() && quotient::layout_ok()
    }
    #[cfg(not(midnight_gpu_cuda))]
    false
}

static MIN_K: AtomicU32 = AtomicU32::new(u32::MAX);

/// The smallest log2 size sent to the device: [`set_min_k`], else
/// `MIDNIGHT_GPU_MIN_K`, else 14. A `MIDNIGHT_GPU_MIN_K` above
/// [`MAX_EXT_K`] is ignored (the default applies), as [`set_min_k`] refuses
/// it.
pub fn min_k() -> u32 {
    let k = MIN_K.load(Relaxed);
    if k != u32::MAX {
        return k;
    }
    let k = std::env::var("MIDNIGHT_GPU_MIN_K")
        .ok()
        .and_then(|s| s.trim().parse().ok())
        .filter(|k| *k <= MAX_EXT_K)
        .unwrap_or(14);
    let _ = MIN_K.compare_exchange(u32::MAX, k, Relaxed, Relaxed);
    MIN_K.load(Relaxed)
}

/// Sets the smallest log2 size sent to the device. Returns `false` and
/// keeps the old value when `k` is above [`MAX_EXT_K`]: no device size
/// would be admitted, and every call would decline (`below-min-k`) without
/// a sign that the setting was wrong.
pub fn set_min_k(k: u32) -> bool {
    let Some(_gate) = crate::batch::admit_ordinary("mode") else {
        return false;
    };
    if k > MAX_EXT_K {
        return false;
    }
    MIN_K.store(k, Relaxed);
    true
}

/// `MIDNIGHT_GPU_MAX_BYTES`, if set.
pub(crate) fn max_device_bytes() -> Option<usize> {
    std::env::var("MIDNIGHT_GPU_MAX_BYTES").ok()?.trim().parse().ok()
}

static MSM_CALLS: AtomicU64 = AtomicU64::new(0);
static NTT_CALLS: AtomicU64 = AtomicU64::new(0);
static DEVICE_ERRORS: AtomicU64 = AtomicU64::new(0);

/// Calls taken by the device since process start.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// MSMs computed on the device.
    pub msm: u64,
    /// Transforms (FFT, inverse FFT) computed on the device.
    pub ntt: u64,
    /// Quotients computed on the device.
    pub quotient: u64,
    /// Calls that reached the device and failed (the caller ran the CPU code).
    pub device_errors: u64,
}

static DECLINES: Mutex<BTreeMap<(&'static str, &'static str), u64>> = Mutex::new(BTreeMap::new());

/// Counts a decline of a hook class (`msm`, `ntt`, `quotient`) for a
/// reason; returns `false` (the decline).
pub(crate) fn decline(class: &'static str, reason: &'static str) -> bool {
    *DECLINES
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .entry((class, reason))
        .or_insert(0) += 1;
    false
}

/// Every decline since the last [`reset_stats`]: `(class, reason, count)`.
/// Classes: `msm`, `ntt`, `quotient`. Reasons: `no-device` (stub
/// build, no usable device, `MIDNIGHT_GPU=off`), `below-min-k`, `shape`
/// (length, root, job layout or version the device does not take),
/// `unreduced` (a scalar not below the modulus), `memory` (the quotient's
/// device need exceeds the limit), `fault` (an injected test fault before
/// the device work), `device-error` (a device call failed, or an injected
/// fault after it), `operation-panic` (the device operation unwound),
/// `teardown` (the device is retired), and `batch` (the entry lacks admission
/// to the current session or an ordinary entry found the gate closed).
pub fn declines() -> Vec<(&'static str, &'static str, u64)> {
    DECLINES
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .iter()
        .map(|(k, v)| (k.0, k.1, *v))
        .collect()
}

/// Resets [`stats`], [`declines`] and the copy counters of [`xfer`].
pub fn reset_stats() {
    for c in [&MSM_CALLS, &NTT_CALLS, &DEVICE_ERRORS] {
        c.store(0, Relaxed);
    }
    DECLINES.lock().unwrap_or_else(|e| e.into_inner()).clear();
    xfer::reset();
}

/// The counters.
pub fn stats() -> Stats {
    Stats {
        msm: MSM_CALLS.load(Relaxed),
        ntt: NTT_CALLS.load(Relaxed),
        quotient: quotient::quotient_counts().0,
        device_errors: DEVICE_ERRORS.load(Relaxed),
    }
}

#[cfg(midnight_gpu_cuda)]
fn count<R>(
    result: Result<Option<R>, ffi::CallError>,
    c: &AtomicU64,
    class: &'static str,
    entry: batch::Entry,
) -> Option<R> {
    if let Ok(Some(value)) = result {
        c.fetch_add(1, Relaxed);
        return Some(value);
    }
    DEVICE_ERRORS.fetch_add(1, Relaxed);
    if matches!(result, Err(ffi::CallError::Panicked)) {
        entry.operation_panic(class);
    } else {
        decline(class, "device-error");
    }
    None
}

/// G1 MSM `sum scalars[i] * bases[i]` (equal lengths), the hook
/// `GpuHooks::msm_g1`. Registered slices use a device table ([`msm`]).
/// Holds the batch admission gate shared for the whole call and
/// declines with reason `batch` while a batch session holds it.
pub fn msm_g1(scalars: &[Scalar], bases: &[G1AffineLimbs]) -> Option<G1JacobianLimbs> {
    let _gate = batch::admit_ordinary("msm")?;
    msm_g1_admitted(scalars, bases, batch::Entry::Ordinary)
}

/// [`msm_g1`] for a caller already admitted on the batch side of the
/// gate ([`batch::isolated_msm_g1`]).
pub(crate) fn msm_g1_admitted(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
    entry: batch::Entry,
) -> Option<G1JacobianLimbs> {
    #[cfg(test)]
    batch::test_hold::maybe_hold();
    if let Err(why) = msm_admission(scalars.len(), bases.len(), MAX_MSM_LOG) {
        decline("msm", why);
        return None;
    }
    if teardown::device_disabled() {
        teardown::note_decline("msm");
        return None;
    }
    if !device_admitted() {
        decline("msm", "no-device");
        return None;
    }
    if !field::all_reduced(scalars) {
        decline("msm", "unreduced");
        return None;
    }
    #[cfg(midnight_gpu_cuda)]
    {
        let r = msm::msm_g1(scalars, bases, entry);
        count(r, &MSM_CALLS, "msm", entry)
    }
    #[cfg(not(midnight_gpu_cuda))]
    {
        let _ = entry;
        None
    }
}

/// The FFT of `a` (length `2^log_n`) at `omega`, natural order, in place:
/// the hook `GpuHooks::fft`. Taken for the standard root of the size and its
/// inverse.
pub fn fft(a: &mut [Scalar], omega: Scalar, log_n: u32) -> bool {
    let Some(_gate) = batch::admit_ordinary("ntt") else {
        return false;
    };
    transform(a, omega, log_n, None, batch::Entry::Ordinary)
}

/// The FFT of `a` at `omega_inv`, then each element times `divisor`: the
/// hook `GpuHooks::ifft`.
pub fn ifft(a: &mut [Scalar], omega_inv: Scalar, log_n: u32, divisor: Scalar) -> bool {
    let Some(_gate) = batch::admit_ordinary("ntt") else {
        return false;
    };
    transform(a, omega_inv, log_n, Some(divisor), batch::Entry::Ordinary)
}

#[allow(unused_variables)]
fn transform(
    a: &mut [Scalar],
    omega: Scalar,
    log_n: u32,
    divisor: Option<Scalar>,
    entry: batch::Entry,
) -> bool {
    // a one-element transform is the identity: `shape`, never sent to the
    // core (which takes sizes 2 ..= 2^28)
    if log_n == 0 || log_n > MAX_EXT_K || a.len() != 1usize << log_n {
        return decline("ntt", "shape");
    }
    if log_n < min_k() {
        return decline("ntt", "below-min-k");
    }
    if teardown::device_disabled() {
        return teardown::note_decline("ntt");
    }
    if !device_admitted() {
        return decline("ntt", "no-device");
    }
    let Some((w, wi)) = field::std_root(log_n) else {
        return decline("ntt", "shape");
    };
    if divisor.is_some_and(|d| !field::is_reduced(&d)) || !field::all_reduced(a) {
        return decline("ntt", "unreduced");
    }
    #[cfg(midnight_gpu_cuda)]
    {
        let n = field::from_u64(1u64 << log_n);
        let ok = if omega == w {
            // forward: no scaling, then the divisor if any
            ntt::ntt(a, log_n, false, divisor)
        } else if omega == wi {
            // sppark's inverse includes 1/n; fix up any other divisor
            let n_inv = field::invert(&n).unwrap();
            let post = match divisor {
                Some(d) if d == n_inv => None,
                Some(d) => Some(field::mul(&d, &n)),
                None => Some(n),
            };
            ntt::ntt(a, log_n, true, post)
        } else {
            return decline("ntt", "shape");
        };
        count(ok.map(|ran| ran.then_some(())), &NTT_CALLS, "ntt", entry).is_some()
    }
    #[cfg(not(midnight_gpu_cuda))]
    false
}

/// Starts an ordinary request if admitted and resets the peak of
/// [`device_bytes`].
pub fn begin_request() {
    if let Some(_gate) = batch::admit_ordinary("request") {
        begin_request_admitted();
    }
}

fn begin_request_admitted() {
    quotient::next_request();
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: a counter.
    unsafe {
        ffi::mgpu_dev_bytes_reset_peak()
    };
}

/// Frees the device contexts of the registered MSM tables and the device
/// copies of the registered proving-key polynomials (the registrations stay;
/// the next MSM or quotient uploads them again). This call declines while a
/// batch holds the gate.
pub fn evict_tables() {
    let Some(_gate) = batch::admit_ordinary("eviction") else {
        return;
    };
    if teardown::device_disabled() {
        // Their device pointers went with the reset context: no CUDA
        // call may free or use them now.
        return;
    }
    msm::evict_contexts(batch::Entry::Ordinary);
    quotient::evict_key_copies_admitted();
}

/// [`end_request`] with its erasure report: `Ok` when every erasure and
/// release succeeded (and, in check mode, every zeroed region checked
/// zero), else `Err` with the same counters.
pub fn end_request_report() -> Result<wipe::WipeStats, Box<wipe::WipeStats>> {
    let before = wipe::erasure_failures();
    let ok = end_request();
    let s = wipe::stats();
    if ok
        && s.erasure_failures == before
        && s.device_nonzero == 0
        && s.check_failures == 0
        && s.core[3] == 0
        && s.stage[3] == 0
    {
        Ok(s)
    } else {
        Err(Box::new(s))
    }
}

/// The end of a request (call it between proofs): zeroes and frees the
/// transform scratch, the bounce and read-back buffers of the CUDA core and
/// the device contexts of the MSM tables (they hold the bucket sums of their
/// last MSM), frees the proving-key copies unless
/// [`quotient::keep_resident`], and retries the regions in quarantine (this
/// crate's and sppark's). `true`: every erasure and release since process
/// start succeeded (the erasure-failure count is sticky, so a failure at a
/// drop during the request is folded in). Returns false during a batch session.
pub fn end_request() -> bool {
    let Some(_gate) = batch::admit_ordinary("request") else {
        return false;
    };
    end_request_admitted(batch::Entry::Ordinary)
}

/// Zeroes and releases the transform scratch and the core's bounce and
/// read-back buffers.
///
/// # Safety
/// Call it on the device-owner thread (inside [`ffi::call_live`]), after
/// every transfer of the current device call has completed.
#[cfg(midnight_gpu_cuda)]
unsafe fn release_shared_scratch() -> bool {
    ntt::release_scratch();
    // SAFETY: the caller's contract (device-owner thread, no transfer in flight).
    unsafe { ffi::mgpu_stage_end() == 0 }
}

fn end_request_admitted(entry: batch::Entry) -> bool {
    if teardown::device_disabled() {
        // Everything the device held went with the reset context: issue
        // no free or retry against it. A forced teardown is an erasure
        // failure, so the report stays negative.
        return !teardown::erasure_failed() && wipe::erasure_failures() == 0;
    }
    #[cfg(midnight_gpu_cuda)]
    {
        if present().is_none() {
            return wipe::erasure_failures() == 0;
        }
        let (_, unconfirmed) = msm::evict_contexts(entry);
        if !quotient::keep_resident() {
            quotient::evict_key_copies_admitted();
        }
        // One actor request; `None` when the device was retired
        // while this call waited for it to start.
        let Some(done) = ffi::call_live(|| {
            // SAFETY: on the device-owner thread; this request starts no transfer.
            let staged = unsafe { release_shared_scratch() };
            let ours = wipe::retry_quarantine();
            // SAFETY: on the actor thread; sppark's quarantined blocks.
            let lib = unsafe { ffi::mgpu_quarantine_retry() } == 0;
            ours && lib && staged
        }) else {
            return false;
        };
        done && !unconfirmed && wipe::erasure_failures() == 0
    }
    #[cfg(not(midnight_gpu_cuda))]
    {
        let _ = entry;
        wipe::erasure_failures() == 0
    }
}

/// Error drains of the CUDA core since process start: `(run, unconfirmed)`.
/// Every error exit of a device call that enqueued copies or kernels waits
/// for them before it returns (a drain), so no transfer still reads or writes
/// the caller's memory. An unconfirmed drain (the stream and the device-wide
/// synchronisation both failed) means a transfer may still target it.
pub fn error_drains() -> (u64, u64) {
    #[allow(unused_mut)]
    let mut c = [0u64; 2];
    #[cfg(midnight_gpu_cuda)]
    if ffi::probe().is_some() {
        // SAFETY: writes 2 u64 into `c`; host memory only.
        unsafe { ffi::mgpu_drain_counters(c.as_mut_ptr()) };
    }
    (c[0], c[1])
}

/// `(live, peak)` device bytes of this crate (sppark's buffers included).
pub fn device_bytes() -> (u64, u64) {
    #[allow(unused_mut)]
    let mut v = [0u64; 2];
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: an out array of two.
    unsafe {
        ffi::mgpu_dev_bytes(v.as_mut_ptr())
    };
    (v[0], v[1])
}

/// `(free, total)` device bytes, when a device is in use and the query is
/// admitted.
pub fn mem_info() -> Option<(usize, usize)> {
    let _gate = batch::admit_ordinary("query")?;
    if !device_admitted() {
        return None;
    }
    #[cfg(midnight_gpu_cuda)]
    {
        ffi::mem_info()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

#[cfg(test)]
mod diag_tests {
    // A diagnostic does not wait for the standard stderr lock: the caller
    // of a device call may hold it while the device owner prints.
    #[test]
    fn diagnostic_does_not_wait_for_the_stderr_lock() {
        use std::{sync::mpsc, time::Duration};
        let (locked, is_locked) = mpsc::channel();
        let (release, released) = mpsc::channel::<()>();
        let holder = std::thread::spawn(move || {
            let held = std::io::stderr().lock();
            locked.send(()).unwrap();
            let _ = released.recv_timeout(Duration::from_secs(30));
            drop(held);
        });
        is_locked.recv_timeout(Duration::from_secs(10)).expect("holder took the lock");
        let (done, wrote) = mpsc::channel();
        std::thread::spawn(move || {
            crate::diag!("midnight-gpu: diagnostic test line");
            let _ = done.send(());
        });
        let got = wrote.recv_timeout(Duration::from_secs(5));
        release.send(()).unwrap();
        holder.join().unwrap();
        got.expect("the diagnostic waited for the stderr lock");
    }

    // A full pipe drops the line instead of blocking the writer.
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    fn diagnostic_never_blocks_on_a_full_pipe() {
        use std::{
            io::Read as _,
            process::{Command, Stdio},
            time::{Duration, Instant},
        };
        const CHILD: &str = "MIDNIGHT_GPU_DIAG_CHILD";
        if std::env::var_os(CHILD).is_some() {
            // far more than a pipe holds, with nobody reading
            for _ in 0..4096 {
                crate::diag!("midnight-gpu: diagnostic test line {}", "x".repeat(200));
            }
            return;
        }
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "diag_tests::diagnostic_never_blocks_on_a_full_pipe",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(20);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() > deadline {
                let _ = child.kill();
                panic!("a diagnostic blocked on a full stderr pipe");
            }
            std::thread::sleep(Duration::from_millis(20));
        };
        assert!(status.success());
        let mut seen = String::new();
        let _ = child.stderr.take().unwrap().read_to_string(&mut seen);
        assert!(seen.contains("diagnostic test line"));
    }

    // A host that closed descriptor 2: the line is dropped and nothing is
    // assumed about the descriptor.
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    fn diagnostic_with_stderr_closed_is_dropped() {
        use std::{
            os::unix::process::CommandExt as _,
            process::{Command, Stdio},
        };
        const CHILD: &str = "MIDNIGHT_GPU_DIAG_CLOSED_CHILD";
        if std::env::var_os(CHILD).is_some() {
            crate::diag!("midnight-gpu: diagnostic test line");
            // the test harness itself must not need stderr either
            std::process::exit(0);
        }
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args([
                "--exact",
                "diag_tests::diagnostic_with_stderr_closed_is_dropped",
            ])
            .env(CHILD, "1")
            .stdout(Stdio::null());
        // SAFETY: `close` is async-signal-safe; the closure runs in the
        // child after fork and only closes descriptor 2.
        unsafe {
            command.pre_exec(|| {
                libc::close(2);
                Ok(())
            });
        }
        let status = command.status().unwrap();
        assert!(status.success(), "{status:?}");
    }

    // A regular file as stderr keeps what it held: the line is appended.
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    fn diagnostic_appends_to_a_file() {
        use std::{
            io::Write as _,
            process::{Command, Stdio},
        };
        const CHILD: &str = "MIDNIGHT_GPU_DIAG_FILE_CHILD";
        if std::env::var_os(CHILD).is_some() {
            crate::diag!("midnight-gpu: diagnostic test line");
            std::process::exit(0);
        }
        let path =
            std::env::temp_dir().join(format!("midnight-gpu-diag-{}.log", std::process::id()));
        let earlier = "earlier line one\nearlier line two\n";
        // the log is opened without append, as a shell redirection does
        let mut log = std::fs::File::create(&path).unwrap();
        log.write_all(earlier.as_bytes()).unwrap();
        let status = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "diag_tests::diagnostic_appends_to_a_file"])
            .env(CHILD, "1")
            .stdout(Stdio::null())
            .stderr(Stdio::from(log))
            .status()
            .unwrap();
        let seen = std::fs::read_to_string(&path).unwrap();
        let _ = std::fs::remove_file(&path);
        assert!(status.success());
        assert_eq!(
            seen,
            format!("{earlier}midnight-gpu: diagnostic test line\n")
        );
    }

    // A socket as stderr cannot be reopened: the line still arrives.
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    fn diagnostic_reaches_a_socket() {
        use std::{
            io::Read as _,
            os::{fd::OwnedFd, unix::net::UnixStream},
            process::{Command, Stdio},
            time::Duration,
        };
        const CHILD: &str = "MIDNIGHT_GPU_DIAG_SOCKET_CHILD";
        if std::env::var_os(CHILD).is_some() {
            crate::diag!("midnight-gpu: diagnostic test line");
            std::process::exit(0);
        }
        let (mut ours, theirs) = UnixStream::pair().unwrap();
        ours.set_read_timeout(Some(Duration::from_secs(20))).unwrap();
        let status = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "diag_tests::diagnostic_reaches_a_socket"])
            .env(CHILD, "1")
            .stdout(Stdio::null())
            .stderr(Stdio::from(OwnedFd::from(theirs)))
            .status()
            .unwrap();
        assert!(status.success());
        let mut seen = String::new();
        let _ = ours.read_to_string(&mut seen);
        assert!(seen.contains("diagnostic test line"), "{seen:?}");
    }
}
