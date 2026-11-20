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

//! Metal backend for the accelerator hooks of `midnight-proofs` (feature
//! `gpu`) on Apple GPUs: BLS12-381 G1 MSM, scalar-field NTT and the quotient.
//! It has the same entry points as the CUDA crate `midnight-gpu` and does not
//! depend on `midnight-proofs`: its functions match the hook fields of
//! `midnight_proofs::gpu::GpuHooks`.
//!
//! ```ignore
//! midnight_proofs::gpu::install(midnight_proofs::gpu::GpuHooks {
//!     msm_g1: Some(midnight_metal::msm_g1),
//!     fft: Some(midnight_metal::fft),
//!     ifft: Some(midnight_metal::ifft),
//!     quotient: Some(midnight_metal::quotient),
//! });
//! midnight_metal::begin_request();
//! let proof = prove(/* ... */);
//! assert!(midnight_metal::end_request());
//! ```
//!
//! # Hook contract
//!
//! - Every entry point returns the exact value of the stock CPU code, or
//!   declines (`None` / `false`) and the caller runs the CPU code.
//! - A decline leaves the caller's buffer unchanged: a result is written only
//!   after the last command buffer completed without error.
//! - No entry point draws randomness or touches a transcript. Any
//!   pseudo-random value (the MSM mask) is a fixed function of the shape.
//! - Every failure, including a panic caught at the entry point, is a counted
//!   decline ([`declines`]), never a panic into the prover.
//!
//! # Requests
//!
//! Per-request device buffers can hold witness values. Between
//! [`begin_request`] and [`end_request`] they are reused across hook calls;
//! [`end_request`] zeroes them. Without an open request every hook call zeroes
//! them before it returns. Large buffers come from a pool of zeroed buffers
//! because a new buffer stalls its first command buffer while its pages are
//! mapped for the GPU.
//!
//! # Thresholds
//!
//! A call below its class's threshold ([`thresholds`]) declines `below-min-k`.
//! The defaults ([`DEFAULT_THRESHOLDS`]) were measured on whole proofs, not
//! isolated kernels, because the GPU clocks down while the CPU works between
//! device calls. By default only MSMs on a registered SRS table
//! ([`register_srs`]) go to the device: other bases need a per-call G1 check
//! that costs more than the CPU MSM. An explicit threshold ([`set_min_k`])
//! replaces every default and opens that one-shot path.
//!
//! # Environment
//!
//! - `MIDNIGHT_METAL=off`: use no device.
//! - `MIDNIGHT_METAL_MIN_K`: one threshold for every class.
//! - `MIDNIGHT_METAL_MSM_CPU_SHARE=off`: run every MSM on the device only.
//! - `MIDNIGHT_METAL_POOL_MIB`: pool size limit (default a quarter of
//!   `recommendedMaxWorkingSetSize`).
//! - `MIDNIGHT_METAL_QUOTIENT_THREADS`: see [`quotient_threads`].
//! - `MIDNIGHT_METAL_KEEP_KEYS=1`: see [`keep_resident`].
//! - `MIDNIGHT_METAL_SHADER_SOURCE=1`: compile the embedded shader source
//!   instead of the metallib ([`library_source`]); also read by `build.rs`.

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
// Other targets keep the host-side code they do not call.
#![cfg_attr(not(target_os = "macos"), allow(dead_code, unused_imports))]

use std::{
    ffi::c_void,
    sync::{
        OnceLock,
        atomic::{AtomicU32, Ordering::Relaxed},
    },
};

mod account;
pub mod field;

#[cfg(target_os = "macos")]
pub mod ctx;
#[cfg(target_os = "macos")]
mod msm;
#[cfg(target_os = "macos")]
mod ntt;
#[cfg(target_os = "macos")]
mod quotient;

/// MSM path, plan and one-shot G1 check count (feature `test-support`).
#[cfg(all(target_os = "macos", any(test, feature = "test-support")))]
#[doc(hidden)]
pub use msm::{MsmStages, msm_g1_stages, one_shot_g1_checks};
#[cfg(target_os = "macos")]
pub use msm::{SrsHandle, msm_counts, register_srs, srs_handles, srs_stale};
/// NTT building blocks (feature `test-support`).
#[cfg(all(target_os = "macos", any(test, feature = "test-support")))]
#[doc(hidden)]
pub use ntt::test_support as ntt_test_support;
/// The stage timings of the last quotient served (feature `test-support`).
#[cfg(all(target_os = "macos", any(test, feature = "test-support")))]
#[doc(hidden)]
pub use quotient::QuotientStages;
/// The quotient job layout, for integration tests.
#[cfg(target_os = "macos")]
#[doc(hidden)]
pub use quotient::abi as quotient_abi;
/// Quotient test entry points (feature `test-support`).
#[cfg(all(target_os = "macos", any(test, feature = "test-support")))]
#[doc(hidden)]
pub use quotient::test_support as quotient_test_support;
#[cfg(target_os = "macos")]
pub use quotient::{
    KeyHandle, evict_key_copies, keep_resident, key_stale, keys_registered, need_bytes,
    quotient_counts, register_key, set_keep_resident, threads as quotient_threads,
};

#[cfg(all(test, target_os = "macos"))]
mod tests;

use account::{Class, Reason};

/// A scalar: `blst_fr`, four little-endian limbs, Montgomery form, reduced
/// modulo [`field::FR_MODULUS`].
pub type Scalar = [u64; 4];
/// An affine G1 point: `blst_p1_affine`, `x` then `y`, Montgomery form; all
/// zero is the point at infinity.
pub type G1AffineLimbs = [u64; 12];
/// A Jacobian G1 point: `blst_p1` limbs.
pub type G1JacobianLimbs = [u64; 18];

/// The largest log2 transform size taken.
pub const MAX_LOG_N: u32 = 28;
/// The largest log2 MSM length taken; a longer one declines (`shape`).
pub const MAX_MSM_LOG: u32 = 28;

/// `floor(log2(n * sqrt 2))`: the size class of an MSM length, so the `n - 1`
/// coefficients of a multi-open are in the class of `n`.
pub(crate) const fn lg2_nearest(n: usize) -> u32 {
    // 181 / 128 = 1.4140625, just below sqrt 2
    let mut m = ((n as u128 * 181) >> 7) as usize;
    let mut r = 0;
    while m > 1 {
        m >>= 1;
        r += 1;
    }
    r
}

// ---------------------------------------------------------------------------
// Device

/// The Metal device as its properties describe it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetalInfo {
    /// Device name (`MTLDevice.name`).
    pub name: String,
    /// `MTLDevice.registryID`.
    pub registry_id: u64,
    /// `hasUnifiedMemory`.
    pub unified_memory: bool,
    /// `recommendedMaxWorkingSetSize` in bytes.
    pub recommended_max_working_set: u64,
    /// `maxBufferLength`: the largest single buffer in bytes.
    pub max_buffer_length: u64,
    /// `maxThreadsPerThreadgroup.width`.
    pub max_threads_per_threadgroup: u64,
    /// The highest `MTLGPUFamilyAppleN` supported (0: none).
    pub apple_family: u32,
    /// Supports `MTLGPUFamilyMetal3`.
    pub metal3: bool,
    /// The Metal Shading Language version of the shaders.
    pub msl_version: &'static str,
}

/// Whether the Metal code is compiled in (a macOS target).
pub const fn metal_built() -> bool {
    cfg!(target_os = "macos")
}

/// Whether `MIDNIGHT_METAL=off` (read once).
fn disabled() -> bool {
    static OFF: OnceLock<bool> = OnceLock::new();
    *OFF.get_or_init(|| std::env::var("MIDNIGHT_METAL").as_deref() == Ok("off"))
}

/// The Metal device, without loading the shader library. `None` on other
/// targets, with no device, or with `MIDNIGHT_METAL=off`.
pub fn present() -> Option<&'static MetalInfo> {
    if disabled() {
        return None;
    }
    #[cfg(target_os = "macos")]
    {
        ctx::probe()
    }
    #[cfg(not(target_os = "macos"))]
    None
}

/// Whether device calls can run: [`present`], and the context (queue, shader
/// library) is made; the first call makes it.
pub fn device() -> bool {
    if present().is_none() {
        return false;
    }
    #[cfg(target_os = "macos")]
    {
        ctx::context().is_ok()
    }
    #[cfg(not(target_os = "macos"))]
    false
}

/// Where the shader library came from: `metallib`, or `source ...` with the
/// reason. `None` before the context is made or when it failed.
pub fn library_source() -> Option<&'static str> {
    #[cfg(target_os = "macos")]
    {
        ctx::context().ok().map(|c| c.library_source())
    }
    #[cfg(not(target_os = "macos"))]
    None
}

/// `(free, total)` device bytes. `total` is `recommendedMaxWorkingSetSize`;
/// `free` is `total` minus `currentAllocatedSize` plus the idle pool buffers,
/// which are released on demand. On unified memory this is a budget hint, not
/// a reservation.
pub fn mem_info() -> Option<(usize, usize)> {
    if !device() {
        return None;
    }
    #[cfg(target_os = "macos")]
    {
        ctx::mem_info()
    }
    #[cfg(not(target_os = "macos"))]
    None
}

// ---------------------------------------------------------------------------
// Thresholds

/// The log2 size from which each class goes to the device.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Thresholds {
    /// Forward FFTs: the transform size `log_n`.
    pub fft: u32,
    /// Inverse FFTs: the transform size `log_n`.
    pub ifft: u32,
    /// MSMs on a registered SRS table: the size class of the length.
    pub msm_table: u32,
    /// MSMs with no registered table: the size class of the length; `None`:
    /// never (the default).
    pub msm_one_shot: Option<u32>,
    /// Quotients: the extended domain `ext_k`.
    pub quotient: u32,
    /// Whether one explicit value applies to every class.
    pub explicit: bool,
}

impl Thresholds {
    /// One value for every class (an explicit `min_k`).
    pub const fn all(k: u32) -> Thresholds {
        Thresholds {
            fft: k,
            ifft: k,
            msm_table: k,
            msm_one_shot: Some(k),
            quotient: k,
            explicit: true,
        }
    }

    /// `(class, log2 size)` pairs for reports; `None`: never.
    pub fn named(&self) -> [(&'static str, Option<u32>); 5] {
        [
            ("fft", Some(self.fft)),
            ("ifft", Some(self.ifft)),
            ("msm-table", Some(self.msm_table)),
            ("msm-one-shot", self.msm_one_shot),
            ("quotient-ext", Some(self.quotient)),
        ]
    }
}

/// Per-class break-evens against the stock CPU code, measured on Apple
/// silicon. The one-shot MSM never breaks even because of its G1 check.
pub const DEFAULT_THRESHOLDS: Thresholds = Thresholds {
    fft: 15,
    ifft: 15,
    msm_table: 13,
    msm_one_shot: None,
    quotient: 14,
    explicit: false,
};

/// [`MIN_K`]: not read yet (the environment is read at the next use).
const MIN_K_UNREAD: u32 = u32::MAX;
/// [`MIN_K`]: no explicit value (the per-class defaults apply).
const MIN_K_DEFAULTS: u32 = u32::MAX - 1;
/// The explicit threshold, or one of the two markers above.
static MIN_K: AtomicU32 = AtomicU32::new(MIN_K_UNREAD);

/// [`set_min_k`], else `MIDNIGHT_METAL_MIN_K` (ignored above
/// [`MAX_LOG_N`]).
fn explicit_min_k() -> Option<u32> {
    let mut k = MIN_K.load(Relaxed);
    if k == MIN_K_UNREAD {
        let env = std::env::var("MIDNIGHT_METAL_MIN_K")
            .ok()
            .and_then(|s| s.trim().parse().ok())
            .filter(|k| *k <= MAX_LOG_N)
            .unwrap_or(MIN_K_DEFAULTS);
        let _ = MIN_K.compare_exchange(MIN_K_UNREAD, env, Relaxed, Relaxed);
        k = MIN_K.load(Relaxed);
    }
    (k <= MAX_LOG_N).then_some(k)
}

/// The effective threshold of each class.
pub fn thresholds() -> Thresholds {
    explicit_min_k().map_or(DEFAULT_THRESHOLDS, Thresholds::all)
}

/// The explicit threshold, else the smallest per-class default.
pub fn min_k() -> u32 {
    let t = thresholds();
    let m = t.fft.min(t.ifft).min(t.msm_table).min(t.quotient);
    t.msm_one_shot.map_or(m, |k| m.min(k))
}

/// Sets one threshold for every class and opens the one-shot MSM. Returns
/// `false` and keeps the old value when `k` is above [`MAX_LOG_N`].
pub fn set_min_k(k: u32) -> bool {
    if k > MAX_LOG_N {
        return false;
    }
    MIN_K.store(k, Relaxed);
    true
}

/// Undoes [`set_min_k`].
pub fn reset_min_k() {
    MIN_K.store(MIN_K_UNREAD, Relaxed);
}

// ---------------------------------------------------------------------------
// Counters

/// Calls served in one class since the last [`reset_stats`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ClassStats {
    /// Calls the device computed.
    pub served: u64,
    /// GPU time of those calls in nanoseconds.
    pub device_nanos: u64,
}

/// Per-class service counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// MSMs.
    pub msm: ClassStats,
    /// Forward FFTs.
    pub fft: ClassStats,
    /// Inverse FFTs.
    pub ifft: ClassStats,
    /// Quotients.
    pub quotient: ClassStats,
}

/// The service counters since the last [`reset_stats`].
pub fn stats() -> Stats {
    Stats {
        msm: account::class_stats(Class::Msm),
        fft: account::class_stats(Class::Fft),
        ifft: account::class_stats(Class::Ifft),
        quotient: account::class_stats(Class::Quotient),
    }
}

/// Every decline since the last [`reset_stats`]: `(class, reason, count)`.
///
/// Reasons:
/// - `no-device`: another target, no usable device, or `MIDNIGHT_METAL=off`;
/// - `below-min-k`: below the threshold or the MSM's effective-size need;
/// - `shape`: a length, root, job layout or version the device does not take;
/// - `unreduced`: a scalar not below the modulus;
/// - `memory`: a buffer too large, a failed allocation or a budget;
/// - `device-error`: a pipeline, encoder or command buffer failed;
/// - `panic`: the backend panicked and the entry point caught it;
/// - `bases-not-in-subgroup` (`msm`): a base outside G1;
/// - `unregistered-bases` (`msm`): no registered table serves the bases and
///   the one-shot path is off.
pub fn declines() -> Vec<(&'static str, &'static str, u64)> {
    account::declines()
}

/// Resets [`stats`] and [`declines`].
pub fn reset_stats() {
    account::reset();
}

// ---------------------------------------------------------------------------
// MSM

/// The length admission of an MSM: `shape` for an empty input, unequal
/// lengths or a length above `2^max_log`; `below-min-k` when the size class
/// is below `msm_table`. [`msm_g1`] may still decline on the bases.
pub fn msm_admission(scalars: usize, bases: usize, max_log: u32) -> Result<(), &'static str> {
    length_admission(scalars, bases, max_log).map_err(Reason::name)
}

/// [`msm_admission`] with the reason as a [`Reason`].
fn length_admission(scalars: usize, bases: usize, max_log: u32) -> Result<(), Reason> {
    if scalars == 0 || scalars != bases || scalars > (1usize << max_log.min(62)) {
        return Err(Reason::Shape);
    }
    if lg2_nearest(scalars) < thresholds().msm_table {
        return Err(Reason::BelowMinK);
    }
    Ok(())
}

/// Admission of an MSM no registered table serves; `Ok` is the threshold.
fn one_shot_admission(len: usize, t: &Thresholds) -> Result<u32, Reason> {
    match t.msm_one_shot {
        None => Err(Reason::UnregisteredBases),
        Some(k) if lg2_nearest(len) < k => Err(Reason::BelowMinK),
        Some(k) => Ok(k),
    }
}

/// Whether [`msm_g1`] takes an MSM of `len` scalars over `bases`, judged on
/// the length and the bases only. It reads no scalar, so the answer does not
/// depend on the witness; [`msm_g1`] may still decline on the scalars. It does
/// not check the device.
pub fn msm_sized(len: usize, bases: &[G1AffineLimbs]) -> bool {
    length_admission(len, bases.len(), MAX_MSM_LOG).is_ok() && sized_by_bases(len, bases)
}

/// [`msm_sized`] of a length that passed [`length_admission`].
fn sized_by_bases(len: usize, bases: &[G1AffineLimbs]) -> bool {
    #[cfg(target_os = "macos")]
    {
        sized_by_lookup(&msm::lookup(bases, len), len, &thresholds())
    }
    #[cfg(not(target_os = "macos"))]
    {
        let _ = bases;
        one_shot_admission(len, &thresholds()).is_ok()
    }
}

/// [`msm_sized`] from the lookup of the bases.
#[cfg(target_os = "macos")]
fn sized_by_lookup(lookup: &msm::Lookup, len: usize, t: &Thresholds) -> bool {
    match lookup {
        msm::Lookup::Table(_) => true,
        msm::Lookup::NotInG1 => false,
        msm::Lookup::Unregistered => one_shot_admission(len, t).is_ok(),
    }
}

/// G1 MSM `sum scalars[i] * bases[i]`: the hook `GpuHooks::msm_g1`. `None`:
/// declined.
///
/// Every check on public facts (lengths, device, registered table, one-shot
/// admission) runs before any scalar is read. Then come the effective size
/// and reduction of the scalars and, on the one-shot path only, the G1 check
/// of every base.
pub fn msm_g1(scalars: &[Scalar], bases: &[G1AffineLimbs]) -> Option<G1JacobianLimbs> {
    guarded(Class::Msm, None, || msm_g1_body(scalars, bases, None))
}

/// [`msm_g1`] and [`msm_sized`] of the same call from one registry lookup, so
/// the bases are compared once per MSM. `sized` is decided before any scalar
/// is read and stands even if the MSM declines or panics.
pub fn msm_g1_sized(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
) -> (bool, Option<G1JacobianLimbs>) {
    let mut sized = false;
    let r = guarded(Class::Msm, None, || {
        msm_g1_body(scalars, bases, Some(&mut sized))
    });
    (sized, r)
}

/// The body of [`msm_g1`]; with `sized`, also stores [`msm_sized`].
fn msm_g1_body(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
    sized: Option<&mut bool>,
) -> Option<G1JacobianLimbs> {
    if let Err(r) = length_admission(scalars.len(), bases.len(), MAX_MSM_LOG) {
        account::decline(Class::Msm, r);
        return None;
    }
    if !device() {
        // `msm_sized` does not look at the device
        if let Some(s) = sized {
            *s = sized_by_bases(scalars.len(), bases);
        }
        account::decline(Class::Msm, Reason::NoDevice);
        return None;
    }
    #[cfg(target_os = "macos")]
    {
        let t = thresholds();
        let n = scalars.len();
        // pick the path from public facts only, before any scalar is read
        let lookup = msm::lookup(bases, n);
        if let Some(s) = sized {
            *s = sized_by_lookup(&lookup, n, &t);
        }
        let (table, need) = match lookup {
            msm::Lookup::Table(tb) => (
                Some(tb),
                msm::effective_need(n, t.msm_table, true, t.explicit),
            ),
            msm::Lookup::NotInG1 => {
                account::decline(Class::Msm, msm::BASES_REASON);
                return None;
            }
            msm::Lookup::Unregistered => match one_shot_admission(n, &t) {
                Ok(k) => (None, msm::effective_need(n, k, false, t.explicit)),
                Err(r) => {
                    account::decline(Class::Msm, r);
                    return None;
                }
            },
        };
        // only the decline is observable, never the count
        if !msm::effective_size_reaches(scalars, need) {
            account::decline(Class::Msm, Reason::BelowMinK);
            return None;
        }
        if !field::all_reduced(scalars) {
            account::decline(Class::Msm, Reason::Unreduced);
            return None;
        }
        let r = msm::msm_g1(scalars, bases, table);
        // the test panic comes after the backend used its scratch
        test_switch::hook_panic(Class::Msm);
        r
    }
    #[cfg(not(target_os = "macos"))]
    None
}

// ---------------------------------------------------------------------------
// Transforms

/// The admission shared by [`fft`] and [`ifft`]: the shape, the threshold,
/// the device, then the reduction of the root, the divisor and the data.
fn transform_admission(
    class: Class,
    a: &[Scalar],
    omega: &Scalar,
    log_n: u32,
    divisor: Option<&Scalar>,
) -> bool {
    if log_n == 0 || log_n > MAX_LOG_N || a.len() != 1usize << log_n {
        return account::decline(class, Reason::Shape);
    }
    let t = thresholds();
    let min = if class == Class::Ifft { t.ifft } else { t.fft };
    if log_n < min {
        return account::decline(class, Reason::BelowMinK);
    }
    if !device() {
        return account::decline(class, Reason::NoDevice);
    }
    if !field::is_reduced(omega)
        || divisor.is_some_and(|d| !field::is_reduced(d))
        || !field::all_reduced(a)
    {
        return account::decline(class, Reason::Unreduced);
    }
    true
}

/// The FFT of `a` (length `2^log_n`) at `omega`, natural order, in place:
/// the hook `GpuHooks::fft`. `false`: declined, `a` unchanged.
pub fn fft(a: &mut [Scalar], omega: Scalar, log_n: u32) -> bool {
    guarded(Class::Fft, false, || fft_body(a, omega, log_n))
}

fn fft_body(a: &mut [Scalar], omega: Scalar, log_n: u32) -> bool {
    if !transform_admission(Class::Fft, a, &omega, log_n, None) {
        return false;
    }
    #[cfg(target_os = "macos")]
    {
        ntt::fft(a, omega, log_n)
    }
    #[cfg(not(target_os = "macos"))]
    false
}

/// The FFT of `a` at `omega_inv`, then each element times `divisor`, in
/// place: the hook `GpuHooks::ifft`. `false`: declined, `a` unchanged.
pub fn ifft(a: &mut [Scalar], omega_inv: Scalar, log_n: u32, divisor: Scalar) -> bool {
    guarded(Class::Ifft, false, || {
        ifft_body(a, omega_inv, log_n, divisor)
    })
}

fn ifft_body(a: &mut [Scalar], omega_inv: Scalar, log_n: u32, divisor: Scalar) -> bool {
    if !transform_admission(Class::Ifft, a, &omega_inv, log_n, Some(&divisor)) {
        return false;
    }
    #[cfg(target_os = "macos")]
    {
        ntt::ifft(a, omega_inv, log_n, divisor)
    }
    #[cfg(not(target_os = "macos"))]
    false
}

// ---------------------------------------------------------------------------
// Quotient

/// The quotient `h(X)` of a job (`midnight_proofs::gpu::abi::QuotientJobAbi`):
/// the hook `GpuHooks::quotient`, writing the first `out.len()` coefficients.
/// `false`: declined, `out` unchanged.
///
/// # Safety
/// `job` is null or points to a valid `QuotientJobAbi` whose pointers live
/// for the call.
pub unsafe fn quotient(job: *const c_void, out: &mut [Scalar]) -> bool {
    // SAFETY: the caller's contract, passed on.
    guarded(Class::Quotient, false, || unsafe {
        quotient_body(job, out)
    })
}

/// # Safety
/// As [`quotient`].
unsafe fn quotient_body(job: *const c_void, out: &mut [Scalar]) -> bool {
    if job.is_null() {
        return account::decline(Class::Quotient, Reason::Shape);
    }
    if !device() {
        return account::decline(Class::Quotient, Reason::NoDevice);
    }
    #[cfg(target_os = "macos")]
    {
        // the test panic comes before the backend: `out` is not written yet
        test_switch::hook_panic(Class::Quotient);
        // SAFETY: the caller's contract.
        unsafe { quotient::quotient(job, out) }
    }
    #[cfg(not(target_os = "macos"))]
    {
        let _ = out;
        false
    }
}

// ---------------------------------------------------------------------------
// The hook boundary

/// Outside a request, zeroes the per-request buffers when the hook call ends,
/// on every path. The wipe takes the device, so it never zeroes a buffer
/// another call is using.
struct HookScope {
    #[cfg(target_os = "macos")]
    open: bool,
}

impl HookScope {
    fn enter() -> Self {
        HookScope {
            #[cfg(target_os = "macos")]
            open: ctx::request_open(),
        }
    }
}

impl Drop for HookScope {
    fn drop(&mut self) {
        #[cfg(target_os = "macos")]
        if !self.open || !ctx::request_open() {
            ctx::wipe_unbracketed();
        }
    }
}

/// Runs a hook body; a panic becomes the decline `panic` with the value
/// `declined`. The caller's buffer is intact because no body writes it before
/// its result is complete.
fn guarded<R>(class: Class, declined: R, body: impl FnOnce() -> R) -> R {
    let _scope = HookScope::enter();
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(body)) {
        Ok(r) => r,
        Err(_) => {
            test_switch::count_panic();
            account::decline(class, Reason::Panic);
            declined
        }
    }
}

/// Test switches of the hook entries.
#[cfg(any(test, feature = "test-support"))]
mod test_switch {
    use std::sync::atomic::{AtomicU32, AtomicU64, Ordering::Relaxed};

    use crate::account::Class;

    /// One bit per class ([`bit`]) whose backend panics.
    static HOOK_PANIC: AtomicU32 = AtomicU32::new(0);
    /// Hook calls whose backend panicked, since process start.
    static HOOK_PANICS: AtomicU64 = AtomicU64::new(0);

    fn bit(class: Class) -> u32 {
        match class {
            Class::Msm => 1,
            Class::Fft => 2,
            Class::Ifft => 4,
            Class::Quotient => 8,
        }
    }

    pub(super) fn set_hook_panic(class: &str, on: bool) {
        let b = [Class::Msm, Class::Fft, Class::Ifft, Class::Quotient]
            .into_iter()
            .find(|c| c.name() == class)
            .map_or(0, bit);
        if on {
            HOOK_PANIC.fetch_or(b, Relaxed);
        } else {
            HOOK_PANIC.fetch_and(!b, Relaxed);
        }
    }

    /// Panics when [`set_hook_panic`] is on for `class`.
    pub(crate) fn hook_panic(class: Class) {
        if HOOK_PANIC.load(Relaxed) & bit(class) != 0 {
            panic!(
                "midnight-metal test switch: a panic in the {} backend",
                class.name()
            );
        }
    }

    pub(super) fn count_panic() {
        HOOK_PANICS.fetch_add(1, Relaxed);
    }

    pub(super) fn hook_panics() -> u64 {
        HOOK_PANICS.load(Relaxed)
    }
}

/// The test switches of a normal build: no-ops.
#[cfg(not(any(test, feature = "test-support")))]
mod test_switch {
    use crate::account::Class;

    #[inline(always)]
    pub(crate) fn hook_panic(_: Class) {}

    #[inline(always)]
    pub(super) fn count_panic() {}
}

/// Makes the hook `class` panic inside its backend (feature `test-support`).
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn set_hook_panic(class: &str, on: bool) {
    test_switch::set_hook_panic(class, on);
}

/// Hook calls whose backend panicked since process start.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn hook_panics() -> u64 {
    test_switch::hook_panics()
}

// ---------------------------------------------------------------------------
// Requests and memory

/// Starts a request: per-request buffers are kept for reuse until
/// [`end_request`]. Also resets the peaks of [`device_bytes`] and
/// [`request_peak_bytes`].
pub fn begin_request() {
    #[cfg(target_os = "macos")]
    {
        ctx::begin_request();
        quotient::begin_request();
    }
}

/// What [`end_request_report`] erased.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WipeStats {
    /// Regions zeroed: the per-request buffers and, in check mode, the idle pool
    /// buffers.
    pub regions: u64,
    /// Their bytes.
    pub bytes: u64,
    /// Whether every region was read back after its zeroing.
    pub checked: bool,
    /// Regions read back (check mode).
    pub checked_regions: u64,
    /// Regions that read back non-zero (check mode).
    pub nonzero_regions: u64,
    /// Regions that could not be read back from the host (check mode).
    pub check_failures: u64,
    /// Of `regions`: idle pool buffers read back (check mode).
    pub pool_regions: u64,
    /// Their bytes.
    pub pool_bytes: u64,
    /// Zeroings that panicked since the last report. Each was redone on the
    /// calling thread and its buffer released, not pooled.
    pub erasure_failures: u64,
}

/// Ends a request: waits for device work and background zeroing, zeroes the
/// per-request buffers and returns them to the pool, then frees the
/// proving-key copies unless [`keep_resident`]. With `check`, every zeroed
/// region and every idle pool buffer is read back.
///
/// `Err` when a region read back non-zero or unreadable, or a zeroing
/// panicked. Such a region is zeroed again and released, never pooled.
pub fn end_request_report(check: bool) -> Result<WipeStats, WipeStats> {
    #[cfg(target_os = "macos")]
    {
        let r = ctx::end_request_report(check);
        quotient::end_request();
        r
    }
    #[cfg(not(target_os = "macos"))]
    Ok(WipeStats {
        checked: check,
        ..WipeStats::default()
    })
}

/// [`end_request_report`] without the read-back; `true` on success.
pub fn end_request() -> bool {
    end_request_report(false).is_ok()
}

/// Releases the pool of zeroed buffers once background zeroing has ended.
/// Returns the bytes released.
pub fn release_pool() -> u64 {
    #[cfg(target_os = "macos")]
    {
        ctx::release_pool()
    }
    #[cfg(not(target_os = "macos"))]
    0
}

/// Bytes of idle, zeroed buffers in the pool.
pub fn pool_bytes() -> u64 {
    #[cfg(target_os = "macos")]
    {
        ctx::pool_bytes()
    }
    #[cfg(not(target_os = "macos"))]
    0
}

/// `(now, peak)` bytes held in this crate's Metal buffers, idle pool buffers
/// included. The peak is since process start or the last [`begin_request`].
pub fn device_bytes() -> (u64, u64) {
    #[cfg(target_os = "macos")]
    {
        ctx::device_bytes()
    }
    #[cfg(not(target_os = "macos"))]
    (0, 0)
}

/// Peak bytes in use since the last [`begin_request`]: buffers handed out,
/// resident SRS tables and key copies, not idle pool buffers. It starts from
/// the bytes in use at [`begin_request`], so it includes what earlier requests
/// left resident.
pub fn request_peak_bytes() -> u64 {
    #[cfg(target_os = "macos")]
    {
        ctx::request_peak_bytes()
    }
    #[cfg(not(target_os = "macos"))]
    0
}
