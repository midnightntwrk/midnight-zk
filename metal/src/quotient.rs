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

//! The quotient on the device and the resident proving-key copies; the
//! counterpart of the CUDA crate's `gpu/src/quotient.rs`.
//!
//! [`quotient`] takes the job of the `midnight_proofs::gpu` quotient hook
//! ([`abi`]), moves the proof's polynomials to the extended coset, runs the
//! numerator kernel over the job's programs, divides by the vanishing
//! polynomial, transforms back and writes the first `len` coefficients.
//!
//! Trust boundary: the caller guarantees that the job's pointers are valid
//! for reads of their counts and not written during the call. Everything else
//! (version, sizes, roots, coset shift, table ranges, reduction of every
//! scalar and polynomial, memory need) is checked here before any polynomial
//! is read.
//!
//! Departures from the CUDA backend:
//! - A Metal kernel takes at most 31 buffers, so the CUDA tables of device
//!   pointers become flat buffers with index tables
//!   (`shaders/include/quotient.h`).
//! - The numerator runs over row ranges of about [`TARGET_NANOS`] each, so no
//!   command buffer runs long.
//! - Proving-key polynomials are also checked reduced.
//! - Outside a request every serve checks the digests of the registered
//!   polynomials it reads; the CUDA crate checks once per request.

pub mod abi;
mod keys;
mod tables;

use std::{
    ffi::c_void,
    sync::atomic::{AtomicU32, AtomicU64, Ordering::Relaxed},
};

use blst::{blst_fr, blst_fr_mul, blst_fr_sqr};
pub use keys::{
    KeyHandle, evict_key_copies, keep_resident, key_stale, keys_registered, register_key,
    set_keep_resident,
};
pub(crate) use keys::{begin_request, end_request};

use self::{
    abi::QuotientJobAbi,
    keys::{Lent, Place, Plan},
    tables::Tables,
};
use crate::{
    MAX_LOG_N, MetalInfo, Scalar,
    account::{self, Class, Reason},
    ctx::{self, Arg, Buffer, Ctx, Error, Pod},
    field,
    ntt::{self, Dir},
};

const SCALAR_BYTES: usize = 32;

/// The GPU time one command buffer of the numerator aims at.
const TARGET_NANOS: u64 = 250_000_000;

/// The Montgomery form of one (`2^256 mod r`).
const ONE: Scalar = [
    0x0000_0001_ffff_fffe,
    0x5884_b7fa_0003_4802,
    0x998c_4fef_ecbc_4ff5,
    0x1824_b159_acc5_056f,
];

fn mul(a: &Scalar, b: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: valid pointers to blst_fr values.
    unsafe { blst_fr_mul(&mut r, &blst_fr { l: *a }, &blst_fr { l: *b }) };
    r.l
}

fn square(a: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: valid pointers to blst_fr values.
    unsafe { blst_fr_sqr(&mut r, &blst_fr { l: *a }) };
    r.l
}

fn pow(b: &Scalar, mut e: u64) -> Scalar {
    let (mut r, mut b) = (ONE, *b);
    while e != 0 {
        if e & 1 == 1 {
            r = mul(&r, &b);
        }
        b = square(&b);
        e >>= 1;
    }
    r
}

// ---------------------------------------------------------------------------
// Counters and settings

static RUNS: AtomicU64 = AtomicU64::new(0);
static DECLINES: AtomicU64 = AtomicU64::new(0);
/// [`threads`] once read (0: not yet).
static THREADS: AtomicU32 = AtomicU32::new(0);
/// The admission's memory limit in bytes besides the device's (tests).
static MEMORY_LIMIT: AtomicU64 = AtomicU64::new(u64::MAX);
/// The GPU time a numerator command buffer aims at (tests lower it).
static TARGET: AtomicU64 = AtomicU64::new(TARGET_NANOS);

/// (quotients computed on the device, quotient jobs declined) since process
/// start.
pub fn quotient_counts() -> (u64, u64) {
    (RUNS.load(Relaxed), DECLINES.load(Relaxed))
}

/// The default of [`threads`]: near the measured best numerator time while
/// keeping the scratch at `nslots * 2 MiB`.
const DEFAULT_THREADS: u32 = 1 << 16;

/// A thread count rounded down to a multiple of 256 in `[256, 2^24]`.
fn normalize_threads(t: u64) -> u32 {
    (t / 256 * 256).clamp(256, 1 << 24) as u32
}

/// The threads of one numerator dispatch, which is also the scratch slot
/// stride: `MIDNIGHT_METAL_QUOTIENT_THREADS`, else 2^16; a multiple of 256 in
/// `[256, 2^24]`.
pub fn threads() -> u32 {
    let t = THREADS.load(Relaxed);
    if t != 0 {
        return t;
    }
    let t = std::env::var("MIDNIGHT_METAL_QUOTIENT_THREADS")
        .ok()
        .and_then(|e| e.trim().parse::<u64>().ok())
        .map_or(DEFAULT_THREADS, normalize_threads);
    let _ = THREADS.compare_exchange(0, t, Relaxed, Relaxed);
    THREADS.load(Relaxed)
}

/// The dispatch threads (the scratch stride) for an extended domain of
/// `2^ext_k` rows.
fn stride(ext_k: u32) -> usize {
    (threads() as usize).min(1usize << ext_k)
}

// ---------------------------------------------------------------------------
// Memory need

/// Every device allocation one quotient call can make, in bytes. [`run`]
/// allocates exactly these, each at most once, so the sum bounds the bytes the
/// call adds. [`run`]'s admission and [`need_bytes`] both sum it, so the two
/// cannot drift.
#[derive(Clone, Copy, Debug)]
struct Need {
    /// One extended coset: `2^ext_k * 32`.
    ebytes: usize,
    /// One coefficient buffer of the coset phase: `2^k * 32` (two of them).
    coeff_bytes: usize,
    /// The proof's polynomials (one flat buffer of cosets).
    nproof: usize,
    /// Key polynomials uploaded for the call at the plan.
    ntemp: usize,
    /// The resident copy, when the call allocates it (0: it exists).
    lent_new: usize,
    /// The second upload after a stale key at [`keys::settle`] (0: no slot is
    /// checked, so none can move).
    restale: usize,
    /// The programs' scratch slots.
    slots_bytes: usize,
    /// The transform scratch, when the call allocates it.
    tmp_new: usize,
    /// The programs' words and uniforms.
    words_bytes: usize,
    uniforms_bytes: usize,
    /// `t_inv` (the inverse phase only).
    t_inv_bytes: usize,
    /// Whether the call divides and transforms back (not the numerator test
    /// path).
    inverse: bool,
}

impl Need {
    fn buffers(&self) -> [usize; 14] {
        let a = |b: usize| b.max(16);
        let e = self.ebytes;
        let opt = |b: usize| if b > 0 { a(b) } else { 0 };
        [
            opt(self.tmp_new),
            a(self.nproof.max(1) * e),
            a(self.coeff_bytes),
            a(self.coeff_bytes),
            a(self.ntemp * e),
            opt(self.lent_new),
            // the dummy argument
            16,
            opt(self.restale * e),
            // the numerator
            a(e),
            a(self.slots_bytes),
            a(self.words_bytes),
            a(self.uniforms_bytes),
            if self.inverse { a(self.t_inv_bytes) } else { 0 },
            // the scaled twiddle table of the inverse transform
            if self.inverse {
                ntt::SCALE_TABLE_BYTES
            } else {
                0
            },
        ]
    }

    /// The sum of the call's allocations.
    fn total(&self) -> usize {
        self.buffers().iter().sum()
    }

    /// The largest single buffer (against `maxBufferLength`).
    fn biggest(&self) -> usize {
        self.buffers().into_iter().max().unwrap_or(0)
    }

    /// Whether the call fits the free device memory and `maxBufferLength`.
    fn fits(&self, info: &MetalInfo) -> bool {
        self.total() as u64 <= memory_limit() && self.biggest() as u64 <= info.max_buffer_length
    }
}

/// An upper bound of the device bytes one quotient job allocates: the `Need`
/// of `run` at its worst over what the shape does not fix. It assumes the
/// resident copy holds only the job's key polynomials and ignores the few KiB
/// of program words and uniforms. The arguments are the fields of
/// `midnight_proofs::gpu::QuotientShape`.
pub fn need_bytes(ext_k: u32, proof_polys: usize, key_polys: usize, nslots: u32) -> usize {
    let e = SCALAR_BYTES << ext_k;
    let mut worst = 0;
    for k in 1..=ext_k.max(1) {
        for resident in 0..=key_polys {
            let n = Need {
                ebytes: e,
                coeff_bytes: SCALAR_BYTES << k,
                nproof: proof_polys,
                ntemp: key_polys - resident,
                lent_new: resident * e,
                restale: if resident > 0 { key_polys } else { 0 },
                slots_bytes: (nslots as usize).max(1) * stride(ext_k) * SCALAR_BYTES,
                tmp_new: ntt::scratch_bytes(ext_k),
                words_bytes: 0,
                uniforms_bytes: 0,
                t_inv_bytes: SCALAR_BYTES << ext_k.saturating_sub(k),
                inverse: true,
            };
            worst = worst.max(n.total());
        }
    }
    worst
}

/// The [`Need`] of a planned call.
fn need_of(
    j: &QuotientJobAbi,
    tab: &Tables<'_>,
    t_inv: &[Scalar],
    plan: &Plan,
    s: &ctx::Session,
    inverse: bool,
) -> Need {
    let ntemp = plan.places.iter().filter(|p| **p == Place::Temp).count();
    let lent_new = plan.lent.as_ref().map_or(0, |l| if l.buf.is_none() { l.bytes() } else { 0 });
    let resident_checked = plan.resident_checked();
    let tmp_need = ntt::scratch_bytes(j.ext_k);
    let tmp_have = s.get_scratch("quotient-tmp").map_or(0, |b| b.len_bytes());
    Need {
        ebytes: SCALAR_BYTES << j.ext_k,
        coeff_bytes: SCALAR_BYTES << j.k,
        nproof: tab.proof.len(),
        ntemp,
        lent_new,
        restale: if resident_checked > 0 {
            ntemp + resident_checked
        } else {
            0
        },
        slots_bytes: (j.nslots as usize).max(1) * stride(j.ext_k) * SCALAR_BYTES,
        // a shorter one is replaced by a new one
        tmp_new: if tmp_need > 0 && tmp_have < tmp_need {
            tmp_need
        } else {
            0
        },
        words_bytes: tab.words.len() * 4,
        uniforms_bytes: tab.uniforms.len() * SCALAR_BYTES,
        t_inv_bytes: t_inv.len() * SCALAR_BYTES,
        inverse,
    }
}

/// Bytes this call may allocate: the free working set (idle pool buffers
/// included) or the test limit, whichever is smaller.
fn memory_limit() -> u64 {
    let free = ctx::mem_info().map_or(0, |(free, _)| free as u64);
    free.min(MEMORY_LIMIT.load(Relaxed))
}

// ---------------------------------------------------------------------------
// Test support

/// The placement counts of the last quotient served.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct QuotientStages {
    /// Command buffers of the numerator.
    pub numerator_runs: u32,
    /// Proving-key polynomials read from a resident copy.
    pub resident_polys: u32,
    /// Proving-key polynomials uploaded for the call.
    pub uploaded_polys: u32,
    /// Slots of the resident copy filled by this call.
    pub key_copies_made: u32,
}

#[cfg(any(test, feature = "test-support"))]
static LAST_STAGES: std::sync::Mutex<Option<QuotientStages>> = std::sync::Mutex::new(None);

/// Test entry points (not a stable interface; [`test_support::numerator`]
/// returns witness-dependent values).
#[cfg(any(test, feature = "test-support"))]
pub mod test_support {
    use super::*;

    /// The exact [`Need`] total of `job` now. `Err`: the decline reason of the
    /// checks before admission.
    ///
    /// # Safety
    /// As [`crate::quotient`].
    pub unsafe fn need_bytes_job(job: *const c_void) -> Result<usize, &'static str> {
        if job.is_null() || !crate::device() {
            return Err("no-device");
        }
        // SAFETY: the caller's contract.
        let j = unsafe { &*(job as *const QuotientJobAbi) };
        checked(j, None).map_err(|r| r.name())?;
        // SAFETY: the caller's contract; `checked` has passed.
        let tab = unsafe { Tables::new(j) }.map_err(|r| r.name())?;
        // SAFETY: the caller's contract.
        let t_inv = unsafe { abi::slice(j.t_inv, j.nt_inv) };
        let s = ctx::lock().map_err(|e| err(e).name())?;
        let mut plan = keys::plan(&tab.keys, 1usize << j.ext_k);
        let need = need_of(j, &tab, t_inv, &plan, &s, true);
        drop(s);
        if let Some(l) = plan.lent.take() {
            l.give_back();
        }
        Ok(need.total())
    }

    /// The placement counts of the last quotient served.
    pub fn last_stages() -> Option<QuotientStages> {
        *LAST_STAGES.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// A device-memory limit for the admission (`None`: the free working
    /// set).
    pub fn set_memory_limit(limit: Option<u64>) {
        MEMORY_LIMIT.store(limit.unwrap_or(u64::MAX), Relaxed);
    }

    /// Sets the numerator's target GPU time per command buffer (`None`:
    /// [`TARGET_NANOS`]).
    pub fn set_target_nanos(ns: Option<u64>) {
        TARGET.store(ns.unwrap_or(TARGET_NANOS).max(1), Relaxed);
    }

    /// Sets the dispatch threads ([`threads`]); `None` restores the default.
    pub fn set_threads(t: Option<u32>) {
        THREADS.store(t.map_or(0, |t| normalize_threads(t.into())), Relaxed);
    }

    /// The numerator of a job, all `2^ext_k` values read back, for testing the
    /// kernel. `Err`: the decline reason.
    ///
    /// # Safety
    /// As [`crate::quotient`].
    pub unsafe fn numerator(job: *const c_void) -> Result<Vec<Scalar>, &'static str> {
        if job.is_null() || !crate::device() {
            return Err("no-device");
        }
        // SAFETY: the caller's contract.
        let j = unsafe { &*(job as *const QuotientJobAbi) };
        let mut nu = Vec::new();
        // SAFETY: the caller's contract.
        unsafe { run(j, &mut [], Some(&mut nu)) }.map(|_| nu).map_err(|r| r.name())
    }
}

// ---------------------------------------------------------------------------
// The entry point

/// The first `out.len()` coefficients of the quotient of `job`. `false`:
/// declined, `out` unchanged.
///
/// # Safety
/// `job` is not null and points to a valid `QuotientJobAbi` whose pointers
/// are valid for reads of their counts and not written during the call.
pub(crate) unsafe fn quotient(job: *const c_void, out: &mut [Scalar]) -> bool {
    // SAFETY: the caller's contract.
    let j = unsafe { &*(job as *const QuotientJobAbi) };
    // SAFETY: the caller's contract.
    match unsafe { run(j, out, None) } {
        Ok((ns, _stages)) => {
            #[cfg(any(test, feature = "test-support"))]
            {
                *LAST_STAGES.lock().unwrap_or_else(|e| e.into_inner()) = Some(_stages);
            }
            RUNS.fetch_add(1, Relaxed);
            account::served(Class::Quotient, ns);
            true
        }
        Err(r) => {
            DECLINES.fetch_add(1, Relaxed);
            account::decline(Class::Quotient, r)
        }
    }
}

/// The coset shift is a primitive cube root of unity `z`; the job gives
/// `[z, z^2]` into the coset and `[z^2, z]` out of it.
fn cube_root_shift(zeta: [Scalar; 2], zeta_out: [Scalar; 2]) -> bool {
    let z = zeta[0];
    let z2 = square(&z);
    z != ONE && mul(&z2, &z) == ONE && zeta[1] == z2 && zeta_out == [z2, z]
}

/// The header checks, in the CUDA crate's order and with its reasons.
/// `out_len` must be the job's `len` (`None`: the numerator test path).
fn checked(j: &QuotientJobAbi, out_len: Option<usize>) -> Result<(), Reason> {
    if j.abi != abi::QUOTIENT_ABI || j.k < 1 || j.k > j.ext_k || j.ext_k > MAX_LOG_N {
        return Err(Reason::Shape);
    }
    let scalars = [
        j.zeta[0],
        j.zeta[1],
        j.y,
        j.beta,
        j.gamma,
        j.delta_start,
        j.delta,
        j.divisor,
        j.zeta_out[0],
        j.zeta_out[1],
    ];
    // the shift check multiplies: only on reduced values
    if !field::all_reduced(&scalars[..2]) || !field::all_reduced(&scalars[8..]) {
        return Err(Reason::Shape);
    }
    if !cube_root_shift(j.zeta, j.zeta_out) {
        return Err(Reason::Shape);
    }
    if j.ext_k < crate::thresholds().quotient {
        return Err(Reason::BelowMinK);
    }
    let en = 1usize << j.ext_k;
    let ok = Some(j.extended_omega) == ntt::std_root(j.ext_k, Dir::Forward)
        && Some(j.omega_inv) == ntt::std_root(j.ext_k, Dir::Inverse)
        && out_len.is_none_or(|l| l == j.len)
        && j.len <= en
        && j.nt_inv.is_power_of_two()
        && j.nt_inv <= en
        && j.gates.noutputs == 1
        && j.perm_nsets <= j.perm_ncolumns.max(1)
        && (j.perm_nsets == 0) == (j.perm_ncolumns == 0)
        && j.perm_chunk_len as usize * j.perm_nsets >= j.perm_ncolumns
        && j.nslots <= abi::INDEX_MASK;
    if !ok {
        return Err(Reason::Shape);
    }
    if !field::all_reduced(&scalars) {
        return Err(Reason::Unreduced);
    }
    Ok(())
}

/// Checks that `t_inv` and the by-value transform scalars are reduced. Most
/// were checked by [`checked`]; checking again next to their use keeps a
/// change there from letting an unreduced value reach the device.
fn check_transform_inputs(j: &QuotientJobAbi, t_inv: &[Scalar]) -> Result<(), Reason> {
    if !field::all_reduced(t_inv) {
        return Err(Reason::Unreduced);
    }
    let by_value = [
        j.zeta[0],
        j.zeta[1],
        j.zeta_out[0],
        j.zeta_out[1],
        j.divisor,
        j.extended_omega,
        j.omega_inv,
    ];
    if !field::all_reduced(&by_value) {
        return Err(Reason::Unreduced);
    }
    Ok(())
}

fn err(e: Error) -> Reason {
    Reason::of(&e)
}

// ---------------------------------------------------------------------------
// Host copies

/// Copies `src` into the start of `dst` on several threads, checking every
/// element reduced; `false` when one is not (the copy may be partial).
fn copy_checked(dst: &mut [Scalar], src: &[Scalar]) -> bool {
    const PART: usize = 1 << 16;
    let dst = &mut dst[..src.len()];
    let one = |d: &mut [Scalar], s: &[Scalar]| {
        d.copy_from_slice(s);
        s.iter().all(field::is_reduced)
    };
    if src.len() <= 2 * PART {
        return one(dst, src);
    }
    let threads = std::thread::available_parallelism().map_or(4, |t| t.get()).min(8);
    let per = src.len().div_ceil(threads).max(PART);
    std::thread::scope(|s| {
        let hs: Vec<_> = dst
            .chunks_mut(per)
            .zip(src.chunks(per))
            .map(|(d, c)| s.spawn(move || one(d, c)))
            .collect();
        hs.into_iter().all(|h| h.join().unwrap_or(false))
    })
}

// ---------------------------------------------------------------------------
// The device run

/// One dispatch of the numerator (`quotient::Params` of
/// `shaders/include/quotient.h`).
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
struct Params {
    ext_k: u32,
    log_scale: u32,
    mask: u32,
    row0: u32,
    row_end: u32,
    threads: u32,
    gates: u32,
    perm_nsets: u32,
    perm_ncolumns: u32,
    perm_chunk_len: u32,
    perm_last_rotation: i32,
    perm: u32,
    nlookups: u32,
    lookups: u32,
    ntrash: u32,
    trash: u32,
    l0: u32,
    l_last: u32,
    l_active: u32,
    pad: [u32; 5],
    y: Scalar,
    beta: Scalar,
    gamma: Scalar,
    delta_start: Scalar,
    delta: Scalar,
    omega: Scalar,
    omega_step: Scalar,
}
// SAFETY: `repr(C)`, 24 four-byte fields then seven `[u64; 4]` (offset 96, a
// multiple of 8): no padding, every bit pattern valid.
unsafe impl Pod for Params {}
const _: () = assert!(size_of::<Params>() == 96 + 7 * 32);

/// The quotient of `j` into `out`, or with `numerator` the whole numerator
/// (and `out` untouched). Returns the GPU time and the placement counts.
///
/// # Safety
/// As [`quotient`].
unsafe fn run(
    j: &QuotientJobAbi,
    out: &mut [Scalar],
    numerator: Option<&mut Vec<Scalar>>,
) -> Result<(u64, QuotientStages), Reason> {
    checked(j, numerator.is_none().then_some(out.len()))?;
    // SAFETY: the caller's contract; `checked` has passed.
    let mut tab = unsafe { Tables::new(j)? };
    // SAFETY: the caller's contract.
    let t_inv = unsafe { abi::slice(j.t_inv, j.nt_inv) };
    check_transform_inputs(j, t_inv)?;

    let mut s = ctx::lock().map_err(err)?;
    let info = crate::present().ok_or(Reason::NoDevice)?;
    let mut plan = keys::plan(&tab.keys, 1usize << j.ext_k);
    // every buffer this call can allocate (the sum of `need_bytes`)
    let need = need_of(j, &tab, t_inv, &plan, &s, numerator.is_none());
    let r = if need.fits(info) {
        device_run(j, &mut tab, t_inv, &mut plan, &mut s, info, out, numerator)
    } else {
        Err(Reason::Memory)
    };
    // on every path, before the session ends
    if let Some(l) = plan.lent.take() {
        l.give_back();
    }
    drop(s);
    r
}

/// The device steps of an admitted job.
#[allow(clippy::too_many_arguments)]
fn device_run(
    j: &QuotientJobAbi,
    tab: &mut Tables<'_>,
    t_inv: &[Scalar],
    plan: &mut Plan,
    s: &mut ctx::Session,
    info: &MetalInfo,
    out: &mut [Scalar],
    numerator: Option<&mut Vec<Scalar>>,
) -> Result<(u64, QuotientStages), Reason> {
    let (k, ext_k) = (j.k, j.ext_k);
    let (n, en) = (1usize << k, 1usize << ext_k);
    let ebytes = SCALAR_BYTES << ext_k;
    let threads = stride(ext_k);
    let c: &'static Ctx = s.ctx();
    let mut stages = QuotientStages::default();
    let mut gpu = 0u64;

    // the transform scratch is per-request (it holds witness values; zeroed at
    // the end of the request)
    let tmp_need = ntt::scratch_bytes(ext_k);
    if tmp_need > 0 {
        s.scratch("quotient-tmp", tmp_need).map_err(err)?;
    }
    let ntemp = plan.places.iter().filter(|p| **p == Place::Temp).count();
    let proof_buf = c.alloc_pooled(tab.proof.len().max(1) * ebytes).map_err(err)?;
    let mut src_a = c.alloc_pooled(n * SCALAR_BYTES).map_err(err)?;
    let mut src_b = c.alloc_pooled(n * SCALAR_BYTES).map_err(err)?;
    let mut key_tmp = c.alloc_pooled(ntemp * ebytes).map_err(err)?;
    if let Some(l) = plan.lent.as_mut()
        && l.buf.is_none()
    {
        l.buf = Some(c.alloc_pooled(l.npolys * ebytes).map_err(err)?);
    }
    let tmp_ref: Option<&Buffer> = if tmp_need > 0 {
        s.get_scratch("quotient-tmp")
    } else {
        None
    };
    // bound for an argument that is not read: the transform scratch of a
    // one-pass size, an empty key bank
    let dummy = c.alloc(0).map_err(err)?;
    let tmp = tmp_ref.unwrap_or(&dummy);

    // keys on CPU threads while the device moves the proof's polynomials to
    // the coset; the first proof polynomial is copied first, as the device
    // waits for it
    if let Some(first) = tab.proof.first()
        && !copy_checked(src_a.as_mut_slice::<Scalar>(), first)
    {
        return Err(Reason::Unreduced);
    }
    // the polynomials whose slot this call fills: their digests are computed
    // over the bytes copied into the slot
    let fills: Vec<bool> = (0..tab.keys.len()).map(|i| plan.fills(i)).collect();
    let (key_work, cosets) = std::thread::scope(|sc| {
        let kh = sc.spawn(|| {
            copy_and_hash_keys(
                &tab.keys,
                &plan.places,
                &plan.check,
                &fills,
                &mut plan.lent,
                &mut key_tmp,
                en,
            )
        });
        let cosets = proof_cosets(c, j, &tab.proof, [&mut src_a, &mut src_b], &proof_buf, tmp);
        // a panicked key thread reads as unreduced copies
        (kh.join().unwrap_or_default(), cosets)
    });
    gpu += cosets?;
    if !key_work.reduced {
        return Err(Reason::Unreduced);
    }
    // a digest missing (a digest thread or a slot that failed): not settled
    if key_work.digests.len() != plan.check.len() {
        return Err(Reason::DeviceError);
    }
    ctx::release_later(vec![src_a, src_b]);

    // the digests settle the placement: a stale polynomial is uploaded
    if keys::settle(plan, &tab.keys, &key_work.digests) {
        key_tmp = upload_again(c, info, &tab.keys, &plan.places, en)?;
    }
    let (bank_of, ntemp) = banks(&plan.places);
    let lagrange = tab.place_keys(&bank_of);
    stages.uploaded_polys = ntemp as u32;
    stages.resident_polys = (plan.places.len() - ntemp) as u32;
    stages.key_copies_made = key_work
        .filled
        .iter()
        .filter(|s| plan.lent.as_ref().is_some_and(|l| l.present[**s]))
        .count() as u32;

    // the numerator, into `nu`
    let nu = c.alloc_pooled(ebytes).map_err(err)?;
    let scratch = c
        .alloc_pooled((j.nslots as usize).max(1) * threads * SCALAR_BYTES)
        .map_err(err)?;
    let words = c.upload(&tab.words).map_err(err)?;
    let unis = if tab.uniforms.is_empty() {
        c.alloc(0)
    } else {
        c.upload(&tab.uniforms)
    }
    .map_err(err)?;
    let key_res: &Buffer = plan.lent.as_ref().and_then(|l| l.buf.as_ref()).unwrap_or(&dummy);
    let key_tmp_b: &Buffer = if ntemp > 0 { &key_tmp } else { &dummy };
    let params = numerator_params(j, tab, lagrange, threads);
    let (ns, runs) = numerator_ranges(
        c,
        [&proof_buf, key_res, key_tmp_b, &words, &unis, &nu, &scratch],
        params,
        tab.cost_per_row,
        en,
        threads,
    )?;
    gpu += ns;
    stages.numerator_runs = runs;
    if let Some(l) = plan.lent.take() {
        l.give_back();
    }
    // zeroed on the CPU in the background while the device divides and
    // transforms; `end_request` waits for it
    ctx::release_later(vec![scratch, proof_buf, key_tmp, words, unis]);

    if let Some(v) = numerator {
        v.clear();
        v.extend_from_slice(&nu.as_slice::<Scalar>()[..en]);
        ctx::release_later(vec![nu]);
        return Ok((gpu, stages));
    }

    // h = nu / t on the coset, then extended_to_coeff, in the inverse
    // transform's command buffers
    let tinv = c.upload(t_inv).map_err(err)?;
    gpu += ntt::divide_extended_to_coeff_dev(
        c,
        &nu,
        tmp,
        ext_k,
        &j.divisor,
        &j.zeta_out,
        &tinv,
        t_inv.len().ilog2(),
    )
    .map_err(err)?;

    // Write `out` last: a panic becomes a decline, which must leave `out`
    // unchanged, so everything that can fail or panic happens first. What
    // follows the copy cannot fail: `ctx::par_copy` and `ctx::release_later`
    // never panic, and the rest only stores counters and takes poison-tolerant
    // locks.
    drop(tinv);
    debug_assert!(plan.lent.is_none());
    let src = &nu.as_slice::<Scalar>()[..out.len()];
    ctx::par_copy(out, src);
    ctx::release_later(vec![nu]);
    Ok((gpu, stages))
}

/// What the key thread of [`device_run`] reports. The default (a panicked
/// thread) reads as unreduced copies.
#[derive(Default)]
struct KeyWork {
    /// The digests of `Plan::check`, in its order; shorter when a digest is
    /// missing.
    digests: Vec<[u8; 32]>,
    /// Whether every polynomial copied was reduced.
    reduced: bool,
    /// The slots of the lent copy filled.
    filled: Vec<usize>,
}

/// The CPU side of the key placement, run while the device builds the proof's
/// cosets: copies `Temp` polynomials into `key_tmp` and `fills` into the lent
/// copy's slots (checking them reduced), and hashes the polynomials of
/// `check`. A filled slot is hashed over the bytes copied into it, so a slot is
/// only marked present at [`keys::settle`] with verified content.
fn copy_and_hash_keys(
    keys: &[&[Scalar]],
    places: &[Place],
    check: &[usize],
    fills: &[bool],
    lent: &mut Option<Lent>,
    key_tmp: &mut Buffer,
    en: usize,
) -> KeyWork {
    let host: Vec<&[Scalar]> = check.iter().filter(|&&i| !fills[i]).map(|&i| keys[i]).collect();
    let (host_digests, reduced, filled) = std::thread::scope(|sc| {
        let dh = sc.spawn(|| keys::digest_many(&host));
        // `key_tmp` holds one coset per `Temp` place, the lent copy one per
        // slot (`keys::plan` places only slots below its `npolys`, and the
        // copy is `npolys` cosets long)
        let tmp = key_tmp.as_mut_slice::<Scalar>();
        // `fills` implies a lent copy, allocated by `device_run`; without one
        // the slot's digest is missing and the call declines
        let mut slots =
            lent.as_mut().and_then(|l| l.buf.as_mut()).map(|b| b.as_mut_slice::<Scalar>());
        let (mut ti, mut reduced, mut filled) = (0, true, Vec::new());
        for (i, (p, pl)) in keys.iter().zip(places).enumerate() {
            match pl {
                Place::Temp => {
                    reduced &= copy_checked(&mut tmp[ti * en..(ti + 1) * en], p);
                    ti += 1;
                }
                Place::Resident(slot) => {
                    if fills[i]
                        && let Some(b) = slots.as_deref_mut()
                    {
                        reduced &= copy_checked(&mut b[slot * en..(slot + 1) * en], p);
                        filled.push(*slot);
                    }
                }
            }
            if !reduced {
                break;
            }
        }
        (dh.join().unwrap_or_default(), reduced, filled)
    });
    if !reduced {
        return KeyWork {
            digests: Vec::new(),
            reduced,
            filled,
        };
    }
    let slot_digests = match lent.as_ref().and_then(|l| l.buf.as_ref()) {
        Some(b) => {
            let b = b.as_slice::<Scalar>();
            let in_slots: Vec<&[Scalar]> =
                filled.iter().map(|s| &b[s * en..(s + 1) * en]).collect();
            keys::digest_many(&in_slots)
        }
        None => Vec::new(),
    };
    // in the order of `check` (both lists follow it)
    let (mut h, mut f) = (host_digests.into_iter(), slot_digests.into_iter());
    let digests: Option<Vec<[u8; 32]>> =
        check.iter().map(|&i| if fills[i] { f.next() } else { h.next() }).collect();
    KeyWork {
        digests: digests.unwrap_or_default(),
        reduced,
        filled,
    }
}

/// Moves the proof's polynomials to the extended coset, polynomial `i` into
/// place `i` of `cosets`. The CPU copies polynomial `i + 1` (checking it
/// reduced) while the device transforms polynomial `i`. Returns the GPU time.
fn proof_cosets(
    c: &Ctx,
    j: &QuotientJobAbi,
    proof: &[&[Scalar]],
    src: [&mut Buffer; 2],
    cosets: &Buffer,
    tmp: &Buffer,
) -> Result<u64, Reason> {
    let [src_a, src_b] = src;
    let (k, ext_k) = (j.k, j.ext_k);
    let ebytes = SCALAR_BYTES << ext_k;
    let mut ns = 0;
    for i in 0..proof.len() {
        let (cur, next) = if i % 2 == 0 {
            (&*src_a, &mut *src_b)
        } else {
            (&*src_b, &mut *src_a)
        };
        let following = proof.get(i + 1).copied();
        let (r, copied) = std::thread::scope(|sc| {
            let h = following.map(|f| sc.spawn(move || copy_checked(next.as_mut_slice(), f)));
            let r =
                ntt::coeff_to_extended_dev_at(c, cur, cosets, i * ebytes, tmp, k, ext_k, &j.zeta);
            (r, h.is_none_or(|h| h.join().unwrap_or(false)))
        });
        ns += r.map_err(err)?;
        if !copied {
            return Err(Reason::Unreduced);
        }
    }
    Ok(ns)
}

/// The uploads again after [`keys::settle`] moved a stale polynomial out of
/// its slot. The call's other buffers already exist, so this one is held to
/// the limits alone.
fn upload_again(
    c: &Ctx,
    info: &MetalInfo,
    keys: &[&[Scalar]],
    places: &[Place],
    en: usize,
) -> Result<Buffer, Reason> {
    let (_, nt) = banks(places);
    let bytes = nt * en * SCALAR_BYTES;
    if bytes as u64 > memory_limit() || bytes as u64 > info.max_buffer_length {
        return Err(Reason::Memory);
    }
    let mut kt = c.alloc_pooled(bytes).map_err(err)?;
    let ks = kt.as_mut_slice::<Scalar>();
    let temps = keys.iter().zip(places).filter(|(_, pl)| **pl == Place::Temp);
    // `kt` holds one coset per `Temp` place
    for (ti, (p, _)) in temps.enumerate() {
        if !copy_checked(&mut ks[ti * en..(ti + 1) * en], p) {
            return Err(Reason::Unreduced);
        }
    }
    Ok(kt)
}

/// The bank and index of each proving-key polynomial, and the number of
/// uploaded ones.
fn banks(places: &[Place]) -> (Vec<(u32, usize)>, usize) {
    let mut ti = 0;
    let bank_of = places
        .iter()
        .map(|p| match p {
            Place::Resident(slot) => (tables::BANK_KEY_RES, *slot),
            Place::Temp => {
                ti += 1;
                (tables::BANK_KEY_TMP, ti - 1)
            }
        })
        .collect();
    (bank_of, ti)
}

/// The dispatch parameters of the numerator, but for the row range.
fn numerator_params(
    j: &QuotientJobAbi,
    tab: &Tables<'_>,
    lagrange: [u32; 3],
    threads: usize,
) -> Params {
    let omega = j.extended_omega;
    Params {
        ext_k: j.ext_k,
        log_scale: j.ext_k - j.k,
        mask: ((1usize << j.ext_k) - 1) as u32,
        threads: threads as u32,
        gates: tab.gates,
        perm_nsets: j.perm_nsets as u32,
        perm_ncolumns: j.perm_ncolumns as u32,
        perm_chunk_len: j.perm_chunk_len,
        perm_last_rotation: j.perm_last_rotation,
        perm: tab.perm,
        nlookups: j.nlookups as u32,
        lookups: tab.lookups,
        ntrash: j.ntrash as u32,
        trash: tab.trash,
        l0: lagrange[0],
        l_last: lagrange[1],
        l_active: lagrange[2],
        y: j.y,
        beta: j.beta,
        gamma: j.gamma,
        delta_start: j.delta_start,
        delta: j.delta,
        omega,
        omega_step: pow(&omega, threads as u64),
        ..Default::default()
    }
}

/// The numerator over `en` rows, one command buffer per row range. The first
/// range is sized from an estimate, the next ones from the measured time per
/// row. Returns the GPU time and the command buffers.
fn numerator_ranges(
    c: &Ctx,
    bufs: [&Buffer; 7],
    mut p: Params,
    cost_per_row: u64,
    en: usize,
    threads: usize,
) -> Result<(u64, u32), Reason> {
    let cost = cost_per_row.max(1) + 8;
    let target = TARGET.load(Relaxed);
    let mut rows = ((target / 2) / cost).max(threads as u64) as usize;
    let (mut row0, mut total, mut runs) = (0usize, 0u64, 0u32);
    while row0 < en {
        let rows_now = rows.min(en - row0).div_ceil(threads) * threads;
        let end = (row0 + rows_now).min(en);
        p.row0 = row0 as u32;
        p.row_end = end as u32;
        let disp = threads.min(end - row0);
        let ns = c
            .run(|cmd| {
                cmd.dispatch(
                    "quotient_numerator",
                    disp,
                    &[
                        Arg::Buffer(bufs[0]),
                        Arg::Buffer(bufs[1]),
                        Arg::Buffer(bufs[2]),
                        Arg::Buffer(bufs[3]),
                        Arg::Buffer(bufs[4]),
                        Arg::Buffer(bufs[5]),
                        Arg::Buffer(bufs[6]),
                        Arg::value(&p),
                    ],
                )
            })
            .map_err(err)?
            .1;
        total += ns;
        runs += 1;
        let per_row = (ns as f64 / (end - row0) as f64).max(0.01);
        let want = (target as f64 / per_row) as usize;
        rows = want.clamp(threads, rows.saturating_mul(8).max(threads));
        row0 = end;
    }
    Ok((total, runs))
}
