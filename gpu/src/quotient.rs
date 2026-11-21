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

//! The quotient on the device, and the resident proving-key copies.
//!
//! [`quotient`] takes the job of the `midnight_proofs::gpu` quotient hook
//! ([`crate::abi::QuotientJobAbi`]): it moves the proof's polynomials to the
//! extended coset on the device, runs the numerator kernel over the job's
//! programs (gates, permutation, LogUp lookups, trash), divides by the
//! vanishing polynomial, transforms back and reads the first `len`
//! coefficients into the caller's buffer. Every device buffer that held a
//! witness-dependent value is zeroed before it is freed. Any shape it does
//! not take, any device error and any armed fault declines: the caller's
//! buffer is then unchanged and the prover computes the quotient on the CPU.
//!
//! Proving-key polynomials (extended cosets) registered with
//! [`register_key`] get a device copy at their first quotient of a request.
//! By default the copies are freed at the end of the request
//! ([`crate::end_request`]); with [`set_keep_resident`] (or
//! `MIDNIGHT_GPU_KEEP_KEYS=1`) they stay while their [`KeyHandle`] lives. A
//! copy is served only after the polynomial's full digest matched the
//! registration in the current request. Other polynomials are uploaded for
//! the call.

use std::{
    collections::HashMap,
    sync::{
        Mutex,
        atomic::{AtomicU64, Ordering::Relaxed},
    },
};

use crate::{Scalar, ident};

/// A registered proving-key polynomial: its digest (the stale check), the
/// request in which its content last matched the digest, and its device copy
/// once a quotient used it.
struct Key {
    id: u64,
    digest: [u8; 32],
    #[cfg_attr(not(midnight_gpu_cuda), allow(dead_code))]
    seen: u64,
    #[cfg(midnight_gpu_cuda)]
    dev: Option<crate::ffi::DevBuf>,
}

/// The current request ([`crate::begin_request`] increments it).
static REQ_EPOCH: AtomicU64 = AtomicU64::new(1);
static KEEP: std::sync::OnceLock<std::sync::atomic::AtomicBool> = std::sync::OnceLock::new();

fn keep() -> &'static std::sync::atomic::AtomicBool {
    KEEP.get_or_init(|| {
        std::sync::atomic::AtomicBool::new(
            std::env::var("MIDNIGHT_GPU_KEEP_KEYS").as_deref() == Ok("1"),
        )
    })
}

/// Whether the device copies of registered proving-key polynomials stay
/// after a request (default `false`, or `MIDNIGHT_GPU_KEEP_KEYS=1`).
pub fn keep_resident() -> bool {
    keep().load(Relaxed)
}

/// Sets [`keep_resident`] when ordinary device work is admitted.
pub fn set_keep_resident(on: bool) {
    let Some(_gate) = crate::batch::admit_ordinary("mode") else {
        return;
    };
    keep().store(on, Relaxed);
}

pub(crate) fn next_request() {
    REQ_EPOCH.fetch_add(1, Relaxed);
}

/// Frees every device copy of a registered polynomial (the registrations
/// stay; the next quotient uploads them again). Returns the bytes freed,
/// or zero when a batch holds the admission gate.
pub fn evict_key_copies() -> u64 {
    let Some(_gate) = crate::batch::admit_ordinary("eviction") else {
        return 0;
    };
    evict_key_copies_admitted()
}

pub(crate) fn evict_key_copies_admitted() -> u64 {
    #[cfg(midnight_gpu_cuda)]
    {
        if crate::teardown::device_disabled() {
            // Their device pointers went with the reset context: no
            // copy is dropped through CUDA now.
            return 0;
        }
        // No device lock is taken: each dropped copy's release is
        // an actor request, queued after any quotient that still
        // uses its address.
        let mut copies = Vec::new();
        if let Some(m) = keys().as_mut() {
            copies.extend(m.values_mut().filter_map(|entry| entry.dev.take()));
        }
        copies.iter().map(|copy| copy.bytes as u64).sum()
    }
    #[cfg(not(midnight_gpu_cuda))]
    0
}

static KEYS: Mutex<Option<HashMap<(usize, usize), Key>>> = Mutex::new(None);
static NEXT_KEY: AtomicU64 = AtomicU64::new(1);
static KEY_STALE: AtomicU64 = AtomicU64::new(0);
static RUNS: AtomicU64 = AtomicU64::new(0);
static DECLINES: AtomicU64 = AtomicU64::new(0);

fn keys() -> std::sync::MutexGuard<'static, Option<HashMap<(usize, usize), Key>>> {
    KEYS.lock().unwrap_or_else(|e| e.into_inner())
}

/// The registration of proving-key polynomials (extended cosets, as
/// `midnight_proofs::plonk::ProvingKey::gpu_resident_polys` lists them).
/// While it lives the registrant keeps them alive and unchanged; the device
/// copies are made at the first quotient and freed when it is dropped.
#[derive(Debug)]
pub struct KeyHandle {
    id: u64,
    keys: Vec<(usize, usize)>,
}

impl KeyHandle {
    /// Whether every registered polynomial still has its registered content
    /// (full digests).
    pub fn verify(&self, polys: &[&[Scalar]]) -> bool {
        let k = keys();
        polys.len() == self.keys.len()
            && polys.iter().zip(&self.keys).all(|(p, key)| {
                (p.as_ptr() as usize, p.len()) == *key
                    && k.as_ref().and_then(|m| m.get(key)).is_some_and(|e| {
                        e.id == self.id && e.digest == ident::digest(ident::bytes_of(p))
                    })
            })
    }
}

impl Drop for KeyHandle {
    fn drop(&mut self) {
        let mut session = crate::batch::registration();
        // Move the copies out before submitting or deferring their release.
        let mut removed = Vec::with_capacity(self.keys.len());
        if let Some(m) = keys().as_mut() {
            for key in &self.keys {
                if m.get(key).is_some_and(|e| e.id == self.id) {
                    removed.extend(m.remove(key));
                }
            }
        }
        release_copies(removed, &mut session);
    }
}

fn release_copies(keys: Vec<Key>, session: &mut Option<crate::batch::SessionState>) {
    #[cfg(midnight_gpu_cuda)]
    for buffer in keys.into_iter().filter_map(|key| key.dev) {
        crate::batch::RegistrationRelease::Key(buffer).submit(session);
    }
    #[cfg(not(midnight_gpu_cuda))]
    let _ = (keys, session);
}

/// Registers proving-key polynomials by their host digests. Replacing a
/// registration releases its previous device copy after unlocking the registry,
/// at the final boundary if a session is active.
pub fn register_key(polys: &[&[Scalar]]) -> KeyHandle {
    let id = NEXT_KEY.fetch_add(1, Relaxed);
    // Finish fallible host work before displacing any live buffer. A
    // hashing worker can unwind if the system cannot start a thread.
    let entries: Vec<_> = polys
        .iter()
        .map(|p| {
            (
                (p.as_ptr() as usize, p.len()),
                ident::digest(ident::bytes_of(p)),
            )
        })
        .collect();
    let mut session = crate::batch::registration();
    let mut replaced = Vec::with_capacity(polys.len());
    let mut k = keys();
    let m = k.get_or_insert_with(HashMap::new);
    let mut ks = Vec::with_capacity(polys.len());
    m.reserve(entries.len());
    for (key, digest) in entries {
        replaced.extend(m.insert(
            key,
            Key {
                id,
                digest,
                seen: REQ_EPOCH.load(Relaxed),
                #[cfg(midnight_gpu_cuda)]
                dev: None,
            },
        ));
        ks.push(key);
    }
    drop(k);
    release_copies(replaced, &mut session);
    KeyHandle { id, keys: ks }
}

/// Registered polynomials now.
pub fn keys_registered() -> usize {
    keys().as_ref().map_or(0, |m| m.len())
}

/// Registered polynomials dropped at a quotient because their content changed.
pub fn key_stale() -> u64 {
    KEY_STALE.load(Relaxed)
}

/// (quotients computed on the device, quotient jobs declined) since process
/// start.
pub fn quotient_counts() -> (u64, u64) {
    (RUNS.load(Relaxed), DECLINES.load(Relaxed))
}

/// The grid threads of the quotient kernel: `MIDNIGHT_GPU_QUOTIENT_THREADS`,
/// else 512 per multiprocessor; a multiple of 256 in `[256, 2^24]`.
pub fn grid_threads() -> u64 {
    let env = std::env::var("MIDNIGHT_GPU_QUOTIENT_THREADS").ok();
    let sm = crate::present().map(|i| i.sm_count as u64);
    normalize_threads(env.as_deref(), sm)
}

/// See [`grid_threads`].
pub fn normalize_threads(env: Option<&str>, sm: Option<u64>) -> u64 {
    let t = env
        .and_then(|e| e.trim().parse::<u64>().ok())
        .unwrap_or_else(|| sm.unwrap_or(64) * 512);
    (t / 256 * 256).clamp(256, 1 << 24)
}

/// The quotient of the job at `job` into `out` (see the module text).
///
/// # Safety
/// `job` points to a [`crate::abi::QuotientJobAbi`] whose pointers and counts
/// are valid for the call, as `midnight_proofs::gpu` passes it.
pub unsafe fn quotient(job: *const std::ffi::c_void, out: &mut [Scalar]) -> bool {
    let Some(_gate) = crate::batch::admit_ordinary("quotient") else {
        return false;
    };
    // SAFETY: the caller keeps the job and its buffers valid for the call.
    unsafe { quotient_admitted(job, out, crate::batch::Entry::Ordinary) }
}

/// [`quotient`] after admission; `entry` names the admission that was taken.
///
/// # Safety
/// The contract of [`quotient`]: `job` points to a
/// [`crate::abi::QuotientJobAbi`] whose pointers and counts are valid for
/// the call.
pub(crate) unsafe fn quotient_admitted(
    job: *const std::ffi::c_void,
    out: &mut [Scalar],
    entry: crate::batch::Entry,
) -> bool {
    if job.is_null() {
        return crate::decline("quotient", "shape");
    }
    // the header checks on host metadata, before the device check: the same
    // reasons with and without the CUDA core
    // SAFETY: the caller's contract.
    if let Err(why) = admit(unsafe { &*(job as *const crate::abi::QuotientJobAbi) }) {
        return crate::decline("quotient", why);
    }
    if crate::teardown::device_disabled() {
        return crate::teardown::note_decline("quotient");
    }
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() {
            return crate::decline("quotient", "no-device");
        }
        // SAFETY: the caller's contract.
        let ok = device::run(
            unsafe { &*(job as *const crate::abi::QuotientJobAbi) },
            out,
            entry,
        );
        if ok {
            RUNS.fetch_add(1, Relaxed);
        } else {
            DECLINES.fetch_add(1, Relaxed);
        }
        ok
    }
    #[cfg(not(midnight_gpu_cuda))]
    {
        let _ = (out, entry);
        crate::decline("quotient", "no-device")
    }
}

/// The job's header on host metadata alone, in the order of the full check:
/// the ABI version and sizes (`shape`), the coset shift (`shape`, at every
/// size), then the minimum size (`below-min-k`).
fn admit(j: &crate::abi::QuotientJobAbi) -> Result<(), &'static str> {
    // k = 0 (one row) is a shape the coset kernel does not take: declined
    // here, before the size gate and the device
    if j.abi != crate::abi::QUOTIENT_ABI || j.k < 1 || j.k > j.ext_k || j.ext_k > crate::MAX_EXT_K {
        return Err("shape");
    }
    if !cube_root_shift(j.zeta, j.zeta_out) {
        return Err("shape");
    }
    if j.ext_k < crate::min_k() {
        return Err("below-min-k");
    }
    Ok(())
}

#[cfg(midnight_gpu_cuda)]
mod device {
    use std::{collections::HashMap, ffi::c_void};

    use super::{KEY_STALE, keys};
    use crate::{
        Scalar,
        abi::{
            COLUMN_ADVICE, COLUMN_FIXED, DeviceOp, DeviceRead, INDEX_MASK, OP_MUL_ADD, ProgramAbi,
            QuotientJobAbi, TAG_READ, TAG_SLOT, TAG_UNIFORM, slice,
        },
        fault::{Class, Point, hit},
        ffi::{self, DevBuf},
        field, ident,
    };

    /// A program of the kernel (device pointers).
    #[repr(C)]
    #[derive(Clone, Copy, Default)]
    struct DProgram {
        ops: u64,
        reads: u64,
        uniforms: u64,
        outputs: u64,
        nops: u32,
        nreads: u32,
        noutputs: u32,
        pad: u32,
    }

    /// The kernel argument (`DJob` of `cuda/quotient.cuh`).
    #[repr(C)]
    #[derive(Default)]
    pub(super) struct DJob {
        out: u64,
        n: u64,
        stride: u64,
        scratch: u64,
        fixed: u64,
        advice: u64,
        instance: u64,
        l0: u64,
        l_last: u64,
        l_active: u64,
        perm_sigma: u64,
        perm_products: u64,
        perm_kind: u64,
        perm_index: u64,
        lookups: u64,
        trash: u64,
        perm_ncolumns: u32,
        perm_nsets: u32,
        perm_chunk_len: u32,
        perm_last_rotation: i32,
        nlookups: u32,
        ntrash: u32,
        log_scale: u32,
        pad: u32,
        gates: DProgram,
        y: Scalar,
        beta: Scalar,
        gamma: Scalar,
        delta_start: Scalar,
        delta: Scalar,
        extended_omega: Scalar,
    }

    /// The tables of a job, packed for one device allocation. A pointer to
    /// another part of the arena is written as its offset and recorded in
    /// `fixups`; the base address is added once the arena is allocated.
    #[derive(Default)]
    struct Arena {
        bytes: Vec<u8>,
        fixups: Vec<usize>,
    }

    /// A pointer field: absolute (a device buffer) or into the arena.
    #[derive(Clone, Copy)]
    enum P {
        Abs(u64),
        Rel(usize),
    }

    impl Arena {
        fn align(&mut self, a: usize) -> usize {
            while !self.bytes.len().is_multiple_of(a) {
                self.bytes.push(0);
            }
            self.bytes.len()
        }

        fn raw<T: Copy>(&mut self, v: &[T], align: usize) -> usize {
            let off = self.align(align);
            self.bytes.extend_from_slice(ident::bytes_of(v));
            off
        }

        fn u32(&mut self, v: u32) {
            self.bytes.extend_from_slice(&v.to_le_bytes());
        }

        fn ptr(&mut self, p: P) {
            match p {
                P::Abs(a) => self.bytes.extend_from_slice(&a.to_le_bytes()),
                P::Rel(o) => {
                    self.fixups.push(self.bytes.len());
                    self.bytes.extend_from_slice(&(o as u64).to_le_bytes());
                }
            }
        }

        fn ptrs(&mut self, v: &[P]) -> usize {
            let off = self.align(8);
            for p in v {
                self.ptr(*p);
            }
            off
        }

        /// A program; returns its fields (pointers relative to the arena).
        fn program(
            &mut self,
            p: &ProgramAbi,
            nslots: u32,
            col_ok: &dyn Fn(u32, u32) -> bool,
        ) -> Result<[usize; 4], &'static str> {
            // SAFETY: the job's contract.
            let (ops, reads, uniforms, outputs) = unsafe {
                (
                    slice(p.ops, p.nops),
                    slice(p.reads, p.nreads),
                    slice(p.uniforms, p.nuniforms),
                    slice(p.outputs, p.noutputs),
                )
            };
            // every operand in range, every slot below the job's slots
            let ok_operand = |o: u32| {
                let i = (o & INDEX_MASK) as usize;
                match o >> 30 {
                    TAG_UNIFORM => i < uniforms.len(),
                    TAG_READ => i < reads.len(),
                    TAG_SLOT => i < nslots as usize,
                    _ => false,
                }
            };
            let ops_ok = ops.iter().all(|op| {
                op.kind <= OP_MUL_ADD
                    && op.dst < nslots
                    && ok_operand(op.a)
                    && ok_operand(op.b)
                    && ok_operand(op.c)
            });
            if !ops_ok
                || !outputs.iter().all(|o| ok_operand(*o))
                || !reads.iter().all(|r| col_ok(r.kind, r.column))
                || p.nslots > nslots
            {
                return Err("shape");
            }
            if !field::all_reduced(uniforms) {
                return Err("unreduced");
            }
            Ok([
                self.raw::<DeviceOp>(ops, 4),
                self.raw::<DeviceRead>(reads, 4),
                self.raw::<Scalar>(uniforms, 32),
                self.raw::<u32>(outputs, 4),
            ])
        }

        /// Writes a `DProgram` at the current (8-aligned) position.
        fn dprogram(&mut self, p: &ProgramAbi, f: [usize; 4]) {
            self.align(8);
            for o in f {
                self.ptr(P::Rel(o));
            }
            self.u32(p.nops as u32);
            self.u32(p.nreads as u32);
            self.u32(p.noutputs as u32);
            self.u32(0);
        }
    }

    /// The device address of a key polynomial (extended coset, `n` values):
    /// its resident copy if registered (made now if needed), else an upload
    /// for this call kept in `temp`.
    fn key_poly(p: *const Scalar, n: usize, temp: &mut Vec<DevBuf>) -> Option<u64> {
        // SAFETY: the job's contract.
        let v = unsafe { slice(p, n) };
        let key = (p as usize, n);
        let mut stale = None;
        let mut k = keys();
        if let Some(m) = k.as_mut()
            && let Some(e) = m.get_mut(&key)
        {
            // the full digest once per request (every serve in a debug build)
            let now = super::REQ_EPOCH.load(std::sync::atomic::Ordering::Relaxed);
            let fresh = (e.seen == now && !cfg!(debug_assertions))
                || e.digest == ident::digest(ident::bytes_of(v));
            if fresh {
                e.seen = now;
            }
            if !fresh {
                KEY_STALE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                crate::diag!(
                    "midnight-gpu: a registered proving-key polynomial changed; its copy is dropped"
                );
                stale = m.remove(&key);
            } else {
                if e.dev.is_none() {
                    let b = DevBuf::new(n * 32, false)?;
                    if !ffi::htod(&b, 0, v) {
                        return None;
                    }
                    e.dev = Some(b);
                }
                return e.dev.as_ref().map(|b| b.addr());
            }
        }
        drop(k);
        drop(stale);
        let b = DevBuf::new(n * 32, false)?;
        if !ffi::htod(&b, 0, v) {
            return None;
        }
        let a = b.addr();
        temp.push(b);
        Some(a)
    }

    /// Checks the job's shape; `Err`: declined, with the reason.
    fn checked(j: &QuotientJobAbi, out_len: usize) -> Result<(usize, usize), &'static str> {
        // an unsupported coset shift is `shape` at every size: it takes
        // precedence over the size gate
        super::admit(j)?;
        let (n, en) = (1usize << j.k, 1usize << j.ext_k);
        let (w, wi) = field::std_root(j.ext_k).ok_or("shape")?;
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
        let ok = j.extended_omega == w
            && j.omega_inv == wi
            && out_len == j.len
            && j.len <= en
            && j.nt_inv.is_power_of_two()
            && j.nt_inv <= en
            && j.gates.noutputs == 1
            && j.perm_nsets <= j.perm_ncolumns.max(1)
            && (j.perm_nsets == 0) == (j.perm_ncolumns == 0)
            && j.perm_chunk_len as usize * j.perm_nsets >= j.perm_ncolumns;
        if !ok {
            return Err("shape");
        }
        if !field::all_reduced(&scalars) {
            return Err("unreduced");
        }
        Ok((n, en))
    }

    /// See [`super::quotient`]. The device part is one exclusive
    /// request to the device-owner actor.
    pub(super) fn run(j: &QuotientJobAbi, out: &mut [Scalar], entry: crate::batch::Entry) -> bool {
        let (n, en) = match checked(j, out.len()) {
            Ok(v) => v,
            Err(why) => return crate::decline("quotient", why),
        };
        // The job header holds raw pointers, so it is not `Send`;
        // its address crosses instead. SAFETY: the caller's
        // contract keeps the job and everything it points to valid
        // for the whole call, and this caller blocks until the
        // actor request has run or was dropped (see `ffi::call`).
        let j_addr = j as *const QuotientJobAbi as usize;
        let result = ffi::call_result(move || {
            // SAFETY: as above.
            let j = unsafe { &*(j_addr as *const QuotientJobAbi) };
            let mut why = "shape";
            let r = run_on_actor(j, out, n, en, &mut why);
            if r.is_none() && why == "device-error" {
                // The core's last error is thread-local: read it
                // here, on the actor thread that made the call.
                crate::diag!("midnight-gpu: quotient: {}", ffi::last_error());
            }
            (r, why)
        });
        finish(result, entry)
    }

    fn finish(
        result: Result<(Option<()>, &'static str), ffi::CallError>,
        entry: crate::batch::Entry,
    ) -> bool {
        let (r, why) = match result {
            Ok(reply) => reply,
            Err(ffi::CallError::Panicked) => return entry.operation_panic("quotient"),
            Err(ffi::CallError::Unavailable) => return crate::teardown::note_decline("quotient"),
        };
        if r.is_none() {
            crate::decline("quotient", why);
        }
        r.is_some()
    }

    #[test]
    fn panicking_quotient_has_its_own_decline() {
        ffi::tests::isolated(|| {
            drop(ffi::tests::empty_key_copy());
            let result = ffi::call_result(|| panic!("test operation"));
            assert!(!finish(result, crate::batch::Entry::Ordinary));
            assert_eq!(crate::declines(), vec![("quotient", "operation-panic", 1)]);
            assert_eq!(crate::teardown::declined_after_teardown(), 0);
            assert!(!crate::batch::batch_erasure_failed());

            let session =
                crate::batch::BatchSession::begin(&midnight_proofs::gpu::batch::BATCH_THREAD)
                    .unwrap();
            struct Payload;
            impl Drop for Payload {
                fn drop(&mut self) {
                    panic!("payload destructor interrupted");
                }
            }
            let result = ffi::call_result(|| std::panic::panic_any(Payload));
            assert!(!finish(result, crate::batch::Entry::Batch));
            assert_eq!(crate::declines(), vec![("quotient", "operation-panic", 2)]);
            assert_eq!(crate::teardown::declined_after_teardown(), 0);
            assert!(crate::batch::batch_erasure_failed());
            assert!(!session.end_wave());
            assert!(!session.finish());
            assert_eq!(ffi::call(ffi::on_actor), Some(true));
        });
    }

    /// The device part of [`run`], on the actor thread; on `None`,
    /// `why` is the reason.
    fn run_on_actor(
        j: &QuotientJobAbi,
        out: &mut [Scalar],
        n: usize,
        en: usize,
        why: &mut &'static str,
    ) -> Option<()> {
        // SAFETY (every `slice` below): the job's contract.
        let advice = unsafe { slice(j.advice, j.nadvice) };
        let instance = unsafe { slice(j.instance, j.ninstance) };
        let fixed = unsafe { slice(j.fixed, j.nfixed) };
        let sigma = unsafe { slice(j.perm_sigma, j.perm_ncolumns) };
        let products = unsafe { slice(j.perm_products, j.perm_nsets) };
        let kinds = unsafe { slice(j.perm_column_kind, j.perm_ncolumns) };
        let index = unsafe { slice(j.perm_column_index, j.perm_ncolumns) };
        let lookups = unsafe { slice(j.lookups, j.nlookups) };
        let trash = unsafe { slice(j.trash, j.ntrash) };
        let t_inv = unsafe { slice(j.t_inv, j.nt_inv) };
        let nslots = j.nslots;

        // columns of the permutation exist
        let col_ok = |kind: u32, c: u32| match kind {
            COLUMN_FIXED => fixed.get(c as usize).is_some_and(|p| !p.is_null()),
            COLUMN_ADVICE => (c as usize) < advice.len(),
            _ => (c as usize) < instance.len(),
        };
        if !kinds.iter().zip(index).all(|(k, c)| col_ok(*k, *c)) {
            return None;
        }
        if !field::all_reduced(t_inv) {
            *why = "unreduced";
            return None;
        }

        // the proof's polynomials, in coefficient form
        let mut proof: Vec<*const Scalar> = Vec::new();
        proof.extend(advice);
        proof.extend(instance);
        proof.extend(products);
        for l in lookups {
            if l.nchunks == 0 {
                return None;
            }
            proof.push(l.aggregator);
            proof.push(l.multiplicities);
            // SAFETY: the job's contract.
            proof.extend(unsafe { slice(l.helpers, l.nchunks) });
        }
        proof.extend(trash.iter().map(|t| t.trash));
        if proof.iter().any(|p| p.is_null()) {
            return None;
        }

        // device memory: the cosets, the numerator, the scratch, key uploads
        let keys = sigma.len() + fixed.iter().filter(|p| !p.is_null()).count() + 3;
        let need = super::need_bytes(j.ext_k, proof.len(), keys, nslots);
        let stride = super::grid_threads().min(((en as u64).div_ceil(256) * 256).max(256));
        *why = "device-error";
        let (free, _) = ffi::mem_info_locked()?;
        *why = "memory";
        let limit = crate::max_device_bytes().unwrap_or(free / 10 * 9);
        if need > limit.min(free) {
            crate::diag!(
                "midnight-gpu: quotient needs {need} device bytes, {} allowed",
                limit.min(free)
            );
            return None;
        }
        *why = "device-error";

        // extended cosets of the proof's polynomials (witness data)
        let mut cosets: HashMap<usize, DevBuf> = HashMap::new();
        if hit(Class::Quotient, Point::Upload) {
            *why = "fault";
            return None;
        }
        for &p in &proof {
            if cosets.contains_key(&(p as usize)) {
                continue;
            }
            // SAFETY: the job's contract: 2^k coefficients.
            let c = unsafe { slice(p, n) };
            if !field::all_reduced(c) {
                *why = "unreduced";
                return None;
            }
            let b = DevBuf::new(en * 32, true)?;
            crate::xfer::note_h2d(n * 32);
            // SAFETY: `c` holds 2^k elements, `b` 2^ext_k.
            let rc = unsafe {
                ffi::mgpu_coeff_to_extended_dev(
                    b.ptr,
                    c.as_ptr() as *const c_void,
                    j.k,
                    j.ext_k,
                    j.zeta.as_ptr() as *const c_void,
                )
            };
            if rc != 0 {
                return None;
            }
            cosets.insert(p as usize, b);
        }
        let coset = |p: *const Scalar| P::Abs(cosets[&(p as usize)].addr());

        // proving-key polynomials (public)
        let mut temp = Vec::new();
        let mut kdev: HashMap<usize, u64> = HashMap::new();
        let mut key = |p: *const Scalar, temp: &mut Vec<DevBuf>| -> Option<u64> {
            if let Some(a) = kdev.get(&(p as usize)) {
                return Some(*a);
            }
            let a = key_poly(p, en, temp)?;
            kdev.insert(p as usize, a);
            Some(a)
        };
        let mut fixed_dev = Vec::with_capacity(fixed.len());
        for &f in fixed {
            fixed_dev.push(P::Abs(if f.is_null() { 0 } else { key(f, &mut temp)? }));
        }
        let mut sigma_dev = Vec::with_capacity(sigma.len());
        for &s in sigma {
            if s.is_null() {
                *why = "shape";
                return None;
            }
            sigma_dev.push(P::Abs(key(s, &mut temp)?));
        }
        if j.l0.is_null() || j.l_last.is_null() || j.l_active.is_null() {
            *why = "shape";
            return None;
        }
        let l0 = key(j.l0, &mut temp)?;
        let l_last = key(j.l_last, &mut temp)?;
        let l_active = key(j.l_active, &mut temp)?;

        // the arena
        let mut a = Arena::default();
        let fixed_t = a.ptrs(&fixed_dev);
        let advice_t = a.ptrs(&advice.iter().map(|p| coset(*p)).collect::<Vec<_>>());
        let instance_t = a.ptrs(&instance.iter().map(|p| coset(*p)).collect::<Vec<_>>());
        let sigma_t = a.ptrs(&sigma_dev);
        let products_t = a.ptrs(&products.iter().map(|p| coset(*p)).collect::<Vec<_>>());
        let kind_t = a.raw(kinds, 4);
        let index_t = a.raw(index, 4);
        let gates_f = a.program(&j.gates, nslots, &col_ok).map_err(|r| *why = r).ok()?;
        let mut lk = Vec::with_capacity(lookups.len());
        for l in lookups {
            // SAFETY: the job's contract.
            let (progs, helpers) =
                unsafe { (slice(l.programs, l.nchunks), slice(l.helpers, l.nchunks)) };
            let mut fs = Vec::with_capacity(progs.len());
            for p in progs {
                if p.noutputs != 4 {
                    *why = "shape";
                    return None;
                }
                fs.push(a.program(p, nslots, &col_ok).map_err(|r| *why = r).ok()?);
            }
            let ps = a.align(8);
            for (p, f) in progs.iter().zip(fs) {
                a.dprogram(p, f);
            }
            let hs = a.ptrs(&helpers.iter().map(|h| coset(*h)).collect::<Vec<_>>());
            lk.push((l, ps, hs));
        }
        let lookups_t = a.align(8);
        for (l, ps, hs) in &lk {
            a.ptr(coset(l.aggregator));
            a.ptr(coset(l.multiplicities));
            a.ptr(P::Rel(*hs));
            a.ptr(P::Rel(*ps));
            a.u32(l.nchunks as u32);
            a.u32(0);
        }
        let mut tf = Vec::with_capacity(trash.len());
        for t in trash {
            if t.program.noutputs != 1
                || fixed.get(t.selector_column as usize).is_none_or(|p| p.is_null())
            {
                *why = "shape";
                return None;
            }
            tf.push(a.program(&t.program, nslots, &col_ok).map_err(|r| *why = r).ok()?);
        }
        let trash_t = a.align(8);
        for (t, f) in trash.iter().zip(tf) {
            a.ptr(coset(t.trash));
            a.dprogram(&t.program, f);
            a.u32(t.selector_column);
            a.u32(0);
        }
        a.align(8);
        let arena = DevBuf::new(a.bytes.len(), false)?;
        let base = arena.addr();
        for &f in &a.fixups {
            let v = u64::from_le_bytes(a.bytes[f..f + 8].try_into().unwrap()) + base;
            a.bytes[f..f + 8].copy_from_slice(&v.to_le_bytes());
        }
        if !ffi::htod(&arena, 0, &a.bytes) {
            return None;
        }
        // the gates program's fields, read back from the arena
        let mut gates = DProgram {
            nops: j.gates.nops as u32,
            nreads: j.gates.nreads as u32,
            noutputs: 1,
            ..Default::default()
        };
        [gates.ops, gates.reads, gates.uniforms, gates.outputs] = gates_f.map(|o| base + o as u64);

        let nu = DevBuf::new(en * 32, true)?;
        let scratch = DevBuf::new((nslots as usize).max(1) * stride as usize * 32, true)?;
        let job = DJob {
            out: nu.addr(),
            n: en as u64,
            stride,
            scratch: scratch.addr(),
            fixed: base + fixed_t as u64,
            advice: base + advice_t as u64,
            instance: base + instance_t as u64,
            l0,
            l_last,
            l_active,
            perm_sigma: base + sigma_t as u64,
            perm_products: base + products_t as u64,
            perm_kind: base + kind_t as u64,
            perm_index: base + index_t as u64,
            lookups: base + lookups_t as u64,
            trash: base + trash_t as u64,
            perm_ncolumns: j.perm_ncolumns as u32,
            perm_nsets: j.perm_nsets as u32,
            perm_chunk_len: j.perm_chunk_len,
            perm_last_rotation: j.perm_last_rotation,
            nlookups: lookups.len() as u32,
            ntrash: trash.len() as u32,
            log_scale: j.ext_k - j.k,
            pad: 0,
            gates,
            y: j.y,
            beta: j.beta,
            gamma: j.gamma,
            delta_start: j.delta_start,
            delta: j.delta,
            extended_omega: j.extended_omega,
        };
        // SAFETY: every address of `job` is a live device buffer of this call.
        if unsafe { ffi::mgpu_quotient_run(&job as *const DJob as *const c_void) } != 0
            || !ffi::sync()
            || hit(Class::Quotient, Point::Launch)
        {
            return None;
        }
        // the proof's cosets are no longer needed
        drop(cosets);
        drop(scratch);

        // h = nu / t on the coset, then extended_to_coeff
        let en_inv = field::invert(&field::from_u64(en as u64))?;
        let post =
            (j.divisor != en_inv).then(|| field::mul(&j.divisor, &field::from_u64(en as u64)));
        // SAFETY: `nu` holds 2^ext_k elements; `t_inv` is a host slice the
        // core copies; the factors are single elements.
        let ok = unsafe {
            ffi::mgpu_mul_periodic_dev(nu.ptr, en, t_inv.as_ptr() as *const c_void, t_inv.len())
                == 0
                && ffi::mgpu_ntt_dev(nu.ptr, j.ext_k, 1) == 0
                && post.is_none_or(|c| {
                    ffi::mgpu_scale_dev(nu.ptr, en, c.as_ptr() as *const c_void) == 0
                })
                && ffi::mgpu_distribute_zeta_dev(nu.ptr, en, j.zeta_out.as_ptr() as *const c_void)
                    == 0
        };
        if !ok || !ffi::sync() || hit(Class::Quotient, Point::Divide) {
            return None;
        }
        if !ffi::dtoh_commit(out, nu.ptr, hit(Class::Quotient, Point::Readback)) {
            return None;
        }
        if !out.is_empty() && hit(Class::Quotient, Point::Corrupt) {
            out[0] = field::add(&out[0], &field::one());
        }
        drop(temp);
        Some(())
    }

    /// The size of the kernel argument agrees with the CUDA core.
    pub(crate) fn layout_ok() -> bool {
        // SAFETY: a constant of the core.
        std::mem::size_of::<DJob>() == unsafe { ffi::mgpu_job_size() }
    }
}

#[cfg(midnight_gpu_cuda)]
pub(crate) use device::layout_ok;

/// The coset shift is a primitive cube root of unity `z` (`z != 1`,
/// `z^3 = 1`), the job gives `[z, z^2]` into the coset and `[z^2, z]` out of
/// it. Any other shift declines (reason `shape`).
fn cube_root_shift(zeta: [Scalar; 2], zeta_out: [Scalar; 2]) -> bool {
    use crate::field;
    let z = zeta[0];
    let z2 = field::square(&z);
    z != field::one() && field::mul(&z2, &z) == field::one() && zeta[1] == z2 && zeta_out == [z2, z]
}

/// The device bytes one quotient job needs, by the arithmetic of the memory
/// check the job passes before it runs: the extended cosets of the proof's
/// polynomials and of the proving-key polynomials it reads, the numerator,
/// and the scratch slots of the evaluator. The arguments are the fields of
/// the job's shape (`midnight_proofs::gpu::QuotientShape`: `ext_k`,
/// `proof_polys`, `key_polys`, `nslots`). The job declines with reason
/// `memory` when this is above `MIDNIGHT_GPU_MAX_BYTES` (default 90% of
/// the free device memory) or the free memory.
pub fn need_bytes(ext_k: u32, proof_polys: usize, key_polys: usize, nslots: u32) -> usize {
    let en = 1usize << ext_k;
    let stride = grid_threads().min(((en as u64).div_ceil(256) * 256).max(256));
    (proof_polys + 1 + key_polys) * en * 32 + nslots as usize * stride as usize * 32
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Only a primitive cube root of unity, given as `[z, z^2]` in and
    /// `[z^2, z]` out, is a shift the device takes.
    #[test]
    fn coset_shift_is_a_primitive_cube_root() {
        use crate::field::{mul, one, square};
        let z = crate::field::primitive_cube_root();
        assert!(z != one() && mul(&square(&z), &z) == one());
        let z2 = square(&z);
        assert!(cube_root_shift([z, z2], [z2, z]));
        assert!(
            cube_root_shift([z2, z], [z, z2]),
            "z^2 is a primitive cube root too"
        );
        assert!(
            !cube_root_shift([one(), one()], [one(), one()]),
            "1 is not primitive"
        );
        let two = crate::field::from_u64(2);
        assert!(!cube_root_shift([two, square(&two)], [square(&two), two]));
        assert!(
            !cube_root_shift([z, z2], [z, z2]),
            "the inverse shift is checked"
        );
    }

    #[test]
    fn threads_normalized() {
        assert_eq!(normalize_threads(None, Some(48)), 48 * 512);
        assert_eq!(normalize_threads(Some("1000"), None), 768);
        assert_eq!(normalize_threads(Some("1"), None), 256);
        assert_eq!(normalize_threads(Some("x"), Some(2)), 1024);
        assert_eq!(normalize_threads(Some("99999999999"), None), 1 << 24);
    }
}

#[cfg(all(test, midnight_gpu_cuda))]
#[test]
fn key_copy_releases_leave_the_registry_unlocked() {
    use std::{
        sync::mpsc,
        time::{Duration, Instant},
    };
    crate::ffi::tests::isolated(|| {
        for operation in 0..3 {
            let poly = [[0; 4]; 1];
            let handle = register_key(&[&poly]);
            let key = handle.keys[0];
            keys().as_mut().unwrap().get_mut(&key).unwrap().dev =
                Some(crate::ffi::tests::empty_key_copy());
            let (ready, entered) = mpsc::channel();
            let caller = std::thread::spawn(move || {
                crate::ffi::call(|| {
                    assert!(crate::ffi::on_actor());
                    ready.send(()).unwrap();
                    let deadline = Instant::now() + Duration::from_secs(3);
                    loop {
                        if KEYS.try_lock().is_ok_and(|registry| {
                            registry
                                .as_ref()
                                .and_then(|m| m.get(&key))
                                .is_none_or(|entry| entry.dev.is_none())
                        }) {
                            return true;
                        }
                        if Instant::now() >= deadline {
                            return false;
                        }
                        std::thread::yield_now();
                    }
                })
            });
            entered.recv_timeout(Duration::from_secs(3)).expect("owner did not start");
            match operation {
                0 => {
                    assert_eq!(evict_key_copies(), 32);
                }
                1 => drop(handle),
                _ => drop(register_key(&[&poly])),
            }
            assert_eq!(
                caller.join().unwrap(),
                Some(true),
                "registry locked across release"
            );
        }
    });
}

#[cfg(all(test, midnight_gpu_cuda))]
#[test]
fn displaced_key_copies_count_once_on_session_unwind() {
    crate::ffi::tests::isolated(|| {
        let poly = [[0; 4]; 1];
        let first = register_key(&[&poly]);
        let key = first.keys[0];
        let session =
            crate::batch::BatchSession::begin(&midnight_proofs::gpu::batch::BATCH_THREAD).unwrap();
        keys().as_mut().unwrap().get_mut(&key).unwrap().dev =
            Some(crate::ffi::tests::empty_key_copy());
        let replacement = register_key(&[&poly, &poly]);
        drop(first);
        assert!(replacement.verify(&[&poly, &poly]));
        keys().as_mut().unwrap().get_mut(&key).unwrap().dev =
            Some(crate::ffi::tests::empty_key_copy());
        drop(replacement);
        assert!(session.end_wave());
        assert_eq!(crate::batch::deferred_releases(), 0);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
            let _session = session;
            panic!("leave session");
        }));
        assert!(result.is_err());
        assert_eq!(crate::batch::deferred_releases(), 2);
        assert!(!crate::batch::batch_erasure_failed());
    });
}
