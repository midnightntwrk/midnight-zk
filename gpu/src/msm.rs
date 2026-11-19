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

//! BLS12-381 G1 MSM on the device (sppark Pippenger) with registered base
//! tables.
//!
//! An MSM on a slice registered by a live [`SrsHandle`], or on a prefix of
//! one (same start address, shorter), is served from the table's device
//! context; any other slice takes the one-shot path (a temporary context,
//! nothing cached). A registered table serves only while the caller's slice
//! still has the registered points: every point of the caller's slice is
//! compared with the registered point at its index at every lookup, in every
//! build; a slice that fails the check drops its table and takes the one-shot
//! path.
//!
//! Skew mask: sppark accumulates each bucket in one thread, so a non-zero
//! scalar repeated many times sends most points of a window to one bucket.
//! The MSM is therefore computed as `MSM(s + r) - MSM(r)` for a fixed
//! pseudo-random public vector `r` (a function of the length only), so no
//! bucket is hot whatever the witness repeats. `MSM(r)` is computed once per
//! table and length. The result is the same group element. No statistic of
//! the scalars is computed, logged or branched on.

use std::{
    collections::HashMap,
    sync::{
        Mutex,
        atomic::{AtomicU64, Ordering::Relaxed},
    },
};

use crate::{G1AffineLimbs, G1JacobianLimbs, Scalar, field, ident};

/// A registered table: the host copy of the points (kept while the handle
/// lives), the device context (made at the first MSM, freed at the end of a
/// request), the mask MSMs by length.
struct Table {
    id: u64,
    digest: [u8; 32],
    host: Vec<G1AffineLimbs>,
    dev: usize,
    masks: HashMap<usize, G1JacobianLimbs>,
}

/// Tables keyed by (address, length) of the registered slice.
static TABLES: Mutex<Option<HashMap<(usize, usize), Table>>> = Mutex::new(None);
static NEXT_ID: AtomicU64 = AtomicU64::new(1);
static STALE: AtomicU64 = AtomicU64::new(0);
static UPLOADS: AtomicU64 = AtomicU64::new(0);
static CACHED: AtomicU64 = AtomicU64::new(0);
static ONE_SHOT: AtomicU64 = AtomicU64::new(0);

fn tables() -> std::sync::MutexGuard<'static, Option<HashMap<(usize, usize), Table>>> {
    TABLES.lock().unwrap_or_else(|e| e.into_inner())
}

/// The registration of an SRS base slice. While it lives, the registrant
/// promises to keep the slice alive and unchanged; MSMs on it or on a prefix
/// of it use a device table. Dropping it frees the table.
#[derive(Debug)]
pub struct SrsHandle {
    id: u64,
    key: (usize, usize),
}

impl SrsHandle {
    /// Number of registered points.
    pub fn len(&self) -> usize {
        self.key.1
    }

    /// Whether no point is registered.
    pub fn is_empty(&self) -> bool {
        self.key.1 == 0
    }

    /// Whether `bases` is the registered slice with the registered content
    /// (a full digest).
    pub fn verify(&self, bases: &[G1AffineLimbs]) -> bool {
        let digest = tables()
            .as_ref()
            .and_then(|t| t.get(&self.key))
            .filter(|e| e.id == self.id)
            .map(|e| e.digest);
        digest.is_some_and(|d| {
            (bases.as_ptr() as usize, bases.len()) == self.key
                && ident::digest(ident::bytes_of(bases)) == d
        })
    }
}

// A live registration in the stub or with the actor permanently unavailable.
// The sentinel cannot reach a device.
#[cfg(test)]
pub(crate) fn mark_context_without_actor(handle: &SrsHandle) {
    #[cfg(midnight_gpu_cuda)]
    crate::ffi::tests::seal_absent_actor();
    tables().as_mut().unwrap().get_mut(&handle.key).unwrap().dev = 1;
}

impl Drop for SrsHandle {
    fn drop(&mut self) {
        // Hand off the context while the registry is still locked.
        let mut session = crate::batch::registration();
        let mut t = tables();
        let removed = match t.as_mut() {
            Some(m) if m.get(&self.key).is_some_and(|e| e.id == self.id) => m.remove(&self.key),
            _ => None,
        };
        if let Some(e) = removed {
            crate::batch::RegistrationRelease::Context(e.dev).submit(&mut session);
        }
    }
}

/// Registers a host copy and digest of an SRS base slice. Replacing a live
/// context releases it immediately or at the active session's final boundary.
pub fn register_srs(bases: &[G1AffineLimbs]) -> SrsHandle {
    let key = (bases.as_ptr() as usize, bases.len());
    let id = NEXT_ID.fetch_add(1, Relaxed);
    let t = Table {
        id,
        digest: ident::digest(ident::bytes_of(bases)),
        host: bases.to_vec(),
        dev: 0,
        masks: HashMap::new(),
    };
    // Hand off the old context under the same locks as handle drop.
    let mut session = crate::batch::registration();
    let mut registry = tables();
    let old = registry.get_or_insert_with(HashMap::new).insert(key, t);
    if let Some(old) = old {
        crate::batch::RegistrationRelease::Context(old.dev).submit(&mut session);
    }
    drop(registry);
    SrsHandle { id, key }
}

/// Live registered tables.
pub fn srs_handles() -> usize {
    tables().as_ref().map_or(0, |t| t.len())
}

/// Tables dropped at an MSM because the caller's slice no longer matched.
pub fn srs_stale() -> u64 {
    STALE.load(Relaxed)
}

/// (MSMs served from a registered table, one-shot MSMs, table uploads)
/// since process start.
pub fn msm_counts() -> (u64, u64, u64) {
    (
        CACHED.load(Relaxed),
        ONE_SHOT.load(Relaxed),
        UPLOADS.load(Relaxed),
    )
}

#[cfg(test)]
std::thread_local! {
    // A test can observe whether a free starts while the registry is locked.
    static FREE_OBSERVER: std::cell::Cell<Option<fn()>> = const { std::cell::Cell::new(None) };
}

pub(crate) fn free_context(dev: usize, entry: crate::batch::Entry) -> bool {
    #[cfg(test)]
    if let Some(observe) = FREE_OBSERVER.get() {
        observe();
    }
    // No device context to free.
    if dev == 0 {
        return false;
    }
    #[cfg(midnight_gpu_cuda)]
    if let Some(freed) = crate::ffi::call_live(move || {
        #[cfg(all(test, feature = "test-fault"))]
        tests::CONTEXT_FREES.fetch_add(1, Relaxed);
        // SAFETY: a live context of ours, freed once. The core quarantines a failed
        // wipe.
        if unsafe { crate::ffi::mgpu_msm_ctx_free(dev as *mut std::ffi::c_void) } != 0 {
            crate::diag!(
                "midnight-gpu: MSM context release failed: {}",
                crate::ffi::last_error()
            );
            return false;
        }
        true
    }) {
        // The core already counted any failure reported by the owner.
        return freed;
    }
    // `call_live` did not run: the device was retired. The context went
    // with the reset context and freeing it would call through CUDA
    // (making a fresh context), so the host object is leaked instead.
    // During ordinary proving a retired device is not an unconfirmed
    // release: the teardown accounted for what it took.
    if entry == crate::batch::Entry::Ordinary && !crate::teardown::device_disabled() {
        crate::wipe::note_erasure_failure();
    }
    false
}

/// Frees the device context of every registered table (the host points and
/// the mask MSMs stay). Called at the end of a request: a context holds the
/// bucket sums of its last MSM. Returns the confirmed free count and whether
/// any live context lacked a release acknowledgment.
pub(crate) fn evict_contexts(entry: crate::batch::Entry) -> (u64, bool) {
    let mut t = tables();
    let mut freed = 0u64;
    let mut unconfirmed = false;
    for e in t.iter_mut().flat_map(|m| m.values_mut()) {
        let dev = std::mem::take(&mut e.dev);
        if dev != 0 {
            if free_context(dev, entry) {
                freed += 1;
            } else if !crate::teardown::device_disabled() {
                unconfirmed = true;
            }
        }
    }
    (freed, unconfirmed)
}

/// The public mask vector of length `n`: splitmix64 words, top limb below
/// 2^61, so every element is reduced; used as Montgomery limbs as they are.
fn mask_vector(n: usize) -> Vec<Scalar> {
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = || {
        x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = x;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    (0..n).map(|_| [next(), next(), next(), next() >> 3]).collect()
}

/// The table that serves an MSM of `m` scalars on the slice `key`: the exact
/// entry, else the shortest live entry at the same address that is longer.
fn table_for(
    t: &mut HashMap<(usize, usize), Table>,
    key: (usize, usize),
    m: usize,
) -> Option<(usize, usize)> {
    if m > key.1 {
        return None;
    }
    if t.contains_key(&key) {
        return Some(key);
    }
    t.keys().filter(|k| k.0 == key.0 && k.1 > key.1).min_by_key(|k| k.1).copied()
}

/// `sum scalars[i] * bases[i]` on the device (see the module text).
#[cfg(midnight_gpu_cuda)]
pub(crate) fn msm_g1(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
    entry: crate::batch::Entry,
) -> Result<Option<G1JacobianLimbs>, crate::ffi::CallError> {
    let key = (bases.as_ptr() as usize, bases.len());
    let n = scalars.len();
    let mut guard = tables();
    if let Some(t) = guard.as_mut() {
        while let Some(tk) = table_for(t, key, n).filter(|tk| !ident::serves(&t[tk].host, bases)) {
            STALE.fetch_add(1, Relaxed);
            crate::diag!(
                "midnight-gpu: msm: a registered SRS slice changed under its handle; its table is dropped"
            );
            if let Some(e) = t.remove(&tk)
                && e.dev != 0
                && !entry.free_context(e.dev)
                && entry == crate::batch::Entry::Batch
            {
                return Ok(None);
            }
        }
        if let Some(tk) = table_for(t, key, n) {
            let entry = t.get_mut(&tk).unwrap();
            // One exclusive actor request (table upload if needed,
            // then the masked MSM). The `TABLES` guard stays with
            // this caller for the whole request, as before.
            return crate::ffi::call_result(|| {
                if entry.dev == 0 {
                    crate::xfer::note_h2d(entry.host.len() * 96);
                    // SAFETY: the host points live in the entry for the call.
                    let ctx = unsafe {
                        crate::ffi::mgpu_msm_ctx_new(
                            entry.host.as_ptr() as *const std::ffi::c_void,
                            entry.host.len(),
                        )
                    };
                    if ctx.is_null() {
                        crate::diag!("midnight-gpu: msm table: {}", crate::ffi::last_error());
                        return None;
                    }
                    UPLOADS.fetch_add(1, Relaxed);
                    entry.dev = ctx as usize;
                }
                CACHED.fetch_add(1, Relaxed);
                masked(
                    entry.dev as *mut std::ffi::c_void,
                    scalars,
                    &mut entry.masks,
                )
            });
        }
    }
    drop(guard);
    ONE_SHOT.fetch_add(1, Relaxed);
    crate::ffi::call_result(|| {
        crate::xfer::note_h2d(n * 96);
        // SAFETY: `bases` holds at least `n` points (checked by the caller).
        let ctx =
            unsafe { crate::ffi::mgpu_msm_ctx_new(bases.as_ptr() as *const std::ffi::c_void, n) };
        if ctx.is_null() {
            crate::diag!(
                "midnight-gpu: msm one-shot table: {}",
                crate::ffi::last_error()
            );
            return None;
        }
        let mut owner = TemporaryContext {
            dev: ctx as usize,
            entry,
            count_batch_free: false,
        };
        let result = masked(ctx, scalars, &mut HashMap::new());
        owner.count_batch_free = entry == crate::batch::Entry::Batch && result.is_some();
        result
    })
}

/// A one-shot context whose stream must be settled before its destructor runs.
#[cfg(any(test, midnight_gpu_cuda))]
struct TemporaryContext {
    dev: usize,
    entry: crate::batch::Entry,
    count_batch_free: bool,
}

#[cfg(any(test, midnight_gpu_cuda))]
impl Drop for TemporaryContext {
    fn drop(&mut self) {
        crate::teardown::check_drains();
        if self.entry.free_context(self.dev) && self.count_batch_free {
            crate::batch::count_evictions(1);
        }
    }
}

/// The masked MSM on the context `ctx` (on the actor thread).
#[cfg(midnight_gpu_cuda)]
fn masked(
    ctx: *mut std::ffi::c_void,
    scalars: &[Scalar],
    masks: &mut HashMap<usize, G1JacobianLimbs>,
) -> Option<G1JacobianLimbs> {
    #[cfg(all(test, feature = "test-fault"))]
    if tests::PANIC_IN_MSM.swap(false, Relaxed) {
        panic!("MSM interrupted");
    }
    let n = scalars.len();
    let r = mask_vector(n);
    let rr = match masks.get(&n) {
        Some(rr) => *rr,
        None => {
            let rr = run(ctx, &r)?;
            masks.insert(n, rr);
            rr
        }
    };
    // the masked scalars are the witness scalars plus a public vector: zeroed
    // on every exit
    let s = crate::wipe::Wiped::new(
        scalars.iter().zip(&r).map(|(a, b)| field::add(a, b)).collect::<Vec<Scalar>>(),
    );
    let got = run(ctx, &s);
    drop(s);
    Some(sub_points(&got?, &rr))
}

/// Test only: two unmasked MSMs on one context over `bases` (the second
/// reuses the first's bucket blob), with the context's bucket records read
/// back after each. Returns the records after the first and after the
/// second MSM and the 64-bit words per record.
#[cfg(all(midnight_gpu_cuda, feature = "test-fault"))]
pub(crate) fn bucket_probe(
    bases: &[G1AffineLimbs],
    first: &[Scalar],
    second: &[Scalar],
) -> Option<(Vec<u64>, Vec<u64>, usize)> {
    crate::ffi::call(|| {
        // SAFETY: `bases` lives for the call.
        let ctx = unsafe {
            crate::ffi::mgpu_msm_ctx_new(bases.as_ptr() as *const std::ffi::c_void, bases.len())
        };
        if ctx.is_null() {
            return None;
        }
        let read = || -> Option<(Vec<u64>, usize)> {
            let mut w = 0u32;
            // SAFETY: a live context; a null output asks for the sizes.
            let n =
                unsafe { crate::ffi::mgpu_test_ctx_buckets(ctx, std::ptr::null_mut(), 0, &mut w) };
            let mut v = vec![0u64; n.max(0) as usize * w as usize];
            // SAFETY: `v` holds `n * w` words.
            let got =
                unsafe { crate::ffi::mgpu_test_ctx_buckets(ctx, v.as_mut_ptr(), v.len(), &mut w) };
            (n > 0 && got == n).then_some((v, w as usize))
        };
        let _owner = TemporaryContext {
            dev: ctx as usize,
            entry: crate::batch::Entry::Ordinary,
            count_batch_free: false,
        };
        run(ctx, first)?;
        let (a, w) = read()?;
        run(ctx, second)?;
        let (b, _) = read()?;
        Some((a, b, w))
    })
    .flatten()
}

/// One sppark MSM (on the actor thread), with the test faults of its class.
#[cfg(midnight_gpu_cuda)]
fn run(ctx: *mut std::ffi::c_void, s: &[Scalar]) -> Option<G1JacobianLimbs> {
    use crate::fault::{Class, Point, hit};
    if hit(Class::Msm, Point::Upload) {
        return None;
    }
    let mut out = [0u64; 18];
    crate::xfer::note_h2d(s.len() * 32);
    // SAFETY: valid context, output and scalar buffers.
    let rc = unsafe {
        crate::ffi::mgpu_msm_ctx_run(
            ctx,
            out.as_mut_ptr() as *mut std::ffi::c_void,
            s.as_ptr() as *const std::ffi::c_void,
            s.len(),
        )
    };
    if rc != 0 {
        crate::diag!("midnight-gpu: msm: {}", crate::ffi::last_error());
        return None;
    }
    if hit(Class::Msm, Point::Launch) {
        return None;
    }
    Some(out)
}

/// `a - b` in Jacobian limbs.
pub(crate) fn sub_points(a: &G1JacobianLimbs, b: &G1JacobianLimbs) -> G1JacobianLimbs {
    use blst::{blst_fp, blst_p1, blst_p1_add_or_double, blst_p1_cneg};
    let p1 = |l: &G1JacobianLimbs| {
        let fp = |i: usize| blst_fp {
            l: l[6 * i..6 * i + 6].try_into().unwrap(),
        };
        blst_p1 {
            x: fp(0),
            y: fp(1),
            z: fp(2),
        }
    };
    let mut nb = p1(b);
    let mut r = blst_p1::default();
    // SAFETY: valid blst points.
    unsafe {
        blst_p1_cneg(&mut nb, true);
        blst_p1_add_or_double(&mut r, &p1(a), &nb);
    }
    let mut out = [0u64; 18];
    out[..6].copy_from_slice(&r.x.l);
    out[6..12].copy_from_slice(&r.y.l);
    out[12..].copy_from_slice(&r.z.l);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(midnight_gpu_cuda, feature = "test-fault"))]
    pub(super) static CONTEXT_FREES: AtomicU64 = AtomicU64::new(0);

    #[cfg(all(midnight_gpu_cuda, feature = "test-fault"))]
    #[test]
    fn one_shot_unconfirmed_drain_skips_context_free() {
        use group::prime::PrimeCurveAffine;
        use midnight_curves::{Fq, G1Affine};
        use midnight_proofs::gpu::adapter;

        crate::ffi::tests::isolated(|| {
            if !crate::device() {
                eprintln!("skipped: no device");
                return;
            }
            crate::set_min_k(1);
            let bases = vec![G1Affine::generator(); 1 << 14];
            let scalars = vec![Fq::from(1); bases.len()];
            let run = || crate::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases));
            assert!(run().is_some());
            assert_eq!(CONTEXT_FREES.load(Relaxed), 1);
            crate::fault::msm_throw_next(1);
            crate::fault::unconfirm_next_drains(1);
            assert!(run().is_none());
            assert!(crate::teardown::device_disabled());
            assert!(crate::error_drains().1 > 0);
            assert_eq!(CONTEXT_FREES.load(Relaxed), 1);
        });
    }

    #[cfg(all(midnight_gpu_cuda, feature = "test-fault"))]
    pub(super) static PANIC_IN_MSM: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(false);

    #[cfg(all(midnight_gpu_cuda, feature = "test-fault"))]
    #[test]
    fn batch_one_shot_counts_frees_and_latches_actor_panic() {
        use group::prime::PrimeCurveAffine;
        use midnight_curves::{Fq, G1Affine};
        use midnight_proofs::gpu::adapter;

        crate::ffi::tests::isolated(|| {
            if !crate::device() {
                eprintln!("skipped: no device");
                return;
            }
            assert!(crate::set_min_k(14));
            let bases = vec![G1Affine::generator(); 1 << 14];
            let scalars = vec![Fq::from(1); bases.len()];
            let session =
                crate::batch::BatchSession::begin(&midnight_proofs::gpu::batch::BATCH_THREAD)
                    .unwrap();
            session.set_worker(true);
            let run = || {
                crate::batch::isolated_msm_g1(adapter::scalars(&scalars), adapter::affine(&bases))
            };
            assert!(run().is_some());
            assert_eq!(crate::batch::batch_msm_counts(), (1, 1, 0));
            PANIC_IN_MSM.store(true, Relaxed);
            assert!(run().is_none());
            assert_eq!(crate::declines(), vec![("msm", "operation-panic", 1)]);
            assert_eq!(CONTEXT_FREES.load(Relaxed), 2);
            assert_eq!(crate::wipe::erasure_failures(), 0);
            assert!(crate::batch::batch_erasure_failed());
            assert!(run().is_none());
            assert_eq!(crate::batch::batch_msm_counts(), (1, 1, 1));
            assert!(!session.finish());
        });
    }

    #[test]
    fn mask_is_reduced_and_fixed() {
        let a = mask_vector(1000);
        assert!(field::all_reduced(&a));
        assert!(a[..10] == mask_vector(10)[..]);
    }

    #[test]
    fn one_shot_guard_frees_during_unwind() {
        FREE_OBSERVER.set(Some(|| FREE_OBSERVER.set(None)));
        let result = std::panic::catch_unwind(|| {
            let _context = TemporaryContext {
                dev: 0,
                entry: crate::batch::Entry::Ordinary,
                count_batch_free: false,
            };
            panic!("MSM interrupted");
        });
        assert!(result.is_err());
        assert!(FREE_OBSERVER.get().is_none());
    }

    #[test]
    fn ordinary_unconfirmed_releases_reach_request_and_session_boundaries() {
        if crate::batch::tests::in_parent() {
            return;
        }
        use midnight_proofs::gpu::batch::BATCH_THREAD;

        use crate::batch::{BatchSession, Entry, SessionError};

        let bases = [[0; 12]; 2];
        let first = register_srs(&bases[..1]);
        let second = register_srs(&bases[1..]);
        assert!(crate::end_request());
        assert!(BatchSession::begin(&BATCH_THREAD).unwrap().finish());
        mark_context_without_actor(&first);
        mark_context_without_actor(&second);
        assert_eq!(crate::wipe::erasure_failures(), 0);
        crate::evict_tables();
        assert_eq!(crate::wipe::erasure_failures(), 2);
        crate::evict_tables();
        assert_eq!(crate::wipe::erasure_failures(), 2);

        mark_context_without_actor(&first);
        let replacement = register_srs(&bases[..1]);
        assert_eq!(crate::wipe::erasure_failures(), 3);
        drop(first);
        drop(replacement);
        assert_eq!(crate::wipe::erasure_failures(), 3);
        mark_context_without_actor(&second);
        drop(second);
        assert_eq!(crate::wipe::erasure_failures(), 4);

        assert!(
            std::panic::catch_unwind(|| {
                let _context = TemporaryContext {
                    dev: 1,
                    entry: Entry::Ordinary,
                    count_batch_free: false,
                };
                panic!("ordinary MSM interrupted");
            })
            .is_err()
        );
        assert_eq!(crate::wipe::erasure_failures(), 5);
        assert!(!crate::end_request());
        assert_eq!(crate::end_request_report().unwrap_err().erasure_failures, 5);
        assert!(matches!(
            BatchSession::begin(&BATCH_THREAD),
            Err(SessionError::ErasureFailed)
        ));
        assert_eq!(crate::wipe::erasure_failures(), 5);
    }

    #[cfg(not(midnight_gpu_cuda))]
    #[test]
    fn unconfirmed_one_shot_release_latches_even_on_decline() {
        if crate::batch::tests::in_parent() {
            return;
        }
        use crate::batch::{BatchSession, Entry};
        let session = BatchSession::begin(&midnight_proofs::gpu::batch::BATCH_THREAD).unwrap();
        session.set_worker(true);
        for entry in [Entry::Ordinary, Entry::Batch] {
            assert!(!crate::batch::batch_erasure_failed());
            drop(TemporaryContext {
                dev: 1,
                entry,
                count_batch_free: false,
            });
        }
        assert!(crate::batch::batch_erasure_failed());
        assert!(crate::batch::isolated_msm_g1(&[], &[]).is_none());
        assert_eq!(crate::batch::batch_msm_counts(), (0, 0, 1));
        assert!(!session.finish());
    }

    /// Replacing a registration keeps exactly the new table; dropping
    /// the replaced handle does not remove it (the free of a replaced
    /// or dropped table completes under the registry lock).
    #[test]
    fn replace_and_drop_keep_registry_consistent() {
        let bases = vec![[0u64; 12]; 4];
        let before = srs_handles();
        let first = register_srs(&bases);
        assert_eq!(srs_handles(), before + 1);
        fn observe_locked_free() {
            assert!(matches!(
                TABLES.try_lock(),
                Err(std::sync::TryLockError::WouldBlock)
            ));
            FREE_OBSERVER.set(None);
        }
        FREE_OBSERVER.set(Some(observe_locked_free));
        let second = register_srs(&bases);
        assert!(FREE_OBSERVER.get().is_none());
        assert_eq!(srs_handles(), before + 1, "replacement keeps one table");
        drop(first);
        assert_eq!(
            srs_handles(),
            before + 1,
            "dropping the replaced handle keeps the new table"
        );
        assert!(second.verify(&bases));
        FREE_OBSERVER.set(Some(observe_locked_free));
        drop(second);
        assert!(FREE_OBSERVER.get().is_none());
        assert_eq!(srs_handles(), before);
    }
}
