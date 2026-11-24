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

//! Erasure of every buffer of this crate that held witness-dependent values.
//!
//! - Device buffers of a call (transform scratch, extended cosets of the
//!   proof's polynomials, the numerator, the quotient scratch) are zeroed
//!   before they are freed. A region whose zeroing or free fails is kept in
//!   quarantine (never handed back with values in it) until
//!   [`crate::end_request`] retries it.
//! - sppark's own device buffers (the per-call MSM buffer, the blob of an MSM
//!   context) are zeroed by the CUDA core before every free.
//! - Host staging: every host `Vec` of this crate that holds witness-dependent
//!   values (the masked MSM scalars) is zeroed with volatile writes before it
//!   is dropped ([`zero`]); the page-locked bounce buffer and the private
//!   read-back buffer of the CUDA core are zeroed and freed by
//!   [`crate::end_request`].
//!
//! In check mode ([`set_check`], or `MIDNIGHT_GPU_WIPE_CHECK=1`) every zeroed
//! device region is checked on the device: a kernel counts its non-zero words
//! and only the count comes back; a non-zero count is an erasure failure.
//! Host buffers of the core are compared with zero on the host.
//!
//! Proving-key copies and SRS tables are public data and are freed as they
//! are.

use std::sync::{
    Mutex, OnceLock,
    atomic::{AtomicBool, AtomicU64, Ordering::Relaxed},
};

static CHECK: AtomicBool = AtomicBool::new(false);
static CHECK_INIT: OnceLock<()> = OnceLock::new();
static BLOCKS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
static CHECKED: AtomicU64 = AtomicU64::new(0);
static NONZERO: AtomicU64 = AtomicU64::new(0);
/// Check calls that failed (the count of non-zero words did not come back).
static CHECK_FAIL: AtomicU64 = AtomicU64::new(0);
static HOST: AtomicU64 = AtomicU64::new(0);
/// Erasure or release failures of the Rust side since process start.
static ERASE_FAIL: AtomicU64 = AtomicU64::new(0);
/// Device regions whose zeroing or free failed: (address, bytes).
static QUARANTINE: Mutex<Vec<(usize, usize)>> = Mutex::new(Vec::new());
// The length and the bytes of the list as last recorded under its lock.
// A report that finds the lock taken (a retry, or a context reset that
// does not return) reads these instead of waiting.
static QUARANTINE_BLOCKS: AtomicU64 = AtomicU64::new(0);
static QUARANTINE_BYTES: AtomicU64 = AtomicU64::new(0);

// Records the list's size; called before its guard is released wherever
// the list changes.
fn record_quarantine(q: &[(usize, usize)]) {
    QUARANTINE_BLOCKS.store(q.len() as u64, Relaxed);
    QUARANTINE_BYTES.store(q.iter().map(|&(_, n)| n as u64).sum(), Relaxed);
}

// `(blocks, bytes, busy)` of the list without waiting for its lock.
fn quarantine_counts() -> (u64, u64, bool) {
    match QUARANTINE.try_lock() {
        Ok(q) => (
            q.len() as u64,
            q.iter().map(|&(_, n)| n as u64).sum(),
            false,
        ),
        Err(std::sync::TryLockError::Poisoned(e)) => {
            let q = e.into_inner();
            (
                q.len() as u64,
                q.iter().map(|&(_, n)| n as u64).sum(),
                false,
            )
        }
        Err(std::sync::TryLockError::WouldBlock) => (
            QUARANTINE_BLOCKS.load(Relaxed),
            QUARANTINE_BYTES.load(Relaxed),
            true,
        ),
    }
}
/// Regions of this crate that a successful context reset took away
/// while their zeroing was still unconfirmed (a reset frees device
/// memory; it does not zero it). Sticky, never reset.
static RESET_UNERASED: AtomicU64 = AtomicU64::new(0);
static RESET_UNERASED_BYTES: AtomicU64 = AtomicU64::new(0);

/// Whether check mode is on. The first call reads `MIDNIGHT_GPU_WIPE_CHECK`
/// and sets the CUDA core's check mode to match; the device context is made
/// only after it (`ffi::context`), so the core's frees are checked from the
/// first one.
pub fn check() -> bool {
    CHECK_INIT.get_or_init(|| {
        let on = std::env::var("MIDNIGHT_GPU_WIPE_CHECK").as_deref() == Ok("1");
        CHECK.store(on, Relaxed);
        #[cfg(midnight_gpu_cuda)]
        // SAFETY: sets a flag of the core.
        unsafe {
            crate::ffi::mgpu_wipe_set_check(on as i32)
        };
    });
    CHECK.load(Relaxed)
}

/// Turns check mode on or off and resets the counters of [`stats`] (the
/// erasure failures are never reset). An active session declines the change.
pub fn set_check(on: bool) {
    let Some(_gate) = crate::batch::admit_ordinary("mode") else {
        return;
    };
    // the Rust flag and the core's flag change together
    static SET: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _s = SET.lock().unwrap_or_else(|e| e.into_inner());
    CHECK_INIT.get_or_init(|| ());
    CHECK.store(on, Relaxed);
    for c in [&BLOCKS, &BYTES, &CHECKED, &NONZERO, &CHECK_FAIL, &HOST] {
        c.store(0, Relaxed);
    }
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: counters only.
    unsafe {
        crate::ffi::mgpu_wipe_reset(on as i32)
    };
}

pub(crate) fn note_erasure_failure() {
    ERASE_FAIL.fetch_add(1, Relaxed);
}

/// Erasure or release failures since process start: the Rust side's and the
/// CUDA core's.
pub fn erasure_failures() -> u64 {
    let core = {
        #[cfg(midnight_gpu_cuda)]
        {
            // SAFETY: a counter.
            unsafe { crate::ffi::mgpu_erase_failures() }
        }
        #[cfg(not(midnight_gpu_cuda))]
        0
    };
    ERASE_FAIL.load(Relaxed) + core
}

/// Device regions in quarantine now: this crate's own and sppark's (kept by
/// the CUDA core's free wrappers).
pub fn quarantined() -> usize {
    // Does not wait for the list's lock: during a retry or a context
    // reset this is the last recorded length.
    #[allow(unused_mut)]
    let mut n = quarantine_counts().0 as usize;
    #[cfg(midnight_gpu_cuda)]
    if crate::ffi::probe().is_some() {
        // SAFETY: a counter.
        n += unsafe { crate::ffi::mgpu_quarantined() } as usize;
    }
    n
}

/// Plain-data element types that [`zero`] and [`Wiped`] take: integers and
/// arrays of `u64` (the limb types), whose all-zero bytes are a valid value
/// and which have nothing to drop. Sealed.
pub trait Plain: Copy + private::Sealed {}
mod private {
    pub trait Sealed {}
}
macro_rules! plain {
    ($($t:ty),*) => {$(impl private::Sealed for $t {} impl Plain for $t {})*};
}
plain!(u8, u16, u32, u64);
impl<const N: usize> private::Sealed for [u64; N] {}
impl<const N: usize> Plain for [u64; N] {}

/// A host vector of witness-dependent values that is zeroed when it drops,
/// on every exit (a return, a `?`, a panic that unwinds). The whole
/// allocation is zeroed, its spare capacity included, and counted. It cannot
/// grow, so no reallocation leaves an unwiped copy behind.
pub struct Wiped<T: Plain>(Vec<T>);

impl<T: Plain> std::fmt::Debug for Wiped<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Wiped(<{} values>)", self.0.len())
    }
}

impl<T: Plain> Wiped<T> {
    /// Takes ownership of `v`; it is zeroed when the `Wiped` drops.
    pub fn new(v: Vec<T>) -> Self {
        Wiped(v)
    }
}

impl<T: Plain> std::ops::Deref for Wiped<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T: Plain> std::ops::DerefMut for Wiped<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}

impl<T: Plain> Drop for Wiped<T> {
    fn drop(&mut self) {
        let cap = self.0.capacity();
        let p = self.0.as_mut_ptr() as *mut u8;
        for i in 0..cap * std::mem::size_of::<T>() {
            // SAFETY: inside the allocation; `T: Plain`, so all-zero bytes
            // are a valid `T`.
            unsafe { std::ptr::write_volatile(p.add(i), 0) };
        }
        std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
        HOST.fetch_add(1, Relaxed);
    }
}

/// Zeroes `v` with volatile writes that the compiler keeps (the memory may
/// be dropped right after). Only [`Plain`] types: a type with a destructor
/// or a niche cannot be zeroed from safe code.
///
/// ```compile_fail
/// let mut v = vec![String::from("x")];
/// midnight_gpu::wipe::zero(&mut v);
/// ```
pub fn zero<T: Plain>(v: &mut [T]) {
    let p = v.as_mut_ptr() as *mut u8;
    for i in 0..std::mem::size_of_val(v) {
        // SAFETY: `i` is inside the slice.
        unsafe { std::ptr::write_volatile(p.add(i), 0) };
    }
    std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
    HOST.fetch_add(1, Relaxed);
}

/// Counters since the last [`set_check`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WipeStats {
    /// Device regions of the Rust side zeroed.
    pub device_blocks: u64,
    /// Their bytes.
    pub device_bytes: u64,
    /// Of them, regions checked on the device in check mode.
    pub device_checked: u64,
    /// Of them, regions whose check found a non-zero word.
    pub device_nonzero: u64,
    /// Of them, regions whose check call failed, so no count came back. Like
    /// a non-zero region, the region is kept in quarantine and an erasure
    /// failure is counted.
    pub check_failures: u64,
    /// sppark's device blocks zeroed by the CUDA core, their bytes, checked
    /// on the device, non-zero, failed calls.
    pub core: [u64; 5],
    /// The CUDA core's host buffers (bounce, read-back) zeroed, bytes, read
    /// back, non-zero.
    pub stage: [u64; 4],
    /// Host vectors zeroed by [`zero`].
    pub host_vecs: u64,
    /// Regions in quarantine.
    pub quarantined: usize,
    /// See [`erasure_failures`].
    pub erasure_failures: u64,
}

/// The counters.
pub fn stats() -> WipeStats {
    #[allow(unused_mut)]
    let (mut core, mut stage) = ([0u64; 5], [0u64; 4]);
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: out arrays of the sizes the core writes.
    unsafe {
        crate::ffi::mgpu_wipe_counters(core.as_mut_ptr());
        crate::ffi::mgpu_stage_wipe_counters(stage.as_mut_ptr());
    }
    WipeStats {
        device_blocks: BLOCKS.load(Relaxed),
        device_bytes: BYTES.load(Relaxed),
        device_checked: CHECKED.load(Relaxed),
        device_nonzero: NONZERO.load(Relaxed),
        check_failures: CHECK_FAIL.load(Relaxed),
        core,
        stage,
        host_vecs: HOST.load(Relaxed),
        quarantined: quarantined(),
        erasure_failures: erasure_failures(),
    }
}

/// Zeroes a device region (on the actor thread); in check mode
/// counts its non-zero words on the device. `false`: the zeroing failed or a
/// word is non-zero.
#[cfg(midnight_gpu_cuda)]
fn zero_device(p: *mut std::ffi::c_void, bytes: usize) -> bool {
    use crate::ffi;
    if crate::fault::hit(crate::fault::Class::Erase, crate::fault::Point::Launch) {
        return false;
    }
    // SAFETY: our device region of `bytes`.
    if unsafe { ffi::mgpu_dev_zero(p, bytes) } != 0 {
        return false;
    }
    BLOCKS.fetch_add(1, Relaxed);
    BYTES.fetch_add(bytes as u64, Relaxed);
    if check() {
        // The check runs on the device: only the count of non-zero words comes back.
        let mut nonzero = 0u64;
        let rc = if crate::fault::hit(crate::fault::Class::Erase, crate::fault::Point::Check) {
            -1
        } else {
            // SAFETY: our device region of `bytes`; `nonzero` is a valid out pointer.
            unsafe { ffi::mgpu_dev_nonzero(p as *const std::ffi::c_void, bytes, &mut nonzero) }
        };
        // a failed call returns no count: a check failure, not a non-zero region
        if rc != 0 {
            CHECK_FAIL.fetch_add(1, Relaxed);
            return false;
        }
        if nonzero != 0 {
            NONZERO.fetch_add(1, Relaxed);
            return false;
        }
        CHECKED.fetch_add(1, Relaxed);
    }
    true
}

/// Zeroes and frees a device region of this crate (on the actor
/// thread); on a failure keeps it in quarantine.
#[cfg(midnight_gpu_cuda)]
pub(crate) fn release(p: *mut std::ffi::c_void, bytes: usize) {
    if crate::teardown::device_disabled() {
        // The region went with the reset context: no CUDA call, and
        // the dead pointer is not put in quarantine (a later retry
        // could zero or free a reused address).
        return;
    }
    // SAFETY: our allocation, freed once.
    if !zero_device(p, bytes) || unsafe { crate::ffi::mgpu_dev_free(p) } != 0 {
        quarantine(p, bytes);
    }
}

/// Keeps a device region whose erasure or release failed and counts the
/// failure. Idempotent: a region already held is neither added nor counted
/// again (the retry frees each address once).
#[cfg_attr(not(midnight_gpu_cuda), allow(dead_code))]
pub(crate) fn quarantine(p: *mut std::ffi::c_void, bytes: usize) {
    let mut q = QUARANTINE.lock().unwrap_or_else(|e| e.into_inner());
    if crate::teardown::device_disabled() || q.contains(&(p as usize, bytes)) {
        return;
    }
    note_erasure_failure();
    q.push((p as usize, bytes));
    record_quarantine(&q);
}

/// What is still unerased now, apart from the historical count of
/// [`erasure_failures`]. A caller that retires a worker after a failed
/// erasure may hand the device to the next one only when
/// [`PendingErasure::clear`] holds.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PendingErasure {
    /// Device regions of this crate in quarantine.
    pub rust_blocks: u64,
    /// Their bytes.
    pub rust_bytes: u64,
    /// sppark blocks in the CUDA core's quarantine whose zeroing is not
    /// confirmed.
    pub lib_unerased: u64,
    /// Their bytes.
    pub lib_unerased_bytes: u64,
    /// sppark blocks zeroed (confirmed) but not freed.
    pub lib_zeroed_unfreed: u64,
    /// Zeroings whose pre-zeroing device synchronisation failed (sticky).
    pub presync_failures: u64,
    /// Quarantined blocks (of this crate and of the CUDA core) that a
    /// successful context reset took away while their zeroing was still
    /// unconfirmed: a reset frees device memory but does not zero it,
    /// so the erasure of these blocks is lost for the rest of the
    /// process (sticky, never reset).
    pub reset_unerased: u64,
    /// Their bytes.
    pub reset_unerased_bytes: u64,
    /// Error drains of the CUDA core that could not be confirmed
    /// (`crate::error_drains`) and that no context reset has settled:
    /// while it is non-zero a transfer may still read or write a host
    /// buffer. Only a successful context teardown sets it back to 0
    /// (the reset ends every transfer).
    pub undrained: u64,
    /// The quarantine of this crate was locked when the report was made:
    /// a retry is running, or a context reset is in progress and has not
    /// returned. `rust_blocks` and `rust_bytes` are then the last
    /// recorded values, and [`PendingErasure::clear`] is false.
    pub reset_in_progress: bool,
}

impl PendingErasure {
    /// No unconfirmed device region is held, none was lost unerased
    /// at a context reset, and no transfer may still be in flight.
    pub fn clear(&self) -> bool {
        !self.reset_in_progress
            && self.rust_blocks == 0
            && self.lib_unerased == 0
            && self.reset_unerased == 0
            && self.undrained == 0
    }
}

/// The pending erasures now. No CUDA call.
pub fn pending_erasure() -> PendingErasure {
    // No wait for the quarantine lock: a watchdog that asks during a
    // reset that does not return gets an answer at once.
    let (rust_blocks, rust_bytes, reset_in_progress) = quarantine_counts();
    let (rust_lost, rust_lost_bytes) = (
        RESET_UNERASED.load(Relaxed),
        RESET_UNERASED_BYTES.load(Relaxed),
    );
    #[allow(unused_mut)]
    let mut c = [0u64; 4];
    #[allow(unused_mut)]
    let mut lost = [0u64; 2];
    #[allow(unused_mut)]
    let mut drains = [0u64; 2];
    #[cfg(midnight_gpu_cuda)]
    if crate::ffi::probe().is_some() {
        // SAFETY: writes 4 u64 into `c` and 2 into `lost`; host memory only.
        unsafe { crate::ffi::mgpu_quarantine_pending(c.as_mut_ptr()) };
        // SAFETY: writes 2 u64 into `lost`; host memory only.
        unsafe { crate::ffi::mgpu_teardown_lost(lost.as_mut_ptr()) };
        // SAFETY: writes 2 u64 into `drains`; host memory only.
        unsafe { crate::ffi::mgpu_drain_counters(drains.as_mut_ptr()) };
    }
    PendingErasure {
        rust_blocks,
        rust_bytes,
        lib_unerased: c[0],
        lib_unerased_bytes: c[1],
        lib_zeroed_unfreed: c[2],
        presync_failures: c[3],
        reset_unerased: rust_lost + lost[0],
        reset_unerased_bytes: rust_lost_bytes + lost[1],
        // a successful context reset ended every transfer: nothing is undrained then
        undrained: if crate::teardown::context_reset_done() {
            0
        } else {
            drains[1]
        },
        reset_in_progress,
    }
}

/// Holds the quarantine through zeroing, reset and accounting. A failed
/// reset keeps all records for the pending-erasure report.
#[cfg(midnight_gpu_cuda)]
pub(crate) fn reset_quarantine(reset: impl FnOnce() -> bool) -> bool {
    let mut held = QUARANTINE.lock().unwrap_or_else(|e| e.into_inner());
    let (mut blocks, mut bytes) = (0u64, 0u64);
    for &(p, n) in held.iter() {
        if !zero_device(p as *mut std::ffi::c_void, n) {
            blocks += 1;
            bytes += n as u64;
        }
    }
    if !reset() {
        return false;
    }
    note_quarantine_reset(&mut held, (blocks, bytes));
    true
}

fn note_quarantine_reset(held: &mut Vec<(usize, usize)>, lost: (u64, u64)) {
    RESET_UNERASED.fetch_add(lost.0, Relaxed);
    RESET_UNERASED_BYTES.fetch_add(lost.1, Relaxed);
    held.clear();
    record_quarantine(held);
}

/// Retries the regions in quarantine (on the actor thread).
/// `true`: none is left.
#[cfg(midnight_gpu_cuda)]
pub(crate) fn retry_quarantine() -> bool {
    let mut q = QUARANTINE.lock().unwrap_or_else(|e| e.into_inner());
    if crate::teardown::device_disabled() {
        // No CUDA call against the dead context. The list was
        // accounted for and cleared by the teardown itself after a
        // successful reset; after a failed reset the regions are
        // still held here, so it is kept as it is.
        return q.is_empty();
    }
    q.retain(|&(p, n)| {
        let p = p as *mut std::ffi::c_void;
        // SAFETY: a region of ours that was not freed.
        !(zero_device(p, n) && unsafe { crate::ffi::mgpu_dev_free(p) } == 0)
    });
    record_quarantine(&q);
    q.is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    // A report made while the quarantine is locked (a retry, or a reset
    // that does not return) answers at once and is not clear.
    #[test]
    fn reports_do_not_wait_for_a_locked_quarantine() {
        use std::{sync::mpsc, time::Duration};
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        let (locked, is_locked) = mpsc::channel();
        let (release, released) = mpsc::channel::<()>();
        let holder = std::thread::spawn(move || {
            let held = QUARANTINE.lock().unwrap_or_else(|e| e.into_inner());
            locked.send(()).unwrap();
            let _ = released.recv_timeout(Duration::from_secs(30));
            drop(held);
        });
        is_locked.recv_timeout(Duration::from_secs(10)).expect("holder took the lock");
        let (done, report) = mpsc::channel();
        std::thread::spawn(move || {
            let _ = done.send((pending_erasure(), quarantined()));
        });
        let got = report.recv_timeout(Duration::from_secs(5));
        release.send(()).unwrap();
        holder.join().unwrap();
        let (pending, _) = got.expect("the report waited for the quarantine lock");
        assert!(pending.reset_in_progress);
        assert!(!pending.clear());
        assert!(!pending_erasure().reset_in_progress || QUARANTINE.try_lock().is_err());
    }

    /// The device count finds every non-zero word, an unaligned tail byte
    /// included, and reads a zeroed region as zero.
    #[cfg(midnight_gpu_cuda)]
    #[test]
    fn device_count_finds_non_zero() {
        use std::ffi::c_void;

        use crate::ffi;
        if ffi::probe().is_none() || !ffi::context() {
            return;
        }
        assert!(
            ffi::call(|| {
                let n = (1usize << 20) + 5;
                // SAFETY: a fresh device region of `n` bytes, freed below.
                let p = unsafe { ffi::mgpu_dev_alloc(n) };
                assert!(!p.is_null());
                let count = |p: *mut c_void| {
                    let mut c = 0u64;
                    // SAFETY: our region of `n` bytes.
                    assert_eq!(unsafe { ffi::mgpu_dev_nonzero(p, n, &mut c) }, 0);
                    c
                };
                // SAFETY: our region of `n` bytes.
                assert_eq!(unsafe { ffi::mgpu_dev_zero(p, n) }, 0);
                assert_eq!(count(p), 0);
                let one = [1u8];
                for off in [0, 8 * 1000 + 3, n - 1] {
                    // SAFETY: one byte inside our region.
                    let rc = unsafe {
                        ffi::mgpu_htod(
                            (p as *mut u8).add(off) as *mut c_void,
                            one.as_ptr() as *const c_void,
                            1,
                        )
                    };
                    assert_eq!(rc, 0);
                }
                assert_eq!(count(p), 3);
                // SAFETY: our region, zeroed then freed once.
                unsafe {
                    assert_eq!(ffi::mgpu_dev_zero(p, n), 0);
                    assert_eq!(count(p), 0);
                    assert_eq!(ffi::mgpu_dev_free(p), 0);
                }
            })
            .is_some(),
            "the actor request ran (a panic inside it would close its reply)"
        );
    }

    // Serialises the quarantine tests: they share the process quarantine.
    static QUAR_SERIAL: Mutex<()> = Mutex::new(());

    #[test]
    #[cfg(midnight_gpu_cuda)]
    fn quarantine_stays_locked_through_reset() {
        crate::ffi::tests::isolated(|| {
            assert!(!reset_quarantine(|| {
                assert!(matches!(
                    QUARANTINE.try_lock(),
                    Err(std::sync::TryLockError::WouldBlock)
                ));
                false
            }));
        });
    }

    /// Host-only bookkeeping of [`quarantine`]: a region is held once and
    /// counted once, however often it is kept. The fake region is never
    /// dereferenced or freed; it is removed again before the assertions so
    /// a failure cannot leave it for a retry.
    #[test]
    fn quarantine_is_idempotent_and_counted_once() {
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        let p = std::ptr::without_provenance_mut::<std::ffi::c_void>(0x51_0000);
        let bytes = 4096usize;
        let held = |p: *mut std::ffi::c_void| {
            QUARANTINE
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .iter()
                .filter(|&&(a, _)| a == p as usize)
                .count()
        };
        let f0 = ERASE_FAIL.load(Relaxed);
        quarantine(p, bytes);
        let (after_one, f_one) = (held(p), ERASE_FAIL.load(Relaxed));
        quarantine(p, bytes);
        let (after_two, f_two) = (held(p), ERASE_FAIL.load(Relaxed));
        QUARANTINE
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .retain(|&(a, _)| a != p as usize);
        let after_remove = held(p);
        assert_eq!(after_one, 1, "the region is held");
        assert_eq!(f_one, f0 + 1, "the failure is counted");
        assert_eq!(after_two, 1, "already held: not added again");
        assert_eq!(f_two, f0 + 1, "already held: not counted again");
        assert_eq!(after_remove, 0);
    }

    /// `clear` holds exactly when no unconfirmed region is held: a region
    /// of this crate or an unconfirmed library block blocks it; a library
    /// block that is zeroed and only waits for its free does not.
    #[test]
    fn pending_erasure_clear() {
        assert!(PendingErasure::default().clear());
        assert!(
            !PendingErasure {
                rust_blocks: 1,
                ..Default::default()
            }
            .clear()
        );
        assert!(
            !PendingErasure {
                lib_unerased: 1,
                ..Default::default()
            }
            .clear()
        );
        assert!(
            PendingErasure {
                lib_zeroed_unfreed: 1,
                presync_failures: 1,
                ..Default::default()
            }
            .clear()
        );
        assert!(
            !PendingErasure {
                reset_unerased: 1,
                ..Default::default()
            }
            .clear(),
            "a block lost unerased at a reset is never clear"
        );
        // No context reset has run in this process, so an unconfirmed
        // drain still blocks; the after-reset case runs on a device
        // (tests/drain_teardown.rs).
        assert!(
            !PendingErasure {
                undrained: 1,
                ..Default::default()
            }
            .clear(),
            "an unconfirmed drain is not clear before a reset"
        );
    }

    /// The accounting after a successful reset: the regions that could
    /// not be zeroed before it are reported as lost unerased, the list
    /// is cleared, and the report is not clear. Host bookkeeping only;
    /// the sticky counters are restored so the sibling tests that
    /// share this process still start from the state they expect.
    #[test]
    fn quarantine_reset_accounting() {
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        let p = std::ptr::without_provenance_mut::<std::ffi::c_void>(0x53_0000);
        let bytes = 4096usize;
        let (lost0, lost_bytes0) = (
            RESET_UNERASED.load(Relaxed),
            RESET_UNERASED_BYTES.load(Relaxed),
        );
        let before = pending_erasure();
        quarantine(p, bytes);
        note_quarantine_reset(&mut QUARANTINE.lock().unwrap(), (1, bytes as u64));
        let after = pending_erasure();
        RESET_UNERASED.store(lost0, Relaxed);
        RESET_UNERASED_BYTES.store(lost_bytes0, Relaxed);
        assert_eq!(after.reset_unerased, before.reset_unerased + 1);
        assert_eq!(
            after.reset_unerased_bytes,
            before.reset_unerased_bytes + bytes as u64
        );
        assert_eq!(after.rust_blocks, before.rust_blocks, "the list is cleared");
        assert_eq!(after.rust_bytes, before.rust_bytes);
        assert!(!after.clear(), "lost unerased is never clear: {after:?}");
    }

    /// The pending report mirrors this crate's quarantine; a kept region
    /// makes it not clear, and removing it restores the report. The fake
    /// region is never dereferenced or freed (see the idempotence test).
    #[test]
    fn pending_erasure_reports_rust_quarantine() {
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        let p = std::ptr::without_provenance_mut::<std::ffi::c_void>(0x52_0000);
        let bytes = 8192usize;
        let before = pending_erasure();
        quarantine(p, bytes);
        let during = pending_erasure();
        QUARANTINE
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .retain(|&(a, _)| a != p as usize);
        let after = pending_erasure();
        assert_eq!(during.rust_blocks, before.rust_blocks + 1);
        assert_eq!(during.rust_bytes, before.rust_bytes + bytes as u64);
        assert!(!during.clear(), "a held region is not clear");
        assert_eq!(after.rust_blocks, before.rust_blocks);
        assert_eq!(after.rust_bytes, before.rust_bytes);
        // The library fields come from the CUDA core; keeping a region of
        // this crate does not change them.
        assert_eq!(during.lib_unerased, before.lib_unerased);
        assert_eq!(during.lib_unerased_bytes, before.lib_unerased_bytes);
        assert_eq!(during.lib_zeroed_unfreed, before.lib_zeroed_unfreed);
        assert_eq!(during.presync_failures, before.presync_failures);
    }

    /// In a stub build there is no CUDA core: the library fields are zero.
    #[cfg(not(midnight_gpu_cuda))]
    #[test]
    fn pending_erasure_stub_is_default() {
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        let p = pending_erasure();
        assert_eq!(p.lib_unerased, 0);
        assert_eq!(p.lib_unerased_bytes, 0);
        assert_eq!(p.lib_zeroed_unfreed, 0);
        assert_eq!(p.presync_failures, 0);
        // The report agrees with the quarantine it reads.
        let q = QUARANTINE.lock().unwrap_or_else(|e| e.into_inner());
        assert_eq!(p.rust_blocks, q.len() as u64);
        assert_eq!(p.rust_bytes, q.iter().map(|&(_, n)| n as u64).sum::<u64>());
        assert_eq!(p.clear(), q.is_empty());
    }

    /// A quarantined region is zeroed and freed by the retry.
    #[cfg(midnight_gpu_cuda)]
    #[test]
    fn quarantine_retry_frees_region() {
        use crate::ffi;
        if ffi::probe().is_none() || !ffi::context() {
            return;
        }
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        assert!(
            ffi::call(|| {
                let bytes = 4096usize;
                // SAFETY: a fresh device region, freed by the retry below.
                let p = unsafe { ffi::mgpu_dev_alloc(bytes) };
                assert!(!p.is_null());
                let q0 = quarantined();
                quarantine(p, bytes);
                assert_eq!(quarantined(), q0 + 1, "the region is held");
                assert!(retry_quarantine(), "the retry frees it");
                assert_eq!(quarantined(), q0, "nothing is held after the retry");
            })
            .is_some(),
            "the actor request ran (a panic inside it would close its reply)"
        );
    }

    /// A public buffer whose free fails once is quarantined, counted
    /// once, and freed by the retry. Only the dev-free switch and
    /// behaviour that predates the quarantine of a failed public free
    /// are used, so this test also compiles on the parent of that fix,
    /// where the quarantine assertion fails (the pointer was dropped
    /// and nothing retried its free).
    ///
    /// The body runs as one actor request. Inside it, `quarantined`
    /// and `erasure_failures` read host counters only,
    /// `crate::device_bytes` reads plain counters of the core, and
    /// `retry_quarantine` expects to run on the actor thread.
    /// `crate::end_request` is not called: it sends its own actor
    /// request, which would only queue behind this one.
    #[cfg(all(midnight_gpu_cuda, feature = "test-fault"))]
    #[test]
    fn public_buffer_failed_free_is_quarantined_and_retried() {
        use crate::ffi;
        if ffi::probe().is_none() || !ffi::context() {
            return;
        }
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        assert!(
            ffi::call(|| {
                let bytes = 4096usize;
                let live0 = crate::device_bytes().0;
                let buf = ffi::DevBuf::new(bytes, false).expect("a public device buffer");
                let live_alloc = crate::device_bytes().0;
                assert_eq!(
                    live_alloc,
                    live0 + bytes as u64,
                    "the allocation is counted live"
                );
                let (q0, f0) = (quarantined(), erasure_failures());
                crate::fault::fail_dev_frees(1);
                drop(buf);
                crate::fault::fail_dev_frees(0);
                assert_eq!(quarantined(), q0 + 1, "the failed free is quarantined");
                assert_eq!(erasure_failures(), f0 + 1, "and counted once");
                assert_eq!(
                    crate::device_bytes().0,
                    live_alloc,
                    "a failed free releases no live bytes"
                );
                assert!(retry_quarantine(), "the retry frees the region");
                assert_eq!(quarantined(), q0, "nothing is held after the retry");
                assert_eq!(
                    crate::device_bytes().0,
                    live0,
                    "the live bytes are back to before the allocation"
                );
                assert_eq!(erasure_failures(), f0 + 1, "the failure stays counted");
            })
            .is_some(),
            "the actor request ran (a panic inside it would close its reply)"
        );
    }

    /// The pending report of the same failed public free: the held
    /// region is one rust block of its bytes and the report is not
    /// clear; the retry restores the report. Separate from the test
    /// above, which must also compile without `pending_erasure`.
    #[cfg(all(midnight_gpu_cuda, feature = "test-fault"))]
    #[test]
    fn public_buffer_failed_free_is_pending_until_retried() {
        use crate::ffi;
        if ffi::probe().is_none() || !ffi::context() {
            return;
        }
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        assert!(
            ffi::call(|| {
                let bytes = 8192usize;
                let buf = ffi::DevBuf::new(bytes, false).expect("a public device buffer");
                let p0 = pending_erasure();
                crate::fault::fail_dev_frees(1);
                drop(buf);
                crate::fault::fail_dev_frees(0);
                let p = pending_erasure();
                assert_eq!(p.rust_blocks, p0.rust_blocks + 1, "one held region: {p:?}");
                assert_eq!(
                    p.rust_bytes,
                    p0.rust_bytes + bytes as u64,
                    "of its bytes: {p:?}"
                );
                assert_eq!(p.lib_unerased, p0.lib_unerased, "no library block: {p:?}");
                assert_eq!(
                    p.lib_zeroed_unfreed, p0.lib_zeroed_unfreed,
                    "no library block: {p:?}"
                );
                assert!(!p.clear(), "a held region is not clear");
                assert!(retry_quarantine(), "the retry frees the region");
                let p = pending_erasure();
                assert_eq!(p.rust_blocks, p0.rust_blocks, "nothing held: {p:?}");
                assert_eq!(p.rust_bytes, p0.rust_bytes, "nothing held: {p:?}");
            })
            .is_some(),
            "the actor request ran (a panic inside it would close its reply)"
        );
    }

    /// In a stub build the dev-free switch has no core to set: arming
    /// and disarming it changes no counter.
    #[cfg(all(not(midnight_gpu_cuda), feature = "test-fault"))]
    #[test]
    fn fail_dev_frees_stub_is_noop() {
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        let (q0, f0, p0) = (quarantined(), erasure_failures(), pending_erasure());
        crate::fault::fail_dev_frees(1);
        crate::fault::fail_dev_frees(0);
        assert_eq!(quarantined(), q0);
        assert_eq!(erasure_failures(), f0);
        assert_eq!(pending_erasure(), p0);
    }

    /// In a stub build the presync and library-free switches have no
    /// core to set: arming and disarming them changes no counter.
    #[cfg(all(not(midnight_gpu_cuda), feature = "test-fault"))]
    #[test]
    fn fail_wipe_presync_and_lib_frees_stub_are_noops() {
        let _s = QUAR_SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        let (q0, f0, p0) = (quarantined(), erasure_failures(), pending_erasure());
        crate::fault::fail_wipe_presync(1);
        crate::fault::fail_wipe_presync(0);
        crate::fault::fail_lib_frees(1);
        crate::fault::fail_lib_frees(0);
        assert_eq!(quarantined(), q0);
        assert_eq!(erasure_failures(), f0);
        assert_eq!(pending_erasure(), p0);
    }

    #[test]
    fn zero_host() {
        let mut v = vec![[7u64; 4]; 100];
        zero(&mut v);
        assert!(v.iter().all(|x| *x == [0; 4]));
    }
}
