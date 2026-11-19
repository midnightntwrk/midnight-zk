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

//! The device side of a concurrent batch of independent proofs (the
//! scheduler is `midnight_proofs::gpu::batch`).
//!
//! Each hook call still serves exactly one proof: one MSM, one transform
//! or one quotient, whose result returns to that proof only. No device
//! work of two proofs is grouped. Every device call of this crate is one
//! request to the device-owner actor, which runs one request at a time,
//! and the quotient's memory admission runs inside its request against
//! the then-current free memory, so concurrent jobs cannot be admitted
//! against the same free bytes: their device phases serialise, and only
//! their host phases overlap.
//!
//! This module is built in every configuration of the device backend.
//!
//! Ordinary proof calls hold a shared admission guard. [`BatchSession::begin`]
//! waits for them to finish and takes exclusive ownership until the session
//! ends. Only the scoped hook table uses the batch entries. Each batch entry
//! holds a read guard on the session state until its device work is complete.
//!
//! [`isolated_msm_g1`] serializes each MSM with eviction and checking of
//! its registered contexts. Host points and public mask corrections survive
//! eviction. An unwind or failed check latches a failure before the next MSM.
//! Transforms and quotients release shared scratch under the same lock.
//! Check [`BatchSession::end_wave`]
//! after its workers join and [`BatchSession::finish`] before releasing the
//! batch result.

#[cfg(test)]
use std::sync::atomic::AtomicBool;
use std::{
    cell::Cell,
    sync::{
        Arc, Mutex, MutexGuard, OnceLock, RwLock, RwLockReadGuard, RwLockWriteGuard, TryLockError,
        atomic::{AtomicU64, Ordering::Relaxed},
    },
    thread::LocalKey,
};

use crate::{G1AffineLimbs, G1JacobianLimbs, Scalar};

/// The one shutdown signal every blocked phase observes. Cloneable;
/// all clones see the same signal.
#[derive(Clone, Debug, Default)]
pub struct Shutdown {
    flag: Arc<OnceLock<()>>,
}

impl From<Arc<OnceLock<()>>> for Shutdown {
    fn from(flag: Arc<OnceLock<()>>) -> Self {
        Self { flag }
    }
}

impl Shutdown {
    /// A fresh, untriggered signal.
    pub fn new() -> Shutdown {
        Shutdown::default()
    }

    /// Triggers the signal. Idempotent. Blocked waiters observe it
    /// on their next shutdown check.
    pub fn trigger(&self) {
        let _ = self.flag.set(());
    }

    /// Whether teardown has begun.
    pub fn is_triggered(&self) -> bool {
        self.flag.get().is_some()
    }
}

pub(crate) type PanicFlag = &'static LocalKey<Cell<bool>>;

thread_local! {
    // Captured at submission so queued work carries its own panic scope.
    pub(crate) static REQUEST_FLAG: Cell<Option<PanicFlag>> = const { Cell::new(None) };
}

struct RequestScope(Option<PanicFlag>);

impl RequestScope {
    fn enter(flag: PanicFlag) -> Self {
        Self(REQUEST_FLAG.replace(Some(flag)))
    }
}

impl Drop for RequestScope {
    fn drop(&mut self) {
        REQUEST_FLAG.set(self.0);
    }
}

static OWNER: Mutex<()> = Mutex::new(());
static BATCH_MSM_CALLS: AtomicU64 = AtomicU64::new(0);
static CONTEXT_EVICTIONS: AtomicU64 = AtomicU64::new(0);
static DEFERRED_RELEASES: AtomicU64 = AtomicU64::new(0);
static DECLINED_AFTER_ERASURE: AtomicU64 = AtomicU64::new(0);
// Accessible on the owner even while its caller holds the session state for
// cleanup. A failed signal stays installed after close to decline future
// sessions.
static SESSION_FAILURE: Mutex<Option<Shutdown>> = Mutex::new(None);

fn session_failure() -> MutexGuard<'static, Option<Shutdown>> {
    SESSION_FAILURE.lock().unwrap_or_else(|e| e.into_inner())
}

fn latch_failure() {
    session_failure().get_or_insert_with(Shutdown::new).trigger();
}

static GATE: RwLock<()> = RwLock::new(());
static SESSION_SLOT: Mutex<()> = Mutex::new(());
// Production actor requests never acquire the session, owner, or admission
// locks.
static SESSION_ACTIVE: RwLock<Option<SessionState>> = RwLock::new(None);

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Entry {
    Ordinary,
    Batch,
}

impl Entry {
    #[cfg(midnight_gpu_cuda)]
    pub(crate) fn operation_panic(self, class: &'static str) -> bool {
        if self == Self::Batch {
            latch_failure();
        }
        crate::decline(class, "operation-panic")
    }
    /// A live context needs a positive release acknowledgment, even on decline.
    /// A batch fails closed: any release the device owner did not confirm
    /// latches the session failure, also when the device was retired
    /// (ordinary proving does not count that case, see
    /// [`crate::msm::free_context`]).
    pub(crate) fn free_context(self, dev: usize) -> bool {
        let freed = crate::msm::free_context(dev, self);
        if self == Self::Batch && dev != 0 && !freed {
            latch_failure();
        }
        freed
    }
}

pub(crate) struct SessionState {
    id: Arc<PanicFlag>,
    // The write guard owns all queue mutations. The mutex lets a read guard
    // share the identity without sharing the contained device buffers.
    releases: Mutex<Vec<RegistrationRelease>>,
}

pub(crate) enum RegistrationRelease {
    Context(usize),
    #[cfg(midnight_gpu_cuda)]
    Key(crate::ffi::DevBuf),
}

impl RegistrationRelease {
    pub(crate) fn submit(self, session: &mut Option<SessionState>) {
        if let Some(state) = session {
            if !matches!(self, Self::Context(0)) {
                state.releases.get_mut().unwrap_or_else(|e| e.into_inner()).push(self);
            }
        } else {
            self.release(Entry::Ordinary);
        }
    }

    fn release(self, entry: Entry) -> bool {
        match self {
            Self::Context(dev) => crate::msm::free_context(dev, entry),
            #[cfg(midnight_gpu_cuda)]
            Self::Key(buffer) => {
                drop(buffer);
                // The final boundary checks the buffer's sticky failure count.
                true
            }
        }
    }
}

// Take this before either registry lock. An in-flight batch call keeps its
// registration through cleanup, and close sees every displaced live resource.
pub(crate) fn registration() -> RwLockWriteGuard<'static, Option<SessionState>> {
    SESSION_ACTIVE.write().unwrap_or_else(|e| e.into_inner())
}

thread_local! {
    static WORKER: std::cell::RefCell<Option<Arc<PanicFlag>>> = const { std::cell::RefCell::new(None) };
}

/// The ordinary side of the gate: a shared guard held for the whole
/// call, or `None` (counted as a `batch` decline) while a batch session
/// holds the gate exclusively.
pub(crate) fn admit_ordinary(class: &'static str) -> Option<RwLockReadGuard<'static, ()>> {
    let guard = match GATE.try_read() {
        Ok(g) => g,
        Err(TryLockError::Poisoned(e)) => e.into_inner(),
        Err(TryLockError::WouldBlock) => {
            crate::decline(class, "batch");
            return None;
        }
    };
    Some(guard)
}

fn admit_batch(
    class: &'static str,
) -> Option<(RwLockReadGuard<'static, Option<SessionState>>, RequestScope)> {
    let guard = SESSION_ACTIVE.read().unwrap_or_else(|e| e.into_inner());
    if let Some(session) = guard.as_ref()
        && WORKER
            .with_borrow(|worker| worker.as_ref().is_some_and(|id| Arc::ptr_eq(id, &session.id)))
    {
        let scope = RequestScope::enter(*session.id);
        Some((guard, scope))
    } else {
        crate::decline(class, "batch");
        None
    }
}

// Tests may arm a fault for the next call of their admitted device wave.
#[cfg(feature = "test-fault")]
pub(crate) fn with_fault_admission(arm: impl FnOnce()) {
    if WORKER.with_borrow(Option::is_some)
        && let Some(_session) = admit_batch("fault")
    {
        arm();
    } else if let Some(_gate) = admit_ordinary("fault") {
        arm();
    }
}

/// Test switch that holds an admitted ordinary call in flight (after the
/// gate is taken, before the rest of the call), so a test can observe a
/// batch start waiting for it.
#[cfg(test)]
pub(crate) mod test_hold {
    use std::sync::atomic::{AtomicBool, Ordering::Relaxed};

    pub static ARMED: AtomicBool = AtomicBool::new(false);
    pub static ENTERED: AtomicBool = AtomicBool::new(false);
    pub static RELEASE: AtomicBool = AtomicBool::new(false);

    pub fn maybe_hold() {
        if !ARMED.load(Relaxed) {
            return;
        }
        ENTERED.store(true, Relaxed);
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        while !RELEASE.load(Relaxed) {
            assert!(
                std::time::Instant::now() < deadline,
                "ordinary call was not released"
            );
            std::hint::spin_loop();
        }
    }
}

/// The erasure state after an eviction, on the same counters as
/// [`crate::end_request_report`].
fn erasure_ok(s: &crate::wipe::WipeStats) -> bool {
    s.erasure_failures == 0
        && s.device_nonzero == 0
        && s.check_failures == 0
        && s.core[3] == 0
        && s.stage[3] == 0
}

/// `(batch MSM calls taken, live contexts evicted after taken batch
/// MSMs, batch MSMs declined after a failed erasure check)` since
/// process start. A declined MSM and a sweep that frees no live
/// context do not move the eviction count.
pub fn batch_msm_counts() -> (u64, u64, u64) {
    (
        BATCH_MSM_CALLS.load(Relaxed),
        CONTEXT_EVICTIONS.load(Relaxed),
        DECLINED_AFTER_ERASURE.load(Relaxed),
    )
}

pub(crate) fn count_evictions(freed: u64) {
    CONTEXT_EVICTIONS.fetch_add(freed, Relaxed);
}

/// Number of deferred registration releases attempted at final boundaries.
// Test support: the integration tests read it; not part of the API.
#[doc(hidden)]
pub fn deferred_releases() -> u64 {
    DEFERRED_RELEASES.load(Relaxed)
}

/// Whether a batch context eviction or request boundary has failed in this
/// process. Every batch proof entry declines while the latch is set.
pub fn batch_erasure_failed() -> bool {
    session_failure().as_ref().is_some_and(Shutdown::is_triggered)
}

/// How often the eviction guard ran (tests only; the production
/// eviction counter counts only live contexts freed after a taken MSM).
#[cfg(test)]
static EVICT_RUNS: AtomicU64 = AtomicU64::new(0);

/// Runs the eviction and the erasure check on every exit of
/// [`isolated_msm_g1`] (dropped after the MSM, before the owner lock it
/// was declared after). A panic of the eviction itself, on the normal
/// path or during an unwind, latches the erasure failure instead of
/// escaping (a second panic during an unwind would abort).
struct EvictOnDrop {
    /// Whether the MSM was taken by the device: the eviction counter
    /// counts only live contexts freed after a taken MSM.
    taken: bool,
}

impl Drop for EvictOnDrop {
    fn drop(&mut self) {
        #[cfg(test)]
        EVICT_RUNS.fetch_add(1, Relaxed);
        let evicted = std::panic::catch_unwind(|| {
            #[cfg(test)]
            if PANIC_ON_EVICT.swap(false, Relaxed) {
                panic!("eviction interrupted");
            }
            crate::msm::evict_contexts(Entry::Batch)
        });
        let clean = cleanup_succeeded(|| {
            !crate::teardown::erasure_failed() && erasure_ok(&crate::wipe::stats())
        });
        match evicted {
            Ok((freed, unconfirmed)) => {
                if self.taken {
                    count_evictions(freed);
                }
                if unconfirmed {
                    latch_failure();
                }
            }
            Err(payload) => {
                // An opaque destructor must never unwind through this guard.
                drop_payload(payload);
                latch_failure();
            }
        }
        if std::thread::panicking() || !clean {
            latch_failure();
        }
    }
}

/// Interrupt the cleanup path while its owner still holds the lock.
#[cfg(test)]
static PANIC_ON_EVICT: AtomicBool = AtomicBool::new(false);
#[cfg(test)]
static PANIC_AFTER_MSM: AtomicBool = AtomicBool::new(false);

/// The G1 MSM hook of a batch: [`crate::msm_g1`] with the registered MSM
/// contexts evicted and the erasure checked afterwards, all under one
/// owner lock (see the module text). The eviction and check run on
/// every exit, an unwind of the MSM included ([`EvictOnDrop`], taken
/// before the MSM starts), and an unwind latches the erasure failure.
/// `None` declines as `crate::msm_g1` does, and after a failed erasure
/// check.
pub fn isolated_msm_g1(scalars: &[Scalar], bases: &[G1AffineLimbs]) -> Option<G1JacobianLimbs> {
    let _session = admit_batch("msm")?;
    if batch_erasure_failed() {
        DECLINED_AFTER_ERASURE.fetch_add(1, Relaxed);
        return None;
    }
    let _owner = lock_owner();
    if batch_erasure_failed() {
        DECLINED_AFTER_ERASURE.fetch_add(1, Relaxed);
        return None;
    }
    let mut evict = EvictOnDrop { taken: false };
    let result = crate::msm_g1_admitted(scalars, bases, Entry::Batch);
    evict.taken = result.is_some();
    #[cfg(test)]
    if PANIC_AFTER_MSM.swap(false, Relaxed) {
        panic!("test panic after the batch MSM");
    }
    if result.is_some() {
        BATCH_MSM_CALLS.fetch_add(1, Relaxed);
    }
    result
}

fn lock_owner() -> MutexGuard<'static, ()> {
    // A poisoned owner lock means a holder unwound: latch the failure
    // and decline below, never proceed as if the check had passed.
    // The poison is cleared once latched: the latch, not the poison,
    // is the sticky fail-closed state from then on.
    match OWNER.lock() {
        Ok(g) => g,
        Err(e) => {
            latch_failure();
            let g = e.into_inner();
            OWNER.clear_poison();
            g
        }
    }
}

/// Holds the same lock as an isolated MSM until all shared private storage
/// has been released, including on a decline or an unwind.
fn with_shared_scratch(call: impl FnOnce() -> bool) -> bool {
    let _owner = lock_owner();
    if batch_erasure_failed() {
        return false;
    }
    struct Release;
    impl Drop for Release {
        fn drop(&mut self) {
            let clean = cleanup_succeeded(|| {
                #[cfg(midnight_gpu_cuda)]
                if crate::present().is_some()
                    // SAFETY: on the device-owner thread, after the batch call's transfers.
                    && crate::ffi::call_live(|| unsafe { crate::release_shared_scratch() })
                        != Some(true)
                {
                    return false;
                }
                !crate::teardown::erasure_failed() && erasure_ok(&crate::wipe::stats())
            });
            if !clean || std::thread::panicking() {
                latch_failure();
            }
        }
    }
    let _release = Release;
    call()
}

/// The batch FFT hook: [`crate::fft`] admitted on the batch side of the
/// gate. Declines when no batch session holds the gate.
pub fn batch_fft(a: &mut [Scalar], omega: Scalar, log_n: u32) -> bool {
    let Some(_session) = admit_batch("ntt") else {
        return false;
    };
    with_shared_scratch(|| crate::transform(a, omega, log_n, None, Entry::Batch))
}

/// The batch inverse FFT hook: [`crate::ifft`] admitted on the batch
/// side of the gate. Declines when no batch session holds the gate.
pub fn batch_ifft(a: &mut [Scalar], omega_inv: Scalar, log_n: u32, divisor: Scalar) -> bool {
    let Some(_session) = admit_batch("ntt") else {
        return false;
    };
    with_shared_scratch(|| crate::transform(a, omega_inv, log_n, Some(divisor), Entry::Batch))
}

/// The batch quotient hook: [`crate::quotient`] admitted on the batch
/// side of the gate. Declines when no batch session holds the gate.
///
/// # Safety
/// The same contract as [`crate::quotient`].
pub unsafe fn batch_quotient(job: *const std::ffi::c_void, out: &mut [Scalar]) -> bool {
    let Some(_session) = admit_batch("quotient") else {
        return false;
    };
    // SAFETY: the caller guarantees the job and buffer lifetimes.
    with_shared_scratch(|| unsafe { crate::quotient::quotient_admitted(job, out, Entry::Batch) })
}

/// A device session could not start.
#[derive(Debug, PartialEq, Eq)]
pub enum SessionError {
    /// Another thread or a suspended caller already holds the session.
    Busy,
    /// The preceding request failed its erasure check.
    ErasureFailed,
}

/// One exclusive batch device request.
#[derive(Debug)]
#[must_use = "check the final erasure result with finish"]
pub struct BatchSession {
    finished: bool,
    id: Arc<PanicFlag>,
    failure: Shutdown,
    _gate: RwLockWriteGuard<'static, ()>,
    _slot: MutexGuard<'static, ()>,
}

/// A scheduler can ask for the session flag before changing worker admission.
pub trait WorkerAdmission {
    /// Returns the requested admission change, if any.
    fn admission(self, failure: &Arc<OnceLock<()>>) -> Option<bool>;
}

#[cfg(test)]
impl WorkerAdmission for bool {
    fn admission(self, _: &Arc<OnceLock<()>>) -> Option<bool> {
        Some(self)
    }
}

impl WorkerAdmission for Result<bool, &mut Option<Arc<OnceLock<()>>>> {
    fn admission(self, failure: &Arc<OnceLock<()>>) -> Option<bool> {
        match self {
            Ok(on) => Some(on),
            Err(slot) => {
                *slot = Some(failure.clone());
                None
            }
        }
    }
}

impl BatchSession {
    /// Starts the batch's request ([`crate::begin_request`]). Takes the
    /// admission gate exclusively, waiting until every ordinary call in
    /// flight has returned. An occupied session returns [`SessionError::Busy`].
    /// From successful admission until close, ordinary entries decline with
    /// reason `batch` and only the batch entries reach the device.
    /// Pass the scheduler's `BATCH_THREAD` key so only this session's device
    /// requests use its panic scope on the owner thread.
    pub fn begin(panic_flag: &'static LocalKey<Cell<bool>>) -> Result<Self, SessionError> {
        let slot = match SESSION_SLOT.try_lock() {
            Ok(guard) => guard,
            Err(TryLockError::WouldBlock) => return Err(SessionError::Busy),
            Err(TryLockError::Poisoned(e)) => e.into_inner(),
        };
        let gate = GATE.write().unwrap_or_else(|e| e.into_inner());
        let mut active = registration();
        let _scope = RequestScope::enter(panic_flag);
        if !checked_boundary() {
            return Err(SessionError::ErasureFailed);
        }
        // Initialize check policy before exposing a session to public queries.
        crate::wipe::check();
        crate::begin_request_admitted();
        let id = Arc::new(panic_flag);
        let failure = {
            let mut current = session_failure();
            let signal = current.get_or_insert_with(Shutdown::new);
            if signal.is_triggered() {
                return Err(SessionError::ErasureFailed);
            }
            signal.clone()
        };
        *active = Some(SessionState {
            id: id.clone(),
            releases: Mutex::default(),
        });
        Ok(BatchSession {
            finished: false,
            id,
            failure,
            _gate: gate,
            _slot: slot,
        })
    }

    /// Admits or releases the current scoped worker for this session.
    /// Pass this method to the scheduler with its batch hooks.
    pub fn set_worker(&self, action: impl WorkerAdmission) {
        if let Some(enabled) = action.admission(&self.failure.flag) {
            WORKER.set(enabled.then(|| self.id.clone()));
        }
    }

    /// Use this signal for every shared resource a job may wait for, as the
    /// budget does.
    pub fn failure_signal(&self) -> Shutdown {
        self.failure.clone()
    }

    /// The end of one wave of the batch: [`crate::end_request`]. `true`
    /// when every erasure and release succeeded. Call it after every
    /// wave that used the device, also when a proof of the wave failed
    /// or panicked.
    pub fn end_wave(&self) -> bool {
        let _boundary = SESSION_ACTIVE.write().unwrap_or_else(|e| e.into_inner());
        let _scope = RequestScope::enter(*self.id);
        checked_boundary()
    }

    /// Ends the final request and reports any erasure failure in this process.
    #[must_use]
    pub fn finish(mut self) -> bool {
        self.close()
    }

    fn close(&mut self) -> bool {
        let mut active = SESSION_ACTIVE.write().unwrap_or_else(|e| e.into_inner());
        let _scope = RequestScope::enter(*self.id);
        if let Some(session) = active.take() {
            for release in session.releases.into_inner().unwrap_or_else(|e| e.into_inner()) {
                DEFERRED_RELEASES.fetch_add(1, Relaxed);
                if !cleanup_succeeded(std::panic::AssertUnwindSafe(|| {
                    release.release(Entry::Batch)
                })) {
                    latch_failure();
                }
            }
        }
        self.finished = true;
        checked_boundary();
        let mut current = session_failure();
        if self.failure.is_triggered() {
            return false;
        }
        *current = None;
        true
    }
}

/// Bound destructor retries and report an unread payload left at the limit.
pub(crate) fn drop_payload(mut payload: Box<dyn std::any::Any + Send>) {
    for _ in 0..8 {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(payload))) {
            Ok(()) => return,
            Err(next) => payload = next,
        }
    }
    std::mem::forget(payload);
    latch_failure();
}

fn cleanup_succeeded(f: impl FnOnce() -> bool + std::panic::UnwindSafe) -> bool {
    std::panic::catch_unwind(f).unwrap_or_else(|payload| {
        drop_payload(payload);
        false
    })
}

#[cfg(test)]
static FAIL_BOUNDARY: AtomicBool = AtomicBool::new(false);

fn checked_boundary() -> bool {
    let clean = cleanup_succeeded(|| {
        crate::end_request_admitted(Entry::Batch) && erasure_ok(&crate::wipe::stats())
    });
    #[cfg(test)]
    let clean = !FAIL_BOUNDARY.swap(false, Relaxed) && clean;
    if !clean {
        latch_failure();
    }
    !batch_erasure_failed()
}

impl Drop for BatchSession {
    fn drop(&mut self) {
        if !self.finished {
            self.close();
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use midnight_proofs::gpu::batch::BATCH_THREAD;

    use super::*;

    // Run each session in a fresh process. Wipe bookkeeping tests in the
    // parent may hold fabricated device addresses and sticky failure counts.
    pub(crate) fn in_parent() -> bool {
        let name = std::thread::current().name().unwrap().to_owned();
        if std::env::var("MIDNIGHT_BATCH_SESSION_TEST").as_deref() == Ok(&name) {
            return false;
        }
        let mut command = std::process::Command::new(std::env::current_exe().unwrap());
        command.args(["--exact", &name]).env("MIDNIGHT_BATCH_SESSION_TEST", &name);
        if name.ends_with("unconfirmed_registered_release_declines_the_next_msm")
            || name.ends_with("ordinary_unconfirmed_releases_reach_request_and_session_boundaries")
            || name.ends_with("releases_batch_waiter")
        {
            command.env("MIDNIGHT_GPU", "off");
        }
        let mut child = command.spawn().unwrap();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
        loop {
            if let Some(status) = child.try_wait().unwrap() {
                assert!(status.success(), "session test failed");
                return true;
            }
            if std::time::Instant::now() >= deadline {
                child.kill().unwrap();
                panic!("session test timed out");
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    /// The erasure check reads the same counters as the request report.
    #[test]
    fn erasure_check_reads_every_counter() {
        let clean = crate::wipe::WipeStats::default();
        assert!(erasure_ok(&clean));
        for dirty in [
            crate::wipe::WipeStats {
                erasure_failures: 1,
                ..clean
            },
            crate::wipe::WipeStats {
                device_nonzero: 1,
                ..clean
            },
            crate::wipe::WipeStats {
                check_failures: 1,
                ..clean
            },
            crate::wipe::WipeStats {
                core: [0, 0, 0, 1, 0],
                ..clean
            },
            crate::wipe::WipeStats {
                stage: [0, 0, 0, 1],
                ..clean
            },
        ] {
            assert!(!erasure_ok(&dirty), "a dirty counter must fail the check");
        }
    }

    /// An empty MSM declines on its shape even when a device is present.
    #[test]
    fn isolated_msm_declines_and_evicts_without_device() {
        if in_parent() {
            return;
        }
        *session_failure() = None;
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        session.set_worker(true);
        let before = batch_msm_counts();
        let runs = EVICT_RUNS.load(Relaxed);
        assert!(isolated_msm_g1(&[], &[]).is_none());
        assert_eq!(batch_msm_counts(), before);
        assert_eq!(EVICT_RUNS.load(Relaxed), runs + 1);
        let clean = session.finish();
        assert_eq!(clean, !batch_erasure_failed());
    }

    #[test]
    fn saved_batch_pointer_requires_worker_admission() {
        if in_parent() {
            return;
        }
        let saved = isolated_msm_g1;
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        let before = batch_decline_count("msm");
        assert!(saved(&[], &[]).is_none());
        assert_eq!(batch_decline_count("msm"), before + 1);
        drop(session);
    }

    #[test]
    fn previous_worker_needs_fresh_admission() {
        if in_parent() {
            return;
        }
        let saved = isolated_msm_g1;
        let first = BatchSession::begin(&BATCH_THREAD).unwrap();
        let retired_signal = first.failure_signal();
        first.set_worker(true);
        let before = batch_decline_count("msm");
        assert!(saved(&[], &[]).is_none());
        assert_eq!(batch_decline_count("msm"), before);
        assert!(first.finish());
        // Keep the old worker identity to exercise the generation check.
        let second = BatchSession::begin(&BATCH_THREAD).unwrap();
        retired_signal.trigger();
        assert!(!second.failure_signal().is_triggered());
        assert!(saved(&[], &[]).is_none());
        assert_eq!(batch_decline_count("msm"), before + 1);
        second.set_worker(true);
        assert!(saved(&[], &[]).is_none());
        assert_eq!(batch_decline_count("msm"), before + 1);
        assert!(second.finish());
    }

    #[test]
    fn handoff_rejects_failed_boundary_before_admission() {
        if in_parent() {
            return;
        }
        FAIL_BOUNDARY.store(true, Relaxed);
        assert!(matches!(
            BatchSession::begin(&BATCH_THREAD),
            Err(SessionError::ErasureFailed)
        ));
        assert!(!FAIL_BOUNDARY.load(Relaxed));
        assert!(batch_erasure_failed());
        assert!(admit_ordinary("request").is_some());
    }

    #[test]
    fn administrative_entries_decline_during_session() {
        if in_parent() {
            return;
        }
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        let check = crate::wipe::check();
        crate::wipe::set_check(!check);
        assert_eq!(crate::wipe::check(), check);
        let keep = crate::quotient::keep_resident();
        crate::quotient::set_keep_resident(!keep);
        assert_eq!(crate::quotient::keep_resident(), keep);
        assert!(!crate::set_min_k(1));
        crate::xfer::record_d2h(true);
        crate::xfer::note_d2h(4);
        assert!(crate::xfer::take_d2h_log().is_empty());
        assert_eq!(batch_decline_count("mode"), 4);
        assert!(crate::mem_info().is_none());
        assert!(!crate::device());
        assert_eq!(batch_decline_count("query"), 2);
        #[cfg(feature = "test-fault")]
        {
            use crate::fault::{self, Class, Point};
            let previous = fault::armed();
            fault::arm(Class::Ntt, Point::Launch, 1);
            assert_eq!(fault::armed(), previous);
            assert!(fault::msm_bucket_records(&[], &[], &[]).is_none());
            assert_eq!(batch_decline_count("fault"), 2);
            session.set_worker(true);
            fault::arm(Class::Ntt, Point::Launch, 1);
            assert_eq!(fault::armed(), previous + 1);
        }
        assert!(!crate::end_request());
        crate::begin_request();
        assert_eq!(batch_decline_count("request"), 2);
        assert!(!crate::teardown_context());
        assert!(!crate::teardown_ntt_tables());
        crate::evict_tables();
        assert_eq!(crate::quotient::evict_key_copies(), 0);
        assert_eq!(batch_decline_count("eviction"), 2);
        assert!(!crate::device_disabled());
        assert!(session.finish());
    }

    #[cfg(not(midnight_gpu_cuda))]
    #[test]
    fn retired_msm_latches_failure_before_the_next_entry() {
        if in_parent() {
            return;
        }
        assert!(crate::set_min_k(1));
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        session.set_worker(true);
        let scalars = [[0; 4]; 2];
        let bases = [[0; 12]; 2];
        crate::teardown::on_unconfirmed_drain();
        assert!(isolated_msm_g1(&scalars, &bases).is_none());
        assert_eq!(crate::teardown::declined_after_teardown(), 1);
        assert!(batch_erasure_failed());
        assert!(isolated_msm_g1(&scalars, &bases).is_none());
        assert_eq!(batch_msm_counts(), (0, 0, 1));
        assert!(!session.finish());
    }

    #[test]
    fn shared_call_unwind_closes_admission() {
        if in_parent() {
            return;
        }
        assert!(
            std::panic::catch_unwind(|| with_shared_scratch(|| panic!("call interrupted")))
                .is_err()
        );
        assert!(batch_erasure_failed());
        assert!(!with_shared_scratch(|| panic!("unexpected call")));
    }

    #[cfg(midnight_gpu_cuda)]
    #[test]
    fn device_owner_marks_only_session_requests() {
        if in_parent() {
            return;
        }
        if !crate::device() {
            eprintln!("skipped: no device");
            return;
        }
        exercise_owner_panic_scope();
    }

    #[cfg(midnight_gpu_cuda)]
    pub(crate) fn exercise_owner_panic_scope() {
        static DELEGATED: AtomicBool = AtomicBool::new(false);
        std::panic::set_hook(Box::new(|info| {
            if info.payload().downcast_ref::<&str>() == Some(&"ordinary owner marker") {
                DELEGATED.store(true, Relaxed);
            } else {
                std::process::exit(1);
            }
        }));
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        let on_actor = AtomicBool::new(false);
        let stderr = std::io::stderr().lock();
        let result = midnight_proofs::gpu::batch::prove_batch(
            &[1],
            1,
            1,
            None,
            |_, _| {
                session.set_worker(true);
                let _admitted = admit_batch("msm").unwrap();
                let answer: Option<()> = crate::ffi::call(|| {
                    on_actor.store(crate::ffi::on_actor(), Relaxed);
                    panic!("owner panic marker");
                });
                answer.is_none()
            },
            || true,
        )
        .unwrap();
        drop(stderr);
        assert!(matches!(result.jobs[..], [Ok(true)]));
        assert!(on_actor.load(Relaxed));
        assert!(!DELEGATED.load(Relaxed));
        assert!(session.finish());
        let answer: Option<()> = crate::ffi::call(|| panic!("ordinary owner marker"));
        assert!(answer.is_none());
        assert!(DELEGATED.load(Relaxed));
    }

    #[test]
    fn cleanup_payload_bound_fails_final_boundary() {
        if in_parent() {
            return;
        }
        static DROPS: AtomicU64 = AtomicU64::new(0);
        struct Again;
        impl Drop for Again {
            fn drop(&mut self) {
                if DROPS.fetch_add(1, Relaxed) < 8 {
                    std::panic::panic_any(Again);
                }
            }
        }
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        drop_payload(Box::new(Again));
        assert_eq!(DROPS.load(Relaxed), 8);
        assert!(session.failure_signal().is_triggered());
        assert!(!session.finish());
    }

    #[cfg(feature = "actor")]
    #[test]
    fn leaked_permit_releases_batch_waiter() {
        if !in_parent() {
            exercise_leaked_permit(false, false);
            exercise_leaked_permit(true, false);
        }
    }

    #[cfg(feature = "actor")]
    #[test]
    fn session_payload_leak_releases_batch_waiter() {
        if !in_parent() {
            exercise_leaked_permit(true, true);
        }
    }

    #[cfg(feature = "actor")]
    fn exercise_leaked_permit(bound: bool, session_leak: bool) {
        use std::time::{Duration, Instant};

        use midnight_proofs::gpu::batch::{BatchHooks, JobPanicked, failure_signal, prove_batch};

        use crate::actor::chan::{Budget, BudgetPermit, ChanError, Shutdown};

        static DROPS: AtomicU64 = AtomicU64::new(0);
        struct Payload(u8, Option<BudgetPermit>);
        impl Drop for Payload {
            fn drop(&mut self) {
                DROPS.fetch_add(1, Relaxed);
                let permit = self.1.take().unwrap();
                if self.0 == 1 {
                    std::panic::panic_any(permit);
                }
                std::panic::panic_any(Payload(self.0 - 1, Some(permit)));
            }
        }

        let caller = rayon::ThreadPoolBuilder::new().num_threads(2).build().unwrap();
        caller.install(|| {
            let session = bound.then(|| BatchSession::begin(&BATCH_THREAD).unwrap());
            let bind = |action: midnight_proofs::gpu::batch::WorkerAction<'_>| {
                session.as_ref().unwrap().set_worker(action);
            };
            let hooks = if bound {
                BatchHooks::new(None, &bind)
            } else {
                None.into()
            };
            let budget = Budget::new(1, 1);
            let permit = Mutex::new(Some(budget.reserve(1, &Shutdown::new()).unwrap()));
            let drops = DROPS.load(Relaxed);
            let outcome = prove_batch(
                &[1, 1],
                2,
                2,
                hooks,
                |i, _| {
                    let signal = Shutdown::from(failure_signal().unwrap());
                    if i == 0 {
                        let permit = permit.lock().unwrap().take();
                        let deadline = Instant::now() + Duration::from_secs(5);
                        while !budget.has_waiter() {
                            assert!(Instant::now() < deadline, "budget waiter did not queue");
                            std::thread::yield_now();
                        }
                        let payload = Payload(8, permit);
                        if session_leak {
                            drop_payload(Box::new(payload));
                            return None;
                        }
                        std::panic::panic_any(payload);
                    }
                    assert!(!signal.is_triggered());
                    let start = Instant::now();
                    let decline = budget.reserve(1, &signal).err();
                    assert!(
                        start.elapsed() < Duration::from_secs(5),
                        "budget decline was late"
                    );
                    decline
                },
                || true,
            )
            .unwrap();
            if session_leak {
                assert!(matches!(outcome.jobs[0], Ok(None)));
            } else {
                assert!(matches!(outcome.jobs[0], Err(JobPanicked)));
            }
            assert!(matches!(outcome.jobs[1], Ok(Some(ChanError::Teardown))));
            assert!(outcome.erasure_failed);
            assert_eq!(DROPS.load(Relaxed) - drops, 8);
            assert_eq!(budget.available_permits(), 0);
            if let Some(s) = session {
                assert!(s.failure_signal().is_triggered());
                assert!(!s.end_wave());
                assert!(!s.finish());
                assert!(batch_erasure_failed());
            }
        });
    }

    #[test]
    fn unconfirmed_registered_release_declines_the_next_msm() {
        if in_parent() {
            return;
        }
        let bases = [[0; 12]];
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        session.set_worker(true);
        let handle = crate::register_srs(&bases);
        crate::msm::mark_context_without_actor(&handle);
        assert!(isolated_msm_g1(&[], &[]).is_none());
        assert!(erasure_ok(&crate::wipe::stats()));
        assert!(batch_erasure_failed());
        assert!(isolated_msm_g1(&[], &[]).is_none());
        assert_eq!(batch_msm_counts(), (0, 0, 1));
        assert!(!session.finish());
    }

    #[cfg(not(midnight_gpu_cuda))]
    #[test]
    fn displaced_contexts_wait_for_final_boundary() {
        if in_parent() {
            return;
        }
        let bases = [[0; 12]];
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        let first = crate::register_srs(&bases);
        crate::msm::mark_context_without_actor(&first);
        let second = crate::register_srs(&bases);
        drop(first);
        assert!(second.verify(&bases));
        crate::msm::mark_context_without_actor(&second);
        drop(second);
        assert_eq!(deferred_releases(), 0);
        assert!(session.end_wave());
        assert_eq!(deferred_releases(), 0);
        // The stub cannot release a live context. Both attempts must run
        // even when the first fails, also when close runs during unwind.
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
            let _session = session;
            panic!("leave session");
        }));
        assert!(caught.is_err());
        assert_eq!(deferred_releases(), 2);
        assert!(erasure_ok(&crate::wipe::stats()));
        assert!(batch_erasure_failed());
        assert!(matches!(
            BatchSession::begin(&BATCH_THREAD),
            Err(SessionError::ErasureFailed)
        ));
    }

    #[test]
    fn cleanup_payload_chain_is_dropped() {
        struct Last;
        static DROPS: AtomicU64 = AtomicU64::new(0);
        impl Drop for Last {
            fn drop(&mut self) {
                DROPS.fetch_add(1, Relaxed);
            }
        }
        struct First;
        impl Drop for First {
            fn drop(&mut self) {
                std::panic::panic_any(Last);
            }
        }
        assert!(!cleanup_succeeded(|| std::panic::panic_any(First)));
        assert_eq!(DROPS.load(Relaxed), 1);
    }

    fn batch_decline_count(class: &str) -> u64 {
        crate::declines()
            .into_iter()
            .filter(|(c, r, _)| *c == class && *r == "batch")
            .map(|(_, _, n)| n)
            .sum()
    }

    /// A direct ordinary call during a batch declines with reason
    /// `batch`, and so does a saved ordinary function pointer.
    #[test]
    fn ordinary_and_saved_pointer_decline_batch_during_session() {
        if in_parent() {
            return;
        }
        let saved: fn(&[crate::Scalar], &[crate::G1AffineLimbs]) -> Option<crate::G1JacobianLimbs> =
            crate::msm_g1;
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        session.set_worker(true);
        let scalars = vec![[0u64; 4]; 4];
        let bases = vec![[0u64; 12]; 4];
        let before = batch_decline_count("msm");
        assert!(crate::msm_g1(&scalars, &bases).is_none());
        assert_eq!(
            batch_decline_count("msm"),
            before + 1,
            "ordinary direct call during a batch must decline as batch"
        );
        assert!(saved(&scalars, &bases).is_none());
        assert_eq!(
            batch_decline_count("msm"),
            before + 2,
            "saved function pointer during a batch must decline as batch"
        );
        let mut a = vec![[0u64; 4]; 16];
        let ntt_before = batch_decline_count("ntt");
        assert!(!crate::fft(&mut a, [0u64; 4], 4));
        assert_eq!(
            batch_decline_count("ntt"),
            ntt_before + 1,
            "ordinary fft during a batch must decline as batch"
        );
        let before = batch_decline_count("quotient");
        for call in [crate::quotient, crate::quotient::quotient] {
            // SAFETY: admission declines before the null job is accessed.
            assert!(!unsafe { call(std::ptr::null(), &mut []) });
        }
        assert_eq!(batch_decline_count("quotient"), before + 2);
        drop(session);
    }

    /// An ordinary call held in flight finishes before a batch session
    /// that started waiting meanwhile is admitted.
    #[test]
    fn batch_start_waits_for_ordinary_call_in_flight() {
        use std::{
            sync::mpsc,
            thread,
            time::{Duration, Instant},
        };
        if in_parent() {
            return;
        }
        let timeout = Duration::from_secs(10);
        test_hold::ENTERED.store(false, Relaxed);
        test_hold::RELEASE.store(false, Relaxed);
        test_hold::ARMED.store(true, Relaxed);
        let prior = crate::declines()
            .into_iter()
            .find(|(c, r, _)| *c == "msm" && *r == "shape")
            .map_or(0, |(_, _, n)| n);
        let (done, finished) = mpsc::channel();
        let ordinary = thread::spawn(move || {
            assert!(crate::msm_g1(&[], &[]).is_none());
            done.send(()).unwrap();
        });
        let deadline = Instant::now() + timeout;
        while !test_hold::ENTERED.load(Relaxed) {
            assert!(Instant::now() < deadline, "ordinary entry timed out");
            thread::yield_now();
        }
        assert!(matches!(GATE.try_write(), Err(TryLockError::WouldBlock)));
        let (started, starting) = mpsc::channel();
        let (entered, admitted) = mpsc::channel();
        let starter = thread::spawn(move || {
            started.send(()).unwrap();
            let session = BatchSession::begin(&BATCH_THREAD).unwrap();
            // The ordinary operation reached its shape check before batch entry.
            let saw_shape = crate::declines()
                .iter()
                .any(|(c, r, n)| *c == "msm" && *r == "shape" && *n > prior);
            assert!(isolated_msm_g1(&[], &[]).is_none());
            drop(session);
            entered.send(saw_shape).unwrap();
        });
        starting.recv_timeout(timeout).unwrap();
        assert!(matches!(
            admitted.recv_timeout(Duration::from_millis(100)),
            Err(mpsc::RecvTimeoutError::Timeout)
        ));
        test_hold::RELEASE.store(true, Relaxed);
        finished.recv_timeout(timeout).unwrap();
        assert!(admitted.recv_timeout(timeout).unwrap());
        test_hold::ARMED.store(false, Relaxed);
        for thread in [ordinary, starter] {
            let deadline = Instant::now() + timeout;
            while !thread.is_finished() {
                assert!(Instant::now() < deadline, "worker did not exit");
                std::thread::yield_now();
            }
            thread.join().unwrap();
        }
    }

    /// A poisoned owner lock (an unwind while it was held) latches the
    /// erasure failure: the next isolated MSM must not proceed as if
    /// the check had passed.
    #[test]
    fn poisoned_owner_latches_erasure_failure() {
        if in_parent() {
            return;
        }
        *session_failure() = None;
        let poisoner = std::panic::catch_unwind(|| {
            let _owner = OWNER.lock().unwrap_or_else(|e| e.into_inner());
            panic!("poison the owner lock");
        });
        assert!(poisoner.is_err(), "the poisoner panicked");
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        session.set_worker(true);
        let scalars = vec![[0u64; 4]; 4];
        let bases = vec![[0u64; 12]; 4];
        let _ = isolated_msm_g1(&scalars, &bases);
        let latched = batch_erasure_failed();
        drop(session);
        *session_failure() = None;
        assert!(
            latched,
            "a poisoned owner lock must latch the erasure failure"
        );
    }

    /// An unwind after the MSM still runs the eviction and latches the
    /// erasure failure.
    #[test]
    fn unwind_after_msm_evicts_and_latches() {
        if in_parent() {
            return;
        }
        *session_failure() = None;
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        session.set_worker(true);
        let evictions0 = EVICT_RUNS.load(Relaxed);
        PANIC_AFTER_MSM.store(true, Relaxed);
        let scalars = vec![[0u64; 4]; 4];
        let bases = vec![[0u64; 12]; 4];
        let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            isolated_msm_g1(&scalars, &bases)
        }));
        let evictions1 = EVICT_RUNS.load(Relaxed);
        let latched = batch_erasure_failed();
        drop(session);
        *session_failure() = None;
        OWNER.clear_poison();
        assert!(panicked.is_err(), "the test panic unwound");
        assert!(evictions1 > evictions0, "the eviction ran on the unwind");
        assert!(latched, "the unwind latched the erasure failure");
    }

    #[test]
    fn eviction_unwind_fails_the_boundary() {
        if in_parent() {
            return;
        }
        *session_failure() = None;
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        session.set_worker(true);
        PANIC_ON_EVICT.store(true, Relaxed);
        assert!(isolated_msm_g1(&[], &[]).is_none());
        assert!(!PANIC_ON_EVICT.load(Relaxed));
        assert!(!session.end_wave());
        assert!(!session.finish());
        *session_failure() = None;
    }

    #[test]
    fn final_erasure_failure_is_reported_and_latched_on_drop() {
        if in_parent() {
            return;
        }
        for explicit in [true, false] {
            *session_failure() = None;
            let session = BatchSession::begin(&BATCH_THREAD).unwrap();
            FAIL_BOUNDARY.store(true, Relaxed);
            if explicit {
                assert!(!session.finish());
            } else {
                drop(session);
            }
            assert!(batch_erasure_failed());
            assert!(!FAIL_BOUNDARY.load(Relaxed));
        }
        *session_failure() = None;
    }

    /// The eviction counter counts only evictions that freed a live
    /// context after a taken MSM: a declined MSM and a sweep of an
    /// empty registry do not move it.
    #[test]
    fn declined_msm_and_empty_sweep_do_not_count_evictions() {
        if in_parent() {
            return;
        }
        *session_failure() = None;
        let session = BatchSession::begin(&BATCH_THREAD).unwrap();
        session.set_worker(true);
        let runs = EVICT_RUNS.load(Relaxed);
        let (_, evictions0, _) = batch_msm_counts();
        assert!(isolated_msm_g1(&[], &[]).is_none());
        assert_eq!(EVICT_RUNS.load(Relaxed), runs + 1);
        let (_, evictions1, _) = batch_msm_counts();
        drop(session);
        assert_eq!(
            evictions1, evictions0,
            "no live context was freed, so no eviction may be counted"
        );
    }
}
