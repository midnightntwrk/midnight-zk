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

//! FFI to the CUDA core (`cuda/midnight_gpu.cu`), present only when it is
//! compiled in (cfg `midnight_gpu_cuda`). One dedicated device-owner
//! thread (the actor, see [`call`]) makes the CUDA context current and
//! is the only thread that calls into the CUDA core for device work;
//! callers send it typed requests and wait for the reply. Detection
//! that makes no context ([`probe`], versions) and the host-memory-only
//! counters stay callable from any thread. There is no device lock.
#![allow(dead_code)]

use std::{
    cell::Cell,
    ffi::{CStr, c_char, c_void},
    sync::OnceLock,
};

use crate::{GpuInfo, actor::chan};

unsafe extern "C" {
    /// The CUDA runtime and driver versions (0 when unknown); makes no
    /// context.
    fn mgpu_versions(runtime: *mut i32, driver: *mut i32);
    fn mgpu_probe(
        name: *mut c_char,
        len: usize,
        sm: *mut i32,
        major: *mut i32,
        minor: *mut i32,
        integrated: *mut i32,
        total: *mut usize,
    ) -> i32;
    fn mgpu_device_count(
        name: *mut c_char,
        len: usize,
        sm: *mut i32,
        major: *mut i32,
        minor: *mut i32,
    ) -> i32;
    fn mgpu_last_error() -> *const c_char;
    pub(crate) fn mgpu_mem_info(free: *mut usize, total: *mut usize) -> i32;
    pub(crate) fn mgpu_msm_ctx_new(points: *const c_void, n: usize) -> *mut c_void;
    /// 0: the context's blob was zeroed, confirmed and freed; -1: an erasure
    /// or release failed (counted; the blob is in the core's quarantine).
    pub(crate) fn mgpu_msm_ctx_free(ctx: *mut c_void) -> i32;
    pub(crate) fn mgpu_quarantine_retry() -> i32;
    pub(crate) fn mgpu_quarantined() -> u64;
    /// `[unconfirmed blocks, their bytes, zeroed-unfreed blocks, failed
    /// pre-zeroing syncs]`. Host memory only.
    pub(crate) fn mgpu_quarantine_pending(out: *mut u64);
    /// `[blocks, bytes]` of the core's quarantine lost unerased at a
    /// context reset (sticky). Host memory only.
    pub(crate) fn mgpu_teardown_lost(out: *mut u64);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_fail_lib_wipes(n: i32);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_fail_dev_frees(n: i32);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_fail_wipe_presync(n: i32);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_fail_lib_frees(n: i32);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_double_quarantine(out: *mut u64) -> i32;
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_error_arms(out: *mut u64) -> i32;
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_msm_throw(n: i32);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_stage_paths(out: *mut u64) -> i32;
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_msm_worker_throw(n: i32);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_unconfirm_drains(n: i32);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_get_after_unconfirmed_drain(out: *mut u64) -> i32;
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_staged_sync_fail(out: *mut u64) -> i32;
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_probe_cooperative(out: *mut i64) -> i32;
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_probe_async_alloc(out: *mut i64) -> i32;
    /// `[error drains run, of them not confirmed]`. Host memory only.
    pub(crate) fn mgpu_drain_counters(out: *mut u64);
    #[cfg(feature = "test-fault")]
    pub(crate) fn mgpu_test_ctx_buckets(
        ctx: *mut c_void,
        out: *mut u64,
        max_words: usize,
        words: *mut u32,
    ) -> i64;
    pub(crate) fn mgpu_wipe_set_check(check: i32);
    pub(crate) fn mgpu_device_count_only() -> i32;
    pub(crate) fn mgpu_primary_ctx_active() -> i32;
    pub(crate) fn mgpu_lib_dtoh(out: *mut u64);
    pub(crate) fn mgpu_lib_dtoh_reset();
    pub(crate) fn mgpu_msm_ctx_run(
        ctx: *mut c_void,
        out: *mut c_void,
        scalars: *const c_void,
        n: usize,
    ) -> i32;
    pub(crate) fn mgpu_dev_alloc(bytes: usize) -> *mut c_void;
    pub(crate) fn mgpu_dev_free(p: *mut c_void) -> i32;
    pub(crate) fn mgpu_dev_bytes(out: *mut u64);
    pub(crate) fn mgpu_dev_bytes_reset_peak();
    pub(crate) fn mgpu_erase_failures() -> u64;
    pub(crate) fn mgpu_dtoh_private(src: *const c_void, bytes: usize, fault: i32) -> *const c_void;
    pub(crate) fn mgpu_host_copy(dst: *mut c_void, src: *const c_void, bytes: usize);
    pub(crate) fn mgpu_dev_zero(p: *mut c_void, bytes: usize) -> i32;
    pub(crate) fn mgpu_dev_nonzero(p: *const c_void, bytes: usize, count: *mut u64) -> i32;
    pub(crate) fn mgpu_wipe_counters(out: *mut u64);
    pub(crate) fn mgpu_wipe_reset(check: i32);
    pub(crate) fn mgpu_dtoh(dst: *mut c_void, src: *const c_void, bytes: usize) -> i32;
    pub(crate) fn mgpu_htod(dst: *mut c_void, src: *const c_void, bytes: usize) -> i32;
    pub(crate) fn mgpu_dev_sync() -> i32;
    pub(crate) fn mgpu_stage_counters(out: *mut u64);
    pub(crate) fn mgpu_stage_wipe_counters(out: *mut u64);
    pub(crate) fn mgpu_stage_end() -> i32;
    pub(crate) fn mgpu_ntt_dev(d: *mut c_void, lg: u32, inverse: i32) -> i32;
    pub(crate) fn mgpu_coeff_to_extended_dev(
        dst: *mut c_void,
        src: *const c_void,
        k: u32,
        ext_k: u32,
        zeta2: *const c_void,
    ) -> i32;
    pub(crate) fn mgpu_distribute_zeta_dev(d: *mut c_void, n: usize, zeta2: *const c_void) -> i32;
    pub(crate) fn mgpu_scale_dev(d: *mut c_void, n: usize, c: *const c_void) -> i32;
    pub(crate) fn mgpu_mul_periodic_dev(
        d: *mut c_void,
        n: usize,
        t: *const c_void,
        tn: usize,
    ) -> i32;
    pub(crate) fn mgpu_quotient_run(job: *const c_void) -> i32;
    pub(crate) fn mgpu_job_size() -> usize;
}

/// A typed request to the device-owner actor. Stage 1 is
/// correctness only: every operation class is exclusive, the actor
/// runs one request at a time, so the device sees exactly the
/// sequence it saw under the old lock.
enum DeviceRequest {
    /// One exclusive device operation (any of the operation classes:
    /// stage, MSM, NTT/coset, quotient, read-back, allocation,
    /// registration, eviction, fault injection). The work runs on
    /// the actor thread and sends its own reply before returning.
    Op(Box<dyn FnOnce() + Send>),
    /// Teardown work: runs even after the shutdown signal, after
    /// the operation in flight. Queued `Op`s behind the signal are
    /// dropped unrun instead (their callers see the closed reply
    /// and decline with the teardown reason).
    TeardownOp(Box<dyn FnOnce() + Send>),
}

impl std::fmt::Debug for DeviceRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeviceRequest::Op(_) => f.write_str("DeviceRequest::Op"),
            DeviceRequest::TeardownOp(_) => f.write_str("DeviceRequest::TeardownOp"),
        }
    }
}

#[derive(Debug)]
struct DeviceActor {
    tx: chan::Tx<ScopedRequest>,
    shutdown: chan::Shutdown,
}

// A teardown before first use seals this slot empty. Startup and retirement
// therefore agree on the owner even while the thread is being started.
static ACTOR: OnceLock<Option<DeviceActor>> = OnceLock::new();
// The outcome of the first context initialization, published once it
// is complete: a caller that arrives while the actor is still making
// the context queues a request instead of reading a half-set state.
static CONTEXT: OnceLock<bool> = OnceLock::new();

thread_local! {
    static ON_ACTOR: Cell<bool> = const { Cell::new(false) };
}

/// Whether the calling thread is the device-owner actor thread.
pub(crate) fn on_actor() -> bool {
    ON_ACTOR.with(|c| c.get())
}

// Makes the CUDA context current on the actor thread (its first
// device operation does this) and remembers the outcome. Actor
// thread only.
fn ensure_context() -> bool {
    *CONTEXT.get_or_init(init_context)
}

fn init_context() -> bool {
    if probe().is_none() {
        return false;
    }
    // the core's check mode before its first free
    crate::wipe::check();
    let mut name = [0 as c_char; 128];
    let (mut sm, mut ma, mut mi) = (0, 0, 0);
    // SAFETY: every out pointer is valid.
    let n = unsafe { mgpu_device_count(name.as_mut_ptr(), name.len(), &mut sm, &mut ma, &mut mi) };
    if n <= 0 {
        crate::diag!("midnight-gpu: no usable device: {}", last_error());
        return false;
    }
    true
}

type ScopedRequest = (DeviceRequest, Option<crate::batch::PanicFlag>);

fn actor_loop(mut rx: chan::Rx<ScopedRequest>, shutdown: chan::Shutdown) {
    ON_ACTOR.with(|c| c.set(true));
    while let Some((req, flag)) = rx.blocking_recv() {
        struct Restore(crate::batch::PanicFlag, bool);
        impl Drop for Restore {
            fn drop(&mut self) {
                self.0.set(self.1);
            }
        }
        let _restore = flag.map(|key| Restore(key, key.replace(true)));
        match req {
            DeviceRequest::Op(work) => {
                // Teardown began while this request was queued:
                // drop it unrun. Its reply sender drops with it, so
                // the caller (still waiting, see `call`) declines
                // and makes no device call on the dead context.
                if shutdown.is_triggered() || crate::teardown::device_disabled() {
                    drop(work);
                    continue;
                }
                if !ensure_context() {
                    drop(work);
                    continue;
                }
                if let Err(payload) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(work)) {
                    crate::batch::drop_payload(payload);
                    if flag.is_none() {
                        crate::diag!("midnight-gpu: device request panicked");
                    }
                }
                if crate::teardown::device_disabled() {
                    shutdown.trigger();
                }
            }
            DeviceRequest::TeardownOp(work) => {
                shutdown.trigger();
                if let Err(payload) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(work)) {
                    crate::batch::drop_payload(payload);
                    if flag.is_none() {
                        crate::diag!("midnight-gpu: teardown request panicked");
                    }
                }
            }
        }
    }
}

/// The device-owner actor, started on first use.
fn actor() -> Option<&'static DeviceActor> {
    ACTOR
        .get_or_init(|| {
            let (tx, rx) = chan::channel::<ScopedRequest>(64);
            let shutdown = chan::Shutdown::new();
            let loop_shutdown = shutdown.clone();
            std::thread::Builder::new()
                .name("midnight-gpu-device".to_string())
                .spawn(move || actor_loop(rx, loop_shutdown))
                .ok()?;
            Some(DeviceActor { tx, shutdown })
        })
        .as_ref()
}

/// Whether the device actor's teardown has begun.
pub(crate) fn tearing_down() -> bool {
    ACTOR.get().and_then(Option::as_ref).is_some_and(|a| a.shutdown.is_triggered())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CallError {
    Unavailable,
    Panicked,
}

// Field order also applies when a request is discarded without running it.
struct Work<F, R> {
    f: F,
    reply: chan::ReplyTx<Result<R, CallError>>,
}

struct CheckDrains<F: FnOnce()>(Option<F>);

impl<F: FnOnce()> Drop for CheckDrains<F> {
    fn drop(&mut self) {
        if let Some(check) = self.0.take() {
            check();
        }
    }
}

impl<F: FnOnce() -> R, R> Work<F, R> {
    fn run(self, check: Option<impl FnOnce()>, batch: bool) {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _drains = CheckDrains(check);
            (self.f)()
        }))
        .map_err(|payload| {
            crate::batch::drop_payload(payload);
            CallError::Panicked
        });
        if result.is_err() && !batch {
            crate::diag!("midnight-gpu: device operation panicked");
        }
        let _ = self.reply.send(result);
    }
}

// A refused send drops the request here. If the actor discards the request,
// Work drops the borrowed closure before closing the reply channel. If it
// runs, the closure returns or unwinds and the drain check finishes before
// the reply. The caller waits unconditionally even after shutdown.
fn dispatch<R: Send>(
    a: &DeviceActor,
    teardown: bool,
    f: impl FnOnce() -> R + Send,
) -> Result<R, CallError> {
    if teardown {
        a.shutdown.trigger();
    }
    if on_actor() {
        return Ok(f());
    }
    let (reply, rrx) = chan::reply_channel();
    let request = Work { f, reply };
    let flag = crate::batch::REQUEST_FLAG.get();
    let work = Box::new(move || {
        request.run(
            (!teardown).then_some(crate::teardown::check_drains),
            flag.is_some(),
        )
    });
    // SAFETY: see the comment above; the caller waits until `work`
    // has run or was dropped by the actor.
    let work: Box<dyn FnOnce() + Send + 'static> =
        unsafe { std::mem::transmute::<Box<dyn FnOnce() + Send + '_>, _>(work) };
    let req = if teardown {
        DeviceRequest::TeardownOp(work)
    } else {
        DeviceRequest::Op(work)
    };
    // A teardown request sends unconditionally (its own signal must
    // not abort it); an operation's send observes the signal, and a
    // refusal there dropped `work` on this thread, unrun.
    let never;
    let send_shutdown = if teardown {
        never = chan::Shutdown::new();
        &never
    } else {
        &a.shutdown
    };
    match a.tx.blocking_send((req, flag), send_shutdown) {
        Ok(()) => {}
        Err(_) => return Err(CallError::Unavailable),
    }
    rrx.blocking_wait_unconditional().map_err(|_| CallError::Unavailable)?
}

/// Runs one device operation on the actor thread and waits for its
/// result. An unavailable actor, an unavailable device, teardown or a
/// panic in the operation gives `None`. Exclusive:
/// one operation in flight at a time (stage 1).
pub(crate) fn call<R: Send>(f: impl FnOnce() -> R + Send) -> Option<R> {
    dispatch(actor()?, false, f).ok()
}

/// [`call`] for device work that must not run on a retired device:
/// `None` when the device is already retired, and the actor drops
/// the request unrun when teardown began while it was queued, so no
/// call runs on the dead context (one would make a fresh context).
/// Callers map `None` to their decline, with the teardown reason
/// where they distinguish it.
pub(crate) fn call_live<R: Send>(f: impl FnOnce() -> R + Send) -> Option<R> {
    call_result(f).ok()
}

pub(crate) fn call_result<R: Send>(f: impl FnOnce() -> R + Send) -> Result<R, CallError> {
    if crate::teardown::device_disabled() {
        return Err(CallError::Unavailable);
    }
    dispatch(actor().ok_or(CallError::Unavailable)?, false, f)
}

/// Stops admission and retires on the existing owner. If teardown wins
/// first use, no owner can subsequently start.
pub(crate) fn call_teardown<R: Send>(f: impl FnOnce() -> R + Send) -> Option<R> {
    match ACTOR.get_or_init(|| None) {
        Some(owner) => dispatch(owner, true, f).ok(),
        None => Some(f()),
    }
}

/// Tables can only exist after a device operation initialized the context.
pub(crate) fn context_ready() -> bool {
    CONTEXT.get() == Some(&true)
}

/// The last error of the CUDA core on this thread.
pub(crate) fn last_error() -> String {
    // SAFETY: the core returns a NUL-terminated thread-local buffer.
    unsafe { CStr::from_ptr(mgpu_last_error()) }.to_string_lossy().into_owned()
}

#[allow(clippy::unnecessary_cast)] // c_char is i8 on some targets
fn name_of(name: &[c_char]) -> String {
    let bytes: Vec<u8> = name.iter().take_while(|c| **c != 0).map(|c| *c as u8).collect();
    String::from_utf8_lossy(&bytes).into_owned()
}

/// Device 0 from its properties (no CUDA context).
pub(crate) fn probe() -> Option<&'static GpuInfo> {
    static PROBE: OnceLock<Option<GpuInfo>> = OnceLock::new();
    PROBE
        .get_or_init(|| {
            let mut name = [0 as c_char; 128];
            let (mut sm, mut ma, mut mi, mut int, mut tot) = (0, 0, 0, 0, 0usize);
            // SAFETY: every out pointer is valid. Properties only:
            // no context is made, so detection stays off the actor.
            let n = unsafe {
                mgpu_probe(
                    name.as_mut_ptr(),
                    name.len(),
                    &mut sm,
                    &mut ma,
                    &mut mi,
                    &mut int,
                    &mut tot,
                )
            };
            let (mut rt, mut drv) = (0, 0);
            // SAFETY: valid out pointers; no context is made.
            unsafe { mgpu_versions(&mut rt, &mut drv) };
            (n > 0).then(|| GpuInfo {
                name: name_of(&name),
                devices: n as u32,
                sm_count: sm as u32,
                compute_capability: (ma as u32, mi as u32),
                integrated: int != 0,
                total_bytes: tot as u64,
                runtime_version: rt.max(0) as u32,
                driver_version: drv.max(0) as u32,
            })
        })
        .as_ref()
}

/// Device 0 with its CUDA context made on the actor thread (the
/// first call makes it, through an actor request).
pub(crate) fn context() -> bool {
    if crate::teardown::device_disabled() {
        return false;
    }
    if probe().is_none() {
        return false;
    }
    if let Some(&ready) = CONTEXT.get() {
        return ready;
    }
    // An empty operation: the actor loop makes the context before
    // running it (and drops it unrun when there is no device).
    call(|| true).unwrap_or(false)
}

/// `(free, total)` device bytes.
pub(crate) fn mem_info() -> Option<(usize, usize)> {
    call_live(mem_info_locked).flatten()
}

/// [`mem_info`] for a caller already on the actor thread.
pub(crate) fn mem_info_locked() -> Option<(usize, usize)> {
    let (mut f, mut t) = (0, 0);
    // SAFETY: valid out pointers.
    (unsafe { mgpu_mem_info(&mut f, &mut t) } == 0).then_some((f, t))
}

/// A device buffer of this crate. Dropping it zeroes it first when it may
/// hold witness values (`secret`); a failed zeroing or free keeps the region
/// in quarantine (see [`crate::wipe`]). Its release is a request to
/// the actor (wipe, confirm, free); on the actor thread it runs inline.
#[derive(Debug)]
pub(crate) struct DevBuf {
    pub(crate) ptr: *mut c_void,
    pub(crate) bytes: usize,
    secret: bool,
}

// SAFETY: a device address; every use runs on the actor thread.
unsafe impl Send for DevBuf {}

impl DevBuf {
    /// Allocates `bytes` (the caller runs on the actor thread).
    pub(crate) fn new(bytes: usize, secret: bool) -> Option<DevBuf> {
        // SAFETY: plain allocation.
        let ptr = unsafe { mgpu_dev_alloc(bytes.max(1)) };
        if ptr.is_null() {
            crate::diag!(
                "midnight-gpu: device allocation of {bytes} bytes: {}",
                last_error()
            );
            return None;
        }
        Some(DevBuf { ptr, bytes, secret })
    }

    pub(crate) fn addr(&self) -> u64 {
        self.ptr as u64
    }
}

impl Drop for DevBuf {
    fn drop(&mut self) {
        if crate::teardown::device_disabled() {
            // The pointer went with the reset context: forget it
            // without a CUDA call (which would also make a fresh
            // context) and count no new erasure failure.
            return;
        }
        // The release (wipe, confirm, free) is a request to the
        // actor; on the actor thread `call` runs it inline. It must
        // not block forever at teardown or after the actor is gone:
        // when the request cannot run, the region is kept in
        // quarantine by its host-side record (no CUDA call), so the
        // pointer is never lost and `pending_erasure` stays exact.
        let (addr, bytes, secret) = (self.ptr as u64, self.bytes, self.secret);
        let ran = call(move || {
            let ptr = addr as *mut c_void;
            if secret {
                crate::wipe::release(ptr, bytes);
            } else {
                // SAFETY: our allocation, freed once.
                if unsafe { mgpu_dev_free(ptr) } != 0 {
                    crate::wipe::quarantine(ptr, bytes);
                }
            }
        });
        if ran.is_none() {
            crate::wipe::quarantine(self.ptr, self.bytes);
        }
    }
}

/// Copies `src` to the device buffer `dst` (staged when large).
pub(crate) fn htod<T>(dst: &DevBuf, offset: usize, src: &[T]) -> bool {
    let bytes = std::mem::size_of_val(src);
    if offset + bytes > dst.bytes {
        return false;
    }
    crate::xfer::note_h2d(bytes);
    // SAFETY: both regions are valid for `bytes`.
    unsafe {
        mgpu_htod(
            (dst.ptr as *mut u8).add(offset) as *mut c_void,
            src.as_ptr() as *const c_void,
            bytes,
        ) == 0
    }
}

/// Copies device bytes into `dst` only once the whole read-back and its
/// synchronisation succeeded: the core reads into a private host buffer of
/// the request first (zeroed at [`crate::end_request`]). `fault`: the test
/// fault fires after the first chunk. `false`: `dst` is unchanged.
pub(crate) fn dtoh_commit<T>(dst: &mut [T], src: *const c_void, fault: bool) -> bool {
    let bytes = std::mem::size_of_val(dst);
    crate::xfer::note_d2h(bytes);
    // SAFETY: `src` is a device region of at least `bytes`.
    let p = unsafe { mgpu_dtoh_private(src, bytes, fault as i32) };
    if p.is_null() {
        return false;
    }
    // SAFETY: the private buffer holds `bytes`; `dst` is valid for them.
    unsafe { mgpu_host_copy(dst.as_mut_ptr() as *mut c_void, p, bytes) };
    true
}

/// Waits for the device stream.
pub(crate) fn sync() -> bool {
    // SAFETY: no arguments.
    unsafe { mgpu_dev_sync() == 0 }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::{
        process::Command,
        time::{Duration, Instant},
    };

    use super::*;

    pub(crate) fn empty_key_copy() -> DevBuf {
        // A public null buffer exercises the actual release request. The core
        // accepts a null free without entering the device runtime.
        CONTEXT.get_or_init(|| true);
        DevBuf {
            ptr: std::ptr::null_mut(),
            bytes: 32,
            secret: false,
        }
    }

    pub(crate) fn seal_absent_actor() {
        assert!(ACTOR.get_or_init(|| None).is_none());
    }

    // Retirement and first use are process-wide. Run each case with fresh state.
    pub(crate) fn isolated(test: impl FnOnce()) {
        let thread = std::thread::current();
        let name = thread.name().unwrap();
        if std::env::var("MGPU_OWNER_TEST").as_deref() == Ok(name) {
            test();
            return;
        }
        let mut command = Command::new(std::env::current_exe().unwrap());
        command.args(["--exact", name, "--nocapture"]).env("MGPU_OWNER_TEST", name);
        if name.ends_with("owner_panic_scope_without_device") {
            command.env("MIDNIGHT_GPU", "off");
        }
        #[cfg(target_os = "linux")]
        if name.ends_with("failed_diagnostic_keeps_owner_alive") {
            command.stderr(std::fs::File::options().write(true).open("/dev/full").unwrap());
        }
        let mut child = command.spawn().unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        loop {
            if let Some(status) = child.try_wait().unwrap() {
                assert!(status.success(), "isolated test failed");
                return;
            }
            if Instant::now() >= deadline {
                child.kill().expect("could not stop isolated test");
                let reap = Instant::now() + Duration::from_secs(5);
                while child.try_wait().unwrap().is_none() {
                    assert!(Instant::now() < reap, "isolated test did not exit");
                    std::thread::sleep(Duration::from_millis(10));
                }
                panic!("isolated test timed out");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    #[test]
    fn owner_panic_scope_without_device() {
        isolated(|| {
            // Only host closures run. Session cleanup skips device discovery.
            assert!(crate::present().is_none());
            CONTEXT.set(true).unwrap();
            crate::batch::tests::exercise_owner_panic_scope();
        });
    }

    #[test]
    fn teardown_uses_started_actor_before_context_creation() {
        isolated(|| {
            let _ = actor();
            assert!(crate::teardown::teardown_context());
            assert!(tearing_down(), "owner did not receive teardown");
            assert!(CONTEXT.get().is_none());
        });
    }

    #[test]
    fn disabled_owner_drops_queued_work_without_shutdown_signal() {
        isolated(|| {
            assert!(crate::teardown::teardown_context());
            CONTEXT.set(true).unwrap();
            let (tx, rx) = chan::channel(1);
            let (reply, wait) = chan::reply_channel();
            let request = DeviceRequest::Op(Box::new(move || reply.send(()).unwrap()));
            let signal = chan::Shutdown::new();
            tx.blocking_send((request, None), &signal).unwrap();
            drop(tx);
            actor_loop(rx, signal);
            assert_eq!(
                wait.blocking_wait_unconditional(),
                Err(chan::ChanError::Closed)
            );
        });
    }

    #[test]
    fn retirement_rejects_a_late_quarantine_record() {
        isolated(|| {
            assert!(crate::teardown::teardown_context());
            let before = crate::wipe::pending_erasure();
            crate::wipe::quarantine(std::ptr::dangling_mut(), 32);
            assert_eq!(crate::wipe::pending_erasure(), before);
        });
    }

    #[test]
    fn retirement_before_start_seals_the_owner_slot() {
        isolated(|| {
            assert!(crate::teardown::teardown_context());
            assert!(actor().is_none());
        });
    }

    #[test]
    fn disconnected_owner_never_retires_on_caller() {
        isolated(|| {
            let (tx, rx) = chan::channel(1);
            drop(rx);
            ACTOR
                .set(Some(DeviceActor {
                    tx,
                    shutdown: chan::Shutdown::new(),
                }))
                .unwrap();
            assert!(!crate::teardown::teardown_context());
            #[cfg(feature = "test-fault")]
            {
                crate::teardown::trigger_unconfirmed_drain_for_test();
                crate::teardown::retire_after_holding_lock_for_test(Duration::ZERO);
            }
            assert!(!crate::teardown::device_disabled());
            assert!(!crate::teardown::erasure_failed());
        });
    }

    #[test]
    fn empty_table_teardown_leaves_context_uninitialized() {
        isolated(|| {
            if crate::present().is_none() {
                eprintln!("skipped: no device");
                return;
            }
            assert!(crate::teardown::teardown_ntt_tables());
            assert!(CONTEXT.get().is_none());
            assert!(ACTOR.get().is_none());
        });
    }

    #[test]
    fn table_teardown_during_shutdown_succeeds() {
        isolated(|| {
            CONTEXT.set(true).unwrap();
            actor().unwrap().shutdown.trigger();
            assert!(!crate::teardown::device_disabled());
            assert!(crate::teardown::teardown_ntt_tables());
        });
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn failed_diagnostic_keeps_owner_alive() {
        isolated(|| {
            CONTEXT.set(true).unwrap();
            assert_eq!(
                call_result(|| panic!("test operation")),
                Err(CallError::Panicked)
            );
            assert_eq!(call_result(on_actor), Ok(true));
        });
    }

    #[cfg(feature = "test-fault")]
    #[test]
    fn panic_after_unconfirmed_drain_retires_before_reply() {
        isolated(|| {
            if !crate::device() {
                eprintln!("skipped: no device");
                return;
            }
            let drains = crate::error_drains().1;
            let mut injected = false;
            let result = call_result(|| {
                injected = crate::fault::gets_after_unconfirmed_drain().is_some();
                panic!("test operation");
            });
            assert_eq!(result, Err::<(), _>(CallError::Panicked));
            assert!(injected);
            assert!(crate::error_drains().1 > drains);
            assert!(crate::teardown::device_disabled());
            assert!(crate::teardown::context_reset_done());
            assert_eq!(crate::wipe::pending_erasure().undrained, 0);
        });
    }

    #[test]
    fn panicking_work_checks_drains_before_answering() {
        let (reply, wait) = chan::reply_channel();
        let (began, started) = std::sync::mpsc::channel();
        let (release, gate) = std::sync::mpsc::channel();
        let (answer, result) = std::sync::mpsc::channel();
        let bound = Duration::from_secs(3);
        std::thread::spawn(move || {
            let work = Work {
                f: || panic!("test operation"),
                reply,
            };
            work.run(
                Some(|| {
                    began.send(std::thread::panicking()).unwrap();
                    gate.recv_timeout(bound).expect("drain check timed out");
                }),
                false,
            );
        });
        std::thread::spawn(move || answer.send(wait.blocking_wait_unconditional()).unwrap());
        assert!(
            started.recv_timeout(bound).unwrap(),
            "check did not run during unwind"
        );
        assert_eq!(
            result.recv_timeout(Duration::from_millis(50)),
            Err(std::sync::mpsc::RecvTimeoutError::Timeout)
        );
        release.send(()).unwrap();
        assert_eq!(
            result.recv_timeout(bound),
            Ok(Ok(Err::<(), _>(CallError::Panicked)))
        );
    }

    #[test]
    fn discarded_work_drops_borrow_before_reply_closes() {
        use std::sync::mpsc;
        struct Borrow {
            began: mpsc::Sender<()>,
            release: mpsc::Receiver<()>,
        }
        impl Drop for Borrow {
            fn drop(&mut self) {
                self.began.send(()).unwrap();
                self.release.recv_timeout(Duration::from_secs(3)).expect("destructor timed out");
            }
        }
        isolated(|| {
            let (began, dropping) = mpsc::channel();
            let (release, gate) = mpsc::channel();
            let (answer, result) = mpsc::channel();
            let (tx, mut rx) = chan::channel(1);
            let local = DeviceActor {
                tx,
                shutdown: chan::Shutdown::new(),
            };
            std::thread::spawn(move || {
                let borrow = Borrow {
                    began,
                    release: gate,
                };
                answer.send(dispatch(&local, false, move || drop(borrow))).unwrap();
            });
            std::thread::spawn(move || drop(rx.blocking_recv().unwrap()));
            dropping.recv_timeout(Duration::from_secs(3)).unwrap();
            assert_eq!(
                result.recv_timeout(Duration::from_millis(100)),
                Err(mpsc::RecvTimeoutError::Timeout)
            );
            release.send(()).unwrap();
            assert_eq!(
                result.recv_timeout(Duration::from_secs(3)),
                Ok(Err(CallError::Unavailable))
            );
        });
    }
}
