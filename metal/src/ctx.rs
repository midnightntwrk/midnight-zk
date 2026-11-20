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

//! The Metal device context: the default `MTLDevice`, one command queue, the
//! shader library and a pipeline cache, made at first use ([`context`]).
//!
//! ```ignore
//! let mut s = ctx::lock()?;                  // serialises device work
//! let a = s.ctx().upload(scalars)?;           // a scoped, zeroed-on-drop buffer
//! let tw = s.scratch("ntt-twiddles", bytes)?; // a per-request buffer
//! let ns = s.ctx().run(|c| {
//!     c.dispatch("ntt_radix2", n / 2, &[Arg::Buffer(&a), Arg::value(&n)])?;
//!     Ok(())
//! })?.1;
//! a.read(out);
//! ```
//!
//! [`lock`] returns a [`Session`], which also guards the per-request buffers,
//! so [`end_request`] never zeroes a buffer a kernel is using. [`Ctx::run`]
//! encodes dispatches into one command buffer with one serial encoder and
//! waits for it; a command buffer in the error state is [`Error::Device`].
//!
//! Every buffer is `MTLResourceStorageModeShared`, so host access is a plain
//! copy. Caller slices are copied rather than wrapped (wrapping needs
//! page-aligned slices), which also means the caller's slice is written only
//! once the device result is complete.
//!
//! Buffers:
//! - [`Buffer`]: owned by the caller, zeroed when dropped if it may hold a
//!   non-zero byte.
//! - Pooled ([`Ctx::alloc_pooled`]): taken from and returned to a pool of
//!   zeroed buffers, because a new buffer delays its first command buffer
//!   while Metal maps it.
//! - Per-request ([`Session::scratch`], [`take_request_buffer`]): kept under a
//!   key until [`end_request_report`] zeroes them, or zeroed at the end of a
//!   hook call made outside a request (`wipe_unbracketed`).

use std::{
    collections::{BTreeSet, HashMap, hash_map::Entry},
    ffi::c_void,
    marker::PhantomData,
    panic::{AssertUnwindSafe, catch_unwind},
    ptr::NonNull,
    sync::{
        Arc, Condvar, Mutex, MutexGuard, OnceLock,
        atomic::{
            AtomicBool, AtomicU64,
            Ordering::{Relaxed, SeqCst},
        },
    },
};

#[cfg(midnight_metal_metallib)]
use dispatch2::DispatchData;
use objc2::{rc::Retained, runtime::ProtocolObject};
use objc2_foundation::{NSObjectProtocol, NSString};
use objc2_metal::{
    MTLBuffer, MTLCommandBuffer, MTLCommandBufferStatus, MTLCommandEncoder, MTLCommandQueue,
    MTLCompileOptions, MTLComputeCommandEncoder, MTLComputePipelineState,
    MTLCreateSystemDefaultDevice, MTLDevice, MTLGPUFamily, MTLLanguageVersion, MTLLibrary,
    MTLResidencySet, MTLResidencySetDescriptor, MTLResource, MTLResourceOptions, MTLSize,
    MTLStorageMode,
};

use crate::{MetalInfo, account::Reason};

// MTLCreateSystemDefaultDevice returns no device unless the process links
// CoreGraphics.
#[link(name = "CoreGraphics", kind = "framework")]
unsafe extern "C" {}

/// The Metal Shading Language version of the shaders (set by `build.rs`).
pub const MSL_VERSION: &str = env!("MIDNIGHT_METAL_MSL_VERSION");

#[cfg(midnight_metal_metallib)]
static METALLIB: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/midnight_metal.metallib"));
static SOURCE: &str = include_str!(concat!(env!("OUT_DIR"), "/midnight_metal.metal"));

/// A device failure, mapped to a decline reason by [`Error::reason`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// No usable device, or the context could not be made.
    NoDevice(String),
    /// A buffer could not be allocated (or is above `maxBufferLength`).
    Memory(String),
    /// A pipeline, encoder or command buffer failed.
    Device(String),
    /// A scalar argument of a device building block is not reduced.
    Unreduced(String),
}

impl Error {
    /// The decline reason of this error.
    pub fn reason(&self) -> &'static str {
        Reason::of(self).name()
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::NoDevice(m) => write!(f, "no device: {m}"),
            Error::Memory(m) => write!(f, "memory: {m}"),
            Error::Device(m) => write!(f, "device error: {m}"),
            Error::Unreduced(m) => write!(f, "unreduced: {m}"),
        }
    }
}

type Device = Retained<ProtocolObject<dyn MTLDevice>>;
type Pipeline = Retained<ProtocolObject<dyn MTLComputePipelineState>>;

// ---------------------------------------------------------------------------
// Detection

struct Probe {
    device: Device,
    info: MetalInfo,
}

static PROBE: OnceLock<Option<Probe>> = OnceLock::new();

fn probe_device() -> Option<&'static Probe> {
    PROBE
        .get_or_init(|| {
            let device = MTLCreateSystemDefaultDevice()?;
            let tg = device.maxThreadsPerThreadgroup();
            let apple_family = (1..=10u32)
                .rev()
                .find(|f| device.supportsFamily(MTLGPUFamily(1000 + *f as isize)))
                .unwrap_or(0);
            let info = MetalInfo {
                name: device.name().to_string(),
                registry_id: device.registryID(),
                unified_memory: device.hasUnifiedMemory(),
                recommended_max_working_set: device.recommendedMaxWorkingSetSize(),
                max_buffer_length: device.maxBufferLength() as u64,
                max_threads_per_threadgroup: tg.width as u64,
                apple_family,
                metal3: device.supportsFamily(MTLGPUFamily::Metal3),
                msl_version: MSL_VERSION,
            };
            Some(Probe { device, info })
        })
        .as_ref()
}

/// The device's properties, without loading the library. `None`: no Metal
/// device.
pub fn probe() -> Option<&'static MetalInfo> {
    probe_device().map(|p| &p.info)
}

// ---------------------------------------------------------------------------
// Context

/// The process-wide device context.
pub struct Ctx {
    device: Device,
    queue: Retained<ProtocolObject<dyn MTLCommandQueue>>,
    library: Retained<ProtocolObject<dyn MTLLibrary>>,
    library_source: String,
    pipelines: Mutex<HashMap<String, Pipeline>>,
    /// The queue's residency set; `None` before macOS 15.
    resident: Option<Mutex<Resident>>,
}

/// Buffers of at least this many bytes stay in the queue's residency set.
const RESIDENT_MIN: usize = 1 << 20;

/// The queue's residency set.
///
/// Metal evicts a buffer unused for about two seconds even while the GPU is
/// busy, and its next use then waits while it is made resident again. A proof
/// takes about that long, so large buffers would be re-made resident every
/// proof. [`Ctx`] adds every buffer of at least [`RESIDENT_MIN`] bytes when it
/// is made (idle pool buffers included) and removes it when released.
struct Resident {
    set: Retained<ProtocolObject<dyn MTLResidencySet>>,
}

// SAFETY: a residency set may be used from any thread; every change goes
// through the mutex around it.
unsafe impl Send for Resident {}

impl Ctx {
    fn residency(&self) -> Option<MutexGuard<'_, Resident>> {
        self.resident.as_ref().map(|r| r.lock().unwrap_or_else(|e| e.into_inner()))
    }

    /// Adds a new buffer to the residency set (when it is large enough).
    fn keep(&self, b: &ProtocolObject<dyn MTLBuffer>) {
        if b.length() >= RESIDENT_MIN
            && let Some(r) = self.residency()
        {
            r.set.addAllocation(ProtocolObject::from_ref(b));
            r.set.commit();
            r.set.requestResidency();
        }
    }
}

/// Removes a buffer being released from the residency set. A buffer is
/// released by its last owner, after the GPU work that used it.
fn unkeep(b: &ProtocolObject<dyn MTLBuffer>) {
    if b.length() >= RESIDENT_MIN
        && let Some(Ok(c)) = CTX.get()
        && let Some(r) = c.residency()
    {
        r.set.removeAllocation(ProtocolObject::from_ref(b));
        r.set.commit();
    }
}

impl std::fmt::Debug for Ctx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ctx")
            .field("device", &self.device.name().to_string())
            .field("library_source", &self.library_source)
            .finish_non_exhaustive()
    }
}

static CTX: OnceLock<Result<Ctx, String>> = OnceLock::new();

/// The context, made at the first call. A failure is kept: later calls
/// return it without trying again.
pub fn context() -> Result<&'static Ctx, Error> {
    CTX.get_or_init(make_context).as_ref().map_err(|e| Error::NoDevice(e.clone()))
}

/// Why the context could not be made, if it was tried and failed.
pub fn context_error() -> Option<&'static str> {
    match CTX.get() {
        Some(Err(e)) => Some(e),
        _ => None,
    }
}

fn make_context() -> Result<Ctx, String> {
    let probe = probe_device().ok_or("no Metal device")?;
    let device = probe.device.clone();
    let queue = device.newCommandQueue().ok_or("newCommandQueue returned nil")?;
    let (library, library_source) = load_library(&device)?;
    // the residency set of the large buffers (macOS 15+)
    let resident = if device.respondsToSelector(objc2::sel!(newResidencySetWithDescriptor:error:)) {
        let desc = MTLResidencySetDescriptor::new();
        device.newResidencySetWithDescriptor_error(&desc).ok().map(|set| {
            queue.addResidencySet(&set);
            Mutex::new(Resident { set })
        })
    } else {
        None
    };
    Ok(Ctx {
        device,
        queue,
        library,
        library_source,
        pipelines: Mutex::new(HashMap::new()),
        resident,
    })
}

/// The shader library and its origin: the embedded metallib, else the
/// embedded source compiled now.
fn load_library(
    device: &Device,
) -> Result<(Retained<ProtocolObject<dyn MTLLibrary>>, String), String> {
    #[cfg(midnight_metal_metallib)]
    let how = if std::env::var("MIDNIGHT_METAL_SHADER_SOURCE").as_deref() == Ok("1") {
        "source (MIDNIGHT_METAL_SHADER_SOURCE=1)".to_string()
    } else {
        let data = DispatchData::from_static_bytes(METALLIB);
        match device.newLibraryWithData_error(&data) {
            Ok(lib) => return Ok((lib, "metallib".into())),
            Err(e) => {
                let why = e.localizedDescription().to_string();
                eprintln!(
                    "midnight-metal: the embedded metallib did not load ({why}); \
                     compiling the embedded shader source"
                );
                format!("source (metallib refused: {why})")
            }
        }
    };
    #[cfg(not(midnight_metal_metallib))]
    let how = "source (no metallib was built)".to_string();
    let options = MTLCompileOptions::new();
    options.setLanguageVersion(language_version()?);
    let lib = device
        .newLibraryWithSource_options_error(&NSString::from_str(SOURCE), Some(&options))
        .map_err(|e| format!("shader compile failed: {}", e.localizedDescription()))?;
    Ok((lib, how))
}

/// [`MSL_VERSION`] as `MTLCompileOptions.languageVersion`.
fn language_version() -> Result<MTLLanguageVersion, String> {
    let (major, minor) = MSL_VERSION
        .split_once('.')
        .and_then(|(a, b)| Some((a.parse::<usize>().ok()?, b.parse::<usize>().ok()?)))
        .ok_or_else(|| format!("bad MSL version {MSL_VERSION}"))?;
    Ok(MTLLanguageVersion((major << 16) + minor))
}

// ---------------------------------------------------------------------------
// Byte accounting

static BYTES_NOW: AtomicU64 = AtomicU64::new(0);
static BYTES_PEAK: AtomicU64 = AtomicU64::new(0);
/// Bytes in buffers that are not idle in the pool.
static IN_USE: AtomicU64 = AtomicU64::new(0);
/// The peak of [`IN_USE`] since process start or the last [`begin_request`].
static IN_USE_PEAK: AtomicU64 = AtomicU64::new(0);

/// Adds `bytes` to [`IN_USE`] and raises its peak.
fn in_use_add(bytes: u64) {
    let now = IN_USE.fetch_add(bytes, Relaxed) + bytes;
    IN_USE_PEAK.fetch_max(now, Relaxed);
}

/// Counts a new buffer of `bytes` bytes (held and in use).
fn count_alloc(bytes: u64) {
    let now = BYTES_NOW.fetch_add(bytes, Relaxed) + bytes;
    BYTES_PEAK.fetch_max(now, Relaxed);
    in_use_add(bytes);
}

/// `(now, peak)` bytes held in this crate's Metal buffers, idle pool buffers
/// included. The peak is since process start or the last [`begin_request`].
pub fn device_bytes() -> (u64, u64) {
    (BYTES_NOW.load(Relaxed), BYTES_PEAK.load(Relaxed))
}

/// Bytes in buffers in use now: [`device_bytes`] without idle pool buffers.
pub fn in_use_bytes() -> u64 {
    IN_USE.load(Relaxed)
}

/// The peak of [`in_use_bytes`] since the last [`begin_request`], which resets
/// it to the bytes in use then.
pub fn request_peak_bytes() -> u64 {
    IN_USE_PEAK.load(Relaxed)
}

/// Whether a request is open.
static REQUEST_OPEN: AtomicBool = AtomicBool::new(false);

/// Opens a request and resets the peaks of [`device_bytes`] and
/// [`request_peak_bytes`].
pub fn begin_request() {
    BYTES_PEAK.store(BYTES_NOW.load(Relaxed), Relaxed);
    IN_USE_PEAK.store(IN_USE.load(Relaxed), Relaxed);
    REQUEST_OPEN.store(true, SeqCst);
}

/// Whether a request is open ([`begin_request`] was called and its
/// [`end_request_report`] has not started).
pub fn request_open() -> bool {
    REQUEST_OPEN.load(SeqCst)
}

// ---------------------------------------------------------------------------
// The pool of zeroed buffers

/// Zeroed buffers kept for reuse ([`Ctx::alloc_pooled`]).
///
/// Invariant: every buffer in the pool reads zero. A buffer enters only
/// zero-filled by Metal and never written, or after its whole allocation was
/// zeroed ([`pool_put`]), so a buffer that held a witness value is never
/// handed out again unzeroed. A buffer whose zeroing panicked or that failed
/// the erasure check is released instead. The pool keeps at most
/// [`pool_limit`] bytes.
struct Pool {
    free: Vec<Retained<ProtocolObject<dyn MTLBuffer>>>,
    bytes: u64,
}

// SAFETY: Metal buffers may be used from any thread; the pool's buffers are
// idle (no host reference to their contents, no GPU work).
unsafe impl Send for Pool {}

/// The pool of zeroed buffers.
static POOL: Mutex<Pool> = Mutex::new(Pool {
    free: Vec::new(),
    bytes: 0,
});
/// [`pool_limit`]: [`POOL_LIMIT_UNREAD`] until read.
static POOL_LIMIT: AtomicU64 = AtomicU64::new(POOL_LIMIT_UNREAD);
/// [`POOL_LIMIT`] before the environment is read.
const POOL_LIMIT_UNREAD: u64 = u64::MAX;

/// The pool, locked; a poisoned lock is taken over (no update under it is
/// left half done).
fn pool() -> MutexGuard<'static, Pool> {
    POOL.lock().unwrap_or_else(|e| e.into_inner())
}

/// The most bytes the pool keeps idle: `MIDNIGHT_METAL_POOL_MIB` (read once),
/// else a quarter of `recommendedMaxWorkingSetSize`.
pub fn pool_limit() -> u64 {
    let l = POOL_LIMIT.load(Relaxed);
    if l != POOL_LIMIT_UNREAD {
        return l;
    }
    // a huge value saturates below the marker, so it is read once
    let l = std::env::var("MIDNIGHT_METAL_POOL_MIB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .map(|m| m.saturating_mul(1 << 20))
        .unwrap_or_else(|| probe().map_or(0, |i| i.recommended_max_working_set / 4))
        .min(POOL_LIMIT_UNREAD - 1);
    let _ = POOL_LIMIT.compare_exchange(POOL_LIMIT_UNREAD, l, Relaxed, Relaxed);
    POOL_LIMIT.load(Relaxed)
}

/// Sets [`pool_limit`] in bytes (`None`: the default again) and releases
/// idle buffers above it. Test support.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn set_pool_limit(limit: Option<u64>) {
    POOL_LIMIT.store(
        limit.map_or(POOL_LIMIT_UNREAD, |l| l.min(POOL_LIMIT_UNREAD - 1)),
        Relaxed,
    );
    let limit = pool_limit();
    let freed: Vec<_> = {
        let mut p = pool();
        let mut out = Vec::new();
        while p.bytes > limit {
            let Some(b) = p.free.pop() else { break };
            p.bytes -= b.length() as u64;
            out.push(b);
        }
        out
    };
    release_raw(freed);
}

/// Bytes of the idle (zeroed) buffers in the pool.
pub fn pool_bytes() -> u64 {
    pool().bytes
}

/// Releases idle buffers taken out of the pool (a debug build reads each one
/// back first).
fn release_raw(bufs: Vec<Retained<ProtocolObject<dyn MTLBuffer>>>) -> u64 {
    debug_assert!(
        bufs.iter().all(|b| raw_reads_zero(b)),
        "an idle buffer of the pool does not read zero"
    );
    release_unchecked(bufs)
}

/// Releases buffers taken out of the pool: out of the residency set and the
/// byte count. Returns their bytes.
fn release_unchecked(bufs: Vec<Retained<ProtocolObject<dyn MTLBuffer>>>) -> u64 {
    let bytes: u64 = bufs.iter().map(|b| b.length() as u64).sum();
    for b in &bufs {
        unkeep(b);
    }
    drop(bufs);
    BYTES_NOW.fetch_sub(bytes, Relaxed);
    bytes
}

/// Releases every idle buffer of the pool once background zeroing has ended.
/// Returns the bytes released.
pub fn release_pool() -> u64 {
    settle_releases();
    let bufs = {
        let mut p = pool();
        p.bytes = 0;
        std::mem::take(&mut p.free)
    };
    release_raw(bufs)
}

/// The smallest pooled buffer of at least `bytes` and at most a quarter
/// more.
fn pool_take(bytes: usize) -> Option<Retained<ProtocolObject<dyn MTLBuffer>>> {
    let mut p = pool();
    let max = bytes.saturating_add(bytes / 4);
    let i = p
        .free
        .iter()
        .enumerate()
        .filter(|(_, b)| (bytes..=max).contains(&b.length()))
        .min_by_key(|(_, b)| b.length())?
        .0;
    let b = p.free.swap_remove(i);
    p.bytes -= b.length() as u64;
    in_use_add(b.length() as u64);
    Some(b)
}

/// Releases idle buffers of the pool, the largest first, until at least
/// `need` bytes are freed or the pool is empty. Returns the bytes freed.
fn release_idle(need: u64) -> u64 {
    let freed: Vec<_> = {
        let mut p = pool();
        p.free.sort_by_key(|b| b.length());
        let mut out = Vec::new();
        let mut got = 0u64;
        while got < need {
            let Some(b) = p.free.pop() else { break };
            let len = b.length() as u64;
            p.bytes -= len;
            got += len;
            out.push(b);
        }
        out
    };
    release_raw(freed)
}

/// Puts a zeroed buffer into the pool, or releases it when the pool would
/// exceed its limit. The caller has zeroed the whole allocation (or it is
/// Metal-zeroed and unwritten): the callers are [`Buffer`]'s drop after
/// [`Buffer::erase`] and the erasure report, neither of which pools a buffer
/// that failed.
fn pool_put(raw: Retained<ProtocolObject<dyn MTLBuffer>>) {
    let len = raw.length() as u64;
    IN_USE.fetch_sub(len, Relaxed);
    let limit = pool_limit();
    let back = {
        let mut p = pool();
        if p.bytes + len <= limit {
            p.bytes += len;
            p.free.push(raw);
            None
        } else {
            Some(raw)
        }
    };
    if let Some(b) = back {
        release_raw(vec![b]);
    }
}

/// Background zeroing ([`release_later`]): each call has a ticket, and
/// `outstanding` holds the tickets not yet complete.
struct Releases {
    next: u64,
    outstanding: BTreeSet<u64>,
}

/// The tickets of [`release_later`].
static RELEASES: Mutex<Releases> = Mutex::new(Releases {
    next: 0,
    outstanding: BTreeSet::new(),
});
/// Notified whenever a ticket of [`RELEASES`] completes.
static RELEASED: Condvar = Condvar::new();

/// The tickets, locked (a poisoned lock is taken over).
fn releases() -> MutexGuard<'static, Releases> {
    RELEASES.lock().unwrap_or_else(|e| e.into_inner())
}

/// Zeroings that panicked (each completed on the calling thread, its buffer
/// released) since the last [`end_request_report`].
static ERASE_FAULTS: AtomicU64 = AtomicU64::new(0);

/// Drops `bufs` (each zeroed, then pooled or released) on a background
/// thread, or on this one when no thread can be made. [`settle_releases`]
/// waits for it, so at the end of a request every such buffer is zeroed.
pub fn release_later(bufs: Vec<Buffer>) {
    if bufs.is_empty() {
        return;
    }
    let ticket = {
        let mut r = releases();
        let t = r.next;
        r.next += 1;
        r.outstanding.insert(t);
        t
    };
    // the buffers stay reachable from here if the thread is not made
    let slot = Arc::new(Mutex::new(Some(bufs)));
    let theirs = Arc::clone(&slot);
    let spawned = std::thread::Builder::new()
        .name("midnight-metal-release".into())
        .spawn(move || release_now(&theirs, ticket));
    if spawned.is_err() {
        release_now(&slot, ticket);
    }
}

/// Drops the buffers of a [`release_later`] call and completes its ticket.
/// Never panics.
fn release_now(slot: &Mutex<Option<Vec<Buffer>>>, ticket: u64) {
    let bufs = slot.lock().unwrap_or_else(|e| e.into_inner()).take();
    for b in bufs.into_iter().flatten() {
        // `Buffer::drop` does not unwind (its zeroing catches a panic); a
        // panic from the pool or residency bookkeeping after it is counted
        if catch_unwind(AssertUnwindSafe(|| drop(b))).is_err() {
            ERASE_FAULTS.fetch_add(1, Relaxed);
        }
    }
    releases().outstanding.remove(&ticket);
    RELEASED.notify_all();
}

/// Whether a [`release_later`] call has not completed yet.
pub(crate) fn releases_pending() -> bool {
    !releases().outstanding.is_empty()
}

/// Waits until every [`release_later`] call made before this one has
/// completed.
pub fn settle_releases() {
    let mut r = releases();
    let target = r.next;
    while r.outstanding.first().is_some_and(|t| *t < target) {
        r = RELEASED.wait(r).unwrap_or_else(|e| e.into_inner());
    }
}

// ---------------------------------------------------------------------------
// Host copies

/// Copies `src` into `dst` on several threads when long. Never panics: a part
/// whose thread cannot be made is copied here, so a copy into a caller's slice
/// never stops half way.
pub(crate) fn par_copy(dst: &mut [crate::Scalar], src: &[crate::Scalar]) {
    const PART: usize = 1 << 15;
    if src.len() <= 2 * PART {
        dst.copy_from_slice(src);
        return;
    }
    let threads = std::thread::available_parallelism().map_or(4, |t| t.get()).min(8);
    let per = src.len().div_ceil(threads).max(PART);
    std::thread::scope(|s| {
        for (d, c) in dst.chunks_mut(per).zip(src.chunks(per)) {
            // the part stays reachable from here if the thread is not made
            // (a failed `spawn_scoped` drops its closure)
            let part = Arc::new(Mutex::new(Some((d, c))));
            let theirs = Arc::clone(&part);
            let spawned = std::thread::Builder::new().spawn_scoped(s, move || {
                if let Some((d, c)) = theirs.lock().unwrap_or_else(|e| e.into_inner()).take() {
                    d.copy_from_slice(c);
                }
            });
            if spawned.is_err()
                && let Some((d, c)) = part.lock().unwrap_or_else(|e| e.into_inner()).take()
            {
                d.copy_from_slice(c);
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Buffers

/// Plain data: every bit pattern is valid and there is no padding.
///
/// # Safety
/// Implement it only for such types.
pub unsafe trait Pod: Copy + 'static {}
// SAFETY: integers and arrays of them have no padding and no invalid values.
unsafe impl Pod for u8 {}
// SAFETY: as above.
unsafe impl Pod for u32 {}
// SAFETY: as above.
unsafe impl Pod for u64 {}
// SAFETY: as above.
unsafe impl<T: Pod, const N: usize> Pod for [T; N] {}

/// A shared-storage Metal buffer, zeroed when dropped.
pub struct Buffer {
    raw: Retained<ProtocolObject<dyn MTLBuffer>>,
    bytes: usize,
    /// Goes back to the pool when dropped; cleared when its zeroing panicked
    /// or it failed the erasure check, so it is released instead.
    pooled: bool,
    /// May hold a non-zero byte: written by the host or bound to a kernel
    /// since last zeroed.
    dirty: AtomicBool,
}

// SAFETY: Metal buffers may be used from any thread; host access to the
// contents goes through `&self` / `&mut self`, and GPU access happens only
// inside `Ctx::run`, which borrows the buffer and waits for the GPU.
unsafe impl Send for Buffer {}
// SAFETY: as above.
unsafe impl Sync for Buffer {}

impl std::fmt::Debug for Buffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Buffer").field("bytes", &self.bytes).finish()
    }
}

/// Byte runs of at least this size are processed on several threads.
const PAR_BYTES: usize = 4 << 20;

/// The threads of a parallel host pass over memory.
fn mem_threads() -> usize {
    std::thread::available_parallelism().map_or(4, |t| t.get()).min(8)
}

/// `f(start, len)` over `[0, len)` in parts of at least [`PAR_BYTES`] (a
/// multiple of 64), on several threads; `true` when every part returned
/// `true`. A part whose thread cannot be made or panicked is redone on the
/// calling thread, so with a non-panicking `f` this covers the whole range.
fn par_ranges(len: usize, f: impl Fn(usize, usize) -> bool + Sync) -> bool {
    if len < 2 * PAR_BYTES {
        return f(0, len);
    }
    let per = len.div_ceil(mem_threads()).max(PAR_BYTES).next_multiple_of(64);
    std::thread::scope(|s| {
        let parts: Vec<_> = (0..len)
            .step_by(per)
            .map(|a| {
                let n = per.min(len - a);
                let f = &f;
                let h = std::thread::Builder::new().spawn_scoped(s, move || f(a, n)).ok();
                (a, n, h)
            })
            .collect();
        let mut all = true;
        for (a, n, h) in parts {
            let ok = match h {
                Some(h) => h.join().unwrap_or_else(|_| f(a, n)),
                None => f(a, n),
            };
            all &= ok;
        }
        all
    })
}

/// Zeroes the whole allocation of `raw`. Does not panic. The caller has
/// exclusive use of the contents (no host reference, no GPU work).
fn raw_zero(raw: &ProtocolObject<dyn MTLBuffer>) {
    let base = raw.contents().as_ptr() as usize;
    par_ranges(raw.length(), |a, n| {
        // SAFETY: `contents` is valid for `length()` bytes, the caller has
        // exclusive use of them, and the parts are disjoint.
        unsafe { std::ptr::write_bytes((base + a) as *mut u8, 0, n) };
        true
    });
    std::sync::atomic::compiler_fence(SeqCst);
}

/// Whether `raw`'s whole allocation reads zero (volatile word loads). Does
/// not panic.
fn raw_reads_zero(raw: &ProtocolObject<dyn MTLBuffer>) -> bool {
    let base = raw.contents().as_ptr() as usize;
    par_ranges(raw.length(), |a, n| {
        let p = (base + a) as *const u8;
        let words = n / 8;
        // SAFETY: `contents` is valid for the allocation's bytes; `a` is a
        // multiple of 64 and `contents` page aligned, so `p` is 8-byte
        // aligned; the reads stay inside the part.
        unsafe {
            (0..words).all(|i| std::ptr::read_volatile(p.cast::<u64>().add(i)) == 0)
                && (words * 8..n).all(|i| std::ptr::read_volatile(p.add(i)) == 0)
        }
    })
}

/// Debug builds: asserts that samples of a new buffer read zero (Metal
/// documents new buffers as zero-filled).
fn debug_assert_zero_filled(raw: &ProtocolObject<dyn MTLBuffer>) {
    if cfg!(debug_assertions) {
        let len = raw.length();
        let p = raw.contents().as_ptr() as *const u8;
        // the first and last bytes, and about 64 bytes spread between
        let step = (len / 64).max(1);
        let ok = (0..len).step_by(step).chain([len - 1]).all(|i| {
            // SAFETY: `i < len`, inside the allocation; nothing else uses
            // the new buffer yet.
            unsafe { std::ptr::read_volatile(p.add(i)) == 0 }
        });
        debug_assert!(ok, "a new Metal buffer of {len} bytes is not zero-filled");
    }
}

impl Buffer {
    /// The length in bytes.
    pub fn len_bytes(&self) -> usize {
        self.bytes
    }

    /// The host address of the contents.
    fn ptr(&self) -> *mut u8 {
        self.raw.contents().as_ptr().cast()
    }

    /// Records that the buffer may now hold a non-zero byte.
    fn touch(&self) {
        self.dirty.store(true, Relaxed);
    }

    /// The contents as a slice of `T`.
    pub fn as_slice<T: Pod>(&self) -> &[T] {
        // SAFETY: `contents` is page aligned, valid for `bytes` bytes, and no
        // GPU work writes it while `&self` is held outside `Ctx::run`.
        unsafe { std::slice::from_raw_parts(self.ptr().cast(), self.bytes / size_of::<T>()) }
    }

    /// The contents as a mutable slice of `T`.
    pub fn as_mut_slice<T: Pod>(&mut self) -> &mut [T] {
        self.touch();
        // SAFETY: as `as_slice`, and `&mut self` is exclusive.
        unsafe { std::slice::from_raw_parts_mut(self.ptr().cast(), self.bytes / size_of::<T>()) }
    }

    /// Copies `data` to the start of the buffer. Panics if it does not fit.
    pub fn write<T: Pod>(&mut self, data: &[T]) {
        self.as_mut_slice::<T>()[..data.len()].copy_from_slice(data);
    }

    /// Copies the start of the buffer into `out`. Panics if it is shorter.
    pub fn read<T: Pod>(&self, out: &mut [T]) {
        out.copy_from_slice(&self.as_slice::<T>()[..out.len()]);
    }

    /// Zeroes the whole allocation (which may exceed [`Buffer::len_bytes`]).
    /// Does not panic and always zeroes every byte.
    pub fn zero(&mut self) {
        // exclusive: `&mut self`
        raw_zero(&self.raw);
        self.dirty.store(false, Relaxed);
    }

    /// Zeroes the buffer if it may hold a non-zero byte. If the zeroing
    /// panics, it is redone on this thread without threads or allocation, the
    /// buffer is marked not to be pooled, and the fault is counted for
    /// [`end_request_report`].
    fn erase(&mut self) {
        if !self.dirty.load(Relaxed) {
            return;
        }
        let r = catch_unwind(AssertUnwindSafe(|| {
            test_switch::zeroing_panic(self.ptr() as usize);
            self.zero()
        }));
        if r.is_err() {
            // SAFETY: valid for `raw.length()` bytes, exclusive (`&mut self`).
            unsafe { std::ptr::write_bytes(self.ptr(), 0, self.raw.length()) };
            std::sync::atomic::compiler_fence(SeqCst);
            self.dirty.store(false, Relaxed);
            self.pooled = false;
            ERASE_FAULTS.fetch_add(1, Relaxed);
        }
    }

    /// The bytes [`Buffer::zero`] writes: the whole allocation.
    pub(crate) fn alloc_bytes(&self) -> usize {
        self.raw.length()
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        self.erase();
        if self.pooled {
            pool_put(self.raw.clone());
        } else {
            unkeep(&self.raw);
            IN_USE.fetch_sub(self.raw.length() as u64, Relaxed);
            BYTES_NOW.fetch_sub(self.raw.length() as u64, Relaxed);
        }
    }
}

impl Ctx {
    /// The library's origin: `metallib`, or `source` with the reason.
    pub fn library_source(&self) -> &str {
        &self.library_source
    }

    /// A new [`Buffer`]: counted, and in the residency set when large.
    fn wrap(
        &self,
        raw: Option<Retained<ProtocolObject<dyn MTLBuffer>>>,
        bytes: usize,
        dirty: bool,
    ) -> Result<Buffer, Error> {
        let raw = raw.ok_or_else(|| Error::Memory(format!("buffer of {bytes} bytes")))?;
        count_alloc(raw.length() as u64);
        self.keep(&raw);
        Ok(Buffer {
            raw,
            bytes,
            pooled: false,
            dirty: AtomicBool::new(dirty),
        })
    }

    /// The allocation length for `bytes`; `Err` above `maxBufferLength`.
    fn check_len(&self, bytes: usize) -> Result<usize, Error> {
        let max = self.device.maxBufferLength();
        if bytes > max {
            return Err(Error::Memory(format!(
                "{bytes} bytes is above maxBufferLength {max}"
            )));
        }
        // Metal refuses a zero-length buffer
        Ok(bytes.max(16))
    }

    /// A new zero-filled shared buffer (never from the pool). Metal documents
    /// new buffers as zero-filled, so it starts clean and may be pooled
    /// unwritten.
    ///
    /// The pool never causes a failed allocation: idle buffers are released
    /// first when this would exceed `recommendedMaxWorkingSetSize`, and all
    /// of them before one retry when Metal returns no buffer.
    pub fn alloc(&self, bytes: usize) -> Result<Buffer, Error> {
        let len = self.check_len(bytes)?;
        let total = self.device.recommendedMaxWorkingSetSize();
        let used = self.device.currentAllocatedSize() as u64;
        let over = (used + len as u64).saturating_sub(total);
        if over > 0 && pool_bytes() > 0 {
            release_idle(over);
        }
        let make = || {
            self.device
                .newBufferWithLength_options(len, MTLResourceOptions::StorageModeShared)
        };
        let mut raw = make();
        if raw.is_none() && pool_bytes() > 0 {
            release_idle(u64::MAX);
            raw = make();
        }
        if let Some(r) = raw.as_deref() {
            debug_assert_zero_filled(r);
        }
        self.wrap(raw, bytes, false)
    }

    /// A zero-filled buffer from the pool (at most a quarter longer), else a
    /// new one. When dropped it is zeroed and goes back to the pool, or is
    /// released if that failed.
    pub fn alloc_pooled(&self, bytes: usize) -> Result<Buffer, Error> {
        let len = self.check_len(bytes)?;
        let mut took = pool_take(len);
        if took.is_none() && releases_pending() {
            // a buffer being zeroed in the background may fit, and waiting for it
            // is faster than mapping a new buffer
            settle_releases();
            took = pool_take(len);
        }
        let mut b = match took {
            Some(raw) => Buffer {
                raw,
                bytes,
                pooled: true,
                dirty: AtomicBool::new(false),
            },
            None => self.alloc(bytes)?,
        };
        b.pooled = true;
        Ok(b)
    }

    /// A shared buffer holding a copy of `data`; bytes past the data read
    /// zero.
    pub fn upload<T: Pod>(&self, data: &[T]) -> Result<Buffer, Error> {
        let bytes = size_of_val(data);
        let b = self.alloc(bytes)?;
        if bytes > 0 {
            b.touch();
            // SAFETY: `data` is valid for `bytes` bytes, the new buffer for
            // at least `bytes` bytes (its allocation is `max(bytes, 16)`),
            // nothing else uses it yet, and the two do not overlap.
            unsafe { std::ptr::copy_nonoverlapping(data.as_ptr().cast::<u8>(), b.ptr(), bytes) };
        }
        Ok(b)
    }

    /// The compute pipeline of a kernel, compiled at first use and cached.
    pub fn pipeline(&self, kernel: &str) -> Result<Pipeline, Error> {
        let mut cache = self.pipelines.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(p) = cache.get(kernel) {
            return Ok(p.clone());
        }
        let function = self
            .library
            .newFunctionWithName(&NSString::from_str(kernel))
            .ok_or_else(|| Error::Device(format!("no kernel `{kernel}` in the library")))?;
        let p = self.device.newComputePipelineStateWithFunction_error(&function).map_err(|e| {
            Error::Device(format!("pipeline `{kernel}`: {}", e.localizedDescription()))
        })?;
        cache.insert(kernel.to_string(), p.clone());
        Ok(p)
    }

    /// Encodes the dispatches of `f` into one command buffer, commits it and
    /// waits. Returns `f`'s value and the GPU time in nanoseconds. An error
    /// from `f` is returned only after the encoded work completed, so no
    /// buffer is in use when this returns.
    pub fn run<'a, R>(
        &'a self,
        f: impl FnOnce(&mut Command<'a>) -> Result<R, Error>,
    ) -> Result<(R, u64), Error> {
        objc2::rc::autoreleasepool(|_| {
            let cb = self
                .queue
                .commandBuffer()
                .ok_or_else(|| Error::Device("commandBuffer returned nil".into()))?;
            let enc = cb
                .computeCommandEncoder()
                .ok_or_else(|| Error::Device("computeCommandEncoder returned nil".into()))?;
            let mut cmd = Command {
                ctx: self,
                enc,
                _args: PhantomData,
            };
            let value = f(&mut cmd);
            cmd.enc.endEncoding();
            cb.commit();
            cb.waitUntilCompleted();
            let status = cb.status();
            if status != MTLCommandBufferStatus::Completed {
                let why = cb
                    .error()
                    .map(|e| format!("{} (code {})", e.localizedDescription(), e.code()))
                    .unwrap_or_else(|| format!("status {}", status.0));
                return Err(Error::Device(format!("command buffer failed: {why}")));
            }
            let ns = ((cb.GPUEndTime() - cb.GPUStartTime()) * 1e9).max(0.0) as u64;
            Ok((value?, ns))
        })
    }
}

// ---------------------------------------------------------------------------
// Dispatch

/// A kernel argument, bound at the index of its position in the list.
#[derive(Clone, Copy, Debug)]
pub enum Arg<'a> {
    /// A buffer from its start.
    Buffer(&'a Buffer),
    /// A buffer from a byte offset.
    BufferAt(&'a Buffer, usize),
    /// Bytes copied into the command (`setBytes`, at most 4 KiB).
    Bytes(&'a [u8]),
}

impl<'a> Arg<'a> {
    /// A plain value as [`Arg::Bytes`].
    pub fn value<T: Pod>(v: &'a T) -> Self {
        // SAFETY: a Pod value is valid to view as its bytes.
        Arg::Bytes(unsafe { std::slice::from_raw_parts((v as *const T).cast(), size_of::<T>()) })
    }
}

/// The command buffer being encoded in [`Ctx::run`]: one serial compute
/// encoder, so each dispatch sees the writes of the earlier ones.
pub struct Command<'a> {
    ctx: &'a Ctx,
    enc: Retained<ProtocolObject<dyn MTLComputeCommandEncoder>>,
    _args: PhantomData<&'a Buffer>,
}

impl std::fmt::Debug for Command<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Command").finish_non_exhaustive()
    }
}

impl<'a> Command<'a> {
    /// Sets the pipeline, arguments and threadgroup memory of `kernel`.
    fn bind(&self, kernel: &str, args: &[Arg<'a>], tg_mem: &[usize]) -> Result<Pipeline, Error> {
        let p = self.ctx.pipeline(kernel)?;
        self.enc.setComputePipelineState(&p);
        for (i, a) in args.iter().enumerate() {
            match *a {
                Arg::Buffer(b) => {
                    b.touch();
                    // SAFETY: the buffer outlives the command (`'a`), and
                    // `run` waits for the GPU before returning.
                    unsafe { self.enc.setBuffer_offset_atIndex(Some(&b.raw), 0, i) }
                }
                Arg::BufferAt(b, off) => {
                    b.touch();
                    if off > b.bytes {
                        return Err(Error::Device(format!(
                            "argument {i}: offset {off} past the buffer"
                        )));
                    }
                    // SAFETY: as above, and the offset is inside the buffer.
                    unsafe { self.enc.setBuffer_offset_atIndex(Some(&b.raw), off, i) }
                }
                Arg::Bytes(v) => {
                    if v.is_empty() || v.len() > 4096 {
                        return Err(Error::Device(format!(
                            "argument {i}: {} bytes inline",
                            v.len()
                        )));
                    }
                    // SAFETY: valid for `v.len()` bytes; Metal copies them
                    // and never writes through the pointer.
                    unsafe {
                        self.enc.setBytes_length_atIndex(
                            NonNull::from(v).cast::<c_void>(),
                            v.len(),
                            i,
                        )
                    }
                }
            }
        }
        for (i, len) in tg_mem.iter().enumerate() {
            // SAFETY: the length is checked by Metal against the device limit
            // when the pipeline is dispatched.
            unsafe { self.enc.setThreadgroupMemoryLength_atIndex(*len, i) };
        }
        Ok(p)
    }

    /// `threads` threads in threadgroups of up to 256; the last group may be
    /// partial, so kernels check their index.
    pub fn dispatch(
        &mut self,
        kernel: &str,
        threads: usize,
        args: &[Arg<'a>],
    ) -> Result<(), Error> {
        let p = self.bind(kernel, args, &[])?;
        let tg = p.maxTotalThreadsPerThreadgroup().clamp(1, 256);
        self.threads(threads, tg);
        Ok(())
    }

    /// `threads` threads in groups of `group` threads, with threadgroup memory
    /// of `tg_mem[i]` bytes at `[[threadgroup(i)]]`.
    pub fn dispatch_with(
        &mut self,
        kernel: &str,
        threads: usize,
        group: usize,
        args: &[Arg<'a>],
        tg_mem: &[usize],
    ) -> Result<(), Error> {
        let p = self.bind(kernel, args, tg_mem)?;
        check_group(kernel, &p, group)?;
        self.threads(threads, group);
        Ok(())
    }

    /// `groups` whole threadgroups of `group` threads, with threadgroup
    /// memory as [`Command::dispatch_with`].
    pub fn dispatch_groups(
        &mut self,
        kernel: &str,
        groups: usize,
        group: usize,
        args: &[Arg<'a>],
        tg_mem: &[usize],
    ) -> Result<(), Error> {
        let p = self.bind(kernel, args, tg_mem)?;
        check_group(kernel, &p, group)?;
        if groups > 0 {
            self.enc.dispatchThreadgroups_threadsPerThreadgroup(size1(groups), size1(group));
        }
        Ok(())
    }

    /// Dispatches `threads` threads in groups of `group` (none when zero).
    fn threads(&self, threads: usize, group: usize) {
        if threads > 0 {
            self.enc.dispatchThreads_threadsPerThreadgroup(size1(threads), size1(group));
        }
    }
}

/// Checks a threadgroup size against the pipeline's limit.
fn check_group(kernel: &str, p: &Pipeline, group: usize) -> Result<(), Error> {
    let max = p.maxTotalThreadsPerThreadgroup();
    if group == 0 || group > max {
        return Err(Error::Device(format!(
            "`{kernel}`: threadgroup of {group} threads (pipeline max {max})"
        )));
    }
    Ok(())
}

/// A one-dimensional `MTLSize`.
fn size1(width: usize) -> MTLSize {
    MTLSize {
        width,
        height: 1,
        depth: 1,
    }
}

// ---------------------------------------------------------------------------
// Sessions and per-request buffers

/// The per-request buffers of [`Session::scratch`], by key.
#[derive(Default)]
struct State {
    scratch: HashMap<&'static str, Buffer>,
}

/// The device lock and the per-request buffers it guards.
static STATE: Mutex<Option<State>> = Mutex::new(None);
/// Whether a per-request buffer may exist, so a call with nothing to wipe
/// can skip taking the device ([`wipe_unbracketed`]).
static SCRATCH_ANY: AtomicBool = AtomicBool::new(false);

/// Exclusive use of the device: the context and the per-request buffers.
pub struct Session {
    ctx: &'static Ctx,
    state: MutexGuard<'static, Option<State>>,
}

impl std::fmt::Debug for Session {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Session").finish_non_exhaustive()
    }
}

/// Takes the device, making the context if needed.
pub fn lock() -> Result<Session, Error> {
    let ctx = context()?;
    let mut state = STATE.lock().unwrap_or_else(|e| e.into_inner());
    state.get_or_insert_with(State::default);
    Ok(Session { ctx, state })
}

impl Session {
    /// The context.
    pub fn ctx(&self) -> &'static Ctx {
        self.ctx
    }

    /// The per-request buffer `key` of at least `bytes`: the existing one
    /// with its contents if long enough, else a zero-filled one (the shorter
    /// one goes back to the pool).
    pub fn scratch(&mut self, key: &'static str, bytes: usize) -> Result<&mut Buffer, Error> {
        let ctx = self.ctx;
        let st = self.state.get_or_insert_with(State::default);
        if st.scratch.get(key).is_some_and(|b| b.bytes < bytes) {
            st.scratch.remove(key);
        }
        Ok(match st.scratch.entry(key) {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => {
                let b = e.insert(ctx.alloc_pooled(bytes)?);
                SCRATCH_ANY.store(true, SeqCst);
                b
            }
        })
    }

    /// The per-request buffer `key`, if it exists.
    pub fn get_scratch(&self, key: &'static str) -> Option<&Buffer> {
        self.state.as_ref()?.scratch.get(key)
    }

    /// Several per-request buffers at once (for binding them together).
    pub fn scratch_many<const N: usize>(&self, keys: [&'static str; N]) -> Option<[&Buffer; N]> {
        let st = self.state.as_ref()?;
        let found: Vec<&Buffer> = keys.iter().map(|k| st.scratch.get(k)).collect::<Option<_>>()?;
        found.try_into().ok()
    }

    /// Bytes held in per-request buffers. Test support.
    #[cfg(any(test, feature = "test-support"))]
    #[doc(hidden)]
    pub fn scratch_bytes(&self) -> u64 {
        self.state.as_ref().map_or(0, |s| {
            s.scratch.values().map(|b| b.raw.length() as u64).sum()
        })
    }
}

/// Per-request buffers given back by [`take_request_buffer`] callers, by key.
struct Lendable {
    /// The request of the buffers ([`end_request_report`] increments it).
    epoch: u64,
    free: Vec<(&'static str, Buffer)>,
}

/// The idle buffers of [`take_request_buffer`].
static LENDABLE: Mutex<Lendable> = Mutex::new(Lendable {
    epoch: 0,
    free: Vec::new(),
});

/// The idle lendable buffers, locked.
fn lendable() -> MutexGuard<'static, Lendable> {
    LENDABLE.lock().unwrap_or_else(|e| e.into_inner())
}

/// A per-request buffer under `key` taken without the device, so a call can
/// fill it on the CPU while another call holds the device. It is the idle
/// buffer an earlier call of the request gave back, with its contents, else a
/// zero-filled one. [`end_request_report`] zeroes the idle ones; one given
/// back after its request ended is zeroed then.
pub fn take_request_buffer(key: &'static str, bytes: usize) -> Result<RequestBuffer, Error> {
    let (epoch, found) = {
        let mut l = lendable();
        let epoch = l.epoch;
        let found = l
            .free
            .iter()
            .enumerate()
            .filter(|(_, (k, b))| *k == key && b.bytes >= bytes)
            .min_by_key(|(_, (_, b))| b.bytes)
            .map(|(i, _)| i)
            .map(|i| l.free.swap_remove(i).1);
        (epoch, found)
    };
    let buf = match found {
        Some(b) => b,
        None => context()?.alloc_pooled(bytes)?,
    };
    Ok(RequestBuffer { key, epoch, buf })
}

/// A per-request buffer checked out by [`take_request_buffer`]. Dropped
/// instead of given back, it is zeroed and pooled.
#[derive(Debug)]
pub struct RequestBuffer {
    key: &'static str,
    epoch: u64,
    buf: Buffer,
}

impl RequestBuffer {
    /// The buffer.
    pub fn buf(&self) -> &Buffer {
        &self.buf
    }

    /// The buffer, mutably.
    pub fn buf_mut(&mut self) -> &mut Buffer {
        &mut self.buf
    }

    /// Gives the buffer back to its request; after the request ended it is
    /// zeroed and pooled instead.
    pub fn give_back(self) {
        let RequestBuffer { key, epoch, buf } = self;
        let mut l = lendable();
        if l.epoch == epoch {
            l.free.push((key, buf));
        } else {
            drop(l);
            drop(buf);
        }
    }
}

/// Test switches. In other builds they are no-ops, so no code outside the
/// crate can force an erasure failure.
#[cfg(any(test, feature = "test-support"))]
mod test_switch {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};

    use objc2::runtime::ProtocolObject;
    use objc2_metal::MTLBuffer;

    /// [`super::set_plant_nonzero`].
    pub(super) static PLANT_NONZERO: AtomicBool = AtomicBool::new(false);
    /// The contents address of the region of the last planted byte.
    pub(super) static LAST_PLANT: AtomicUsize = AtomicUsize::new(0);
    /// The contents address of the buffer whose next zeroing panics (0: none).
    pub(super) static ZEROING_PANIC: AtomicUsize = AtomicUsize::new(0);

    /// After the zeroing of region `i`: plants a non-zero byte into the first
    /// region of a checked wipe when [`super::set_plant_nonzero`] is on.
    pub(super) fn plant_after_zeroing(check: bool, i: usize, raw: &ProtocolObject<dyn MTLBuffer>) {
        if check && i == 0 && PLANT_NONZERO.load(Relaxed) {
            plant_raw(raw);
        }
    }

    /// Panics once, in the zeroing of the buffer at `addr`, after
    /// [`super::set_zeroing_panic`].
    pub(super) fn zeroing_panic(addr: usize) {
        if addr != 0 && ZEROING_PANIC.compare_exchange(addr, 0, Relaxed, Relaxed).is_ok() {
            panic!("midnight-metal test switch: a panic in a zeroing");
        }
    }

    /// Writes one non-zero byte into the middle of `raw` behind the crate's
    /// back (`dirty` not set) and records its address. The caller has
    /// exclusive use of the buffer.
    pub(super) fn plant_raw(raw: &ProtocolObject<dyn MTLBuffer>) {
        let p = raw.contents().as_ptr().cast::<u8>();
        // SAFETY: the middle byte is inside the allocation; the caller has
        // exclusive use of the buffer.
        unsafe { std::ptr::write_volatile(p.add(raw.length() / 2), 0xa5) };
        LAST_PLANT.store(p as usize, Relaxed);
    }
}

/// The test switches of a normal build: no-ops.
#[cfg(not(any(test, feature = "test-support")))]
mod test_switch {
    use objc2::runtime::ProtocolObject;
    use objc2_metal::MTLBuffer;

    #[inline(always)]
    pub(super) fn plant_after_zeroing(_: bool, _: usize, _: &ProtocolObject<dyn MTLBuffer>) {}

    #[inline(always)]
    pub(super) fn zeroing_panic(_: usize) {}
}

/// Makes every later [`end_request_report`]`(true)` plant a non-zero byte in
/// its first region after zeroing, so the read-back fails. Test support.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn set_plant_nonzero(on: bool) {
    test_switch::PLANT_NONZERO.store(on, Relaxed);
}

/// The contents address of the last planted byte. Test support.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn last_planted() -> usize {
    test_switch::LAST_PLANT.load(Relaxed)
}

/// Makes the next zeroing of the dropped buffer at `addr` panic once; 0
/// stops it. Test support.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn set_zeroing_panic(addr: usize) {
    test_switch::ZEROING_PANIC.store(addr, Relaxed);
}

/// Writes a non-zero byte into an idle pool buffer, breaking the pool's
/// invariant; returns its contents address. Test support.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn plant_in_idle_pool() -> Option<usize> {
    let p = pool();
    let b = p.free.first()?;
    test_switch::plant_raw(b);
    Some(b.contents().as_ptr() as usize)
}

/// The contents addresses of the idle buffers of the pool. Test support.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn idle_pool_addresses() -> Vec<usize> {
    pool().free.iter().map(|b| b.contents().as_ptr() as usize).collect()
}

/// Whether every idle pool buffer reads zero. Test support.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn idle_pool_reads_zero() -> bool {
    pool().free.iter().all(|b| raw_reads_zero(b))
}

/// The per-request buffers now: `(key, allocation bytes, reads zero,
/// contents address)`. Takes the device. Test support.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn request_buffers() -> Vec<(&'static str, usize, bool, usize)> {
    let row = |k: &'static str, b: &Buffer| {
        (k, b.alloc_bytes(), raw_reads_zero(&b.raw), b.ptr() as usize)
    };
    let state = STATE.lock().unwrap_or_else(|e| e.into_inner());
    let mut out: Vec<_> = state
        .as_ref()
        .map(|st| st.scratch.iter().map(|(k, b)| row(k, b)).collect())
        .unwrap_or_default();
    out.extend(lendable().free.iter().map(|(k, b)| row(k, b)));
    out
}

/// The result of reading one region back from the host mapping.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReadBack {
    /// Every byte reads zero.
    Zero,
    /// A byte reads non-zero.
    NonZero,
    /// Not in shared storage: the host cannot read it back.
    Unreadable,
}

/// Reads back a region's whole allocation and counts the result in `w`.
fn read_back(raw: &ProtocolObject<dyn MTLBuffer>, w: &mut crate::WipeStats) -> ReadBack {
    w.checked_regions += 1;
    if raw.storageMode() != MTLStorageMode::Shared {
        w.check_failures += 1;
        ReadBack::Unreadable
    } else if !raw_reads_zero(raw) {
        w.nonzero_regions += 1;
        ReadBack::NonZero
    } else {
        ReadBack::Zero
    }
}

/// Check mode: reads back every idle pool buffer. One that reads non-zero is
/// zeroed and read back again; it, and one that cannot be read back, is
/// taken out of the pool and released.
fn check_idle_pool(w: &mut crate::WipeStats) {
    let bad: Vec<_> = {
        let mut p = pool();
        let mut bad = Vec::new();
        let mut i = 0;
        while i < p.free.len() {
            let raw = &p.free[i];
            let len = raw.length() as u64;
            w.regions += 1;
            w.bytes += len;
            w.pool_regions += 1;
            w.pool_bytes += len;
            let fault = match read_back(raw, w) {
                ReadBack::Zero => false,
                ReadBack::Unreadable => true,
                ReadBack::NonZero => {
                    // idle under the pool's lock: exclusive
                    raw_zero(raw);
                    let _again = raw_reads_zero(raw);
                    true
                }
            };
            if fault {
                let b = p.free.swap_remove(i);
                p.bytes -= len;
                bad.push(b);
            } else {
                i += 1;
            }
        }
        bad
    };
    // not `release_raw`: its debug read-back would fail on a buffer that is
    // not host-readable
    release_unchecked(bad);
}

/// Zeroes every per-request buffer (`state` is the device lock) after
/// background zeroing; with `check`, reads back the idle pool and each region.
/// A region that reads back non-zero or unreadable is zeroed again and
/// released, never pooled or kept; the others go back to the pool.
fn wipe_locked(state: &mut Option<State>, check: bool, w: &mut crate::WipeStats) {
    settle_releases();
    if check {
        check_idle_pool(w);
    }
    let lent: Vec<Buffer> = {
        let mut l = lendable();
        l.epoch += 1;
        l.free.drain(..).map(|(_, b)| b).collect()
    };
    let scratch: Vec<Buffer> = state
        .as_mut()
        .map(|st| st.scratch.drain().map(|(_, b)| b).collect())
        .unwrap_or_default();
    SCRATCH_ANY.store(false, SeqCst);
    for (i, mut b) in scratch.into_iter().chain(lent).enumerate() {
        b.zero();
        w.regions += 1;
        w.bytes += b.alloc_bytes() as u64;
        // exclusive: the region is owned here
        test_switch::plant_after_zeroing(check, i, &b.raw);
        if check && read_back(&b.raw, w) != ReadBack::Zero {
            // zeroed again unconditionally, read back again, released
            b.zero();
            let _again = raw_reads_zero(&b.raw);
            b.pooled = false;
        }
        // zero (and not dirty): pooled, or released when it failed
        drop(b);
    }
}

/// Zeroes every per-request buffer after any device work and background
/// zeroing, and closes the request.
///
/// With `check`, reads back every idle pool buffer and each per-request
/// buffer after zeroing (on unified memory this is the memory the GPU used).
/// A region that reads back non-zero or cannot be read is zeroed again and
/// released; the report is then `Err`, as it is when a zeroing panicked since
/// the last report.
pub fn end_request_report(check: bool) -> Result<crate::WipeStats, crate::WipeStats> {
    let mut w = crate::WipeStats {
        checked: check,
        ..crate::WipeStats::default()
    };
    let mut state = STATE.lock().unwrap_or_else(|e| e.into_inner());
    REQUEST_OPEN.store(false, SeqCst);
    wipe_locked(&mut state, check, &mut w);
    drop(state);
    w.erasure_failures = ERASE_FAULTS.swap(0, Relaxed);
    if w.nonzero_regions == 0 && w.check_failures == 0 && w.erasure_failures == 0 {
        Ok(w)
    } else {
        Err(w)
    }
}

/// [`end_request_report`] without the read-back. `true` when done.
pub fn end_request() -> bool {
    end_request_report(false).is_ok()
}

/// The wipe of a hook call made outside a request (`crate::HookScope`): as
/// [`end_request`] without closing a request or reading back. It takes the
/// device, so it never zeroes a buffer another call is using; a
/// [`take_request_buffer`] buffer is not idle until given back. With nothing
/// to wipe it does not take the device.
pub(crate) fn wipe_unbracketed() {
    let idle_lent = !lendable().free.is_empty();
    if !(SCRATCH_ANY.load(SeqCst) || idle_lent || releases_pending()) {
        return;
    }
    let mut state = STATE.lock().unwrap_or_else(|e| e.into_inner());
    let mut w = crate::WipeStats::default();
    wipe_locked(&mut state, false, &mut w);
}

/// `(free, total)`: `total` is `recommendedMaxWorkingSetSize`, `free` is that
/// minus `currentAllocatedSize` plus the idle pool buffers, which count as
/// free because an allocation that would not fit releases them first.
pub fn mem_info() -> Option<(usize, usize)> {
    let ctx = context().ok()?;
    let total = ctx.device.recommendedMaxWorkingSetSize() as usize;
    let used = ctx.device.currentAllocatedSize();
    let idle = pool_bytes() as usize;
    Some(((total + idle).saturating_sub(used).min(total), total))
}
