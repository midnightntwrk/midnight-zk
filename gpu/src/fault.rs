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

//! Fault injection into the device calls (feature `test-fault`, never a
//! default). An armed fault makes the next `count` passes of a device call
//! of its class through its point fail as a device error would; the caller
//! then runs the stock CPU code on its unchanged input.
//!
//! `MIDNIGHT_GPU_FAULT=class:point[:count],...` arms faults at the first
//! check (count 1 by default). Classes: `msm`, `ntt`, `quotient`,
//! `erase`. Points: `upload` (after the input reached the device), `launch`
//! (after the kernel, before the read-back), `divide` (quotient: after the
//! numerator), `readback` (the read-back fails after its first chunk),
//! `corrupt` (quotient: one output coefficient is changed after the
//! read-back; only the prover's check mode can see it), `check` (erase: the
//! check-mode count of a zeroed region fails as a failed call would).

use std::sync::{
    Mutex, OnceLock,
    atomic::{AtomicU64, Ordering::Relaxed},
};

/// The device call a fault hits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Class {
    /// The G1 MSM.
    Msm,
    /// The NTT.
    Ntt,
    /// The quotient.
    Quotient,
    /// The zeroing of a device region.
    Erase,
}

/// Every class.
pub const CLASSES: [Class; 4] = [Class::Msm, Class::Ntt, Class::Quotient, Class::Erase];

impl Class {
    /// The name in `MIDNIGHT_GPU_FAULT`.
    pub fn name(self) -> &'static str {
        match self {
            Class::Msm => "msm",
            Class::Ntt => "ntt",
            Class::Quotient => "quotient",
            Class::Erase => "erase",
        }
    }

    /// The class of a name.
    pub fn parse(s: &str) -> Option<Class> {
        CLASSES.into_iter().find(|c| c.name() == s)
    }
}

/// Where in the call a fault hits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Point {
    /// After the input reached the device.
    Upload,
    /// After the kernel, before the read-back.
    Launch,
    /// Quotient: after the numerator.
    Divide,
    /// The read-back fails after its first chunk.
    Readback,
    /// Quotient: one output coefficient is changed after the read-back.
    Corrupt,
    /// Erase: the check-mode count of a zeroed region fails (no count).
    Check,
}

const POINTS: [Point; 6] = [
    Point::Upload,
    Point::Launch,
    Point::Divide,
    Point::Readback,
    Point::Corrupt,
    Point::Check,
];

impl Point {
    /// The name in `MIDNIGHT_GPU_FAULT`.
    pub fn name(self) -> &'static str {
        match self {
            Point::Upload => "upload",
            Point::Launch => "launch",
            Point::Divide => "divide",
            Point::Readback => "readback",
            Point::Corrupt => "corrupt",
            Point::Check => "check",
        }
    }

    /// The point of a name.
    pub fn parse(s: &str) -> Option<Point> {
        POINTS.into_iter().find(|p| p.name() == s)
    }
}

static ARMED: Mutex<Vec<(Class, Point, u64)>> = Mutex::new(Vec::new());
static FIRED: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];
static ENV: OnceLock<()> = OnceLock::new();

fn armed_list() -> std::sync::MutexGuard<'static, Vec<(Class, Point, u64)>> {
    ENV.get_or_init(|| {
        if let Ok(spec) = std::env::var("MIDNIGHT_GPU_FAULT") {
            match parse(&spec) {
                Ok(v) => ARMED.lock().unwrap_or_else(|e| e.into_inner()).extend(v),
                Err(e) => crate::diag!("midnight-gpu: MIDNIGHT_GPU_FAULT ignored: {e}"),
            }
        }
    });
    ARMED.lock().unwrap_or_else(|e| e.into_inner())
}

/// Arms `count` faults of `class` at `point`.
pub fn arm(class: Class, point: Point, count: u64) {
    crate::batch::with_fault_admission(|| armed_list().push((class, point, count)));
}

/// Disarms every fault and resets the fired counters.
pub fn reset() {
    let Some(_gate) = crate::batch::admit_ordinary("fault") else {
        return;
    };
    armed_list().clear();
    for f in &FIRED {
        f.store(0, Relaxed);
    }
}

/// Faults of `class` fired since the last [`reset`].
pub fn fired(class: Class) -> u64 {
    FIRED[class as usize].load(Relaxed)
}

/// Faults armed and not fired.
pub fn armed() -> u64 {
    armed_list().iter().map(|a| a.2).sum()
}

/// Parses `class:point[:count],...`.
pub fn parse(spec: &str) -> Result<Vec<(Class, Point, u64)>, String> {
    spec.split(',')
        .filter(|s| !s.trim().is_empty())
        .map(|item| {
            let parts: Vec<&str> = item.trim().split(':').collect();
            let class = parts.first().and_then(|c| Class::parse(c));
            let point = parts.get(1).and_then(|p| Point::parse(p));
            let count = match parts.get(2) {
                None => Some(1),
                Some(c) => c.parse().ok(),
            };
            match (class, point, count, parts.len() <= 3) {
                (Some(c), Some(p), Some(n), true) => Ok((c, p, n)),
                _ => Err(format!("bad fault {item:?}")),
            }
        })
        .collect()
}

/// Whether a fault of `class` at `point` fires now (one armed count is used).
pub(crate) fn hit(class: Class, point: Point) -> bool {
    let mut a = armed_list();
    if let Some(e) = a.iter_mut().find(|e| e.0 == class && e.1 == point && e.2 > 0) {
        e.2 -= 1;
        FIRED[class as usize].fetch_add(1, Relaxed);
        a.retain(|e| e.2 > 0);
        return true;
    }
    false
}

/// The next `n` zeroings of sppark's own device blocks (the per-call MSM
/// buffer, a context blob) fail in the CUDA core's free wrapper, as a failed
/// memset would: each block is kept in quarantine, an erasure failure is
/// counted, and `end_request` retries it.
pub fn fail_lib_wipes(n: i32) {
    let Some(_gate) = crate::batch::admit_ordinary("fault") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: sets a counter of the core.
    unsafe {
        crate::ffi::mgpu_test_fail_lib_wipes(n)
    };
    #[cfg(not(midnight_gpu_cuda))]
    let _ = n;
}

/// The next `n` frees of this crate's own device buffers fail in the CUDA
/// core without freeing (and without uncounting the live device bytes),
/// as a failed `cudaFree` would: the buffer's region is kept in
/// quarantine, an erasure failure is counted, and `end_request` retries
/// it.
pub fn fail_dev_frees(n: i32) {
    let Some(_gate) = crate::batch::admit_ordinary("fault") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: sets a counter of the core.
    unsafe {
        crate::ffi::mgpu_test_fail_dev_frees(n)
    };
    #[cfg(not(midnight_gpu_cuda))]
    let _ = n;
}

/// The next `n` pre-zeroing device synchronisations of sppark's own
/// device blocks in the CUDA core count as failed. The synchronisation
/// itself still runs and the zeroing is still attempted, but it is not
/// confirmed: the block is kept in quarantine as unerased (see
/// `wipe::pending_erasure`), the failed synchronisation is counted, and
/// `end_request` retries the block.
pub fn fail_wipe_presync(n: i32) {
    let Some(_gate) = crate::batch::admit_ordinary("fault") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: sets a counter of the core.
    unsafe {
        crate::ffi::mgpu_test_fail_wipe_presync(n)
    };
    #[cfg(not(midnight_gpu_cuda))]
    let _ = n;
}

/// The next `n` frees of sppark's own device blocks in the CUDA core
/// after a confirmed zeroing count as failed without freeing, as a
/// failed `cudaFree` would: the block is kept in quarantine as zeroed
/// but unfreed (see `wipe::pending_erasure`), an erasure failure is
/// counted, and `end_request` retries the free.
pub fn fail_lib_frees(n: i32) {
    let Some(_gate) = crate::batch::admit_ordinary("fault") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: sets a counter of the core.
    unsafe {
        crate::ffi::mgpu_test_fail_lib_frees(n)
    };
    #[cfg(not(midnight_gpu_cuda))]
    let _ = n;
}

/// Two MSMs on one reused context over `bases`, `first` then `second`
/// (unmasked: the scalars go to sppark as given), with the context's bucket
/// records read back after each: `(after_first, after_second,
/// words_per_record)`. Each record is `X`, `Y`, `ZZZ`, `ZZ` in equal parts.
/// `None` without a device or on a device error.
pub fn msm_bucket_records(
    bases: &[crate::G1AffineLimbs],
    first: &[crate::Scalar],
    second: &[crate::Scalar],
) -> Option<(Vec<u64>, Vec<u64>, usize)> {
    let _gate = crate::batch::admit_ordinary("fault")?;
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() || first.len() != bases.len() || second.len() != bases.len() {
            return None;
        }
        crate::msm::bucket_probe(bases, first, second)
    }
    #[cfg(not(midnight_gpu_cuda))]
    {
        let _ = (bases, first, second);
        None
    }
}

/// The next `n` sppark MSMs throw a non-CUDA exception (as `std::bad_alloc`
/// or a failed thread start would) after their bucket-row copies are
/// enqueued. The MSM must return an error and the caller fall back; no
/// exception may reach Rust.
pub fn msm_throw_next(n: i32) {
    let Some(_gate) = crate::batch::admit_ordinary("fault") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: sets a counter of the core.
    unsafe {
        crate::ffi::mgpu_test_msm_throw(n)
    };
    #[cfg(not(midnight_gpu_cuda))]
    let _ = n;
}

/// The next `n` row passes of sppark's MSM collect workers (host threads)
/// throw. The collector must join every worker, throw after the join, and
/// the MSM return an error; no exception may escape a worker thread.
pub fn msm_worker_throw_next(n: i32) {
    let Some(_gate) = crate::batch::admit_ordinary("fault") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: sets a counter of the core.
    unsafe {
        crate::ffi::mgpu_test_msm_worker_throw(n)
    };
    #[cfg(not(midnight_gpu_cuda))]
    let _ = n;
}

/// The host buffers of the CUDA core after a drain that could not be
/// confirmed (a transfer may still target them). Makes one drain report "not
/// confirmed" and returns `[stage_get refuses the bounce buffer, stage_free
/// keeps it unwiped, rb_free keeps the read-back buffer unwiped]`, each `1`
/// when the buffer is protected; the first two are `2` when this device does
/// not stage copies. The buffers stay held for the rest of the process.
/// `None` without a device.
pub fn stage_paths_after_unconfirmed_drain() -> Option<[u64; 3]> {
    let _gate = crate::batch::admit_ordinary("fault")?;
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() {
            return None;
        }
        crate::ffi::call(move || {
            let mut out = [0u64; 3];
            // SAFETY: `out` holds three words; on the actor thread.
            let rc = unsafe { crate::ffi::mgpu_test_stage_paths(out.as_mut_ptr()) };
            (rc == 0 || out[0] == 2).then_some(out)
        })
        .flatten()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

/// Whether the CUDA core hands out a fresh host buffer after a drain that
/// could not be confirmed. For a process that has not staged a copy or read
/// back yet: makes one drain report "not confirmed" and returns `[stage_get
/// refuses a new bounce buffer, rb_get refuses a new read-back buffer]`, each
/// `1` when no buffer is handed out; the first is `2` when this device does
/// not stage copies. The device is retired when the call returns. `None`
/// without a device, or when a host buffer already existed.
pub fn gets_after_unconfirmed_drain() -> Option<[u64; 2]> {
    let _gate = crate::batch::admit_ordinary("fault")?;
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() {
            return None;
        }
        crate::ffi::call(move || {
            let mut out = [0u64; 2];
            // SAFETY: `out` holds two words; on the actor thread.
            let rc = unsafe { crate::ffi::mgpu_test_get_after_unconfirmed_drain(out.as_mut_ptr()) };
            (rc == 0).then_some(out)
        })
        .flatten()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

/// A staged host-to-device copy (through the bounce buffer) whose final
/// synchronisation fails with work still queued, and whose error drain is
/// made to report "not confirmed". Returns `[the copy returned an error, the
/// stream was idle when it returned, drains run, of them not confirmed, the
/// bounce buffer is then held (not handed out, not wiped or freed), erasure
/// failures added]`, each word `2` when this device does not stage copies.
/// The bounce buffer stays held for the rest of the process. `None` without
/// a device or when the buffers could not be made.
pub fn staged_sync_fail() -> Option<[u64; 6]> {
    let _gate = crate::batch::admit_ordinary("fault")?;
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() {
            return None;
        }
        crate::ffi::call(move || {
            let mut out = [0u64; 6];
            // SAFETY: `out` holds six words; on the actor thread.
            let rc = unsafe { crate::ffi::mgpu_test_staged_sync_fail(out.as_mut_ptr()) };
            (rc == 0 || rc == -2).then_some(out)
        })
        .flatten()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

/// The error arms of the CUDA core that [`error_arms`] fails, in order.
pub const ERROR_ARMS: [&str; 8] = [
    "copy",
    "read-back",
    "zeta",
    "scale",
    "periodic copy",
    "periodic kernel",
    "msm",
    "msm context",
];

/// Fails each error arm of the CUDA core once, with work still queued on the
/// stream (a spinning kernel), and returns per arm (in [`ERROR_ARMS`] order)
/// whether the call returned an error and whether the stream was idle when it
/// returned. `None` without a device.
pub fn error_arms() -> Option<Vec<(&'static str, bool, bool)>> {
    let _gate = crate::batch::admit_ordinary("fault")?;
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() {
            return None;
        }
        crate::ffi::call(move || {
            let mut out = [0u64; 2 * ERROR_ARMS.len()];
            // SAFETY: `out` holds two words per arm; on the actor thread.
            let n = unsafe { crate::ffi::mgpu_test_error_arms(out.as_mut_ptr()) };
            (n == ERROR_ARMS.len() as i32).then(|| {
                ERROR_ARMS
                    .iter()
                    .enumerate()
                    .map(|(i, a)| (*a, out[2 * i] != 0, out[2 * i + 1] != 0))
                    .collect()
            })
        })
        .flatten()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

/// One CUDA-core block whose zeroing fails in its release and whose sppark
/// teardown then fails too (both paths keep it). Returns the quarantine
/// entries of that block and the erasure failures added, `None` without a
/// device. The block stays in quarantine until `end_request` retries it.
pub fn double_quarantine() -> Option<(u64, u64)> {
    let _gate = crate::batch::admit_ordinary("fault")?;
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() {
            return None;
        }
        crate::ffi::call(move || {
            let mut out = [0u64; 2];
            // SAFETY: a valid out array; on the actor thread.
            (unsafe { crate::ffi::mgpu_test_double_quarantine(out.as_mut_ptr()) } == 0)
                .then_some((out[0], out[1]))
        })
        .flatten()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

/// The next `n` error drains of the CUDA core report "not confirmed"
/// after they synchronised, as a drain whose synchronisations failed
/// would: the unconfirmed count of `error_drains` grows, so a public
/// device call whose error arm drains (for example a transform with
/// an armed `readback` fault) takes the failed-drain path.
pub fn unconfirm_next_drains(n: i32) {
    let Some(_gate) = crate::batch::admit_ordinary("fault") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: sets a counter of the core.
    unsafe {
        crate::ffi::mgpu_test_unconfirm_drains(n)
    };
    #[cfg(not(midnight_gpu_cuda))]
    let _ = n;
}

/// Measurements of [`probe_cooperative`].
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CoopProbe {
    /// `cudaError_t` code of the second cooperative launch.
    pub second_launch_code: i64,
    /// The second launch was accepted (queued).
    pub queued: bool,
    /// The second kernel started at or after the first kernel ended.
    pub sequential: bool,
    /// First kernel duration, milliseconds.
    pub a_ms: f64,
    /// Second kernel start offset from the first start, milliseconds.
    pub b_start_offset_ms: f64,
    /// Second kernel duration, milliseconds.
    pub b_ms: f64,
    /// Host time of the second launch call, microseconds.
    pub launch_call_us: i64,
}

/// Probe (a): a cooperative kernel resident on stream A, then a second
/// cooperative launch on stream B. `None` without a device.
pub fn probe_cooperative() -> Option<CoopProbe> {
    let _gate = crate::batch::admit_ordinary("fault")?;
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() {
            return None;
        }
        crate::ffi::call(move || {
            let mut out = [0i64; 7];
            // SAFETY: `out` holds seven words; on the actor thread.
            (unsafe { crate::ffi::mgpu_test_probe_cooperative(out.as_mut_ptr()) } == 0).then_some(
                CoopProbe {
                    second_launch_code: out[0],
                    queued: out[1] != 0,
                    sequential: out[2] != 0,
                    a_ms: out[3] as f64 / 1000.0,
                    b_start_offset_ms: out[4] as f64 / 1000.0,
                    b_ms: out[5] as f64 / 1000.0,
                    launch_call_us: out[6],
                },
            )
        })
        .flatten()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

/// Measurements of [`probe_async_alloc`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AllocProbe {
    /// Host time of the `cudaMallocAsync` call on stream B, microseconds.
    pub malloc_b_call_us: i64,
    /// From that call to the first use of the block on B completing,
    /// microseconds.
    pub first_use_b_wait_us: i64,
    /// Kernel time stream A still had left after B's first use
    /// completed, microseconds.
    pub kernel_a_remaining_us: i64,
    /// B's first use completed only once A's kernel was done.
    pub b_waited_for_a: bool,
    /// B received the address freed on A.
    pub same_address: bool,
}

/// Probe (b): allocate on stream A, run a long kernel on A using the
/// block, free it async on A, then allocate the same size async on
/// stream B and time the call and the first use on B. `None` without
/// a device.
pub fn probe_async_alloc() -> Option<AllocProbe> {
    let _gate = crate::batch::admit_ordinary("fault")?;
    #[cfg(midnight_gpu_cuda)]
    {
        if !crate::device_admitted() {
            return None;
        }
        crate::ffi::call(move || {
            let mut out = [0i64; 5];
            // SAFETY: `out` holds five words; on the actor thread.
            (unsafe { crate::ffi::mgpu_test_probe_async_alloc(out.as_mut_ptr()) } == 0).then_some(
                AllocProbe {
                    malloc_b_call_us: out[0],
                    first_use_b_wait_us: out[1],
                    kernel_a_remaining_us: out[2],
                    b_waited_for_a: out[3] != 0,
                    same_address: out[4] != 0,
                },
            )
        })
        .flatten()
    }
    #[cfg(not(midnight_gpu_cuda))]
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_specs() {
        assert_eq!(
            parse("msm:upload,quotient:corrupt:3").unwrap(),
            vec![
                (Class::Msm, Point::Upload, 1),
                (Class::Quotient, Point::Corrupt, 3)
            ]
        );
        assert!(parse("msm").is_err());
        assert!(parse("gpu:upload").is_err());
        assert!(parse("ntt:upload:x").is_err());
    }
}
