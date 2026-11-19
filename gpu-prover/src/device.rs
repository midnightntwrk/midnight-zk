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

//! The device layer: the one place where this crate meets the CUDA crate
//! `midnight-gpu` and the hook layer `midnight_proofs::gpu`.
//!
//! The service talks to a device only through the [`Device`] trait. Two
//! implementations exist:
//!
//! - [`NoDevice`]: no device. Every phase runs on the CPU. Used by a build
//!   without the `cuda` feature, by `device = "off"`, and when the run-time
//!   detection finds no device.
//! - `CudaDevice` (module `cuda`): the hooks of `midnight_proofs::gpu` backed
//!   by `midnight-gpu`. It is compiled only when the build has the cfg
//!   `midnight_gpu_linked`, which the build script sets with the `cuda`
//!   feature.
//!
//! Tests and embedders can implement [`Device`] themselves, for example to
//! give the admission ladder a fake memory reading.

use std::collections::BTreeMap;

use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    plonk::ProvingKey,
    poly::kzg::{KZGCommitmentScheme, params::ParamsKZG},
};
use serde::Serialize;

/// The proving key type the service serves.
pub type Pk = ProvingKey<Fq, KZGCommitmentScheme<midnight_curves::Bls12>>;

/// A set of proof phases that can run on the device.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Phases(u32);

impl Phases {
    /// No phase on the device.
    pub const NONE: Phases = Phases(0);
    /// Multi-scalar multiplications of the commitments.
    pub const MSM: Phases = Phases(1);
    /// Forward NTTs of the base domain (`fft`).
    pub const FFT: Phases = Phases(2);
    /// Inverse NTTs of the base domain (`ifft`).
    pub const IFFT: Phases = Phases(4);
    /// The quotient job: the extended cosets (they stay on the device), the
    /// numerator, its division by the vanishing polynomial and the inverse
    /// transform.
    pub const QUOTIENT: Phases = Phases(8);
    /// Every phase.
    pub const ALL: Phases = Phases(15);

    /// The raw bits.
    pub fn bits(self) -> u32 {
        self.0
    }
    /// The set of these bits (unknown bits are dropped).
    pub fn from_bits(b: u32) -> Phases {
        Phases(b & Self::ALL.0)
    }
    /// Whether every phase of `o` is in `self`.
    pub fn contains(self, o: Phases) -> bool {
        self.0 & o.0 == o.0
    }
    /// Whether the set is empty.
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }
    /// The union.
    pub fn union(self, o: Phases) -> Phases {
        Phases(self.0 | o.0)
    }
    /// `self` without the phases of `o`.
    pub fn without(self, o: Phases) -> Phases {
        Phases(self.0 & !o.0)
    }
    /// The phase names, in a fixed order.
    pub fn names(self) -> Vec<&'static str> {
        [
            (Self::MSM, "msm"),
            (Self::FFT, "fft"),
            (Self::IFFT, "ifft"),
            (Self::QUOTIENT, "quotient"),
        ]
        .into_iter()
        .filter(|(p, _)| self.contains(*p))
        .map(|(_, n)| n)
        .collect()
    }
}

impl Serialize for Phases {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.names().serialize(s)
    }
}

/// Facts about the device, for the start record.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct DeviceInfo {
    /// Device name as the driver reports it (a GPU model, never a host name).
    pub name: String,
    /// Compute capability of the device, for example `"12.0"`.
    pub arch: String,
    /// Device architectures the device code of this build was compiled for.
    pub build_archs: String,
    /// CUDA runtime version.
    pub runtime_version: String,
    /// Driver version.
    pub driver_version: String,
    /// Total device memory, bytes.
    pub total_bytes: u64,
}

/// Free and total device memory, bytes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct MemInfo {
    /// Free bytes as the runtime reports them.
    pub free: u64,
    /// Total bytes of the device.
    pub total: u64,
}

/// Device bytes this process holds between phases.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct Held {
    /// Resident proving-key copies.
    pub resident: u64,
    /// Point bytes of the registered MSM base tables.
    pub tables: u64,
}

/// The counts the device memory need is computed from. The device layer
/// derives them from the proving key with the code that builds the device
/// quotient job, so the need cannot drift from what the job allocates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct Shape {
    /// log2 of the row count.
    pub k: u32,
    /// log2 of the extended domain size.
    pub ext_k: u32,
    /// Extended cosets computed per proof (advice, instance, permutation
    /// products, lookups, trash).
    pub proof_cosets: u32,
    /// Extended proving-key cosets kept on the device for the quotient.
    pub resident_polys: u32,
    /// Scratch slots of the quotient kernel.
    pub nslots: u32,
    /// Stride of the quotient kernel's scratch slots on this device.
    pub grid_threads: u64,
    /// Device bytes of the quotient job by the job's own memory check
    /// (`midnight_gpu::quotient::need_bytes`): the extended cosets of the
    /// proof (lookup helpers included) and of the key polynomials, the
    /// numerator and the compiled program's scratch slots. 0 when unknown;
    /// the need is then estimated from the counts above.
    pub quotient_bytes: u64,
}

/// One phase that fell back to the CPU.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Fallback {
    /// Phase name (`msm`, `fft`, `ifft`, `quotient`).
    pub phase: String,
    /// Reason, a fixed text of the device layer (never a value).
    pub reason: String,
    /// How many calls fell back for this phase and reason.
    pub count: u64,
}

/// Device counters of one request. Every field is a count, a size or a
/// time; no field depends on a scalar value.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct DeviceCounters {
    /// MSMs that ran on the device.
    pub msm_count: u64,
    /// Seconds spent in device MSMs.
    pub msm_seconds: f64,
    /// Device calls by operation name.
    pub calls: BTreeMap<String, u64>,
    /// Fallbacks to the CPU: declines of an admitted phase that the device
    /// should have taken.
    pub fallbacks: Vec<Fallback>,
    /// Every declined hook call by phase and reason, fallbacks included:
    /// also the size threshold (`below-min-k`), no device (`no-device`) and
    /// the admission's decision (`not-admitted`).
    pub declines: Vec<Fallback>,
    /// Peak device bytes this process held during the request.
    pub peak_bytes: u64,
    /// Seconds per prover phase, by phase name.
    pub phase_seconds: BTreeMap<String, f64>,
}

impl DeviceCounters {
    /// Total fallback count.
    pub fn fallback_count(&self) -> u64 {
        self.fallbacks.iter().map(|f| f.count).sum()
    }
}

/// What the end of a request erased on the device and in host staging.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct WipeReport {
    /// Regions zeroed before their free.
    pub regions: u64,
    /// Bytes zeroed.
    pub bytes: u64,
    /// Whether the regions were read back and compared with zero.
    pub checked: bool,
    /// Regions that read back non-zero after the erasure (check mode).
    pub nonzero_regions: u64,
    /// Check calls that failed, so no count came back (check mode). Any
    /// failed check fails the request's erasure report.
    pub check_failures: u64,
    /// Erasure or release calls that failed.
    pub erasure_failures: u64,
}

/// The device layer as the service sees it.
///
/// A request runs as: [`Device::begin_request`] with the admitted phases,
/// the proof, then [`Device::end_request`], which must zero and free every
/// device and staging buffer that held witness-dependent values. If
/// `end_request` fails, the service stops serving (it cannot confirm the
/// erasure).
pub trait Device: Send + Sync {
    /// The device facts, or `None` when there is no usable device.
    fn info(&self) -> Option<DeviceInfo>;
    /// Free and total memory now, or `None` when there is no device.
    fn mem(&self) -> Option<MemInfo>;
    /// Bytes this process holds on the device now.
    fn held(&self) -> Held;
    /// The shape of the device quotient for `pk`, or `None` when the device
    /// quotient does not take this key (the quotient then runs on the CPU).
    fn shape(&self, pk: &Pk) -> Option<Shape>;
    /// Gives the device the public key material of the next request before
    /// [`Device::begin_request`]: the SRS bases (MSM tables) and the proving
    /// key (resident quotient polynomials), and whether the request ends with
    /// a read-back check of the erasure. The default does nothing.
    fn prepare(&self, params: &ParamsKZG<Bls12>, pk: &Pk, check: bool) {
        let _ = (params, pk, check);
    }
    /// Starts the erasure accounting of a request: resets the counters that
    /// [`Device::end_request`] reports and sets whether the request ends
    /// with a read-back check. The service calls it for every request, also
    /// for one that the admission keeps off the device. The default does
    /// nothing.
    fn begin_wipe(&self, check: bool) {
        let _ = check;
    }
    /// Prepares the device for a request with `phases` on the device.
    /// Returns the phases it can serve (a subset).
    fn begin_request(&self, phases: Phases) -> Phases;
    /// Withdraws the admitted phases of the running request: every later
    /// device call declines and the prover finishes on the CPU. Returns
    /// whether phases were withdrawn. The default withdraws nothing.
    fn revoke(&self) -> bool {
        false
    }
    /// Sets the request's cancel check (`None` between requests). The
    /// device layer runs it before each device phase launch and, when it is
    /// `true`, withdraws the device phases at once (no launch waits for the
    /// service's poll). The default does nothing.
    fn set_gate(&self, gate: Option<crate::service::Cancel>) {
        let _ = gate;
    }
    /// Whether the gate withdrew the device phases since the last call.
    fn withdrawn(&self) -> bool {
        false
    }
    /// Makes the device context, so that [`Device::mem`] reads the free
    /// memory. The admission calls it when it considers a device phase on a
    /// native host: before that, no context exists. The default does
    /// nothing.
    fn activate(&self) {}

    #[cfg(test)]
    /// Test barrier after the service starts watching the request for
    /// cancellation.
    fn observe_proving(&self) {}
    /// Keeps the device copies of the key polynomials between requests
    /// (resident policy `keep`) or frees them at each request's end
    /// (`evict`). The default does nothing.
    fn set_keep(&self, keep: bool) {
        let _ = keep;
    }
    /// Frees the resident proving-key copies, and with `tables` the MSM base
    /// tables too. Returns the bytes freed.
    fn evict(&self, tables: bool) -> u64;
    /// Ends a request: zeroes and frees every witness-dependent buffer, with
    /// a read-back check when `check` is set. An error means the erasure
    /// could not be confirmed.
    fn end_request(&self, check: bool) -> Result<WipeReport, String>;
    /// The counters since the last [`Device::reset_counters`].
    fn counters(&self) -> DeviceCounters;
    /// Resets the counters.
    fn reset_counters(&self);
}

/// No device: every phase on the CPU.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoDevice;

impl Device for NoDevice {
    fn info(&self) -> Option<DeviceInfo> {
        None
    }
    fn mem(&self) -> Option<MemInfo> {
        None
    }
    fn held(&self) -> Held {
        Held::default()
    }
    fn shape(&self, _: &Pk) -> Option<Shape> {
        None
    }
    fn begin_request(&self, _: Phases) -> Phases {
        Phases::NONE
    }
    fn evict(&self, _: bool) -> u64 {
        0
    }
    fn end_request(&self, check: bool) -> Result<WipeReport, String> {
        Ok(WipeReport {
            checked: check,
            ..WipeReport::default()
        })
    }
    fn counters(&self) -> DeviceCounters {
        DeviceCounters::default()
    }
    fn reset_counters(&self) {}
}

/// A text that only a build with the `test-seed` feature contains. The
/// binaries write it to stderr at start, so it is in every binary of such a
/// build; `container/check-no-test-seed.sh` refuses an image that has it.
#[cfg(feature = "test-seed")]
pub const TEST_SEED_MARKER: &str = "MIDNIGHT-GPU-PROVER-TEST-SEED-BUILD-NOT-FOR-RELEASE";

/// Writes `TEST_SEED_MARKER` to stderr in a `test-seed` build; nothing
/// otherwise.
pub fn warn_test_seed_build() {
    #[cfg(feature = "test-seed")]
    eprintln!("{TEST_SEED_MARKER}: seeded proving is compiled in; never ship this build");
}

/// The cargo features this build has, for the start record.
pub fn build_features() -> Vec<&'static str> {
    let mut v = Vec::new();
    if cfg!(feature = "cuda") {
        v.push("cuda");
    }
    if cfg!(feature = "test-seed") {
        v.push("test-seed");
    }
    if cfg!(midnight_gpu_linked) {
        v.push("midnight-gpu-linked");
    }
    v
}

/// The device of this build and configuration: a CUDA device when the build
/// links the device crates, `select` is not `off` and one is detected;
/// otherwise [`NoDevice`].
pub fn detect(select: crate::config::DeviceSelect) -> Box<dyn Device> {
    if select == crate::config::DeviceSelect::Off {
        return Box::new(NoDevice);
    }
    #[cfg(all(feature = "cuda", midnight_gpu_linked))]
    if let Some(d) = cuda::CudaDevice::detect() {
        return Box::new(d);
    }
    Box::new(NoDevice)
}

/// The binding to `midnight-gpu` and `midnight_proofs::gpu`: every call into
/// those crates is in this module. Compiled only with the cfg
/// `midnight_gpu_linked`, which the build script sets with the `cuda` feature.
///
/// The hooks are installed once per process. Each one is a thin wrapper that
/// declines (the prover then runs the stock CPU code) when its phase is not
/// admitted for the current request, so the admission ladder decides per
/// request which phases reach the device. [`Device::prepare`] registers the
/// SRS bases (device MSM tables) and the proving-key polynomials the quotient
/// reads (resident device copies); [`Device::evict`] drops the registrations.
#[cfg(all(feature = "cuda", midnight_gpu_linked))]
mod cuda {
    use std::{
        sync::{
            Mutex, OnceLock,
            atomic::{AtomicU32, AtomicU64, Ordering::Relaxed},
        },
        time::Instant,
    };

    use midnight_gpu::{self as gpu, G1AffineLimbs, G1JacobianLimbs, Scalar};
    use midnight_proofs::{
        gpu::{self as hooks, GpuHooks, adapter},
        poly::{Coeff, LagrangeCoeff},
    };

    use super::*;

    /// The phases admitted for the current request (bits of [`Phases`]).
    static ADMITTED: AtomicU32 = AtomicU32::new(0);
    /// Device MSMs and their time in nanoseconds, since the last reset.
    static MSM_NS: AtomicU64 = AtomicU64::new(0);
    /// The decline and success classes of the crate contract.
    const CLASSES: [&str; 4] = ["msm", "fft", "ifft", "quotient"];
    const PHASES: [Phases; 4] = [Phases::MSM, Phases::FFT, Phases::IFFT, Phases::QUOTIENT];
    /// Hook calls declined because their phase was not admitted, by class,
    /// since the last reset.
    static NOT_ADMITTED: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];
    /// Forward and inverse transforms that ran on the device, since the last
    /// reset.
    static FFT_OK: AtomicU64 = AtomicU64::new(0);
    /// The device layer's quotient count (since process start) at the last
    /// counter reset: the request's quotients are the difference.
    static QUOTIENT_BASE: AtomicU64 = AtomicU64::new(0);
    static IFFT_OK: AtomicU64 = AtomicU64::new(0);
    /// Transform declines of the device layer, by direction: the device
    /// layer counts both under one `ntt` class, so the hooks attribute each
    /// to `fft` or `ifft` (under [`NTT_ATTR`], so concurrent calls are not
    /// counted twice). `(class, reason, count)`.
    static NTT_DECLINES: Mutex<Vec<(&'static str, String, u64)>> = Mutex::new(Vec::new());
    static NTT_ATTR: Mutex<()> = Mutex::new(());

    /// The erasure report of a request from the device layer's counters;
    /// `Err` when the device layer did not confirm the erasure or a check
    /// call failed.
    fn wipe_result(
        w: &gpu::wipe::WipeStats,
        check: bool,
        confirmed: bool,
    ) -> Result<WipeReport, String> {
        let r = WipeReport {
            regions: w.device_blocks + w.core[0],
            bytes: w.device_bytes + w.core[1],
            checked: check,
            nonzero_regions: w.device_nonzero + w.core[3] + w.stage[3],
            check_failures: w.check_failures + w.core[4],
            erasure_failures: w.erasure_failures,
        };
        if confirmed && r.check_failures == 0 {
            return Ok(r);
        }
        Err(format!(
            "the device erasure was not confirmed ({} non-zero regions, {} failed checks, \
             {} failed erasures, {} regions in quarantine)",
            r.nonzero_regions, r.check_failures, r.erasure_failures, w.quarantined
        ))
    }

    /// The part of a since-start count `now` after the snapshot `base`.
    fn request_delta(now: u64, base: &AtomicU64) -> u64 {
        now.saturating_sub(base.load(Relaxed))
    }

    /// The device layer's `ntt` declines by reason.
    fn ntt_declines() -> Vec<(&'static str, u64)> {
        gpu::declines()
            .into_iter()
            .filter(|d| d.0 == "ntt")
            .map(|d| (d.1, d.2))
            .collect()
    }

    /// Runs one transform and attributes a device-layer decline to `class`.
    fn transform(class: &'static str, ok_count: &AtomicU64, run: impl FnOnce() -> bool) -> bool {
        let _g = NTT_ATTR.lock().unwrap_or_else(|e| e.into_inner());
        let before = ntt_declines();
        let ok = run();
        if ok {
            ok_count.fetch_add(1, Relaxed);
            return true;
        }
        let mut v = NTT_DECLINES.lock().unwrap_or_else(|e| e.into_inner());
        for (reason, after) in ntt_declines() {
            let was = before.iter().find(|b| b.0 == reason).map_or(0, |b| b.1);
            if after > was {
                match v.iter_mut().find(|e| e.0 == class && e.1 == reason) {
                    Some(e) => e.2 += after - was,
                    None => v.push((class, reason.to_string(), after - was)),
                }
            }
        }
        false
    }

    /// The request's cancel check ([`Device::set_gate`]).
    static GATE: std::sync::RwLock<Option<crate::service::Cancel>> = std::sync::RwLock::new(None);
    /// The gate withdrew the device phases.
    static WITHDRAWN: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

    /// Whether `p` is admitted; counts a `not-admitted` decline of `class`
    /// when it is not. Before a device phase launches, the request's gate
    /// runs synchronously (lease still held, client still connected); when
    /// it fails, every device phase is withdrawn.
    fn admitted(p: Phases, class: usize) -> bool {
        let mut ok = Phases::from_bits(ADMITTED.load(Relaxed)).contains(p);
        if ok && GATE.read().unwrap_or_else(|e| e.into_inner()).as_ref().is_some_and(|g| g()) {
            ADMITTED.store(0, Relaxed);
            WITHDRAWN.store(true, Relaxed);
            ok = false;
        }
        if !ok {
            NOT_ADMITTED[class].fetch_add(1, Relaxed);
        }
        ok
    }

    fn msm(scalars: &[Scalar], bases: &[G1AffineLimbs]) -> Option<G1JacobianLimbs> {
        if !admitted(Phases::MSM, 0) {
            return None;
        }
        let t = Instant::now();
        let r = gpu::msm_g1(scalars, bases);
        if r.is_some() {
            MSM_NS.fetch_add(t.elapsed().as_nanos() as u64, Relaxed);
        }
        r
    }

    fn fft(a: &mut [Scalar], omega: Scalar, log_n: u32) -> bool {
        admitted(Phases::FFT, 1) && transform("fft", &FFT_OK, || gpu::fft(a, omega, log_n))
    }

    fn ifft(a: &mut [Scalar], omega_inv: Scalar, log_n: u32, divisor: Scalar) -> bool {
        admitted(Phases::IFFT, 2)
            && transform("ifft", &IFFT_OK, || gpu::ifft(a, omega_inv, log_n, divisor))
    }

    /// # Safety
    /// As [`midnight_gpu::quotient`]: `job` is the job the prover passes.
    unsafe fn quotient(job: *const std::ffi::c_void, out: &mut [Scalar]) -> bool {
        // SAFETY: the prover's job pointer, passed through unchanged
        admitted(Phases::QUOTIENT, 3) && unsafe { gpu::quotient(job, out) }
    }

    /// A CUDA version number (`1000 * major + 10 * minor`) as `major.minor`;
    /// empty when unknown (0).
    fn version(v: u32) -> String {
        if v == 0 {
            String::new()
        } else {
            format!("{}.{}", v / 1000, (v % 1000) / 10)
        }
    }

    /// Installs the hooks once per process. `false`: another component
    /// installed hooks first.
    fn install() -> bool {
        static INSTALLED: OnceLock<bool> = OnceLock::new();
        *INSTALLED.get_or_init(|| {
            hooks::install(GpuHooks {
                msm_g1: Some(msm),
                fft: Some(fft),
                ifft: Some(ifft),
                quotient: Some(quotient),
            })
        })
    }

    /// Decline reasons that mean the device was asked and the CPU code ran
    /// instead (a fallback). `below-min-k` and `no-device` are by design,
    /// `not-admitted` is the admission's decision.
    fn is_fallback(reason: &str) -> bool {
        matches!(
            reason,
            "memory" | "device-error" | "fault" | "shape" | "unreduced"
        )
    }

    #[derive(Default)]
    struct State {
        /// Registered SRS tables (monomial and Lagrange bases): host work
        /// only. Their device contexts exist during a request and are freed
        /// at its end under either policy, so they never count as held.
        srs: Vec<gpu::SrsHandle>,
        /// Registered proving-key polynomials and their bytes.
        key: Option<gpu::KeyHandle>,
        key_bytes: u64,
        admitted: Phases,
        /// The extended domain of the prepared key reaches the device size
        /// threshold (`midnight_gpu::min_k`).
        sized: bool,
        /// Resident policy `keep`: key copies stay between requests.
        keep: bool,
        /// A quotient ran on the device since the last eviction while `keep`
        /// is on: the key copies are on the device.
        uploaded: bool,
    }

    /// The CUDA device of this process (device 0).
    pub struct CudaDevice {
        state: Mutex<State>,
    }

    impl CudaDevice {
        /// The device, when the runtime sees one with the properties the
        /// kernels need and the hooks are installed. Makes no CUDA context:
        /// the first device operation of a request makes it.
        pub fn detect() -> Option<CudaDevice> {
            if gpu::device_count() == 0 || gpu::present().is_none() || !install() {
                return None;
            }
            ADMITTED.store(0, Relaxed);
            Some(CudaDevice {
                state: Mutex::new(State::default()),
            })
        }

        fn state(&self) -> std::sync::MutexGuard<'_, State> {
            self.state.lock().unwrap_or_else(|e| e.into_inner())
        }
    }

    impl Device for CudaDevice {
        fn info(&self) -> Option<DeviceInfo> {
            let i = gpu::present()?;
            let (major, minor) = i.compute_capability;
            Some(DeviceInfo {
                name: i.name.clone(),
                arch: format!("sm_{major}{minor}"),
                build_archs: gpu::build_archs().unwrap_or_default().to_string(),
                runtime_version: version(i.runtime_version),
                driver_version: version(i.driver_version),
                total_bytes: i.total_bytes,
            })
        }

        fn mem(&self) -> Option<MemInfo> {
            // only once the context exists (reading the memory info would
            // make one): before, the free memory is unknown, and another
            // process may hold any of it, so none is reported free
            if gpu::context_active() != Some(true) {
                let i = gpu::present()?;
                return Some(MemInfo {
                    free: 0,
                    total: i.total_bytes,
                });
            }
            gpu::mem_info().map(|(free, total)| MemInfo {
                free: free as u64,
                total: total as u64,
            })
        }

        fn held(&self) -> Held {
            let s = self.state();
            // only buffers on the device between requests, each once: a
            // registration alone holds no device memory; the key copies
            // exist after a device quotient and stay only under `keep`; the
            // MSM table contexts are freed at every request's end
            Held {
                resident: if s.key.is_some() && s.uploaded {
                    s.key_bytes
                } else {
                    0
                },
                tables: 0,
            }
        }

        fn shape(&self, pk: &Pk) -> Option<Shape> {
            let q = hooks::quotient_shape(pk)?;
            Some(Shape {
                k: q.k,
                ext_k: q.ext_k,
                proof_cosets: q.proof_polys as u32,
                resident_polys: q.key_polys as u32,
                nslots: q.nslots,
                grid_threads: gpu::quotient::grid_threads(),
                quotient_bytes: gpu::quotient::need_bytes(
                    q.ext_k,
                    q.proof_polys,
                    q.key_polys,
                    q.nslots,
                ) as u64,
            })
        }

        fn set_keep(&self, keep: bool) {
            gpu::quotient::set_keep_resident(keep);
            self.state().keep = keep;
        }

        fn prepare(&self, params: &ParamsKZG<Bls12>, pk: &Pk, check: bool) {
            gpu::wipe::set_check(check);
            let mut s = self.state();
            s.sized = pk.get_vk().get_domain().extended_k() >= gpu::min_k();
            if s.srs.is_empty() {
                let coeff = params.bases::<Coeff>();
                let lagrange = params.bases::<LagrangeCoeff>();
                s.srs = vec![
                    gpu::register_srs(adapter::affine(coeff)),
                    gpu::register_srs(adapter::affine(lagrange)),
                ];
            }
            if s.key.is_none()
                && let Some(polys) = pk.gpu_resident_polys()
            {
                let limbs: Vec<&[Scalar]> = polys.iter().map(|p| adapter::scalars(p)).collect();
                s.key_bytes = 32 * polys.iter().map(|p| p.len() as u64).sum::<u64>();
                s.key = Some(gpu::register_key(&limbs));
            }
        }

        fn begin_wipe(&self, check: bool) {
            // counters and the check flag only: no device call
            gpu::wipe::set_check(check);
        }

        fn begin_request(&self, phases: Phases) -> Phases {
            // the first device operation: makes the context
            if phases.is_empty() || !gpu::device() {
                return Phases::NONE;
            }
            gpu::begin_request();
            self.state().admitted = phases;
            ADMITTED.store(phases.bits(), Relaxed);
            phases
        }

        fn revoke(&self) -> bool {
            ADMITTED.swap(0, Relaxed) != 0
        }

        fn set_gate(&self, gate: Option<crate::service::Cancel>) {
            *GATE.write().unwrap_or_else(|e| e.into_inner()) = gate;
        }

        fn withdrawn(&self) -> bool {
            WITHDRAWN.swap(false, Relaxed)
        }

        fn activate(&self) {
            // the primary context (the first device operation)
            let _ = gpu::device();
        }

        fn evict(&self, tables: bool) -> u64 {
            let mut s = self.state();
            let mut freed = 0;
            if s.key.take().is_some() && s.uploaded {
                freed += gpu::quotient::evict_key_copies().max(s.key_bytes);
            }
            s.uploaded = false;
            if tables && !s.srs.is_empty() {
                // the contexts were freed at the request's end: the
                // registrations are host memory
                s.srs.clear();
                gpu::evict_tables();
            }
            freed
        }

        fn end_request(&self, check: bool) -> Result<WipeReport, String> {
            ADMITTED.store(0, Relaxed);
            {
                let mut s = self.state();
                if s.keep && request_delta(gpu::stats().quotient, &QUOTIENT_BASE) > 0 {
                    s.uploaded = true;
                }
            }
            match gpu::end_request_report() {
                Ok(w) => wipe_result(&w, check, true),
                Err(w) => wipe_result(&w, check, false),
            }
        }

        fn counters(&self) -> DeviceCounters {
            let s = self.state();
            let st = gpu::stats();
            let calls: BTreeMap<String, u64> = [
                ("msm", st.msm),
                ("fft", FFT_OK.load(Relaxed)),
                ("ifft", IFFT_OK.load(Relaxed)),
                ("quotient", request_delta(st.quotient, &QUOTIENT_BASE)),
            ]
            .into_iter()
            .filter(|(_, n)| *n > 0)
            .map(|(k, n)| (k.to_string(), n))
            .collect();
            // the device layer's declines; its `ntt` class is split by
            // direction in the hooks
            let mut declines: Vec<Fallback> = gpu::declines()
                .into_iter()
                .filter(|d| d.0 != "ntt")
                .map(|(class, reason, count)| Fallback {
                    phase: class.to_string(),
                    reason: reason.to_string(),
                    count,
                })
                .collect();
            for (class, reason, count) in
                NTT_DECLINES.lock().unwrap_or_else(|e| e.into_inner()).iter()
            {
                declines.push(Fallback {
                    phase: class.to_string(),
                    reason: reason.clone(),
                    count: *count,
                });
            }
            // the hook layer's own declines (before it calls the hook); its
            // `hook` reason mirrors a decline counted above, so it is left
            // out: each declined call is counted once
            for (class, reason, count) in hooks::hook_declines() {
                if reason != "hook" {
                    declines.push(Fallback {
                        phase: class.to_string(),
                        reason: reason.to_string(),
                        count,
                    });
                }
            }
            for (i, c) in CLASSES.iter().enumerate() {
                let n = NOT_ADMITTED[i].load(Relaxed);
                if n > 0 {
                    declines.push(Fallback {
                        phase: c.to_string(),
                        reason: "not-admitted".into(),
                        count: n,
                    });
                }
            }
            // a fallback: a decline of an admitted phase for a reason other
            // than size or a missing device
            let fallbacks = declines
                .iter()
                .filter(|d| is_fallback(&d.reason))
                .filter(|d| {
                    CLASSES.iter().position(|c| *c == d.phase).is_some_and(|i| {
                        let p = PHASES[i];
                        s.admitted.contains(p) && (p != Phases::QUOTIENT || s.sized)
                    })
                })
                .cloned()
                .collect();
            let msm_seconds = MSM_NS.load(Relaxed) as f64 * 1e-9;
            DeviceCounters {
                msm_count: st.msm,
                msm_seconds,
                calls,
                fallbacks,
                declines,
                // the device layer resets its peak only when a request
                // starts on the device
                peak_bytes: if s.admitted.is_empty() {
                    0
                } else {
                    gpu::device_bytes().1
                },
                phase_seconds: BTreeMap::from([("msm".to_string(), msm_seconds)]),
            }
        }

        fn reset_counters(&self) {
            gpu::reset_stats();
            // the quotient count is not reset with the other statistics
            QUOTIENT_BASE.store(gpu::stats().quotient, Relaxed);
            hooks::reset_hook_declines();
            MSM_NS.store(0, Relaxed);
            FFT_OK.store(0, Relaxed);
            IFFT_OK.store(0, Relaxed);
            NTT_DECLINES.lock().unwrap_or_else(|e| e.into_inner()).clear();
            for c in &NOT_ADMITTED {
                c.store(0, Relaxed);
            }
            self.state().admitted = Phases::NONE;
        }
    }

    #[cfg(test)]
    mod tests {
        use std::sync::Mutex;

        use super::*;

        /// The binding's counters are process-wide: one test at a time.
        static SERIAL: Mutex<()> = Mutex::new(());

        fn device() -> CudaDevice {
            CudaDevice {
                state: Mutex::new(State::default()),
            }
        }

        /// A3: a declined call is counted once, by phase and reason, and a
        /// size decline is not a fallback.
        #[test]
        fn a_below_min_k_msm_is_one_decline_by_reason() {
            let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
            let d = device();
            d.reset_counters();
            d.state().admitted = Phases::MSM;
            ADMITTED.store(Phases::MSM.bits(), Relaxed);
            assert!(msm(&[[0u64; 4]], &[[0u64; 12]]).is_none());
            // a phase that was not admitted is a decline of its own reason
            assert!(!fft(&mut [[0u64; 4]; 2], [0u64; 4], 1));
            assert!(!ifft(&mut [[0u64; 4]; 2], [0u64; 4], 1, [0u64; 4]));
            ADMITTED.store(0, Relaxed);
            let c = d.counters();
            let row = |p: &str, r: &str| {
                c.declines
                    .iter()
                    .filter(|f| f.phase == p && f.reason == r)
                    .map(|f| f.count)
                    .sum::<u64>()
            };
            assert_eq!(row("msm", "below-min-k"), 1, "{:?}", c.declines);
            assert_eq!(row("fft", "not-admitted"), 1, "{:?}", c.declines);
            assert_eq!(row("ifft", "not-admitted"), 1, "{:?}", c.declines);
            assert_eq!(
                c.declines.iter().map(|f| f.count).sum::<u64>(),
                3,
                "{:?}",
                c.declines
            );
            assert_eq!(c.fallback_count(), 0);
            // the success counters split forward and inverse transforms
            assert!(!c.calls.contains_key("coset") && !c.calls.contains_key("ntt"));
        }

        /// A4: `keep` turns on the backend's keep setting, and a key
        /// registration alone holds no device memory.
        #[test]
        fn keep_sets_the_backend_and_held_counts_uploads_only() {
            let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
            let d = device();
            d.set_keep(true);
            assert!(gpu::quotient::keep_resident());
            let poly = vec![[0u64; 4]; 8];
            {
                let mut s = d.state();
                s.key = Some(gpu::register_key(&[&poly]));
                s.key_bytes = 256;
            }
            assert_eq!(d.held().resident, 0, "a registration is not an upload");
            d.state().uploaded = true;
            assert_eq!(d.held().resident, 256);
            d.evict(false);
            assert_eq!(d.held().resident, 0);
            d.set_keep(false);
            assert!(!gpu::quotient::keep_resident());
        }

        /// ORACLE-05: a failed check call is its own count, not a non-zero
        /// region, and it fails the request's erasure report.
        #[test]
        fn a_failed_check_is_counted_and_fails_the_wipe() {
            let w = gpu::wipe::WipeStats {
                device_blocks: 3,
                check_failures: 1,
                ..Default::default()
            };
            let e = wipe_result(&w, true, true).unwrap_err();
            assert!(e.contains("1 failed checks"), "{e}");
            let w = gpu::wipe::WipeStats {
                device_blocks: 3,
                ..Default::default()
            };
            let r = wipe_result(&w, true, true).unwrap();
            assert_eq!(
                (r.nonzero_regions, r.check_failures, r.erasure_failures),
                (0, 0, 0)
            );
            let w = gpu::wipe::WipeStats {
                device_nonzero: 2,
                check_failures: 1,
                ..Default::default()
            };
            let e = wipe_result(&w, true, false).unwrap_err();
            assert!(e.contains("2 non-zero regions, 1 failed checks"), "{e}");
        }

        /// QA4 ORACLE-02: the gate runs before a device phase launches; a
        /// failed gate withdraws every device phase at once.
        #[test]
        fn a_failed_gate_withdraws_before_the_launch() {
            let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
            let d = device();
            d.reset_counters();
            d.withdrawn();
            let all = Phases::FFT.union(Phases::IFFT);
            ADMITTED.store(all.bits(), Relaxed);
            d.set_gate(Some(std::sync::Arc::new(|| true)));
            assert!(!fft(&mut [[0u64; 4]; 2], [0u64; 4], 1));
            assert_eq!(ADMITTED.load(Relaxed), 0);
            assert!(d.withdrawn());
            d.set_gate(None);
            d.reset_counters();
        }

        /// r13 BLOCKING 1: before the context exists the free memory is
        /// unknown; none is reported free (another process may hold it).
        #[test]
        fn a_cold_device_reports_no_free_memory() {
            let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
            if gpu::present().is_none() || gpu::context_active() == Some(true) {
                return;
            }
            let m = device().mem().unwrap();
            assert!(m.total > 0);
            assert_eq!(m.free, 0, "the total is not free memory");
            assert_ne!(gpu::context_active(), Some(true), "mem() made a context");
        }

        /// r13 BLOCKING 3: with no device phase admitted the peak is 0.
        #[test]
        fn no_device_phase_reports_no_peak() {
            let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
            let d = device();
            d.reset_counters();
            assert_eq!(d.counters().peak_bytes, 0);
            assert!(!d.counters().calls.contains_key("quotient"));
        }

        /// GPU-025: the registered SRS tables are host work; their device
        /// contexts are freed at every request's end, so a prepared key with
        /// no device quotient yet holds nothing on the device.
        #[cfg(feature = "test-seed")]
        #[test]
        fn held_counts_only_device_resident_buffers() {
            let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
            let d = device();
            d.set_keep(true);
            let c = midnight_proofs::gpu::test_switches::RandomCircuit::new(1, true, 8);
            d.prepare(c.params(), c.pk(), false);
            assert!(!d.state().srs.is_empty(), "the tables are registered");
            assert_eq!(d.held(), Held::default());
            d.evict(true);
            d.set_keep(false);
        }

        /// A5: the admission's quotient need is the job's own memory check
        /// (`need_bytes`), on a random constraint system with lookups,
        /// a permutation and a trash argument.
        #[cfg(feature = "test-seed")]
        #[test]
        fn quotient_need_is_the_job_memory_check() {
            use crate::need::DeviceNeed;
            let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
            let d = device();
            for seed in 0..4 {
                let c = midnight_proofs::gpu::test_switches::RandomCircuit::new(seed, true, 8);
                let q = hooks::quotient_shape(c.pk()).expect("the job takes the key");
                let shape = d.shape(c.pk()).unwrap();
                let need = DeviceNeed::of(&shape, 0);
                let job = gpu::quotient::need_bytes(q.ext_k, q.proof_polys, q.key_polys, q.nslots);
                assert_eq!(need.quotient + need.resident, job as u64, "seed {seed}");
                assert_eq!(shape.nslots, q.nslots);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn phases_names_and_sets() {
        assert_eq!(Phases::ALL.names(), vec!["msm", "fft", "ifft", "quotient"]);
        // the reduced set: no quotient, the transforms split by direction
        assert_eq!(
            Phases::ALL.without(Phases::QUOTIENT).names(),
            vec!["msm", "fft", "ifft"]
        );
        assert!(Phases::ALL.contains(Phases::MSM.union(Phases::FFT).union(Phases::IFFT)));
        assert!(Phases::from_bits(0xff).contains(Phases::ALL));
        assert_eq!(Phases::from_bits(0xf0), Phases::NONE);
    }

    /// The `cuda` feature links the device crates: a build where the feature
    /// is on but the binding is compiled out fails here.
    #[cfg(feature = "cuda")]
    #[test]
    fn cuda_feature_links_the_device_crates() {
        assert!(cfg!(midnight_gpu_linked));
        assert!(build_features().contains(&"midnight-gpu-linked"));
        // a build that requires the CUDA core must have compiled it
        if std::env::var_os("MIDNIGHT_GPU_REQUIRE_CUDA").is_some_and(|v| v == "1") {
            assert!(midnight_gpu::cuda_built());
        }
        // callable whether or not a device is present
        let _ = midnight_gpu::present();
    }

    #[test]
    fn no_device_is_inert() {
        let d = NoDevice;
        assert!(d.info().is_none() && d.mem().is_none());
        assert_eq!(d.begin_request(Phases::ALL), Phases::NONE);
        assert_eq!(d.evict(true), 0);
        assert!(d.end_request(true).unwrap().checked);
        assert_eq!(d.counters().fallback_count(), 0);
    }
}
