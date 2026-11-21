// SPDX-License-Identifier: Apache-2.0

use std::{
    collections::BTreeMap,
    ffi::c_void,
    sync::{
        Mutex, OnceLock,
        atomic::{AtomicBool, AtomicU64, Ordering::Relaxed},
    },
};

use midnight_gpu::{self as gpu, G1AffineLimbs, G1JacobianLimbs, Scalar};
use midnight_proofs::gpu::{self as hooks, GpuHooks, test_switches::QUOTIENT_CHECK};

// The installed hooks, threshold, counters and without_hooks switch are
// process-wide.
static SERIAL: Mutex<()> = Mutex::new(());
static SHORT_INPUT: AtomicBool = AtomicBool::new(false);
pub static NONPRIMITIVE_SHIFT: AtomicBool = AtomicBool::new(false);

#[derive(Clone, Copy)]
pub enum Expected {
    Bypassed,
    Device,
    Decline(&'static str),
}

pub struct Calls {
    class: &'static str,
    offered: AtomicU64,
    completed: fn(gpu::Stats) -> u64,
}

impl Calls {
    const fn new(class: &'static str, completed: fn(gpu::Stats) -> u64) -> Self {
        Self {
            class,
            offered: AtomicU64::new(0),
            completed,
        }
    }

    fn declines(&self) -> BTreeMap<&'static str, u64> {
        gpu::declines()
            .into_iter()
            .filter(|&(class, _, _)| class == self.class)
            .map(|(_, reason, count)| (reason, count))
            .collect()
    }

    pub fn check<T>(&self, expected: Expected, run: impl FnOnce() -> T) -> T {
        let mut declines = self.declines();
        let reason = match expected {
            Expected::Device if !gpu::cuda_built() => Some("no-device"),
            Expected::Decline(reason) => Some(reason),
            _ => None,
        };
        if let Some(reason) = reason {
            *declines.entry(reason).or_default() += 1;
        }
        let attempts = self.offered.load(Relaxed);
        let before = gpu::stats();
        let result = run();
        let after = gpu::stats();
        assert_eq!(
            self.offered.load(Relaxed) - attempts,
            u64::from(!matches!(expected, Expected::Bypassed)),
            "hook offers"
        );
        assert_eq!(
            (self.completed)(after) - (self.completed)(before),
            u64::from(matches!(expected, Expected::Device) && gpu::cuda_built()),
            "successful device calls"
        );
        assert_eq!(self.declines(), declines, "{} decline labels", self.class);
        assert_eq!(
            after.device_errors, before.device_errors,
            "unexpected device error"
        );
        result
    }
}

pub static MSM: Calls = Calls::new("msm", |s| s.msm);
pub static FFT: Calls = Calls::new("ntt", |s| s.ntt);
pub static IFFT: Calls = Calls::new("ntt", |s| s.ntt);
pub static QUOTIENT: Calls = Calls::new("quotient", |s| s.quotient);

// Quotient tests set min_k above the base domain. Include the prover's
// incidental MSM and NTT offers in the decline-label checks.
pub fn check_base_declines<T>(prove: impl FnOnce() -> T) -> T {
    let offers = || {
        [
            MSM.offered.load(Relaxed),
            FFT.offered.load(Relaxed) + IFFT.offered.load(Relaxed),
        ]
    };
    let before = offers();
    let expected = [MSM.declines(), FFT.declines()];
    let result = prove();
    let after = offers();
    for (i, (calls, mut labels)) in [&MSM, &FFT].into_iter().zip(expected).enumerate() {
        let count = after[i] - before[i];
        if count > 0 {
            *labels.entry("below-min-k").or_default() += count;
        }
        assert_eq!(
            calls.declines(),
            labels,
            "{} base-domain declines",
            calls.class
        );
    }
    result
}

fn msm(s: &[Scalar], p: &[G1AffineLimbs]) -> Option<G1JacobianLimbs> {
    MSM.offered.fetch_add(1, Relaxed);
    gpu::msm_g1(s, p)
}

fn input_len(n: usize) -> usize {
    if SHORT_INPUT.load(Relaxed) { n - 1 } else { n }
}

pub fn fft(a: &mut [Scalar], w: Scalar, k: u32) -> bool {
    FFT.offered.fetch_add(1, Relaxed);
    let n = input_len(a.len());
    gpu::fft(&mut a[..n], w, k)
}

pub fn ifft(a: &mut [Scalar], w: Scalar, k: u32, d: Scalar) -> bool {
    IFFT.offered.fetch_add(1, Relaxed);
    let n = input_len(a.len());
    gpu::ifft(&mut a[..n], w, k, d)
}

unsafe fn quotient(job: *const c_void, out: &mut [Scalar]) -> bool {
    QUOTIENT.offered.fetch_add(1, Relaxed);
    let mut changed;
    let job = if NONPRIMITIVE_SHIFT.load(Relaxed) {
        // SAFETY: the prover owns this packed header and all referenced tables for this
        // call.
        changed = unsafe { *job.cast::<hooks::abi::QuotientJobAbi>() };
        changed.zeta = [gpu::field::one(); 2];
        changed.zeta_out = changed.zeta;
        std::ptr::from_ref(&changed).cast()
    } else {
        job
    };
    let before = gpu::xfer::stats();
    // SAFETY: forward the packed job and its original output slice within the
    // prover call.
    let ok = unsafe { gpu::quotient(job, out) };
    let after = gpu::xfer::stats();
    // Only the truncated coefficients may return from the quotient call.
    assert_eq!(after.d2h_copies - before.d2h_copies, u64::from(ok));
    let bytes = if ok { std::mem::size_of_val(out) } else { 0 };
    assert_eq!(after.d2h_bytes - before.d2h_bytes, bytes as u64);
    ok
}

pub fn run(min_k: u32, short_input: bool, test: impl FnOnce() + Send) {
    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    let _guard = SERIAL.lock().unwrap_or_else(|p| p.into_inner());
    let pool = POOL.get_or_init(|| {
        assert!(hooks::install(GpuHooks {
            msm_g1: Some(msm),
            fft: Some(fft),
            ifft: Some(ifft),
            quotient: Some(quotient),
        }));
        if cfg!(feature = "cuda") || std::env::var_os("FUZZ_REQUIRE_DEVICE").is_some() {
            assert!(
                gpu::cuda_built() && gpu::device(),
                "CUDA tests require a usable device"
            );
        }
        rayon::ThreadPoolBuilder::new().num_threads(4).build().unwrap()
    });
    gpu::set_min_k(min_k);
    SHORT_INPUT.store(short_input, Relaxed);
    QUOTIENT_CHECK.store(true, Relaxed);
    pool.install(test);
    assert!(gpu::end_request(), "device scratch cleanup");
}
