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

//! A real device call whose error arm drains its stream, with that
//! drain made unconfirmed, retires the device for the rest of the
//! process: the call itself declines as a device error (the caller
//! falls back to the CPU on its intact input), and every later device
//! call declines for the teardown. The state is sticky, so the
//! sequence runs in a child process and the parent checks that it
//! exited with status 0. Without a device the child takes its skip
//! path. On the code before the wiring nothing retired the device,
//! so the first assertion after the failed call (the device is
//! disabled) is the one that fires.
#![cfg(feature = "test-fault")]

use ff::{Field, PrimeField};
use group::prime::PrimeCurveAffine;
use midnight_curves::{Fq, G1Affine, fft::best_fft};
use midnight_gpu::{self as gpu, abi::QuotientJobAbi, fault, field};
use midnight_proofs::gpu::adapter;

const CHILD: &str = "MGPU_DRAIN_TEARDOWN_CHILD";

fn declined(class: &str, reason: &str) -> u64 {
    gpu::declines()
        .into_iter()
        .filter(|(c, r, _)| *c == class && *r == reason)
        .map(|(_, _, n)| n)
        .sum()
}

fn root(k: u32) -> Fq {
    let mut w = Fq::ROOT_OF_UNITY;
    for _ in k..Fq::S {
        w = w.square();
    }
    w
}

#[test]
fn unconfirmed_drain_in_a_device_call_retires_the_device() {
    if std::env::var_os(CHILD).is_none() {
        let exe = std::env::current_exe().expect("test binary path");
        let out = std::process::Command::new(exe)
            .args([
                "--exact",
                "unconfirmed_drain_in_a_device_call_retires_the_device",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .expect("run the child test process");
        assert!(
            out.status.success(),
            "child exited with {:?}\nstdout: {}\nstderr: {}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        // The state is per process: the parent is untouched.
        assert!(!gpu::teardown::device_disabled());
        assert!(!gpu::teardown::erasure_failed());
        return;
    }
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    gpu::set_min_k(1);
    assert!(!gpu::teardown::device_disabled());
    assert!(!gpu::teardown::erasure_failed());

    // One good transform first, so device state exists at the reset.
    let mut warm = vec![Fq::ONE; 64];
    assert!(gpu::fft(
        adapter::scalars_mut(&mut warm),
        adapter::scalar(root(6)),
        6
    ));

    let input: Vec<Fq> = (0..64u64).map(|i| Fq::from(i * i + 1)).collect();
    let mut expected = input.clone();
    best_fft(&mut expected, root(6), 6);
    let mut a = input.clone();
    let (run0, bad0) = gpu::error_drains();

    // A real failed device call whose error arm drains: the read-back
    // fault fails the private copy after its first chunk, and that
    // exit drains the stream; the switch makes the drain report not
    // confirmed.
    fault::arm(fault::Class::Ntt, fault::Point::Readback, 1);
    fault::unconfirm_next_drains(1);
    let ok = gpu::fft(adapter::scalars_mut(&mut a), adapter::scalar(root(6)), 6);
    fault::unconfirm_next_drains(0);
    fault::reset();

    // The first assertion after the call: the one that fires on the
    // code before the wiring.
    assert!(
        gpu::teardown::device_disabled(),
        "an unconfirmed drain in a device call retires the device \
         (drains now {:?}, were ({run0}, {bad0}))",
        gpu::error_drains()
    );
    assert!(!ok, "the call that saw the failed drain declines");
    assert_eq!(a, input, "the caller's buffer is intact");
    best_fft(&mut a, root(6), 6);
    assert_eq!(a, expected, "the CPU fallback gives the right result");
    let (run1, bad1) = gpu::error_drains();
    assert!(run1 > run0, "the error arm drained");
    assert!(bad1 > bad0, "the drain was not confirmed");
    assert!(gpu::teardown::erasure_failed());
    assert_ne!(
        gpu::context_active(),
        Some(true),
        "no context is left, and none was made again"
    );
    assert_eq!(
        declined("ntt", "teardown"),
        0,
        "the call itself declined as a device error, not a teardown"
    );
    assert!(
        declined("ntt", "device-error") >= 1,
        "{:?}",
        gpu::declines()
    );
    let p = gpu::wipe::pending_erasure();
    assert_eq!(
        p.undrained, 0,
        "the reset ended every transfer, so nothing is undrained: {p:?}"
    );
    assert!(p.clear(), "nothing is pending after the reset: {p:?}");

    // Every later device call declines for the teardown.
    let n0 = gpu::teardown::declined_after_teardown();
    let bases = [G1Affine::generator(); 32];
    let scalars = [Fq::from(1); 32];
    assert!(gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases)).is_none());
    assert_eq!(declined("msm", "teardown"), 1);
    let mut b = input.clone();
    assert!(!gpu::fft(
        adapter::scalars_mut(&mut b),
        adapter::scalar(root(6)),
        6
    ));
    assert_eq!(b, input, "a declined transform changes nothing");
    assert_eq!(declined("ntt", "teardown"), 1);

    // SAFETY: a plain repr(C) struct of integers and pointers; zero is
    // valid. A header only: the passing header stops at the teardown
    // before any pointer field is read.
    let mut j: QuotientJobAbi = unsafe { std::mem::zeroed() };
    j.abi = gpu::abi::QUOTIENT_ABI;
    (j.k, j.ext_k) = (5, 6);
    let z = field::primitive_cube_root();
    let z2 = field::square(&z);
    j.zeta = [z, z2];
    j.zeta_out = [z2, z];
    let mut out = vec![[7u64; 4]; 8];
    // SAFETY: the header-only job, as above.
    assert!(!unsafe { gpu::quotient(&j as *const _ as *const std::ffi::c_void, &mut out) });
    assert!(out.iter().all(|v| *v == [7u64; 4]));
    assert_eq!(declined("quotient", "teardown"), 1);
    assert_eq!(gpu::teardown::declined_after_teardown(), n0 + 3);
    assert!(
        !gpu::end_request(),
        "a forced teardown is an erasure failure"
    );
}
