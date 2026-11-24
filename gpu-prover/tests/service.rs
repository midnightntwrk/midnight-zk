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

//! The service on the CPU path and with fake device layers: start refusals,
//! admission, resident policy, fallback labelling, retirement, records.

mod common;

use common::*;
use midnight_gpu_prover::{
    Error, ProverService, RequestOptions,
    admission::Step,
    config::{ResidentPolicy, RunMode, WslSelect},
    device::{NoDevice, Phases},
    example::{PoseidonPreimage, example_input},
    input::SecretBytes,
    report::Label,
    service::vk_sha256,
};

fn input(seed: u64) -> SecretBytes {
    SecretBytes::new(example_input(seed))
}

#[test]
fn cpu_proof_verifies_and_is_labelled_cpu() {
    let mut s = service(config(), Box::new(NoDevice));
    let served = s.prove(&input(1), RequestOptions::default()).unwrap();
    let r = &served.record;
    assert_eq!((r.label, r.step), (Label::Cpu, Step::None));
    assert_eq!(r.request, 1);
    assert_eq!(r.fallback_count, 0);
    assert!(r.prove_s > 0.0 && r.verify_s > 0.0 && r.host_hwm_bytes > 0);
    // the stock verifier of the standard library accepts the proof
    let (inst, _) =
        midnight_gpu_prover::ServedRelation::decode_input(&PoseidonPreimage, &example_input(1))
            .unwrap();
    midnight_zk_stdlib::verify::<PoseidonPreimage, blake2b_simd::State, _>(
        s.verifier_params(),
        s.vk(),
        &inst,
        None,
        &served.proof,
    )
    .unwrap();
    // two proofs of one input differ (fresh blinding)
    let again = s.prove(&input(1), RequestOptions::default()).unwrap();
    assert_ne!(again.proof, served.proof);
    assert_eq!(again.record.public_inputs_sha256, r.public_inputs_sha256);
}

#[test]
fn record_holds_no_request_content() {
    let mut s = service(config(), Box::new(NoDevice));
    let served = s.prove(&input(5), RequestOptions::default()).unwrap();
    let text = serde_json::to_string(&served.record).unwrap();
    let raw = example_input(5);
    for chunk in raw.chunks(32) {
        assert!(!text.contains(&hex::encode(chunk)));
    }
    let start = serde_json::to_string(s.start_record()).unwrap();
    assert!(start.contains("\"vk_sha256\""));
}

#[test]
fn start_refuses_bad_k_and_small_srs() {
    let e = ProverService::with_device(
        PoseidonPreimage,
        srs(),
        midnight_gpu_prover::Config {
            max_k: 5,
            ..config()
        },
        Box::new(NoDevice),
    )
    .unwrap_err();
    assert!(
        matches!(e, Error::Refused(ref m) if m.contains("max_k")),
        "{e}"
    );
    let mut small = srs();
    small.downsize(5);
    let e = ProverService::with_device(PoseidonPreimage, small, config(), Box::new(NoDevice))
        .unwrap_err();
    assert!(
        matches!(e, Error::Refused(ref m) if m.contains("SRS")),
        "{e}"
    );
}

#[test]
fn start_checks_the_vk_pin() {
    let s = service(config(), Box::new(NoDevice));
    let good = vk_sha256(s.vk());
    assert_eq!(good, s.start_record().vk_sha256);
    let cfg = midnight_gpu_prover::Config {
        vk_sha256: Some("00".repeat(32)),
        ..config()
    };
    let e =
        ProverService::with_device(PoseidonPreimage, srs(), cfg, Box::new(NoDevice)).unwrap_err();
    assert!(
        matches!(e, Error::Refused(ref m) if m.contains("pin")),
        "{e}"
    );
    let cfg = midnight_gpu_prover::Config {
        vk_sha256: Some(good),
        ..config()
    };
    assert!(ProverService::with_device(PoseidonPreimage, srs(), cfg, Box::new(NoDevice)).is_ok());
}

#[test]
fn wsl_profile_refuses_keep() {
    let cfg = midnight_gpu_prover::Config {
        wsl: WslSelect::On,
        resident: ResidentPolicy::Keep,
        ..config()
    };
    let e =
        ProverService::with_device(PoseidonPreimage, srs(), cfg, Box::new(NoDevice)).unwrap_err();
    assert!(matches!(e, Error::Refused(_)));
}

#[test]
fn resident_policy_evicts_by_default_and_keeps_on_request() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        ..Fake::default()
    };
    let log = f.log.clone();
    let mut s = service(config(), Box::new(f));
    s.prove(&input(1), RequestOptions::default()).unwrap();
    s.prove(&input(2), RequestOptions::default()).unwrap();
    assert_eq!(*log.evicts.lock().unwrap(), vec![true, true]);
    let f = Fake {
        shape: Some(Fake::big_shape()),
        ..Fake::default()
    };
    let log = f.log.clone();
    let cfg = midnight_gpu_prover::Config {
        resident: ResidentPolicy::Keep,
        ..config()
    };
    let mut s = service(cfg, Box::new(f));
    let r = s.prove(&input(1), RequestOptions::default()).unwrap().record;
    assert!(log.evicts.lock().unwrap().is_empty());
    assert_eq!(
        (r.label, r.step, r.admitted),
        (Label::Gpu, Step::Gpu, Phases::ALL)
    );
    assert_eq!(r.wipe.regions, 3);
    assert_eq!(log.ends.load(std::sync::atomic::Ordering::SeqCst), 1);
}

#[test]
fn a_key_the_device_quotient_does_not_take_runs_the_quotient_on_the_cpu() {
    let f = Fake::default(); // no shape
    let log = f.log.clone();
    let mut s = service(config(), Box::new(f));
    assert_eq!(
        s.start_record().phases,
        Phases::ALL.without(Phases::QUOTIENT)
    );
    let r = s.prove(&input(1), RequestOptions::default()).unwrap().record;
    assert_eq!(
        log.begins.lock().unwrap()[0],
        Phases::ALL.without(Phases::QUOTIENT)
    );
    assert!(r.degraded_reasons.iter().any(|m| m.contains("quotient")));
    // no hook fell back: the label is `gpu` (GPU-085, GPU-012)
    assert_eq!(r.label, Label::Gpu);
    // acceptance mode refuses it before any device work
    let f = Fake::default();
    let log = f.log.clone();
    let cfg = midnight_gpu_prover::Config {
        mode: RunMode::Acceptance,
        ..config()
    };
    let mut s = service(cfg, Box::new(f));
    assert!(matches!(
        s.prove(&input(1), RequestOptions::default()),
        Err(Error::Degraded(_))
    ));
    assert!(log.begins.lock().unwrap().is_empty());
}

#[test]
fn admission_moves_phases_off_the_device_when_memory_is_short() {
    let cfg = midnight_gpu_prover::Config {
        wait_s: 0.0,
        ..config()
    };
    // enough for the reduced set only
    let need = midnight_gpu_prover::need::DeviceNeed::of(&Fake::big_shape(), 768 << 20);
    let f = Fake {
        shape: Some(Fake::big_shape()),
        free: need.reduced(Default::default()) + 1,
        ..Fake::default()
    };
    let mut s = service(cfg.clone(), Box::new(f));
    let r = s.prove(&input(1), RequestOptions::default()).unwrap().record;
    // the quotient left at admission is no hook fallback: the label is
    // `gpu`, the step and the reason mark the proof degraded (GPU-023)
    assert_eq!((r.step, r.label), (Step::Evict, Label::Gpu));
    assert!(!r.degraded_reasons.is_empty());
    assert_eq!(r.admitted, Phases::ALL.without(Phases::QUOTIENT));
    // nothing fits: CPU, served
    let f = Fake {
        shape: Some(Fake::big_shape()),
        free: 1 << 20,
        ..Fake::default()
    };
    let mut s = service(cfg.clone(), Box::new(f));
    let r = s.prove(&input(1), RequestOptions::default()).unwrap().record;
    assert_eq!(
        (r.step, r.label, r.admitted),
        (Step::Cpu, Label::Cpu, Phases::NONE)
    );
    // acceptance mode: a degraded admission fails the request
    let f = Fake {
        shape: Some(Fake::big_shape()),
        free: 1 << 20,
        ..Fake::default()
    };
    let log = f.log.clone();
    let mut s = service(
        midnight_gpu_prover::Config {
            mode: RunMode::Acceptance,
            ..cfg
        },
        Box::new(f),
    );
    let e = s.prove(&input(1), RequestOptions::default()).unwrap_err();
    assert!(matches!(e, Error::Degraded(_)), "{e}");
    assert!(log.begins.lock().unwrap().is_empty(), "no proof starts");
}

#[test]
fn wsl_budget_is_used_instead_of_the_free_memory_query() {
    // the device reports no free memory, but the WSL2 budget (total -
    // reserve) fits
    let f = Fake {
        shape: Some(Fake::big_shape()),
        free: 0,
        total: 32 * GIB,
        ..Fake::default()
    };
    let dir = tempfile::tempdir().unwrap();
    let lock = dir.path().join("dev.lock");
    let held = midnight_gpu_prover::lock::lock_exclusive(&lock).unwrap();
    let cfg = midnight_gpu_prover::Config {
        wsl: WslSelect::On,
        lock_path: Some(lock.clone()),
        ..config()
    };
    let mut s = service(cfg, Box::new(f));
    use std::os::fd::AsFd;
    let fd = held.as_fd().try_clone_to_owned().unwrap();
    let lease = midnight_gpu_prover::lock::Lease::validate(&lock, Some(fd)).unwrap();
    let r = s
        .prove(
            &input(1),
            RequestOptions {
                lease: Some(lease),
                ..RequestOptions::default()
            },
        )
        .unwrap()
        .record;
    assert_eq!((r.step, r.free), (Step::Gpu, 28 * GIB));
    // without a lease: CPU, marked
    let r = s
        .prove(
            &input(1),
            RequestOptions {
                lease_refused: Some("not-held"),
                ..RequestOptions::default()
            },
        )
        .unwrap()
        .record;
    assert_eq!((r.step, r.label), (Step::Cpu, Label::Cpu));
    assert!(r.degraded_reasons[0].contains("not-held"));
}

#[test]
fn a_counted_fallback_is_served_degraded_in_production_and_fails_acceptance() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        fallbacks: 2,
        ..Fake::default()
    };
    let mut s = service(config(), Box::new(f));
    let r = s.prove(&input(1), RequestOptions::default()).unwrap().record;
    assert_eq!((r.label, r.fallback_count), (Label::GpuDegraded, 2));
    assert_eq!(r.fallbacks[0].phase, "fft");
    let f = Fake {
        shape: Some(Fake::big_shape()),
        fallbacks: 1,
        ..Fake::default()
    };
    let log = f.log.clone();
    let cfg = midnight_gpu_prover::Config {
        mode: RunMode::Acceptance,
        ..config()
    };
    let mut s = service(cfg, Box::new(f));
    assert!(matches!(
        s.prove(&input(1), RequestOptions::default()),
        Err(Error::Degraded(_))
    ));
    // the wipe ran although the request failed
    assert_eq!(log.ends.load(std::sync::atomic::Ordering::SeqCst), 1);
}

#[test]
fn a_device_layer_that_takes_fewer_phases_marks_the_proof_degraded() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        take: Some(Phases::MSM),
        ..Fake::default()
    };
    let mut s = service(config(), Box::new(f));
    let r = s.prove(&input(1), RequestOptions::default()).unwrap().record;
    // marked by its reason (GPU-023); no hook fell back, so the label is
    // `gpu` (GPU-085, GPU-012)
    assert!(r.degraded_reasons.iter().any(|m| m.contains("fewer phases")));
    assert_eq!((r.label, r.admitted), (Label::Gpu, Phases::MSM));
    let f = Fake {
        shape: Some(Fake::big_shape()),
        take: Some(Phases::MSM),
        ..Fake::default()
    };
    let log = f.log.clone();
    let cfg = midnight_gpu_prover::Config {
        mode: RunMode::Acceptance,
        ..config()
    };
    let mut s = service(cfg, Box::new(f));
    assert!(matches!(
        s.prove(&input(1), RequestOptions::default()),
        Err(Error::Degraded(_))
    ));
    assert_eq!(
        log.ends.load(std::sync::atomic::Ordering::SeqCst),
        1,
        "the wipe ran"
    );
}

/// GPU-085 with GPU-012: the label `gpu-degraded` needs a served device
/// call and a counted fallback. A request admitted in degraded mode (step
/// `evict`, a key the device quotient does not take, a device layer that
/// takes fewer phases) whose hooks never fell back is labelled `gpu`; its
/// admission reasons stay in `degraded_reasons` (GPU-023).
#[test]
fn a_degraded_admission_without_a_fallback_is_labelled_gpu() {
    let cfg = midnight_gpu_prover::Config {
        wait_s: 0.0,
        ..config()
    };
    let need = midnight_gpu_prover::need::DeviceNeed::of(&Fake::big_shape(), 768 << 20);
    let run = |f: Fake| {
        let mut s = service(cfg.clone(), Box::new(f));
        s.prove(&input(1), RequestOptions::default()).unwrap().record
    };
    let evict = run(Fake {
        shape: Some(Fake::big_shape()),
        free: need.reduced(Default::default()) + 1,
        ..Fake::default()
    });
    let no_quotient = run(Fake::default());
    let fewer = run(Fake {
        shape: Some(Fake::big_shape()),
        take: Some(Phases::MSM),
        ..Fake::default()
    });
    assert_eq!(evict.step, Step::Evict);
    for r in [&evict, &no_quotient, &fewer] {
        assert_eq!(r.fallback_count, 0);
        assert!(!r.degraded_reasons.is_empty());
        assert_eq!(r.label, Label::Gpu, "{:?}", r.degraded_reasons);
    }
}

#[test]
fn an_unconfirmed_wipe_retires_the_service() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        wipe_fails: true,
        ..Fake::default()
    };
    let log = f.log.clone();
    let mut s = service(config(), Box::new(f));
    let e = s.prove(&input(1), RequestOptions::default()).unwrap_err();
    assert!(matches!(e, Error::Retired(_)), "{e}");
    assert!(s.retired().is_some());
    // no further witness is taken
    assert!(matches!(
        s.prove(&input(2), RequestOptions::default()),
        Err(Error::Retired(_))
    ));
    assert_eq!(log.begins.lock().unwrap().len(), 1);
}

#[test]
fn bad_input_is_refused_before_any_device_work() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        ..Fake::default()
    };
    let log = f.log.clone();
    let mut s = service(config(), Box::new(f));
    let e = s
        .prove(&SecretBytes::new(vec![1, 2, 3]), RequestOptions::default())
        .unwrap_err();
    assert!(matches!(e, Error::Input(_)));
    assert!(log.begins.lock().unwrap().is_empty());
}

/// The seeded entry proves and the proof verifies. Without the hook layer's
/// seeded quotient blinding the stock quotient blinding draws from the
/// operating system, so byte identity is asserted only in `gpu.rs`.
#[cfg(feature = "test-seed")]
#[test]
fn seeded_entry_proves() {
    let mut s = service(config(), Box::new(NoDevice));
    let a = s.prove_seeded(&input(1), RequestOptions::default(), 42).unwrap();
    assert_eq!(a.record.label, Label::Cpu);
}
