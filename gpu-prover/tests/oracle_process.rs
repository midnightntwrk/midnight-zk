// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

//! Process and deadline observations outside the finite service trace codec.
#![cfg(all(not(feature = "cuda"), not(feature = "test-seed")))]

use std::{
    fs,
    path::Path,
    process::{Command, Output},
    time::{Duration, Instant},
};

use midnight_gpu_prover::{
    admission::{Ladder, Step, admit},
    device::{Held, Phases},
    need::DeviceNeed,
    report::sha256_hex,
};
use serde_json::Value;

const DAEMON: &str = env!("CARGO_BIN_EXE_midnight-gpu-proverd");

fn launch(args: &[&str], setting: Option<(&str, &str)>) -> Output {
    let dir = tempfile::tempdir().unwrap();
    // A regular file as a parent makes a successful socket bind impossible.
    fs::write(dir.path().join("occupied"), []).unwrap();
    let mut cmd = Command::new(DAEMON);
    cmd.current_dir(dir.path()).env_clear().env("MIDNIGHT_GPU_PROVER_THREADS", "2");
    if let Some((key, value)) = setting {
        cmd.env(key, value);
    }
    cmd.args(["--socket", "occupied/socket"]).args(args).output().unwrap()
}

#[test]
fn production_switch_refused_before_service_start() {
    let out = launch(&["--insecure-test-srs"], Some(("MIDNIGHT_GPU_FAULT", "1")));
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(!out.status.success());
    assert!(
        !stderr.contains(r#""event":"start""#),
        "production daemon emitted start"
    );
    assert!(
        stderr.contains("MIDNIGHT_GPU_FAULT") || stderr.to_lowercase().contains("test switch"),
        "missing test-switch diagnostic: {stderr}"
    );
}

#[test]
fn excessive_k_refused_before_srs_open() {
    let out = launch(
        &["--srs", "missing-srs"],
        Some(("MIDNIGHT_GPU_PROVER_MAX_K", "1")),
    );
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(!out.status.success());
    assert!(
        !stderr.contains("missing-srs"),
        "SRS accessed before size refusal: {stderr}"
    );
    assert!(
        stderr.to_lowercase().contains('k'),
        "missing size diagnostic: {stderr}"
    );
}

#[test]
fn start_record_contains_executable_sha256() {
    let out = launch(&["--insecure-test-srs"], None);
    let stderr = String::from_utf8(out.stderr).unwrap();
    let start = stderr
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .find(|event| event["event"] == "start")
        .expect("daemon start record");
    let hash = sha256_hex(&fs::read(Path::new(DAEMON)).unwrap());
    assert!(
        start["data"].as_object().unwrap().values().any(|v| v.as_str() == Some(&hash)),
        "start record lacks the running executable digest"
    );
}

#[test]
fn memory_first_available_after_deadline_cannot_win_wait() {
    let begin = Instant::now();
    let decision = admit(&Ladder {
        need: &DeviceNeed {
            scratch: 1,
            ..Default::default()
        },
        phases: Phases::MSM,
        wait_s: 0.020,
        poll: Duration::from_millis(150),
        free: &|| u64::from(begin.elapsed() >= Duration::from_millis(100)),
        held: &Held::default,
        evict: &|_| {},
    });
    assert_ne!(
        decision.step,
        Step::Wait,
        "admitted late memory after {:.3}s",
        decision.waited_s
    );
}
