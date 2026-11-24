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

//! Between a drain that could not be confirmed and the context teardown,
//! a transfer may still be in flight: the CUDA core hands out no host
//! buffer (a fresh one included), and the pending report shows the drain
//! until a successful teardown settles it. The state is sticky, so each
//! sequence runs in a child process and the parent checks that it exited
//! with status 0. Without a device the child takes its skip path.
#![cfg(feature = "test-fault")]

use midnight_gpu as gpu;

const CHILD: &str = "MGPU_DRAIN_PENDING_CHILD";

fn run_child(test: &str) {
    let exe = std::env::current_exe().expect("test binary path");
    let out = std::process::Command::new(exe)
        .args(["--exact", test, "--nocapture"])
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
}

fn child(test: &str) -> bool {
    if std::env::var_os(CHILD).is_none() {
        run_child(test);
        assert!(!gpu::teardown::device_disabled());
        return false;
    }
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return false;
    }
    true
}

/// A buffer allocated after the failed drain would take the grown count
/// as its snapshot and could later be wiped or freed under the transfer
/// that is still in flight: no buffer is handed out at all.
#[test]
fn no_host_buffer_is_handed_out_after_an_unconfirmed_drain() {
    if !child("no_host_buffer_is_handed_out_after_an_unconfirmed_drain") {
        return;
    }
    // The drain check is off, so the state before the teardown is seen.
    gpu::teardown::set_drain_check_for_test(false);
    let allocs = gpu::xfer::stats().stage[5];
    let got = gpu::fault::gets_after_unconfirmed_drain().expect("no host buffer exists yet");
    assert_ne!(got[0], 0, "a fresh bounce buffer was handed out");
    assert_eq!(got[1], 1, "a fresh read-back buffer was handed out");
    assert_eq!(
        gpu::xfer::stats().stage[5],
        allocs,
        "no bounce buffer was allocated"
    );
    assert!(!gpu::teardown::device_disabled());
}

/// The pending report shows the unconfirmed drain until the teardown.
#[test]
fn unconfirmed_drain_is_pending_until_the_teardown() {
    if !child("unconfirmed_drain_is_pending_until_the_teardown") {
        return;
    }
    assert!(gpu::wipe::pending_erasure().clear());
    gpu::teardown::set_drain_check_for_test(false);
    let _ = gpu::fault::gets_after_unconfirmed_drain().expect("no host buffer exists yet");
    let p = gpu::wipe::pending_erasure();
    assert_eq!(p.undrained, 1, "{p:?}");
    assert!(!p.clear(), "an unconfirmed drain is pending: {p:?}");
    assert!(!gpu::teardown::device_disabled());

    assert!(gpu::teardown::teardown_context(), "the reset succeeded");
    let p = gpu::wipe::pending_erasure();
    assert_eq!(p.undrained, 0, "the teardown settled the drain: {p:?}");
    assert!(p.clear(), "{p:?}");
    assert_eq!(gpu::error_drains().1, 1, "the history count stays");
}

/// With the drain check on (the default), the unconfirmed drain retires
/// the device before the actor replies to the operation.
#[test]
fn unconfirmed_drain_retires_the_device_at_the_lock_release() {
    if !child("unconfirmed_drain_retires_the_device_at_the_lock_release") {
        return;
    }
    let got = gpu::fault::gets_after_unconfirmed_drain().expect("no host buffer exists yet");
    assert_ne!(got[0], 0);
    assert_eq!(got[1], 1);
    assert!(gpu::teardown::device_disabled());
    assert!(gpu::teardown::erasure_failed());
    assert_ne!(gpu::context_active(), Some(true));
    assert_eq!(gpu::wipe::pending_erasure().undrained, 0);
}
