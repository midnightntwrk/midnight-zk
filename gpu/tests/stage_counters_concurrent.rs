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

//! The staging bounce-buffer size is written on the device-owner thread and
//! read without it by the statistics call (`mgpu_stage_counters`, through
//! `xfer::stats`): it must be atomic in the core. The device test polls
//! the counter from a second thread while staged copies run and accepts
//! only a consistent size (none, the full ring or the reduced ring). A
//! data race is not deterministic, so the device test is weak evidence
//! by construction.

use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, Ordering::Relaxed},
};

use midnight_gpu as gpu;

/// The bounce ring of `cuda/midnight_gpu.cu` (`STAGE_BYTES`, and its
/// reduced size when the full allocation fails).
const STAGE_SIZES: [u64; 3] = [0, 256 << 20, 64 << 20];

#[test]
fn stage_counters_consistent_while_staging() {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    gpu::set_min_k(1);

    let stop = Arc::new(AtomicBool::new(false));
    let bad = Arc::new(AtomicU64::new(0));
    let reads = Arc::new(AtomicU64::new(0));
    let reader = {
        let stop = Arc::clone(&stop);
        let bad = Arc::clone(&bad);
        let reads = Arc::clone(&reads);
        std::thread::spawn(move || {
            while !stop.load(Relaxed) {
                let n = gpu::xfer::stats().stage[7];
                if !STAGE_SIZES.contains(&n) {
                    bad.fetch_add(1, Relaxed);
                }
                reads.fetch_add(1, Relaxed);
            }
        })
    };

    // 2^20 scalars are 32 MiB: at and above the staging threshold, so
    // the uploads and read-backs of these transforms use the ring on a
    // discrete device (an integrated device does not stage; the size
    // then stays 0, also consistent).
    let k = 20;
    let mut a: Vec<gpu::Scalar> =
        (0..1usize << k).map(|i| gpu::field::from_u64(i as u64)).collect();
    let w = gpu::field::std_root(k).expect("a standard root").0;
    for _ in 0..4 {
        assert!(gpu::fft(&mut a, w, k), "fft k={k}");
    }
    gpu::end_request();

    stop.store(true, Relaxed);
    reader.join().expect("the reader thread");
    assert!(reads.load(Relaxed) > 0, "the reader polled");
    assert_eq!(bad.load(Relaxed), 0, "an inconsistent staging size");
    assert_eq!(
        gpu::xfer::stats().stage[7],
        0,
        "the ring is released at the end of the request"
    );
}
