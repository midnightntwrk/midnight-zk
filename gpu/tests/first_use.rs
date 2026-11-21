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

//! Concurrent first use: every caller that asks for the device while
//! the first request is still making the CUDA context gets the outcome
//! of that initialization, not a "no device" answer. This binary holds
//! one test, so the callers below are the first users in the process.

use std::{
    sync::{Arc, Barrier},
    thread,
    time::Duration,
};

use midnight_gpu as gpu;

#[test]
fn concurrent_first_callers_agree_on_the_device() {
    if gpu::present().is_none() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    const CALLERS: usize = 8;
    let start = Arc::new(Barrier::new(CALLERS));
    let callers: Vec<_> = (0..CALLERS)
        .map(|i| {
            let start = start.clone();
            thread::spawn(move || {
                start.wait();
                // Spread the callers over the time the first one needs
                // to make the context.
                thread::sleep(Duration::from_millis(5 * i as u64));
                gpu::device()
            })
        })
        .collect();
    let answers: Vec<bool> = callers.into_iter().map(|c| c.join().unwrap()).collect();
    assert!(
        answers.iter().all(|&a| a),
        "a caller during the first initialization was told there is no device: {answers:?}"
    );
}
