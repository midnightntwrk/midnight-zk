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

use midnight_gpu as gpu;
use midnight_proofs::gpu::{self as hooks, GpuHooks, batch::BatchHooks};

static BATCH_HOOKS: GpuHooks = GpuHooks {
    msm_g1: Some(gpu::batch::isolated_msm_g1),
    fft: None,
    ifft: None,
    quotient: None,
};

#[test]
fn saved_installed_hook_declines_during_session() {
    let (done, result) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let caller = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
        caller.install(|| exercise_session(&caller));
        done.send(()).unwrap();
    });
    result
        .recv_timeout(std::time::Duration::from_secs(30))
        .expect("session test timed out");
}

fn exercise_session(caller: &rayon::ThreadPool) {
    assert!(hooks::install(GpuHooks {
        msm_g1: Some(gpu::msm_g1),
        ..Default::default()
    }));
    let saved = hooks::hooks().unwrap().msm_g1.unwrap();
    let declines = || {
        gpu::declines()
            .into_iter()
            .find(|(class, reason, _)| *class == "msm" && *reason == "batch")
            .map_or(0, |(_, _, count)| count)
    };
    let session = gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD)
        .expect("device session admission");
    let before = declines();
    let saved_batch = BATCH_HOOKS.msm_g1.unwrap();
    use std::sync::atomic::{AtomicBool, Ordering};
    let worker_admitted = AtomicBool::new(false);
    let outcome = hooks::batch::prove_batch(
        &[1, 2],
        1,
        1,
        BatchHooks::new(Some(&BATCH_HOOKS), &|on| {
            let enabled = on.as_ref().ok().copied();
            session.set_worker(on);
            if let Some(enabled) = enabled {
                worker_admitted.store(enabled, Ordering::Release);
            }
        }),
        |job, _| {
            if job == 1 {
                assert!(!worker_admitted.load(Ordering::Acquire));
                return hooks::hooks().is_none() && saved_batch(&[], &[]).is_none();
            }
            assert!(hooks::hooks().is_some());
            assert!(matches!(
                gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD),
                Err(gpu::batch::SessionError::Busy)
            ));
            assert!(saved_batch(&[], &[]).is_none());
            let (send, receive) = std::sync::mpsc::channel();
            caller.spawn(move || {
                send.send(matches!(
                    gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD),
                    Err(gpu::batch::SessionError::Busy)
                ))
                .unwrap();
            });
            assert!(receive.recv_timeout(std::time::Duration::from_secs(10)).unwrap());
            let (done, finished) = std::sync::mpsc::channel();
            std::thread::spawn(move || {
                done.send(
                    hooks::hooks().is_none()
                        && saved(&[], &[]).is_none()
                        && saved_batch(&[], &[]).is_none(),
                )
                .unwrap();
            });
            finished.recv_timeout(std::time::Duration::from_secs(10)).unwrap()
        },
        || {
            assert!(!worker_admitted.load(Ordering::Acquire));
            session.end_wave()
        },
    )
    .unwrap();
    assert!(matches!(outcome.jobs[..], [Ok(true), Ok(true)]));
    assert!(!outcome.erasure_failed);
    assert_eq!(declines(), before + 3);
    assert!(session.finish());
}
