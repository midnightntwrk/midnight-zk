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

//! Proves N random circuits in one concurrent batch and verifies
//! each proof with the stock verifier (inside
//! `RandomCircuit::prove_with_rng`). Usage: `batch [N] [k]` (defaults 4 and
//! 10). With a device the batch uses the isolated batch hooks; without one
//! every job runs on the CPU. Only counts are printed, never a proof or
//! a value.

use std::process::ExitCode;

use midnight_gpu as gpu;
use midnight_proofs::gpu::{
    GpuHooks,
    batch::{BATCH_THREAD, BatchHooks, prove_batch},
    test_switches::RandomCircuit,
};
use rand_core::{OsRng, RngCore};

static BATCH_HOOKS: GpuHooks = GpuHooks {
    msm_g1: Some(gpu::batch::isolated_msm_g1),
    fft: Some(gpu::batch::batch_fft),
    ifft: Some(gpu::batch::batch_ifft),
    quotient: Some(gpu::batch::batch_quotient),
};

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let n: u64 = args.next().and_then(|a| a.parse().ok()).unwrap_or(4);
    let k: u32 = args.next().and_then(|a| a.parse().ok()).unwrap_or(10);

    run(n, k, gpu::device())
}

fn run(n: u64, k: u32, on_device: bool) -> ExitCode {
    let circuits: Vec<RandomCircuit> =
        (0..n).map(|_| RandomCircuit::new(OsRng.next_u64(), true, k)).collect();
    // The device bytes each quotient needs; the wave budget is the free
    // device memory when a device is in use.
    let weights: Vec<u64> = circuits
        .iter()
        .map(|c| match c.shape() {
            Some(s) => {
                gpu::quotient::need_bytes(s.ext_k, s.proof_polys, s.key_polys, s.nslots) as u64
            }
            None => u64::MAX,
        })
        .collect();
    let budget = if on_device {
        gpu::mem_info().map(|(free, _)| free as u64 / 10 * 9).unwrap_or(u64::MAX)
    } else {
        u64::MAX
    };

    let t = std::time::Instant::now();
    let session =
        match on_device.then(|| gpu::batch::BatchSession::begin(&BATCH_THREAD)).transpose() {
            Ok(session) => session,
            Err(error) => {
                eprintln!("session: {error:?}");
                return ExitCode::FAILURE;
            }
        };
    let result = prove_batch(
        &weights,
        budget,
        n as usize,
        BatchHooks::new(on_device.then_some(&BATCH_HOOKS), &|on| {
            if let Some(session) = &session {
                session.set_worker(on);
            }
        }),
        |i, rng| circuits[i].prove_with_rng(rng),
        || session.as_ref().is_none_or(|session| session.end_wave()),
    );
    let finished = session.is_none_or(gpu::batch::BatchSession::finish);
    let outcome = match result {
        Ok(outcome) => outcome,
        Err(error) => {
            eprintln!("scheduler: {error:?}");
            return ExitCode::FAILURE;
        }
    };
    if !finished || outcome.erasure_failed {
        eprintln!("batch erasure failed");
        return ExitCode::FAILURE;
    }
    let results = outcome.jobs;
    let elapsed = t.elapsed();
    let mut verified = 0usize;
    for r in &results {
        let Ok((proof, ok)) = r else {
            eprintln!("batch job panicked");
            return ExitCode::FAILURE;
        };
        assert!(!proof.is_empty());
        verified += usize::from(*ok);
    }
    let (batch_msms, evictions, _) = gpu::batch::batch_msm_counts();
    println!(
        "batch: {verified}/{} proofs verified in {elapsed:?} (k={k}, device: {}, batch MSMs: {batch_msms}, evictions: {evictions})",
        results.len(),
        if on_device { "yes" } else { "no, CPU" },
    );
    assert_eq!(verified, results.len(), "every proof verifies");
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admission_errors_exit_with_one_line() {
        use std::{
            process::{Command, ExitCode, Stdio},
            time::{Duration, Instant},
        };
        const CASE: &str = "MIDNIGHT_BATCH_EXAMPLE_TEST";
        if let Ok(case) = std::env::var(CASE) {
            let held = gpu::batch::BatchSession::begin(&BATCH_THREAD).unwrap();
            assert!(!gpu::device());
            let outcome = prove_batch(
                &[1],
                1,
                1,
                None,
                |_, _| {
                    let probe = case == "session" || gpu::device();
                    run(1, 6, probe)
                },
                || true,
            )
            .unwrap();
            assert!(held.finish());
            let status = outcome.jobs.into_iter().next().unwrap().unwrap();
            std::process::exit(i32::from(status == ExitCode::FAILURE));
        }
        for case in ["scheduler", "session"] {
            let name = std::thread::current().name().unwrap().to_owned();
            let mut child = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", &name, "--nocapture"])
                .env(CASE, case)
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
            let deadline = Instant::now() + Duration::from_secs(30);
            while child.try_wait().unwrap().is_none() {
                if Instant::now() >= deadline {
                    child.kill().unwrap();
                    panic!("example admission timed out");
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            let output = child.wait_with_output().unwrap();
            assert_eq!(output.status.code(), Some(1));
            assert!(
                output.stderr == format!("{case}: Busy\n").as_bytes(),
                "unexpected admission diagnostic"
            );
        }
    }
}
