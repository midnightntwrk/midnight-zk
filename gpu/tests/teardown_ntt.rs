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

//! The NTT twiddle tables can be freed explicitly and are built again by
//! the next transform. The device sequence runs in a child process (only
//! this test, so “before any NTT” holds there) and the parent checks that
//! the child exited with status 0: no static object of the vendored
//! library runs a CUDA call from a destructor inside `exit()`. With no
//! device the child checks the teardown call only.

use ff::{Field, PrimeField};
use midnight_curves::{Fq, fft::best_fft};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;

const CHILD: &str = "MGPU_TEARDOWN_NTT_CHILD";

fn root(k: u32) -> Fq {
    let mut w = Fq::ROOT_OF_UNITY;
    for _ in k..Fq::S {
        w = w.square();
    }
    w
}

#[test]
fn ntt_process_exits_cleanly() {
    if std::env::var_os(CHILD).is_some() {
        // Before any NTT in this process: nothing was built.
        assert!(gpu::teardown::teardown_ntt_tables());
        if !gpu::device() {
            eprintln!(
                "skipped: no device (CUDA core built: {})",
                gpu::cuda_built()
            );
            return;
        }
        gpu::set_min_k(1);
        let k = 6;
        let n = 1usize << k;
        let a: Vec<Fq> = (0..n as u64).map(|i| Fq::from(i * i + 1)).collect();
        let mut cpu = a.clone();
        best_fft(&mut cpu, root(k), k);

        let mut first = a.clone();
        assert!(gpu::fft(
            adapter::scalars_mut(&mut first),
            adapter::scalar(root(k)),
            k
        ));
        assert_eq!(first, cpu);

        assert!(gpu::teardown::teardown_ntt_tables());
        // A second teardown has nothing left to free.
        assert!(gpu::teardown::teardown_ntt_tables());

        // The next transform builds the tables again.
        let mut second = a;
        assert!(gpu::fft(
            adapter::scalars_mut(&mut second),
            adapter::scalar(root(k)),
            k
        ));
        assert_eq!(second, cpu);
        assert_eq!(second, first);
        assert!(gpu::teardown::teardown_ntt_tables());
        return;
    }
    let exe = std::env::current_exe().expect("test binary path");
    let out = std::process::Command::new(exe)
        .args(["--exact", "ntt_process_exits_cleanly", "--nocapture"])
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

#[test]
fn teardown_ntt_tables_stub() {
    if gpu::cuda_built() {
        return;
    }
    assert!(gpu::teardown::teardown_ntt_tables());
}
