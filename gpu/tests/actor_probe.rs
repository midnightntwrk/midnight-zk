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

//! Two device probes whose answers decide scheduling rules (see the
//! design note): (a) a second cooperative launch on another stream
//! while one cooperative grid is resident: error or queue, and do the
//! two run one after the other? (b) the stream-ordered allocator: a
//! block freed with `cudaFreeAsync` on stream A and reallocated with
//! `cudaMallocAsync` on stream B: does B wait for A's kernel?
//!
//! Prints one fixed-format line per probe; paste them into the design
//! note. Asserts only that the probes ran. Without a device (or in a
//! stub build) it prints a skip line and passes, like the other
//! device tests; the reviewer runs it on a real device:
//! `cargo test -p midnight-gpu --features cuda,test-fault --test actor_probe --
//! --nocapture`.
#![cfg(feature = "test-fault")]

#[test]
fn actor_device_probes() {
    if !midnight_gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            midnight_gpu::cuda_built()
        );
        println!("probe_cooperative: skipped=no-device");
        println!("probe_async_alloc: skipped=no-device");
        return;
    }
    let coop =
        midnight_gpu::fault::probe_cooperative().expect("cooperative probe ran on a live device");
    println!(
        "probe_cooperative: second_launch_code={} queued={} sequential={} a_ms={:.3} b_start_offset_ms={:.3} b_ms={:.3} launch_call_us={}",
        coop.second_launch_code,
        coop.queued,
        coop.sequential,
        coop.a_ms,
        coop.b_start_offset_ms,
        coop.b_ms,
        coop.launch_call_us
    );

    let alloc = midnight_gpu::fault::probe_async_alloc()
        .expect("async allocator probe ran on a live device");
    println!(
        "probe_async_alloc: malloc_b_call_us={} first_use_b_wait_us={} kernel_a_remaining_us={} b_waited_for_a={} same_address={}",
        alloc.malloc_b_call_us,
        alloc.first_use_b_wait_us,
        alloc.kernel_a_remaining_us,
        alloc.b_waited_for_a,
        alloc.same_address
    );
}
