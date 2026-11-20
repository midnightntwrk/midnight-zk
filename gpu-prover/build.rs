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

//! Build script: sets the `midnight_gpu_linked` cfg with the `cuda` feature
//! and `midnight_metal_linked` with `metal`, marking builds in which the
//! device crate and the `gpu` feature of `midnight-proofs` are linked (see
//! `src/device.rs`), and `rc1_device` for a benchmark build with a device.

fn main() {
    println!("cargo::rustc-check-cfg=cfg(midnight_gpu_linked)");
    // the `cuda` feature links `midnight-gpu` and the hooks of midnight-proofs
    if std::env::var_os("CARGO_FEATURE_CUDA").is_some() {
        println!("cargo::rustc-cfg=midnight_gpu_linked");
    }
    println!("cargo::rustc-check-cfg=cfg(midnight_metal_linked)");
    if std::env::var_os("CARGO_FEATURE_METAL").is_some() {
        println!("cargo::rustc-cfg=midnight_metal_linked");
    }
    println!("cargo::rustc-check-cfg=cfg(rc1_device)");
    if std::env::var_os("CARGO_FEATURE_RC1_BENCH_CUDA").is_some()
        || std::env::var_os("CARGO_FEATURE_RC1_BENCH_METAL").is_some()
    {
        println!("cargo::rustc-cfg=rc1_device");
    }
    println!("cargo::rerun-if-changed=build.rs");
}
