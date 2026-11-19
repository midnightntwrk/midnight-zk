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

//! Build script: sets the `midnight_gpu_linked` cfg with the `cuda` feature.
//! The cfg marks a build in which the CUDA crate `midnight-gpu` and the `gpu`
//! feature of `midnight-proofs` are linked (see `src/device.rs`).

fn main() {
    println!("cargo::rustc-check-cfg=cfg(midnight_gpu_linked)");
    // the `cuda` feature links `midnight-gpu` and the hooks of midnight-proofs
    if std::env::var_os("CARGO_FEATURE_CUDA").is_some() {
        println!("cargo::rustc-cfg=midnight_gpu_linked");
    }
    println!("cargo::rerun-if-changed=build.rs");
}
