// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Records the compiler version and the midnight-proofs source in the binary, so
//! that every result row names the build that made it.

use std::process::Command;

fn main() {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let version = Command::new(rustc)
        .arg("-V")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".into());
    println!("cargo:rustc-env=BENCH_RUSTC={version}");
    let source = std::env::var("BENCH_PROOFS_SOURCE")
        .unwrap_or_else(|_| "crates.io:midnight-proofs-0.8.3".into());
    println!("cargo:rustc-env=BENCH_PROOFS_SOURCE={source}");
    println!("cargo:rerun-if-env-changed=BENCH_PROOFS_SOURCE");
    println!("cargo:rerun-if-changed=build.rs");
}
