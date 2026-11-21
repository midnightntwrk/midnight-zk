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

//! Seeded proofs of the example relation on the CPU path and, when the build
//! links the device crates and a device is detected, on the device path.
//!
//! ```sh
//! cargo run --release -p midnight-gpu-prover --example seeded_prove \
//!     --features test-seed[,cuda] -- OUT_DIR [INPUT]
//! ```
//!
//! Both runs use seed 7, 8 prover threads, one SRS made from a fixed seed
//! (insecure, test only) and one input: `INPUT` (96 bytes, mode 600) or the
//! built-in example input. Each proof is written to `OUT_DIR/cpu.proof` and
//! `OUT_DIR/gpu.proof`, and one line `PATH SHA256` is printed per proof. Equal
//! hashes mean the device path gives the CPU proof byte for byte.
//!
//! Test builds only (`required-features = ["test-seed"]`): a seeded proof is
//! not zero knowledge.

use std::path::{Path, PathBuf};

use midnight_gpu_prover::{
    Config, ProverService, RequestOptions,
    config::{DeviceSelect, WslSelect},
    device::{self, Device, NoDevice},
    example::{PoseidonPreimage, example_input},
    input::{self, SecretBytes},
    report::sha256_hex,
};
use midnight_proofs::poly::kzg::params::ParamsKZG;
use rand::SeedableRng;

const SEED: u64 = 7;
const THREADS: usize = 8;

fn prove(dev: Box<dyn Device>, input: &SecretBytes, out: &Path) -> Result<(), String> {
    let k = midnight_zk_stdlib::optimal_k(&PoseidonPreimage);
    let params = ParamsKZG::unsafe_setup(k, rand_chacha::ChaCha20Rng::seed_from_u64(0x5eed));
    let cfg = Config {
        threads: THREADS,
        wsl: WslSelect::Off,
        ..Config::default()
    };
    let mut svc = ProverService::with_device(PoseidonPreimage, params, cfg, dev)
        .map_err(|e| e.to_string())?;
    let served = svc
        .prove_seeded(input, RequestOptions::default(), SEED)
        .map_err(|e| e.to_string())?;
    input::write_owner_only(out, &served.proof).map_err(|e| e.to_string())?;
    println!("{} {}", out.display(), sha256_hex(&served.proof));
    eprintln!("{}: label {:?}", out.display(), served.record.label);
    Ok(())
}

fn run() -> Result<(), String> {
    device::warn_test_seed_build();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (out, inp) = match args.as_slice() {
        [o] => (PathBuf::from(o), None),
        [o, i] => (PathBuf::from(o), Some(PathBuf::from(i))),
        _ => return Err("usage: seeded_prove OUT_DIR [INPUT]".into()),
    };
    std::fs::create_dir_all(&out).map_err(|e| format!("{}: {e}", out.display()))?;
    let input = match inp {
        Some(p) => input::read_input(&p).map_err(|e| e.to_string())?,
        None => SecretBytes::new(example_input(1)),
    };
    // the CPU path first: the device layer installs its hooks process-wide
    prove(Box::new(NoDevice), &input, &out.join("cpu.proof"))?;
    let dev = device::detect(DeviceSelect::Auto);
    if dev.info().is_none() {
        eprintln!("no device (or no device support in this build): device path skipped");
        return Ok(());
    }
    prove(dev, &input, &out.join("gpu.proof"))
}

fn main() {
    if let Err(e) = run() {
        eprintln!("seeded_prove: {e}");
        std::process::exit(1);
    }
}
