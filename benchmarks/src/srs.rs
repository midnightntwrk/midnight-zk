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

//! Loading of the structured reference string.

use std::{env, fs::File, io::BufReader, path::PathBuf};

use midnight_curves::Bls12;
use midnight_proofs::{poly::kzg::params::ParamsKZG, utils::SerdeFormat};
use midnight_zk_stdlib::MidnightPCS;

/// The largest Filecoin SRS available, as a power of two.
pub const MAX_SRS_K: u32 = 19;

/// The directory holding the SRS files: `$SRS_DIR` if set, otherwise the
/// assets of the `zk_stdlib` examples.
pub fn srs_dir() -> PathBuf {
    match env::var_os("SRS_DIR") {
        Some(dir) => dir.into(),
        None => concat!(env!("CARGO_MANIFEST_DIR"), "/../zk_stdlib/examples/assets").into(),
    }
}

/// Whether circuits of size `2^k` fit in the available SRS under `PCS`.
pub fn fits<PCS: MidnightPCS>(k: u32) -> bool {
    PCS::srs_k(k) <= MAX_SRS_K
}

/// Loads Filecoin's SRS for circuits of size `2^k` under `PCS`.
///
/// Reads `bls_filecoin_2p<j>` for `j = PCS::srs_k(k)` if present, and
/// otherwise truncates `bls_filecoin_2p19`. It never writes to the directory,
/// so concurrent runs cannot observe a partial file.
pub fn load<PCS: MidnightPCS>(k: u32) -> ParamsKZG<Bls12> {
    let j = PCS::srs_k(k);
    assert!(j <= MAX_SRS_K, "no SRS of size 2^{j} is available");
    let dir = srs_dir();
    let exact = dir.join(format!("bls_filecoin_2p{j}"));
    let path = if exact.exists() {
        exact
    } else {
        dir.join(format!("bls_filecoin_2p{MAX_SRS_K}"))
    };
    let file = File::open(&path).unwrap_or_else(|e| {
        panic!(
            "cannot open the SRS at {}: {e}; see benchmarks/README.md",
            path.display()
        )
    });
    PCS::load_params(&mut BufReader::new(file), SerdeFormat::RawBytesUnchecked, k)
        .expect("failed to read the SRS")
}
