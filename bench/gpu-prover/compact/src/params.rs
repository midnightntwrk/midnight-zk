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

//! KZG parameters `bls_midnight_2p{k}`, read once from a directory and kept in
//! memory, so that no timed proof reads them from disk.

use std::{collections::HashMap, io, path::PathBuf, sync::Mutex};

use midnight_transient_crypto::proofs::{ParamsProver, ParamsProverProvider, ParamsVerifier};

/// A parameter provider that caches every `k` it has read.
pub struct ParamsCache {
    dir: PathBuf,
    cache: Mutex<HashMap<u8, ParamsProver>>,
    verifier: Mutex<HashMap<u8, ParamsVerifier>>,
}

impl ParamsCache {
    /// A cache over `dir`, which holds the files `bls_midnight_2p{k}`.
    pub fn new(dir: PathBuf) -> Self {
        Self {
            dir,
            cache: Mutex::new(HashMap::new()),
            verifier: Mutex::new(HashMap::new()),
        }
    }

    fn path(&self, k: u8) -> PathBuf {
        self.dir.join(format!("bls_midnight_2p{k}"))
    }

    /// Returns the prover parameters for `k`, and reads them on first use.
    pub fn prover(&self, k: u8) -> io::Result<ParamsProver> {
        let mut c = self.cache.lock().expect("params lock");
        if let Some(p) = c.get(&k) {
            return Ok(p.clone());
        }
        let f = std::fs::File::open(self.path(k))?;
        let p = ParamsProver::read(io::BufReader::new(f))?;
        c.insert(k, p.clone());
        Ok(p)
    }

    /// Returns the verifier parameters derived from the `k` file, as the proof
    /// server derives them for its self-check.
    pub fn verifier(&self, k: u8) -> io::Result<ParamsVerifier> {
        let mut c = self.verifier.lock().expect("params lock");
        if let Some(p) = c.get(&k) {
            return Ok(p.clone());
        }
        let f = std::fs::File::open(self.path(k))?;
        let p = ParamsVerifier::read(io::BufReader::new(f))?;
        c.insert(k, p.clone());
        Ok(p)
    }
}

impl ParamsProverProvider for ParamsCache {
    async fn get_params(&self, k: u8) -> io::Result<ParamsProver> {
        self.prover(k)
    }
}
