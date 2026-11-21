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

//! The job list: one line of JSON per proof, written by `scripts/make-jobs.py`.

use std::{io::BufRead, path::PathBuf};

use midnight_serialize::{Deserializable, tagged_deserialize};
use midnight_transient_crypto::{curve::Fr, proofs::ProofPreimage};
use serde::Deserialize;

/// One proof: a proof preimage and the key material of its circuit.
#[derive(Debug, Clone, Deserialize)]
pub struct Job {
    /// Unique name, `<program>/<call label>.<proof index>`.
    pub job: String,
    /// Program that made the call.
    pub program: String,
    /// Circuit that the proof is for.
    pub circuit: String,
    /// Program whose keys prove the circuit (differs from `program` for a
    /// cross-contract callee).
    pub key_program: String,
    /// Tagged `ProofPreimage` (`midnight:proof-preimage`).
    pub preimage: PathBuf,
    /// Tagged prover key (`<circuit>.prover`).
    pub prover_key: PathBuf,
    /// Tagged verifier key (`<circuit>.verifier`).
    pub verifier_key: PathBuf,
    /// Tagged ZKIR (`<circuit>.bzkir`).
    pub ir: PathBuf,
    /// Communication commitment, hex of the serialized field element.
    pub comm: Option<String>,
    /// Commitment randomness, hex of the serialized field element.
    pub comm_rand: Option<String>,
}

/// Reads a JSON Lines job file. Empty lines and lines that start with `#` are
/// skipped.
pub fn read_jobs(path: &str) -> Vec<Job> {
    let f = std::fs::File::open(path).unwrap_or_else(|e| panic!("open {path}: {e}"));
    std::io::BufReader::new(f)
        .lines()
        .map(|l| l.expect("read job line"))
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| serde_json::from_str(&l).unwrap_or_else(|e| panic!("bad job line {l}: {e}")))
        .collect()
}

/// Decodes a field element from the hex of its serialized form.
pub fn fr_from_hex(s: &str) -> Fr {
    let b = hex::decode(s).expect("hex field element");
    Deserializable::deserialize(&mut &b[..], 0).expect("serialized field element")
}

impl Job {
    /// Loads the preimage and puts in the communication commitment of the call,
    /// as the transaction builder does before it sends the preimage to the
    /// proof server.
    pub fn load_preimage(&self) -> ProofPreimage {
        let bytes = std::fs::read(&self.preimage)
            .unwrap_or_else(|e| panic!("read {}: {e}", self.preimage.display()));
        let mut pre: ProofPreimage =
            tagged_deserialize(&mut &bytes[..]).expect("decode proof preimage");
        if let (Some(c), Some(r)) = (&self.comm, &self.comm_rand) {
            pre.communications_commitment = Some((fr_from_hex(c), fr_from_hex(r)));
        }
        pre
    }
}
