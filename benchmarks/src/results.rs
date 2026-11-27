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

//! The records the runner produces, which are also the JSON schema of the
//! result files.

use serde::{Deserialize, Serialize};

use crate::workload::Pcs;

/// The version of the result file format.
pub const SCHEMA_VERSION: u32 = 1;

/// The outcome of one invocation of the runner.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct RunResult {
    /// [`SCHEMA_VERSION`] at the time of writing.
    pub schema_version: u32,
    /// Where and how the run took place.
    pub environment: Environment,
    /// One entry per workload, scheme and thread count.
    pub cases: Vec<CaseResult>,
}

/// The conditions of a run.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Environment {
    /// The git commit of the build, with a `-dirty` suffix if the tree had
    /// uncommitted changes, or `None` if unknown.
    pub commit: Option<String>,
    /// The CPU model, or `None` if unknown.
    pub cpu: Option<String>,
    /// The number of logical cores.
    pub logical_cores: usize,
    /// The operating system and architecture.
    pub os: String,
}

/// The measurements of one workload under one scheme and thread count.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CaseResult {
    /// The name of the workload.
    pub workload: String,
    /// The polynomial commitment scheme.
    pub pcs: Pcs,
    /// The number of threads of the rayon pool.
    pub threads: usize,
    /// The logarithm of the number of rows.
    pub k: u32,
    /// The hexadecimal SHA-256 digest of the verifying key.
    pub vk_hash: String,
    /// The size of the proof in bytes.
    pub proof_bytes: usize,
    /// The wall time of each proof in nanoseconds, in execution order.
    pub samples_ns: Vec<u64>,
    /// The wall time of each verification of the last proof in nanoseconds.
    /// It is empty if verification was skipped.
    pub verify_ns: Vec<u64>,
}
