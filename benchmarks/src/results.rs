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

use midnight_proofs::profiling;
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
    /// Whether the build records the kernel breakdown. Timings of such builds
    /// are not reference numbers.
    pub profiling: bool,
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
    /// The breakdown of the last sample, in builds with profiling.
    pub breakdown: Option<Breakdown>,
}

/// The time of one proof by phase and kernel, in nanoseconds.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Breakdown {
    /// The wall time of the proof.
    pub total_ns: u64,
    /// One entry per phase the prover entered, in order.
    pub phases: Vec<PhaseBreakdown>,
}

/// The time of one phase.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct PhaseBreakdown {
    /// The name of the phase.
    pub phase: String,
    /// The wall time of the phase.
    pub wall_ns: u64,
    /// The wall time during which some kernel was running.
    pub covered_ns: u64,
    /// One entry per kernel.
    pub kernels: Vec<KernelBreakdown>,
}

/// The time of one kernel during one phase.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct KernelBreakdown {
    /// The name of the kernel.
    pub kernel: String,
    /// The wall time during which the kernel was running.
    pub wall_ns: u64,
    /// The sum of the durations of all its calls.
    pub busy_ns: u64,
    /// The number of calls.
    pub calls: u64,
}

impl From<&profiling::Report> for Breakdown {
    fn from(report: &profiling::Report) -> Self {
        let phases = report
            .phases
            .iter()
            .map(|p| PhaseBreakdown {
                phase: p.phase.name().to_owned(),
                wall_ns: p.wall.as_nanos() as u64,
                covered_ns: p.covered.as_nanos() as u64,
                kernels: profiling::Kernel::ALL
                    .iter()
                    .zip(&p.kernels)
                    .map(|(kernel, stats)| KernelBreakdown {
                        kernel: kernel.name().to_owned(),
                        wall_ns: stats.wall.as_nanos() as u64,
                        busy_ns: stats.busy.as_nanos() as u64,
                        calls: stats.calls,
                    })
                    .collect(),
            })
            .collect();
        Breakdown {
            total_ns: report.total.as_nanos() as u64,
            phases,
        }
    }
}
