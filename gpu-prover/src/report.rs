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

//! The start record and the per-proof record.
//!
//! Records hold counts, sizes, times and hashes of public data only: never a
//! witness value, a key, a seed, a path or any other field of a request.

use std::{collections::BTreeMap, sync::Once};

use serde::Serialize;

use crate::{
    admission::Step,
    config::{ResidentPolicy, RunMode},
    device::{DeviceInfo, Fallback, Phases, Shape, WipeReport},
    need::DeviceNeed,
};

/// How a proof was produced.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Label {
    /// At least one call ran on the device and none fell back. Expected
    /// declines (below the size threshold, no device) and a degraded
    /// admission alone (step `evict`) leave this label; their reasons are in
    /// the record's `degraded_reasons`.
    Gpu,
    /// At least one call ran on the device and at least one fell back to
    /// the CPU (shape, unreduced, memory, fault, device-error, or the
    /// request was withdrawn from the device).
    GpuDegraded,
    /// The daemon proved with no device phase (no device, none configured,
    /// admission step `cpu`, or no lease).
    Cpu,
    /// The client proved on the CPU in-process because the daemon could not
    /// serve the request.
    CpuFallback,
}

/// The policy part of the start record.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct PolicyRecord {
    /// Resident policy.
    pub resident: ResidentPolicy,
    /// Run mode.
    pub mode: RunMode,
    /// Longest admission wait, seconds.
    pub wait_s: f64,
    /// Need margin, MiB.
    pub margin_mib: u64,
    /// Whether a device lock is configured.
    pub lock: bool,
    /// Whether the WSL2 profile applies.
    pub wsl: bool,
    /// WSL2 reserve, MiB.
    pub wsl_reserve_mib: u64,
    /// Whether every wipe is read back.
    pub zero_check: bool,
}

/// One line written when the service has its keys, before it serves.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct StartRecord {
    /// Name of the relation, as it reports it.
    pub relation: String,
    /// log2 of the row count.
    pub k: u32,
    /// log2 of the extended domain size.
    pub extended_k: u32,
    /// Constraint degree.
    pub degree: usize,
    /// Advice columns.
    pub advice_columns: usize,
    /// Fixed columns.
    pub fixed_columns: usize,
    /// Instance columns.
    pub instance_columns: usize,
    /// Lookup arguments.
    pub lookups: usize,
    /// Trash arguments.
    pub trashcans: usize,
    /// Columns in the permutation argument.
    pub permutation_columns: usize,
    /// Device quotient shape, `None` when the device quotient does not take
    /// this key or there is no device.
    pub shape: Option<Shape>,
    /// Resident proving-key copies of the device quotient.
    pub resident_polys: u32,
    /// Device facts, `None` without a device.
    pub device: Option<DeviceInfo>,
    /// `CUDA_VISIBLE_DEVICES` as the process sees it.
    pub cuda_visible_devices: Option<String>,
    /// Cargo features of this build.
    pub features: Vec<&'static str>,
    /// SHA-256 of the running executable (`/proc/self/exe`), `None` where it
    /// cannot be read.
    pub binary_sha256: Option<String>,
    /// Phases configured for the device.
    pub phases: Phases,
    /// The policy.
    pub policy: PolicyRecord,
    /// The computed device memory need, by term.
    pub need: DeviceNeed,
    /// Need with nothing on the device, bytes.
    pub need_cold: u64,
    /// Need with the resident copies and tables on the device, bytes.
    pub need_warm: u64,
    /// Rayon threads of the prover.
    pub threads: usize,
    /// SHA-256 of the verifying key.
    pub vk_sha256: String,
    /// Key generation seconds.
    pub keygen_s: f64,
}

/// MSM figures of a proof.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize)]
pub struct MsmRecord {
    /// MSMs on the device.
    pub count: u64,
    /// Seconds in device MSMs.
    pub seconds: f64,
}

/// The record of one served proof.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ProofRecord {
    /// Sequence number of the request in this process.
    pub request: u64,
    /// How the proof was produced.
    pub label: Label,
    /// Admission step.
    pub step: Step,
    /// Phases configured for the device.
    pub configured: Phases,
    /// Phases admitted to the device.
    pub admitted: Phases,
    /// Why fewer phases ran on the device than configured.
    pub degraded_reasons: Vec<String>,
    /// Computed need at the admission, bytes.
    pub need: u64,
    /// Free bytes or budget at the admission.
    pub free: u64,
    /// Admission wait, seconds.
    pub admission_wait_s: f64,
    /// Prover seconds.
    pub prove_s: f64,
    /// Seconds per prover phase.
    pub phase_s: BTreeMap<String, f64>,
    /// Verifier seconds.
    pub verify_s: f64,
    /// MSM figures.
    pub msm: MsmRecord,
    /// Device calls by operation.
    pub device_calls: BTreeMap<String, u64>,
    /// Total fallbacks.
    pub fallback_count: u64,
    /// Fallbacks by phase and reason.
    pub fallbacks: Vec<Fallback>,
    /// Peak device bytes of the request.
    pub device_peak_bytes: u64,
    /// Host high-water mark of the process, bytes.
    pub host_hwm_bytes: u64,
    /// Device bytes freed by the resident policy after the proof.
    pub evicted_bytes: u64,
    /// The first request of this process: the device tables and key copies
    /// were uploaded cold (for example after a restart).
    pub cold: bool,
    /// Every declined device call by phase and reason.
    pub declines: Vec<Fallback>,
    /// What the wipe at the end of the request covered.
    pub wipe: WipeReport,
    /// Proof length, bytes.
    pub proof_bytes: usize,
    /// SHA-256 of the proof.
    pub proof_sha256: String,
    /// SHA-256 of the public inputs (field elements, 32-byte little-endian
    /// each, in order).
    pub public_inputs_sha256: String,
}

/// A field of `/proc/self/status` in KiB (`VmHWM`, `VmRSS`), 0 when absent.
pub fn proc_status_kib(field: &str) -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines().find(|l| l.starts_with(field)).and_then(|l| {
                l[field.len()..].trim_start_matches(':').split_whitespace().next()?.parse().ok()
            })
        })
        .unwrap_or(0)
}

/// The host high-water mark of this process, bytes.
pub fn host_hwm_bytes() -> u64 {
    proc_status_kib("VmHWM") << 10
}

/// Resets the host high-water mark to the current resident size (Linux
/// `clear_refs`); a no-op where the kernel refuses it.
pub fn reset_host_hwm() {
    let _ = std::fs::write("/proc/self/clear_refs", "5");
}

/// Lower-case hex SHA-256.
pub fn sha256_hex(b: &[u8]) -> String {
    use sha2::Digest;
    hex::encode(sha2::Sha256::digest(b))
}

/// SHA-256 of the running executable, read in chunks from
/// `/proc/self/exe`. `None` where that path does not exist.
pub fn binary_sha256() -> Option<String> {
    use std::io::Read;

    use sha2::Digest;
    let mut f = std::fs::File::open("/proc/self/exe").ok()?;
    let mut h = sha2::Sha256::new();
    let mut buf = vec![0u8; 1 << 20];
    loop {
        match f.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => h.update(&buf[..n]),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(_) => return None,
        }
    }
    Some(hex::encode(h.finalize()))
}

/// Replaces the panic hook of the process: a panic prints its source
/// location and never its message, because a message may carry witness data
/// (for example from a relation's decoder or circuit code). Installed once;
/// the daemon and the client call it at start.
pub fn withhold_panic_messages() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        std::panic::set_hook(Box::new(|info| {
            let at = info
                .location()
                .map(|l| format!("{}:{}", l.file(), l.line()))
                .unwrap_or_else(|| "an unknown location".into());
            eprintln!("midnight-gpu-prover: panic at {at}: message withheld");
        }));
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn host_memory_is_read() {
        assert!(host_hwm_bytes() > 0);
        reset_host_hwm();
        assert!(host_hwm_bytes() > 0);
    }

    #[test]
    fn labels_serialize_kebab() {
        assert_eq!(
            serde_json::to_string(&Label::CpuFallback).unwrap(),
            "\"cpu-fallback\""
        );
        assert_eq!(
            serde_json::to_string(&Label::GpuDegraded).unwrap(),
            "\"gpu-degraded\""
        );
    }
}
