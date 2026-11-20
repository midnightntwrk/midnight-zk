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

//! Facts about the machine for the result rows: CPU and GPU model, load, and
//! the CPU time that other processes use while a proof runs. Linux only; on
//! other systems the values read as unknown.

use std::{process::Command, time::Duration};

use sha2::{Digest, Sha256};

/// CPU model name from `/proc/cpuinfo`, or `BENCH_CPU_MODEL` when set.
pub fn cpu_model() -> String {
    if let Ok(m) = std::env::var("BENCH_CPU_MODEL") {
        return m;
    }
    let info = std::fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
    info.lines()
        .find(|l| l.starts_with("model name"))
        .and_then(|l| l.split_once(':'))
        .map(|(_, v)| v.trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

/// GPU model of the first device from `nvidia-smi`, or `BENCH_GPU_MODEL` when
/// set, or `none`.
pub fn gpu_model() -> String {
    if let Ok(m) = std::env::var("BENCH_GPU_MODEL") {
        return m;
    }
    Command::new("nvidia-smi")
        .args(["--query-gpu=name", "--format=csv,noheader"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.lines().next().map(|l| l.trim().to_string()))
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "none".into())
}

/// One-minute load average.
pub fn load1() -> f64 {
    std::fs::read_to_string("/proc/loadavg")
        .ok()
        .and_then(|s| s.split_whitespace().next().and_then(|v| v.parse().ok()))
        .unwrap_or(f64::NAN)
}

/// Waits until the one-minute load is below `max`. Returns the load it saw.
pub fn wait_quiet(max: f64, poll: Duration) -> f64 {
    loop {
        let l = load1();
        if l < max || l.is_nan() {
            return l;
        }
        eprintln!("load {l:.2} >= {max:.2}: waiting");
        std::thread::sleep(poll);
    }
}

/// Busy CPU ticks of the whole machine: user, nice, system, irq, softirq and
/// steal of the `cpu` line of `/proc/stat` (guest time is already in user).
fn machine_busy_ticks() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/stat").ok()?;
    let line = s.lines().next()?;
    let v: Vec<u64> = line.split_whitespace().skip(1).filter_map(|x| x.parse().ok()).collect();
    if v.len() < 8 {
        return None;
    }
    Some(v[..8].iter().sum::<u64>() - v[3] - v[4])
}

/// CPU ticks (user + system) of this process, all threads.
fn own_ticks() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/self/stat").ok()?;
    // Fields after the command name, which is in parentheses.
    let rest = &s[s.rfind(')')? + 2..];
    let f: Vec<&str> = rest.split_whitespace().collect();
    Some(f.get(11)?.parse::<u64>().ok()? + f.get(12)?.parse::<u64>().ok()?)
}

/// Samples machine and own CPU ticks; the difference over an interval is the
/// CPU time that other processes used.
#[derive(Clone, Copy)]
pub struct CpuSample(Option<(u64, u64)>);

impl CpuSample {
    /// Takes a sample now.
    pub fn now() -> Self {
        Self(machine_busy_ticks().zip(own_ticks()))
    }

    /// CPU cores that other processes kept busy on average since `self`, over
    /// `wall` seconds. Ticks are taken as 100 per second (`USER_HZ`).
    pub fn foreign_cores(&self, later: &CpuSample, wall: f64) -> f64 {
        match (self.0, later.0) {
            (Some((m0, o0)), Some((m1, o1))) if wall > 0.0 => {
                let foreign = (m1 - m0).saturating_sub(o1 - o0) as f64 / 100.0;
                foreign / wall
            }
            _ => f64::NAN,
        }
    }
}

/// sha256 of the running binary.
pub fn binary_sha256() -> String {
    std::env::current_exe()
        .and_then(std::fs::read)
        .map(|b| hex::encode(Sha256::digest(&b)))
        .unwrap_or_else(|_| "unknown".into())
}

/// Driver version of the first GPU from `nvidia-smi`, or `BENCH_GPU_DRIVER`, or
/// `none`.
pub fn gpu_driver() -> String {
    if let Ok(m) = std::env::var("BENCH_GPU_DRIVER") {
        return m;
    }
    Command::new("nvidia-smi")
        .args(["--query-gpu=driver_version", "--format=csv,noheader"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.lines().next().map(|l| l.trim().to_string()))
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "none".into())
}

/// Resets the peak resident set size of this process (Linux `clear_refs` 5).
pub fn reset_hwm() {
    let _ = std::fs::write("/proc/self/clear_refs", "5");
}

/// Peak resident set size of this process in bytes (`VmHWM`) since the last
/// [`reset_hwm`], or 0 when unknown.
pub fn hwm_bytes() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse::<u64>().ok()))
        })
        .map_or(0, |kb| kb * 1024)
}
