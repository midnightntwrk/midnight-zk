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

//! Helpers of the integration tests: an SRS, services, fake device layers.

#![allow(dead_code)]

use std::{
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering::SeqCst},
    },
    time::Duration,
};

use midnight_curves::Bls12;
use midnight_gpu_prover::{
    Config, ProverService,
    device::{
        Device, DeviceCounters, DeviceInfo, Fallback, Held, MemInfo, Phases, Pk, Shape, WipeReport,
    },
    example::{PoseidonPreimage, example_input},
};
use midnight_proofs::poly::kzg::params::ParamsKZG;
use rand::SeedableRng;

pub const GIB: u64 = 1 << 30;

/// A test SRS for the example relation.
pub fn srs() -> ParamsKZG<Bls12> {
    let k = midnight_zk_stdlib::optimal_k(&PoseidonPreimage);
    ParamsKZG::unsafe_setup(k, rand_chacha::ChaCha8Rng::seed_from_u64(7))
}

pub fn config() -> Config {
    Config {
        threads: 2,
        wsl: midnight_gpu_prover::config::WslSelect::Off,
        ..Config::default()
    }
}

pub fn service(cfg: Config, dev: Box<dyn Device>) -> ProverService<PoseidonPreimage> {
    ProverService::with_device(PoseidonPreimage, srs(), cfg, dev).unwrap()
}

/// Writes an owner-only input file.
pub fn input_file(dir: &Path, name: &str, seed: u64) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, example_input(seed)).unwrap();
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o600)).unwrap();
    p
}

/// What a fake device was asked to do.
#[derive(Default)]
pub struct Log {
    pub begins: Mutex<Vec<Phases>>,
    pub evicts: Mutex<Vec<bool>>,
    pub ends: AtomicU64,
    pub revokes: AtomicU64,
    /// [`Device::activate`] calls.
    pub activations: AtomicU64,
}

/// A fake device: a memory reading, a shape, scripted fallbacks, a delay in
/// `begin_request` and a scripted wipe failure. It runs nothing on a device:
/// the proof is made by the stock CPU code.
#[derive(Clone)]
pub struct Fake {
    pub free: u64,
    pub total: u64,
    pub shape: Option<Shape>,
    pub held: Held,
    pub fallbacks: u64,
    /// Scripted declines `(phase, reason, count)` of the request.
    pub declines: Vec<(&'static str, &'static str, u64)>,
    pub delay: Duration,
    pub wipe_fails: bool,
    /// The free memory is known only after [`Device::activate`].
    pub lazy: bool,
    /// Device peak bytes the counters report.
    pub peak: u64,
    /// No call ran on the device (every hook declined).
    pub no_calls: bool,
    /// Phases `begin_request` takes (all admitted when `None`).
    pub take: Option<Phases>,
    pub log: Arc<Log>,
}

impl Default for Fake {
    fn default() -> Self {
        Fake {
            free: 32 * GIB,
            total: 32 * GIB,
            shape: None,
            held: Held::default(),
            fallbacks: 0,
            declines: Vec::new(),
            delay: Duration::ZERO,
            wipe_fails: false,
            lazy: false,
            peak: 0,
            no_calls: false,
            take: None,
            log: Arc::new(Log::default()),
        }
    }
}

impl Fake {
    /// A shape of a large key (k = 21) for admission tests.
    pub fn big_shape() -> Shape {
        Shape {
            k: 21,
            ext_k: 23,
            proof_cosets: 17,
            resident_polys: 30,
            nslots: 90,
            grid_threads: 80 * 1024,
            quotient_bytes: 0,
        }
    }
}

impl Device for Fake {
    fn info(&self) -> Option<DeviceInfo> {
        Some(DeviceInfo {
            name: "fake".into(),
            total_bytes: self.total,
            ..DeviceInfo::default()
        })
    }
    fn mem(&self) -> Option<MemInfo> {
        // a lazy device reads its free memory only once activated; before,
        // it reports the whole device (the reading the admission must not
        // trust)
        let active = !self.lazy || self.log.activations.load(SeqCst) > 0;
        Some(MemInfo {
            free: if active { self.free } else { self.total },
            total: self.total,
        })
    }
    fn activate(&self) {
        self.log.activations.fetch_add(1, SeqCst);
    }
    fn held(&self) -> Held {
        self.held
    }
    fn shape(&self, _: &Pk) -> Option<Shape> {
        self.shape
    }
    fn begin_request(&self, phases: Phases) -> Phases {
        self.log.begins.lock().unwrap().push(phases);
        std::thread::sleep(self.delay);
        self.take.unwrap_or(phases)
    }
    fn revoke(&self) -> bool {
        self.log.revokes.fetch_add(1, SeqCst);
        true
    }
    fn evict(&self, tables: bool) -> u64 {
        self.log.evicts.lock().unwrap().push(tables);
        0
    }
    fn end_request(&self, check: bool) -> Result<WipeReport, String> {
        self.log.ends.fetch_add(1, SeqCst);
        if self.wipe_fails {
            return Err("scripted wipe failure".into());
        }
        Ok(WipeReport {
            regions: 3,
            bytes: 3 << 20,
            checked: check,
            ..WipeReport::default()
        })
    }
    fn counters(&self) -> DeviceCounters {
        let mut c = DeviceCounters {
            msm_count: 4,
            msm_seconds: 0.01,
            peak_bytes: self.peak,
            ..DeviceCounters::default()
        };
        if self.no_calls {
            c.msm_count = 0;
        } else {
            c.calls.insert("msm".into(), 4);
        }
        for (p, r, n) in &self.declines {
            c.declines.push(Fallback {
                phase: (*p).into(),
                reason: (*r).into(),
                count: *n,
            });
        }
        if self.fallbacks > 0 {
            c.fallbacks.push(Fallback {
                phase: "fft".into(),
                reason: "scripted".into(),
                count: self.fallbacks,
            });
        }
        c
    }
    fn reset_counters(&self) {}
}
