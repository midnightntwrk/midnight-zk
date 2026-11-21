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

//! Device tests. Compiled only with `--features cuda,test-seed` (the build
//! script then sets the cfg `midnight_gpu_linked`). Each test
//! returns early, with a line on stderr, when no device is detected.
//!
//! The example relation is too small to reach the device (the hooks decline
//! below their size thresholds), so these tests serve a larger relation: a
//! chain of Poseidon hashes with k = 16. Every test asserts device call counts
//! above zero, so a run that silently stays on the CPU fails.

#![cfg(all(feature = "cuda", feature = "test-seed", midnight_gpu_linked))]

use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{AssignmentInstructions, PublicInputInstructions, hash::HashCPU},
};
use midnight_gpu_prover::{
    Config, ProverService, RequestOptions, ServedRelation,
    config::{DeviceSelect, WslSelect},
    device::{self, NoDevice},
    input::SecretBytes,
    report::Label,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::params::ParamsKZG,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::SeedableRng;

type F = midnight_curves::Fq;

const K: u32 = 16;
const ROUNDS: usize = 600;

/// `ROUNDS` chained Poseidon hashes of three inputs; the last is public.
#[derive(Clone, Copy, Debug, Default)]
struct PoseidonChain;

fn chain(w: &[F; 3]) -> F {
    let mut h = <PoseidonChip<F> as HashCPU<F, F>>::hash(w);
    for _ in 1..ROUNDS {
        h = <PoseidonChip<F> as HashCPU<F, F>>::hash(&[h, w[1], w[2]]);
    }
    h
}

impl Relation for PoseidonChain {
    type Instance = F;
    type Witness = [F; 3];
    type Error = Error;

    fn format_instance(i: &F) -> Result<Vec<F>, Error> {
        Ok(vec![*i])
    }

    fn circuit(
        &self,
        std: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _: Value<F>,
        witness: Value<[F; 3]>,
    ) -> Result<(), Error> {
        let w = std.assign_many(layouter, &witness.transpose_array())?;
        let mut h = std.poseidon(layouter, &w)?;
        for _ in 1..ROUNDS {
            h = std.poseidon(layouter, &[h, w[1].clone(), w[2].clone()])?;
        }
        std.constrain_as_public_input(layouter, &h)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonChain)
    }
}

impl ServedRelation for PoseidonChain {
    fn name(&self) -> String {
        "poseidon-chain".into()
    }
    fn decode_input(&self, input: &[u8]) -> Result<(F, [F; 3]), String> {
        let (_, w) = midnight_gpu_prover::example::PoseidonPreimage.decode_input(input)?;
        Ok((chain(&w), w))
    }
    fn k(&self) -> Option<u32> {
        Some(K)
    }
}

fn cfg() -> Config {
    Config {
        threads: 8,
        wsl: WslSelect::Off,
        ..Config::default()
    }
}

fn srs() -> ParamsKZG<midnight_curves::Bls12> {
    ParamsKZG::unsafe_setup(K, rand_chacha::ChaCha8Rng::seed_from_u64(11))
}

/// The hooks, their counters, the fault injector and the blinding seed are
/// process-wide: the tests of this file run one at a time.
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The longest a device test may run. A hung device call would otherwise
/// hold the device (and any device lock of the runner) until killed.
const TEST_LIMIT: std::time::Duration = std::time::Duration::from_secs(120);

/// One test's hold on the device: serialises the tests and aborts the
/// process when the test runs past [`TEST_LIMIT`].
struct Serial {
    _g: std::sync::MutexGuard<'static, ()>,
    done: std::sync::Arc<std::sync::atomic::AtomicBool>,
}

impl Drop for Serial {
    fn drop(&mut self) {
        self.done.store(true, std::sync::atomic::Ordering::Release);
    }
}

fn serial() -> Serial {
    let g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let done = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let d = done.clone();
    let name = std::thread::current().name().unwrap_or("?").to_string();
    std::thread::spawn(move || {
        let t = std::time::Instant::now();
        while t.elapsed() < TEST_LIMIT {
            if d.load(std::sync::atomic::Ordering::Acquire) {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        eprintln!("{name}: no result after {TEST_LIMIT:?}; aborting the test process");
        std::process::abort();
    });
    Serial { _g: g, done }
}

fn gpu_service() -> Option<ProverService<PoseidonChain>> {
    let d = device::detect(DeviceSelect::Auto);
    if d.info().is_none() {
        assert_ne!(
            std::env::var("MIDNIGHT_GPU_REQUIRE_CUDA").as_deref(),
            Ok("1"),
            "daemon conformance requires a usable GPU backend"
        );
        eprintln!("no device detected: skipped");
        return None;
    }
    Some(ProverService::with_device(PoseidonChain, srs(), cfg(), d).unwrap())
}

fn input() -> SecretBytes {
    SecretBytes::new(midnight_gpu_prover::example::example_input(4))
}

#[test]
fn seeded_gpu_proof_equals_cpu_proof() {
    let _g = serial();
    let Some(mut gpu) = gpu_service() else { return };
    let mut cpu =
        ProverService::with_device(PoseidonChain, srs(), cfg(), Box::new(NoDevice)).unwrap();
    // the reference runs with the hooks suspended: the stock CPU code only
    let (c1, c2) = midnight_proofs::gpu::test_switches::without_hooks(|| {
        (
            cpu.prove_seeded(&input(), RequestOptions::default(), 7).unwrap(),
            cpu.prove_seeded(&input(), RequestOptions::default(), 7).unwrap(),
        )
    });
    assert_eq!(c1.record.label, Label::Cpu);
    assert_eq!(
        c1.proof, c2.proof,
        "the seeded CPU path is not deterministic"
    );
    let g = gpu.prove_seeded(&input(), RequestOptions::default(), 7).unwrap();
    assert_eq!(
        g.record.label,
        Label::Gpu,
        "{:?}",
        g.record.degraded_reasons
    );
    assert!(g.record.msm.count > 0 && !g.record.device_calls.is_empty());
    assert_eq!(g.record.fallback_count, 0);
    assert_eq!(g.proof, c1.proof);
}

#[test]
fn zero_check_reads_every_wiped_region_back_as_zero() {
    let _g = serial();
    let Some(mut gpu) = gpu_service() else { return };
    let r = gpu
        .prove(
            &input(),
            RequestOptions {
                zero_check: true,
                ..RequestOptions::default()
            },
        )
        .unwrap()
        .record;
    assert!(r.wipe.checked);
    assert!(r.wipe.regions > 0 && r.wipe.bytes > 0);
    assert!(gpu.retired().is_none());
    // with the default resident policy no proving-key copy stays on the
    // device
    assert_eq!(gpu.held(), device::Held::default());
}

#[test]
fn injected_device_faults_give_a_valid_proof_and_a_counted_fallback() {
    let _g = serial();
    let Some(mut gpu) = gpu_service() else { return };
    use midnight_gpu::fault::{self, Class, Point};
    fault::reset();
    fault::arm(Class::Msm, Point::Launch, 3);
    let r = gpu.prove(&input(), RequestOptions::default()).unwrap().record;
    let fired = fault::fired(Class::Msm);
    fault::reset();
    assert_eq!(fired, 3);
    // the proof passed the stock verifier inside `prove`
    assert!(r.fallback_count >= 1);
    assert_eq!(r.label, Label::GpuDegraded);
    assert!(!r.fallbacks.is_empty());
}

/// r13 BLOCKING 2 and 3: the quotient count and the device peak of a reply
/// are the request's own. After a device proof, a request whose device
/// phases are withdrawn before it starts (all on the CPU) reports no device
/// quotient and no device peak.
#[test]
fn counts_and_peak_are_request_local() {
    let _g = serial();
    let Some(mut gpu) = gpu_service() else { return };
    let first = gpu.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(
        first.device_calls.get("quotient").copied().unwrap_or(0) > 0,
        "{first:?}"
    );
    assert!(first.device_peak_bytes > 0);
    let cpu = gpu
        .prove(
            &input(),
            RequestOptions {
                cancel: Some(std::sync::Arc::new(|| true)),
                ..RequestOptions::default()
            },
        )
        .unwrap()
        .record;
    assert_eq!(
        cpu.device_calls.get("quotient").copied().unwrap_or(0),
        0,
        "{cpu:?}"
    );
    assert_eq!(cpu.msm.count, 0, "{cpu:?}");
    // GPU-085: no call of this request ran on the device
    assert_eq!(cpu.label, Label::Cpu, "{cpu:?}");
}

/// r14: a request that the admission keeps off the device reports no device
/// peak, also after a device proof in the same process (the device layer
/// resets its peak only when a request starts on the device).
#[test]
fn a_cpu_admitted_request_reports_no_device_peak() {
    let _g = serial();
    let Some(mut gpu) = gpu_service() else { return };
    let first = gpu.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(first.device_peak_bytes > 0, "{first:?}");
    // a reserve larger than any device: the admission selects no phase
    let cfg = Config {
        margin_mib: 1 << 30,
        wait_s: 0.0,
        ..cfg()
    };
    let d = device::detect(DeviceSelect::Auto);
    let mut cpu_only = ProverService::with_device(PoseidonChain, srs(), cfg, d).unwrap();
    let cpu = cpu_only.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(cpu.admitted.is_empty(), "{cpu:?}");
    assert_eq!(cpu.device_peak_bytes, 0, "{cpu:?}");
    assert_eq!(cpu.label, Label::Cpu, "{cpu:?}");
}

/// r16: a request that the admission keeps off the device reports no wipe
/// counters of an earlier device request in the same process (the counters
/// reset for every request, not only when a request starts on the device).
#[test]
fn a_cpu_admitted_request_reports_no_wipe_of_an_earlier_request() {
    let _g = serial();
    let Some(mut gpu) = gpu_service() else { return };
    let first = gpu.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(first.wipe.regions > 0 && first.wipe.bytes > 0, "{first:?}");
    // a reserve larger than any device: the admission selects no phase
    let cfg = Config {
        margin_mib: 1 << 30,
        wait_s: 0.0,
        ..cfg()
    };
    let d = device::detect(DeviceSelect::Auto);
    let mut cpu_only = ProverService::with_device(PoseidonChain, srs(), cfg, d).unwrap();
    let cpu = cpu_only.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(cpu.admitted.is_empty(), "{cpu:?}");
    assert_eq!(
        (cpu.wipe.regions, cpu.wipe.bytes, cpu.wipe.nonzero_regions),
        (0, 0, 0),
        "{:?}",
        cpu.wipe
    );
}
