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

//! One proof for compute-sanitizer. Witness synthesis evaluates a polynomial
//! on the base domain through the forward FFT hook. The quotient handles its
//! coset on the device and returns only the quotient coefficients.

use std::sync::atomic::{AtomicBool, Ordering::Relaxed};

use ff::Field;
use midnight_curves::{Bls12, Fq};
use midnight_gpu as gpu;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    gpu::{GpuHooks, install, test_switches::without_hooks},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Instance, Selector,
        create_proof, keygen_pk, keygen_vk_with_k, prepare,
    },
    poly::{
        EvaluationDomain, FftDomain, Rotation,
        commitment::Guard,
        kzg::{KZGCommitmentScheme, params::ParamsKZG},
    },
    transcript::{Blake2b256, CircuitTranscript, Transcript},
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

const K: u32 = 6;
type Scheme = KZGCommitmentScheme<Bls12>;

struct Square(Value<Fq>);

impl Circuit<Fq> for Square {
    type Config = (Column<Advice>, Column<Instance>, Selector);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self(Value::unknown())
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let a = meta.advice_column();
        let public = meta.instance_column();
        let q = meta.selector();
        meta.enable_equality(a);
        meta.enable_equality(public);
        meta.create_gate("square", |v| {
            let x = v.query_advice(a, Rotation::cur());
            let y = v.query_advice(a, Rotation::next());
            Constraints::with_selector(q, vec![x.clone() * x - y])
        });
        (a, public, q)
    }

    fn synthesize(
        &self,
        (a, public, q): Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        let x = self.0.map(|slope| {
            let domain = EvaluationDomain::new(3, K);
            let mut coeffs = domain.empty_coeff();
            coeffs[0] = Fq::from(3);
            coeffs[1] = slope;
            FftDomain::new(&domain).coeff_to_lagrange(coeffs)[1]
        });
        let square = layouter.assign_region(
            || "evaluate and square",
            |mut region| {
                q.enable(&mut region, 0)?;
                region.assign_advice(|| "evaluation", a, 0, || x)?;
                region.assign_advice(|| "square", a, 1, || x.map(|v| v.square()))
            },
        )?;
        layouter.constrain_instance(square.cell(), public, 0)
    }
}

// Install the accelerator only after setup. Verification uses the stock CPU
// path.
fn prove_square(before_proof: impl FnOnce()) -> usize {
    let mut rng = ChaCha20Rng::seed_from_u64(7);
    let params = ParamsKZG::<Bls12>::unsafe_setup(K, &mut rng);
    let slope = Fq::from(2);
    let circuit = Square(Value::known(slope));
    let shape = circuit.without_witnesses();
    let vk = keygen_vk_with_k::<_, Scheme, _>(&params, &shape, K).unwrap();
    let expected = (Fq::from(3) + slope * vk.get_domain().get_omega()).square();
    let pk = keygen_pk(vk, &shape).unwrap();

    before_proof();
    let instances: &[&[Fq]] = &[&[expected]];
    let mut transcript = CircuitTranscript::<Blake2b256>::init();
    create_proof::<_, Scheme, _, _>(&params, &pk, &circuit, 0, instances, &mut transcript, rng)
        .unwrap();
    let proof = transcript.finalize();
    without_hooks(|| {
        let mut transcript = CircuitTranscript::<Blake2b256>::init_from_bytes(&proof);
        prepare::<_, Scheme, _>(pk.get_vk(), &[], instances, &mut transcript)
            .unwrap()
            .verify(&params.verifier_params())
            .unwrap();
    });

    ((1 << K) - 1) * pk.get_vk().get_domain().get_quotient_poly_degree()
}

// Exercise the same circuit, public evaluation and verifier on stub CI.
#[cfg(not(feature = "cuda"))]
#[test]
fn square_proof_on_cpu() {
    prove_square(|| {});
}

#[test]
#[ignore = "requires a CUDA device under compute-sanitizer"]
fn sanitizer_proof() {
    assert!(gpu::device(), "sanitizer requires a working CUDA device");
    static FORWARD: AtomicBool = AtomicBool::new(false);
    static INVERSE: AtomicBool = AtomicBool::new(false);
    let before = gpu::stats();
    let copies = gpu::xfer::stats();
    let quotient_len = prove_square(|| {
        gpu::set_min_k(1);
        assert!(install(GpuHooks {
            msm_g1: Some(gpu::msm_g1),
            fft: Some(|a, w, k| {
                let ok = gpu::fft(a, w, k);
                FORWARD.fetch_or(ok, Relaxed);
                ok
            }),
            ifft: Some(|a, wi, k, divisor| {
                let ok = gpu::ifft(a, wi, k, divisor);
                INVERSE.fetch_or(ok, Relaxed);
                ok
            }),
            quotient: Some(gpu::quotient),
        }));
        gpu::xfer::record_d2h(true);
    });
    gpu::xfer::record_d2h(false);
    let stats = gpu::stats();
    assert!(FORWARD.load(Relaxed), "forward NTT hook");
    assert!(INVERSE.load(Relaxed), "inverse NTT hook");
    assert!(stats.msm > before.msm, "MSM hook: {stats:?}");
    assert_eq!(
        stats.quotient,
        before.quotient + 1,
        "quotient hook: {:?}",
        gpu::declines()
    );
    assert_eq!(
        stats.device_errors,
        before.device_errors,
        "{:?}",
        gpu::declines()
    );

    let after = gpu::xfer::stats();
    assert!(
        after.msm_d2h_copies > copies.msm_d2h_copies,
        "sppark bucket rows"
    );
    let mut actual = gpu::xfer::take_d2h_log();
    let scalar_bytes = std::mem::size_of::<Fq>();
    let mut expected = vec![(1 << K) * scalar_bytes; (stats.ntt - before.ntt) as usize];
    expected.push(quotient_len * scalar_bytes);
    expected.sort_unstable();
    actual.sort_unstable();
    assert_eq!(actual, expected, "base NTTs and one quotient result");
    assert!(gpu::end_request());
}
