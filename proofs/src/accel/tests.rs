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

//! The quotient job against the stock prover on random constraint systems,
//! and the hooks end to end with the CPU reference accelerator.

use std::{marker::PhantomData, sync::Arc, thread::ThreadId};

use ff::Field;
use group::{Curve, Group};
use midnight_curves::{Bls12, Fq, G1Affine, G1Projective};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

use super::{
    quotient::{DeviceProgram, job},
    reference::CpuReference,
    test_circuit::{RandCircuit, Scheme, prove_and_verify, set_shape, setup},
    *,
};
use crate::{
    plonk::{
        evaluation::{Evaluator, FlatGraphEvaluator},
        keygen_vk_with_k,
    },
    poly::{EvaluationDomain, FftDomain, LagrangeCoeff, Polynomial, kzg::params::ParamsKZG},
    transcript::{CircuitTranscript, Transcript},
};

/// Every lowered program of a random constraint system gives the outputs of
/// its flat evaluator, at every row.
#[test]
fn lowered_programs_match_flat_evaluator() {
    for seed in 0..24u64 {
        set_shape(seed, false);
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let params = ParamsKZG::<Bls12>::unsafe_setup(5, &mut rng);
        // The constraint system as keygen leaves it (selectors compiled).
        let vk = keygen_vk_with_k::<Fq, Scheme, _>(&params, &RandCircuit { seed }, 5).unwrap();
        let cs = vk.cs().clone();
        let ev = Evaluator::new(&cs);
        let n = 16usize;
        let rand_cols = |rng: &mut ChaCha20Rng, m: usize| -> Vec<Polynomial<Fq, LagrangeCoeff>> {
            (0..m)
                .map(|_| Polynomial {
                    values: (0..n).map(|_| Fq::random(&mut *rng)).collect(),
                    _marker: PhantomData,
                })
                .collect()
        };
        let fixed = rand_cols(&mut rng, cs.num_fixed_columns);
        let advice = rand_cols(&mut rng, cs.num_advice_columns);
        let instance = rand_cols(&mut rng, cs.num_instance_columns);
        let ch: [Fq; 4] = std::array::from_fn(|_| Fq::random(&mut rng));
        let mut cases: Vec<(&FlatGraphEvaluator<Fq>, Vec<usize>)> = vec![(
            &ev.custom_gates_flat,
            vec![ev.custom_gates_flat.result_idx as usize],
        )];
        for (batch, flats) in ev.lookups.iter().zip(&ev.lookups_flat) {
            for (le, flat) in batch.iter().zip(flats) {
                cases.push((
                    flat,
                    [le.sum_partial_products, le.product, le.table, le.selector]
                        .map(|v| flat.resolve_idx(v))
                        .to_vec(),
                ));
            }
        }
        for flat in &ev.trashcans_flat {
            cases.push((flat, vec![flat.result_idx as usize]));
        }
        for (flat, outs) in cases {
            let prog = DeviceProgram::lower(flat, &outs, ch[0], ch[1], ch[2], ch[3])
                .expect("the lowering takes every evaluator of the prover");
            assert!(prog.nslots as usize <= flat.values_len);
            let mut buf = flat.new_values_buffer(&ch[0], &ch[1], &ch[2], &ch[3]);
            let mut slots = vec![Fq::ZERO; prog.nslots as usize];
            let mut out = vec![Fq::ZERO; outs.len()];
            for idx in 0..n {
                let rots: Vec<usize> = flat
                    .rotations
                    .iter()
                    .map(|r| idx.wrapping_add(*r as isize as usize) & (n - 1))
                    .collect();
                flat.evaluate(&mut buf, &fixed, &advice, &instance, &rots, &Fq::ZERO);
                let read = |r: &DeviceRead| {
                    let row = idx.wrapping_add(r.rotation as isize as usize) & (n - 1);
                    match r.kind {
                        COLUMN_FIXED => fixed[r.column as usize][row],
                        COLUMN_ADVICE => advice[r.column as usize][row],
                        _ => instance[r.column as usize][row],
                    }
                };
                prog.eval(read, &mut slots, &mut out);
                for (o, i) in out.iter().zip(&outs) {
                    assert_eq!(*o, buf[*i], "seed {seed} row {idx}");
                }
            }
        }
    }
}

/// The CPU reference of the quotient job equals the stock numerator and
/// quotient, on random circuits with gates, a lookup, a copy constraint and
/// a trash argument.
#[test]
fn quotient_job_matches_stock() {
    for seed in 0..8u64 {
        let k = 6;
        let (params, pk) = setup(seed, false, k);
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let inst = [Fq::from(rng.next_u64())];
        let mut transcript = CircuitTranscript::<blake2b_simd::State>::init();
        let trace = crate::plonk::compute_trace(
            &params,
            &pk,
            &RandCircuit { seed },
            #[cfg(feature = "committed-instances")]
            0,
            &[&inst],
            &mut transcript,
            &mut rng,
        )
        .unwrap();
        let job = job(&pk, &trace).expect("the job takes the random circuit");
        assert!(!job.lookups.is_empty() && !job.trash.is_empty());
        assert!(job.permutation.is_some());

        let stock_nu = crate::plonk::compute_nu_poly(&pk, &trace);
        let nu = job.numerator_reference();
        assert_eq!(nu, stock_nu.values, "seed {seed}: numerator");

        let mut h = crate::plonk::quotient_coeffs(&pk.fft_domain, stock_nu);
        h.truncate(job.divide.len);
        assert_eq!(job.divide_reference(nu), h, "seed {seed}: quotient");

        let shape = quotient_shape(&pk).unwrap();
        assert_eq!(shape.proof_polys, job.proof_polys().len());
        assert_eq!(shape.len, job.divide.len);
        assert_eq!(shape.nslots, job.nslots());
    }
}

/// The reference transforms and MSM equal the stock ones.
#[test]
fn reference_matches_stock_transforms_and_msm() {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let k = 7;
    let domain = EvaluationDomain::<Fq>::new(3, k);
    let fft_domain = FftDomain::new(&domain);
    let a: Vec<Fq> = (0..1 << k).map(|_| Fq::random(&mut rng)).collect();

    let stock = fft_domain.coeff_to_lagrange(domain.coeff_from_vec(a.clone()));
    let mut ours = a.clone();
    assert!(CpuReference.fft(&mut ours, domain.get_omega(), k));
    assert_eq!(ours, stock.values);

    let stock = fft_domain.lagrange_to_coeff(domain.lagrange_from_vec(a.clone()));
    let mut ours = a;
    let divisor = Fq::from(1u64 << k).invert().unwrap();
    assert!(CpuReference.ifft(&mut ours, domain.get_omega_inv(), k, divisor));
    assert_eq!(ours, stock.values);

    let bases: Vec<G1Affine> =
        (0..100).map(|_| G1Projective::random(&mut rng).to_affine()).collect();
    let scalars: Vec<Fq> = (0..100).map(|_| Fq::random(&mut rng)).collect();
    let stock: G1Projective = scalars.iter().zip(&bases).map(|(s, b)| *b * s).sum();
    assert_eq!(CpuReference.msm_g1(&scalars, &bases), Some(stock));
    let other: Vec<Fq> = (0..100).map(|_| Fq::random(&mut rng)).collect();
    let stock2: G1Projective = other.iter().zip(&bases).map(|(s, b)| *b * s).sum();
    assert_eq!(
        CpuReference.msm_g1_batch(&[&scalars, &other], &bases),
        Some(vec![stock, stock2])
    );
}

/// The reference accelerator, with its quotient corrupted on one thread.
struct Tampered(Option<ThreadId>);

impl Accelerator for Tampered {
    fn msm_g1(&self, s: &[Fq], b: &[G1Affine]) -> Option<G1Projective> {
        CpuReference.msm_g1(s, b)
    }
    fn msm_g1_batch(&self, s: &[&[Fq]], b: &[G1Affine]) -> Option<Vec<G1Projective>> {
        CpuReference.msm_g1_batch(s, b)
    }
    fn fft(&self, a: &mut [Fq], omega: Fq, log_n: u32) -> bool {
        CpuReference.fft(a, omega, log_n)
    }
    fn ifft(&self, a: &mut [Fq], omega_inv: Fq, log_n: u32, divisor: Fq) -> bool {
        CpuReference.ifft(a, omega_inv, log_n, divisor)
    }
    fn quotient(&self, job: &QuotientJob<'_, Fq>, out: &mut [Fq]) -> bool {
        let ok = CpuReference.quotient(job, out);
        if Some(std::thread::current().id()) == self.0 {
            out[0] += Fq::ONE;
        }
        ok
    }
}

/// End to end: with the reference accelerator installed, proofs verify and
/// every hook serves calls; a corrupted quotient makes the proof fail, so
/// the accelerator's output is what the proof is made of.
///
/// The accelerator is process-wide and other unit tests may prove while this
/// one runs. The installed accelerators are exact for every thread except
/// this test's own, so they cannot change another test's outcome.
/// Tests that install an accelerator take this lock: the accelerator is
/// process-wide.
static INSTALLS: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[test]
fn installed_accelerator_end_to_end() {
    let _lock = INSTALLS.lock().unwrap_or_else(|e| e.into_inner());
    let seed = 11;
    let (params, pk) = setup(seed, true, 7);
    assert!(prove_and_verify(&params, &pk, seed), "stock proof");

    install(Arc::new(Tampered(None)));
    let ops = [Op::Msm, Op::MsmBatch, Op::Ifft, Op::Quotient];
    let before = ops.map(stats);
    assert!(prove_and_verify(&params, &pk, seed), "reference proof");
    let after = ops.map(stats);
    for (op, (b, a)) in
        ["msm", "msm batch", "ifft", "quotient"].iter().zip(before.iter().zip(&after))
    {
        assert!(a.0 > b.0, "{op}: no call served ({b:?} -> {a:?})");
    }

    install(Arc::new(Tampered(Some(std::thread::current().id()))));
    assert!(
        !prove_and_verify(&params, &pk, seed),
        "a corrupted quotient must not verify"
    );

    uninstall();
    assert!(prove_and_verify(&params, &pk, seed), "stock proof again");
}

/// Counts `begin_proof` and `end_proof` on one thread.
struct Bracketed(
    ThreadId,
    std::sync::atomic::AtomicI64,
    std::sync::atomic::AtomicI64,
);

impl Accelerator for Bracketed {
    fn begin_proof(&self) {
        if std::thread::current().id() == self.0 {
            self.1.fetch_add(1, Ordering::Relaxed);
        }
    }
    fn end_proof(&self) {
        if std::thread::current().id() == self.0 {
            self.2.fetch_add(1, Ordering::Relaxed);
        }
    }
}

/// Every proof is bracketed by exactly one `begin_proof` and one
/// `end_proof` on its own thread.
#[test]
fn proofs_are_bracketed() {
    let _lock = INSTALLS.lock().unwrap_or_else(|e| e.into_inner());
    let seed = 12;
    let (params, pk) = setup(seed, true, 7);
    let acc = Arc::new(Bracketed(
        std::thread::current().id(),
        Default::default(),
        Default::default(),
    ));
    install(acc.clone());
    assert!(prove_and_verify(&params, &pk, seed));
    assert!(prove_and_verify(&params, &pk, seed));
    uninstall();
    let (b, e) = (acc.1.load(Ordering::Relaxed), acc.2.load(Ordering::Relaxed));
    assert!(b == 2 && e == 2, "begin {b}, end {e}");
}
