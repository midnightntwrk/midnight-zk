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

//! The quotient job against the stock evaluator, on random constraint
//! systems (CPU only).

use std::marker::PhantomData;

use ff::Field;
use midnight_curves::{Bls12, Fq};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

use super::*;
use crate::{
    plonk::{evaluation::Evaluator, keygen_vk_with_k},
    poly::{LagrangeCoeff, Polynomial, kzg::params::ParamsKZG},
    test_circuit::{RandCircuit, Scheme, set_shape, setup},
    transcript::{CircuitTranscript, Transcript},
};

/// Every lowered program of a random constraint system gives the outputs
/// of its flat evaluator, at every row.
#[test]
fn lowered_programs_match_flat_evaluator() {
    for seed in 0..24u64 {
        set_shape(seed, false);
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let params = ParamsKZG::<Bls12>::unsafe_setup(5, &mut rng);
        // the constraint system as keygen leaves it (selectors compiled)
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

fn job_matches_stock(seed: u64) {
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
    let stock = test_switches::without_hooks(|| crate::plonk::compute_nu_poly(&pk, &trace));
    let nu = job.numerator_reference();
    assert_eq!(nu, stock.values, "seed {seed}: numerator");
    let domain = pk.vk.get_domain();
    let mut h = pk.fft_domain.extended_to_coeff(domain.divide_by_vanishing_poly(stock));
    h.truncate(job.divide.len);
    assert_eq!(job.divide_reference(nu), h, "seed {seed}: quotient");
    // the packed job keeps the shape
    let packed = abi::PackedJob::new(&job);
    // SAFETY: `packed` lives for this block.
    let j = unsafe { &*(packed.as_ptr() as *const abi::QuotientJobAbi) };
    assert_eq!(j.abi, abi::QUOTIENT_ABI);
    assert_eq!((j.k, j.ext_k, j.len), (job.k, job.ext_k, job.divide.len));
    assert_eq!((j.nlookups, j.ntrash), (job.lookups.len(), job.trash.len()));
    let shape = quotient_shape(&pk).unwrap();
    assert_eq!(shape.proof_polys, job.proof_polys().len());
    assert_eq!(shape.nslots, job.nslots());
    assert_eq!(shape.len, job.divide.len);
    // the job's Debug prints shapes only: no witness value reaches a log
    let dbg = format!("{job:?}");
    for p in job.advice.iter().chain(&job.instance) {
        for v in p.iter().filter(|v| **v != Fq::ZERO && **v != Fq::ONE).take(4) {
            assert!(
                !dbg.contains(&format!("{v:?}")),
                "seed {seed}: a value in Debug"
            );
        }
    }
    assert!(dbg.contains("values>"), "seed {seed}: lengths are printed");
    // the resident list holds the key polynomials the job reads
    let res = pk.gpu_resident_polys().unwrap();
    assert_eq!(
        res.len(),
        job.fixed.iter().flatten().count() + pk.sigmas.cosets.len() + 3
    );
}

/// The job's CPU interpreter equals the stock numerator and quotient on
/// random constraint systems with gates, a permutation, LogUp lookups and
/// trash arguments.
#[test]
fn job_matches_stock_numerator() {
    for seed in 0..6u64 {
        job_matches_stock(seed);
    }
}

/// The same over many random constraint systems (slow).
#[test]
#[ignore]
fn job_matches_stock_numerator_many() {
    for seed in 1000..1200u64 {
        job_matches_stock(seed);
    }
}

/// After the owner is dropped, the whole caller-owned allocation it was
/// built over (capacity, not only length) reads zero.
#[test]
fn erasing_owner_zeroes_whole_capacity_on_drop() {
    use crate::gpu::erasing::ErasingVec;

    let sentinel = Fq::from(0x5eed_u64);
    let len = 3usize;
    let cap = 8usize;
    let mut storage = vec![sentinel; cap].into_boxed_slice();
    let ptr = storage.as_mut_ptr();
    std::mem::forget(storage);
    // SAFETY: `ptr` is a live allocation of `cap` field elements, leaked
    // above and reclaimed below; the owner zeroing it does not free it.
    let owner = unsafe { ErasingVec::from_raw_parts_in_caller_storage(ptr, len, cap) };
    assert_eq!(owner.len(), len);
    assert_eq!(owner.capacity(), cap);
    drop(owner);
    // SAFETY: the allocation is still live (the owner did not free it).
    let reclaimed = unsafe { Box::from_raw(std::slice::from_raw_parts_mut(ptr, cap)) };
    assert!(
        reclaimed.iter().all(|v| *v == Fq::ZERO),
        "the whole capacity is zero after drop"
    );
}

/// The owner's address and capacity do not change through its API, and
/// pushing past the fixed capacity fails instead of reallocating.
#[test]
fn erasing_owner_never_reallocates() {
    use crate::gpu::erasing::ErasingVec;

    let mut owner = ErasingVec::<Fq>::with_capacity_zeroed(6, 4);
    let (ptr, cap) = (owner.as_ptr(), owner.capacity());
    owner[0] = Fq::from(11_u64);
    owner.push_fixed(Fq::from(12_u64));
    owner.truncate(2);
    owner.push_fixed(Fq::from(13_u64));
    assert_eq!(owner.as_ptr(), ptr, "the allocation did not move");
    assert_eq!(owner.capacity(), cap, "the capacity did not change");
    assert_eq!(
        &owner[..],
        &[Fq::from(11_u64), Fq::ZERO, Fq::from(13_u64)][..]
    );

    let mut full = ErasingVec::<Fq>::zeroed(2);
    let overflow = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        full.push_fixed(Fq::ONE);
    }));
    assert!(overflow.is_err(), "pushing past capacity must not grow");
}

/// Adopting a `Vec` and handing the allocation back as a `Vec` move the
/// same allocation: neither copies nor reallocates.
#[test]
fn erasing_owner_vec_hand_over_moves_allocation() {
    use crate::gpu::erasing::ErasingVec;

    let v = vec![Fq::from(3_u64), Fq::from(4_u64)];
    let (ptr, cap) = (v.as_ptr(), v.capacity());
    let owner = ErasingVec::from_vec(v);
    assert_eq!((owner.as_ptr(), owner.capacity()), (ptr, cap));
    let back = owner.into_vec();
    assert_eq!((back.as_ptr(), back.capacity()), (ptr, cap));
    assert_eq!(back, vec![Fq::from(3_u64), Fq::from(4_u64)]);
}

/// Serialises the tests that read the process-wide drop records.
static DROP_RECORD_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// On a real random-circuit job, the numerator and quotient buffers of
/// the CPU reference are zeroed over their whole capacity when released.
#[test]
fn quotient_reference_buffers_are_zeroed_on_release() {
    let _lock = DROP_RECORD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let seed = 0u64;
    let (params, pk) = setup(seed, false, 6);
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
    let ext_len = 1usize << job.ext_k;
    let _ = erasing::take_drop_records();
    let nu = job.numerator_reference();
    assert_eq!(nu.len(), ext_len);
    assert!(nu.iter().any(|v| *v != Fq::ZERO), "a non-zero numerator");
    let h = job.divide_reference(nu);
    assert_eq!(h.len(), job.divide.len);
    assert!(h.iter().any(|v| *v != Fq::ZERO), "a non-zero quotient");
    drop(h);
    let records = erasing::take_drop_records();
    // The numerator buffer (whole extended length) and the quotient
    // buffer it becomes were both released through the erasing owner.
    assert!(
        records.iter().any(|r| r.cap == ext_len && r.nonzero_before && r.all_zero_after),
        "the numerator/quotient buffer is zeroed on release: {records:?}"
    );
    // Every buffer released on this path that held non-zero bytes was
    // zero when its drop finished.
    assert!(
        records.iter().all(|r| r.all_zero_after),
        "every released buffer is zero after drop: {records:?}"
    );
}

/// A quotient hook that fills the read-back buffer with a sentinel and
/// accepts. It is passed to the quotient path directly, without the
/// process-wide install, so this test binary stays hook-free.
unsafe fn sentinel_quotient(_job: *const std::ffi::c_void, out: &mut [Scalar]) -> bool {
    let s = adapter::scalar(Fq::from(7_u64));
    for x in out {
        *x = s;
    }
    true
}

/// On the real quotient path, the hook read-back buffer and, in check
/// mode, the stock reference buffer are zeroed when they are released.
#[test]
fn quotient_hook_buffers_are_zeroed_on_release() {
    let _lock = DROP_RECORD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let seed = 1u64;
    let (params, pk) = setup(seed, false, 6);
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
    let len = quotient_shape(&pk).expect("a quotient shape").len;

    // The read-back of an accepting hook.
    let _ = erasing::take_drop_records();
    let out = quotient_coeffs_with(
        sentinel_quotient,
        &pk,
        &trace,
        || -> Vec<Fq> { panic!("the stock closure runs in check mode only") },
        false,
    )
    .expect("the sentinel hook accepts");
    assert_eq!(out.len(), len);
    assert!(out.iter().all(|v| *v == Fq::from(7_u64)));
    drop(out);
    let records = erasing::take_drop_records();
    assert!(
        records.iter().any(|r| r.len == len && r.nonzero_before && r.all_zero_after),
        "the hook read-back is zeroed on release: {records:?}"
    );

    // Check mode: the device read-back is dropped inside the path and
    // the stock reference, adopted from the stock closure's `Vec`, is
    // what is returned and then released by the caller.
    let _ = erasing::take_drop_records();
    let checks_before = quotient_checks();
    let stock = quotient_coeffs_with(
        sentinel_quotient,
        &pk,
        &trace,
        || vec![Fq::from(9_u64); len],
        true,
    )
    .expect("check mode returns the stock quotient");
    assert!(quotient_checks() > checks_before, "the check ran");
    assert!(stock.iter().all(|v| *v == Fq::from(9_u64)));
    let inner = erasing::take_drop_records();
    assert!(
        inner.iter().any(|r| r.len == len && r.nonzero_before && r.all_zero_after),
        "the device read-back is zeroed inside check mode: {inner:?}"
    );
    drop(stock);
    let records = erasing::take_drop_records();
    assert!(
        records.iter().any(|r| r.len == len && r.nonzero_before && r.all_zero_after),
        "the stock reference is zeroed on release: {records:?}"
    );
}

/// A whole proof: when `h(X)` is split into limbs for the commitment,
/// the buffer that held all of `h` is zeroed over its whole capacity
/// when it is released, and the proof still verifies.
#[test]
fn quotient_commit_buffers_are_zeroed_on_release() {
    let _lock = DROP_RECORD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let seed = 3u64;
    let (params, pk) = setup(seed, true, 6);
    let len = quotient_shape(&pk).expect("a quotient shape").len;
    let _ = erasing::take_drop_records();
    let (proof, ok) = crate::test_circuit::prove(&params, &pk, seed, true);
    assert!(ok, "the proof verifies");
    assert!(!proof.is_empty());
    let records = erasing::take_drop_records();
    assert!(
        records.iter().any(|r| r.len == len && r.nonzero_before && r.all_zero_after),
        "the buffer of h is zeroed when the limbs are split off: {records:?}"
    );
    assert!(
        records.iter().all(|r| r.all_zero_after),
        "every released buffer is zero after drop: {records:?}"
    );
}

/// A whole proof: every blinded limb of `h(X)` that the quotient group
/// holds after the commitment is zeroed over its whole capacity when the
/// group is released at the end of the proof, and the commitment of the
/// group makes no further copy of a limb (a copy would show up as a
/// further limb-sized erasure, and an unerased copy or limb would show
/// up as a missing one). Exactly one limb-sized erasure per limb is
/// therefore recorded, and the proof still verifies.
#[test]
fn quotient_final_limbs_are_zeroed_on_release() {
    let _lock = DROP_RECORD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let seed = 5u64;
    let (params, pk) = setup(seed, true, 6);
    let domain = pk.get_vk().get_domain();
    let nb_limbs = domain.get_quotient_poly_degree() + 1;
    let limb_len = domain.n as usize;
    assert!(nb_limbs >= 2, "several quotient limbs: {nb_limbs}");
    let _ = erasing::take_drop_records();
    let (proof, ok) = crate::test_circuit::prove(&params, &pk, seed, true);
    assert!(ok, "the proof verifies");
    assert!(!proof.is_empty());
    // Another test that proves may run at the same time in this binary
    // and shares the record list, so only this thread's records count:
    // this proof and the release of its quotient group ran here.
    let me = std::thread::current().id();
    let records: Vec<_> =
        erasing::take_drop_records().into_iter().filter(|r| r.thread == me).collect();
    let limbs: Vec<_> = records.iter().filter(|r| r.len == limb_len && r.cap == limb_len).collect();
    assert_eq!(
        limbs.len(),
        nb_limbs,
        "one erasure per quotient limb held by the group, and no \
         commitment copy of a limb: {records:?}"
    );
    assert!(
        limbs.iter().all(|r| r.all_zero_after),
        "every quotient limb is zero over its whole capacity at its \
         release: {records:?}"
    );
    assert!(
        limbs.iter().any(|r| r.nonzero_before),
        "the limbs held witness-dependent values before erasure: {records:?}"
    );
    assert!(
        records.iter().all(|r| r.all_zero_after),
        "every released buffer is zero after drop: {records:?}"
    );
}

#[test]
fn second_install_rejected_shape() {
    // `install` is process-wide; this binary installs nothing, so only the
    // getter is checked here (the install test has its own binary).
    assert!(hooks().is_none());
}
