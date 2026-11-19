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

//! A seeded random circuit for tests: random gates, a batched LogUp lookup,
//! a copy constraint and a trash argument (unit tests, and the feature
//! `gpu-test`).

use std::cell::Cell;

use ff::Field;
use midnight_curves::{Bls12, Fq};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

use crate::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Fixed, Instance,
        ProvingKey, Selector, TableColumn, VirtualCells, create_proof, keygen_pk, keygen_vk_with_k,
        prepare, trash,
    },
    poly::{
        Rotation,
        commitment::Guard,
        kzg::{KZGCommitmentScheme, params::ParamsKZG},
    },
    transcript::{CircuitTranscript, Transcript},
};

thread_local! {
    static SHAPE: Cell<(u64, bool)> = const { Cell::new((0, false)) };
}

/// The commitment scheme of the test circuit.
pub(crate) type Scheme = KZGCommitmentScheme<Bls12>;

/// Sets the seed of the circuit shape `configure` builds on this thread and
/// whether the witness must satisfy the circuit.
pub(crate) fn set_shape(seed: u64, satisfied: bool) {
    SHAPE.with(|s| s.set((seed, satisfied)));
}

// Static configuration of the legacy fixture reads a thread-local shape.
// Restore an enclosing key generation if this worker runs another fixture.
#[cfg(feature = "gpu")]
pub(crate) fn with_shape<T>(seed: u64, satisfied: bool, f: impl FnOnce() -> T) -> T {
    struct Restore((u64, bool));
    impl Drop for Restore {
        fn drop(&mut self) {
            SHAPE.set(self.0);
        }
    }
    let _restore = Restore(SHAPE.replace((seed, satisfied)));
    f()
}

/// A random expression over the columns of `cfg` of depth at most `depth`.
fn rand_expr(
    rng: &mut ChaCha20Rng,
    vc: &mut VirtualCells<'_, Fq>,
    cfg: &Cfg,
    depth: u32,
) -> Expression<Fq> {
    let rots = [
        Rotation::cur(),
        Rotation::next(),
        Rotation::prev(),
        Rotation(2),
    ];
    let leaf = |rng: &mut ChaCha20Rng, vc: &mut VirtualCells<'_, Fq>| -> Expression<Fq> {
        let r = rots[(rng.next_u32() % 4) as usize];
        match rng.next_u32() % 5 {
            0 => vc.query_advice(cfg.a[(rng.next_u32() % 3) as usize], r),
            1 => vc.query_fixed(cfg.f[(rng.next_u32() % 2) as usize], r),
            2 => vc.query_instance(cfg.inst, r),
            3 => Expression::Constant(Fq::from(rng.next_u64())),
            _ => vc.query_advice(cfg.a[0], Rotation::cur()),
        }
    };
    if depth == 0 || rng.next_u32().is_multiple_of(4) {
        return leaf(rng, vc);
    }
    let x = rand_expr(rng, vc, cfg, depth - 1);
    match rng.next_u32() % 6 {
        0 => x + rand_expr(rng, vc, cfg, depth - 1),
        1 => x - rand_expr(rng, vc, cfg, depth - 1),
        2 => x * rand_expr(rng, vc, cfg, depth - 1),
        3 => -x,
        // the evaluator lowers a product with the constant 2 to a doubling
        4 => x * Expression::Constant(Fq::from(2)),
        _ => x.clone() * x,
    }
}

/// The columns of [`RandCircuit`].
#[derive(Clone, Debug)]
pub(crate) struct Cfg {
    #[cfg(feature = "gpu")]
    satisfied: bool,
    a: [Column<Advice>; 3],
    f: [Column<Fixed>; 2],
    q: Column<Fixed>,
    zero: Column<Fixed>,
    s: Selector,
    t: TableColumn,
    inst: Column<Instance>,
}

/// A circuit whose gates, lookup inputs and trash constraints are random,
/// from the shape seed of [`set_shape`]. Its witness satisfies the lookup
/// and the copy constraint. Unsatisfied, the gates and the trash argument
/// do not hold (a numerator test needs no valid witness); satisfied, every
/// gate is multiplied by a zero fixed column and the trash selector is zero.
#[derive(Clone, Debug, Default)]
pub(crate) struct RandCircuit {
    /// Seed of the witness.
    pub seed: u64,
}

const TABLE: u64 = 16;
const ROWS: usize = 20;

impl Circuit<Fq> for RandCircuit {
    type Config = Cfg;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Cfg {
        let (seed, satisfied) = SHAPE.with(|s| s.get());
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let cfg = Cfg {
            #[cfg(feature = "gpu")]
            satisfied,
            a: [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ],
            f: [meta.fixed_column(), meta.fixed_column()],
            q: meta.fixed_column(),
            zero: meta.fixed_column(),
            s: meta.complex_selector(),
            t: meta.lookup_table_column(),
            inst: meta.instance_column(),
        };
        meta.enable_equality(cfg.a[0]);
        meta.enable_equality(cfg.a[1]);
        meta.enable_equality(cfg.inst);
        if rng.next_u32().is_multiple_of(2) {
            meta.enable_equality(cfg.f[0]);
        }
        let ngates = 1 + rng.next_u32() % 3;
        for _ in 0..ngates {
            let nc = 1 + rng.next_u32() % 3;
            let mut r2 = ChaCha20Rng::seed_from_u64(rng.next_u64());
            let c = cfg.clone();
            meta.create_gate("random", move |vc| {
                let z = vc.query_fixed(c.zero, Rotation::cur());
                Constraints::without_selector(
                    (0..nc)
                        .map(|_| {
                            let e = rand_expr(&mut r2, vc, &c, 3);
                            if satisfied { z.clone() * e } else { e }
                        })
                        .collect::<Vec<_>>(),
                )
            });
        }
        // A batched lookup of a[2] at a few rotations (all in the table).
        let ninputs = 1 + (rng.next_u32() % 4) as i32;
        meta.batched_lookup("lookup", Some(cfg.s), |vc| {
            let inputs = (0..ninputs).map(|r| vc.query_advice(cfg.a[2], Rotation(r))).collect();
            vec![(inputs, cfg.t)]
        });
        // A trash argument with a fixed selector and random constraints.
        let mut r3 = ChaCha20Rng::seed_from_u64(rng.next_u64());
        let ntrash = 1 + r3.next_u32() % 2;
        let mut trash_parts = None;
        let c = cfg.clone();
        meta.create_gate("trash queries", |vc| {
            let q = vc.query_fixed(c.q, Rotation::cur());
            let exprs: Vec<_> = (0..ntrash).map(|_| rand_expr(&mut r3, vc, &c, 2)).collect();
            trash_parts = Some((q.clone(), exprs));
            Constraints::without_selector(vec![q * Expression::Constant(Fq::ZERO)])
        });
        let (q, exprs) = trash_parts.unwrap();
        let idx = meta.trashcans.len();
        meta.trashcans.push(trash::Argument::new(idx, q, exprs));
        cfg
    }

    fn synthesize(&self, cfg: Cfg, mut layouter: impl Layouter<Fq>) -> Result<(), Error> {
        #[cfg(not(feature = "gpu"))]
        let satisfied = SHAPE.with(|s| s.get().1);
        #[cfg(feature = "gpu")]
        let satisfied = cfg.satisfied;
        layouter.assign_table(
            || "table",
            |mut table| {
                for i in 0..TABLE {
                    table.assign_cell(|| "t", cfg.t, i as usize, || Value::known(Fq::from(i)))?;
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "main",
            |mut region| {
                let mut rng = ChaCha20Rng::seed_from_u64(self.seed ^ 0x5eed);
                let mut first: Option<(Fq, crate::circuit::Cell)> = None;
                for row in 0..ROWS {
                    let v0 = Fq::from(rng.next_u64());
                    let c0 = region.assign_advice(|| "a0", cfg.a[0], row, || Value::known(v0))?;
                    let v1 = if row == 1 {
                        first.unwrap().0
                    } else {
                        Fq::from(rng.next_u64())
                    };
                    let c1 = region.assign_advice(|| "a1", cfg.a[1], row, || Value::known(v1))?;
                    if row == 0 {
                        first = Some((v0, c0.cell()));
                    }
                    if row == 1 {
                        region.constrain_equal(c1.cell(), first.unwrap().1)?;
                    }
                    let t = Fq::from(rng.next_u64() % TABLE);
                    region.assign_advice(|| "a2", cfg.a[2], row, || Value::known(t))?;
                    for f in cfg.f {
                        region.assign_fixed(
                            || "f",
                            f,
                            row,
                            || Value::known(Fq::from(rng.next_u64())),
                        )?;
                    }
                    let q = if satisfied {
                        Fq::ZERO
                    } else {
                        Fq::from(rng.next_u64() % 2)
                    };
                    region.assign_fixed(|| "q", cfg.q, row, || Value::known(q))?;
                    if row + 4 < ROWS {
                        cfg.s.enable(&mut region, row)?;
                    }
                }
                Ok(())
            },
        )
    }
}

/// A proof using an existing key needs only the column configuration for
/// synthesis. Bind it before the prover can yield to another job.
#[cfg(feature = "gpu")]
#[derive(Clone)]
pub(crate) struct ConfiguredCircuit {
    circuit: RandCircuit,
    cfg: Cfg,
}

#[cfg(feature = "gpu")]
impl ConfiguredCircuit {
    pub(crate) fn new(seed: u64, satisfied: bool) -> Self {
        let cfg = with_shape(seed, satisfied, || {
            RandCircuit::configure(&mut ConstraintSystem::default())
        });
        Self {
            circuit: RandCircuit { seed },
            cfg,
        }
    }
}

#[cfg(feature = "gpu")]
impl Circuit<Fq> for ConfiguredCircuit {
    type Config = ();
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(_: &mut ConstraintSystem<Fq>) {}

    fn synthesize(&self, (): (), layouter: impl Layouter<Fq>) -> Result<(), Error> {
        self.circuit.synthesize(self.cfg.clone(), layouter)
    }
}

/// The SRS and keys of the circuit of shape `seed` at `2^k` rows.
pub(crate) fn setup(
    seed: u64,
    satisfied: bool,
    k: u32,
) -> (ParamsKZG<Bls12>, ProvingKey<Fq, Scheme>) {
    set_shape(seed, satisfied);
    let params = ParamsKZG::<Bls12>::unsafe_setup(k, ChaCha20Rng::seed_from_u64(seed));
    let circuit = RandCircuit { seed };
    let vk = keygen_vk_with_k::<Fq, Scheme, _>(&params, &circuit, k).unwrap();
    let pk = keygen_pk(vk, &circuit).unwrap();
    (params, pk)
}

/// The instance of a proof.
pub(crate) fn instance(seed: u64) -> [Fq; 1] {
    [Fq::from(seed.wrapping_mul(31).wrapping_add(7))]
}

/// A proof for the circuit of shape `seed` with every random draw seeded
/// (the quotient blinding included). Returns the proof bytes, and whether
/// the proof verifies.
pub(crate) fn prove(
    params: &ParamsKZG<Bls12>,
    pk: &ProvingKey<Fq, Scheme>,
    seed: u64,
    satisfied: bool,
) -> (Vec<u8>, bool) {
    // The shape and the blinding seed are process-wide: one seeded proof at a
    // time, so two tests that prove at once keep their own draws.
    static SEEDED: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let seeded = SEEDED.lock().unwrap_or_else(|e| e.into_inner());
    #[cfg(not(feature = "gpu"))]
    set_shape(seed, satisfied);
    // The seed is removed on every exit, unwind included, and before the
    // lock is released (locals drop in reverse order).
    #[cfg(feature = "gpu")]
    struct ClearSeed;
    #[cfg(feature = "gpu")]
    impl Drop for ClearSeed {
        fn drop(&mut self) {
            crate::plonk::prover::test_blinding::set(None);
        }
    }
    crate::plonk::prover::test_blinding::set(Some(seed ^ 0xb11d));
    #[cfg(feature = "gpu")]
    let clear = ClearSeed;
    let inst = instance(seed);
    let mut transcript = CircuitTranscript::<blake2b_simd::State>::init();
    create_proof::<Fq, Scheme, _, _>(
        params,
        pk,
        #[cfg(not(feature = "gpu"))]
        &RandCircuit { seed },
        #[cfg(feature = "gpu")]
        &ConfiguredCircuit::new(seed, satisfied),
        #[cfg(feature = "committed-instances")]
        0,
        &[&inst],
        &mut transcript,
        ChaCha20Rng::seed_from_u64(seed ^ 0x9e37),
    )
    .unwrap();
    #[cfg(feature = "gpu")]
    drop(clear);
    #[cfg(not(feature = "gpu"))]
    crate::plonk::prover::test_blinding::set(None);
    drop(seeded);
    let proof = transcript.finalize();
    let mut transcript = CircuitTranscript::<blake2b_simd::State>::init_from_bytes(&proof);
    let ok = prepare::<Fq, Scheme, _>(
        pk.get_vk(),
        #[cfg(feature = "committed-instances")]
        &[],
        &[&inst],
        &mut transcript,
    )
    .is_ok_and(|g| g.verify(&params.verifier_params()).is_ok());
    (proof, ok)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The digest of a seeded proof. The same in every build of this crate:
    /// the feature `gpu` without installed hooks proves byte for byte as a
    /// build without it (CI runs the unit tests in both builds).
    #[test]
    fn seeded_proof_digest() {
        let (params, pk) = setup(3, true, 6);
        let (proof, ok) = prove(&params, &pk, 3, true);
        assert!(ok, "the satisfied circuit verifies");
        let (again, _) = prove(&params, &pk, 3, true);
        assert_eq!(proof, again, "seeded proofs are reproducible");
        let digest = blake2b_simd::Params::new().hash_length(32).hash(&proof);
        assert_eq!(digest.to_hex().as_str(), GOLDEN, "proof bytes changed");
    }

    const GOLDEN: &str = "5177fc0d3371a3ee809efe70428114afb17eddddc866a104b37e6369c5da96f2";
}
