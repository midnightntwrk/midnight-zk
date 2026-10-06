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

//! Consistency tests between the off-circuit MMR and its gadget. The CPU
//! implementation is documented as the specification of the in-circuit one, so
//! the two must accept and reject exactly the same witnesses, honest or not.

use ff::Field;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};

use crate::{
    field::{NativeChip, NativeGadget, decomposition::chip::P2RDecompositionChip},
    hash::poseidon::PoseidonChip,
    instructions::hash::HashCPU,
    mmr::{
        cpu::{Mmr, MmrState, SummitPath},
        mmr_gadget::MmrGadget,
    },
    testing_utils::FromScratch,
};

const CAPACITY: usize = 5;
type F = midnight_curves::Fq;
type H = PoseidonChip<F>;
type Ng = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

struct PrefixCircuit {
    small: Value<MmrState<F, CAPACITY>>,
    big: Value<MmrState<F, CAPACITY>>,
    path: Value<SummitPath<F, CAPACITY>>,
}

impl Circuit<F> for PrefixCircuit {
    type Config = <MmrGadget<F, Ng, H> as FromScratch<F>>::Config;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        PrefixCircuit {
            small: Value::unknown(),
            big: Value::unknown(),
            path: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let committed = meta.instance_column();
        let instance = meta.instance_column();
        MmrGadget::<F, Ng, H>::configure_from_scratch(
            meta,
            &mut vec![],
            &mut vec![],
            &[committed, instance],
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let ng = Ng::new_from_scratch(&config.0);
        let hash = H::new_from_scratch(&config.1);
        let gadget = MmrGadget::<F, Ng, H>::new(&ng, &hash);
        let small = gadget.assign(&mut layouter, self.small)?;
        let big = gadget.assign(&mut layouter, self.big)?;
        let path = gadget.assign_summit_path(&mut layouter, self.path)?;
        gadget.assert_prefix(&mut layouter, &small, &big, &path)?;
        gadget.load_from_scratch(&mut layouter)
    }
}

fn circuit_ok(
    small: MmrState<F, CAPACITY>,
    big: MmrState<F, CAPACITY>,
    path: SummitPath<F, CAPACITY>,
) -> bool {
    let circuit = PrefixCircuit {
        small: Value::known(small),
        big: Value::known(big),
        path: Value::known(path),
    };
    MockProver::run(&circuit, vec![vec![], vec![]]).unwrap().verify().is_ok()
}

fn all_mmrs(first: u64, n: u64) -> Vec<Mmr<F, H, CAPACITY>> {
    let mut mmrs = vec![Mmr::new()];
    for i in 0..n {
        let mut next = mmrs[i as usize].clone();
        next.append(F::from(first + i));
        mmrs.push(next);
    }
    mmrs
}

/// `Mmr::is_prefix` is documented as the gate-by-gate specification of
/// `assert_prefix`. Cross-check them on honest and adversarial witnesses.
#[test]
fn consistency_prefix_cpu_vs_circuit() {
    const MAX: u64 = 12;
    let mmrs = all_mmrs(0, MAX);
    let shifted = all_mmrs(1, MAX);

    for b in 0..=MAX as usize {
        for a in 0..=b {
            let honest = mmrs[b].prove_prefix(a as u64);
            let mut cases = vec![("honest", mmrs[a].state(), honest)];
            for i in 0..CAPACITY {
                let mut tampered = honest;
                tampered.steps[i] += F::ONE;
                cases.push(("tampered-step", mmrs[a].state(), tampered));
            }
            if a > 0 {
                cases.push(("shifted-content", shifted[a].state(), honest));
            }
            if b < MAX as usize {
                cases.push((
                    "reversed",
                    mmrs[b + 1].state(),
                    mmrs[b].prove_prefix(b as u64),
                ));
            }

            for (tag, small, path) in cases {
                let cpu = Mmr::<F, H, CAPACITY>::is_prefix(&small, &mmrs[b].state(), &path);
                let zk = circuit_ok(small, mmrs[b].state(), path);
                assert_eq!(
                    cpu, zk,
                    "DISAGREE a={a} b={b} case={tag}: cpu={cpu} circuit={zk}"
                );
            }
        }
    }
}

/// Absent peak slots are never read, so garbage there is harmless. The gadget
/// canonicalizes them to zero at assignment, the CPU spec ignores them, and
/// `from_public_input` rejects them: three definitions of well-formed.
#[test]
fn noncanonical_state_cpu_vs_circuit() {
    let mmrs = all_mmrs(0, 12);
    let (a, b) = (8usize, 11usize);
    let path = mmrs[b].prove_prefix(a as u64);

    for slot in 0..CAPACITY {
        let mut small = mmrs[a].state();
        if (small.size >> slot) & 1 == 1 {
            continue;
        }
        small.peaks[slot] = F::from(12345);
        let cpu = Mmr::<F, H, CAPACITY>::is_prefix(&small, &mmrs[b].state(), &path);
        let zk = circuit_ok(small, mmrs[b].state(), path);
        assert_eq!(cpu, zk, "non-canonical small state, slot {slot}");
    }

    for slot in 0..CAPACITY {
        let mut big = mmrs[b].state();
        if (big.size >> slot) & 1 == 1 {
            continue;
        }
        big.peaks[slot] = F::from(12345);
        let cpu = Mmr::<F, H, CAPACITY>::is_prefix(&mmrs[a].state(), &big, &path);
        let zk = circuit_ok(mmrs[a].state(), big, path);
        assert_eq!(cpu, zk, "non-canonical big state, slot {slot}");
    }
}

/// The soundness crux: residual peaks above the lowest are taken from A's own
/// commitment, so each is pinned to one node of B at one position. Substituting
/// a genuine node of B at the wrong position must fail.
#[test]
fn prefix_residual_peaks_are_position_bound() {
    let mmrs = all_mmrs(0, 12);
    // a = 3 = 0b011: residual peaks at height 1 (leaves 0-1) and height 0 (leaf 2).
    let (a, b) = (3usize, 11usize);
    let path = mmrs[b].prove_prefix(a as u64);
    let good = mmrs[a].state();
    assert!(Mmr::<F, H, CAPACITY>::is_prefix(
        &good,
        &mmrs[b].state(),
        &path
    ));

    // The height-1 node covering leaves 2-3: a real node of B, wrong position.
    let mut forged = good;
    forged.peaks[1] = <H as HashCPU<F, F>>::hash(&[
        <H as HashCPU<F, F>>::hash(&[F::from(2)]),
        <H as HashCPU<F, F>>::hash(&[F::from(3)]),
    ]);
    assert!(!Mmr::<F, H, CAPACITY>::is_prefix(
        &forged,
        &mmrs[b].state(),
        &path
    ));
    assert!(!circuit_ok(forged, mmrs[b].state(), path));

    let mut swapped = good;
    swapped.peaks.swap(0, 1);
    assert!(!Mmr::<F, H, CAPACITY>::is_prefix(
        &swapped,
        &mmrs[b].state(),
        &path
    ));
    assert!(!circuit_ok(swapped, mmrs[b].state(), path));
}

/// `height` and `leaf_index` are prover hints: bits of `leaf_index` above
/// `height` are never consulted, so membership fixes no absolute position.
#[test]
fn membership_leaf_index_is_free_above_height() {
    const MSIZE: usize = 6;
    let n = 22u64; // 0b10110
    let mut mmr = Mmr::<F, H, MSIZE>::new();
    for i in 0..n {
        mmr.append(F::from(i));
    }
    let state = mmr.state();

    // Leaf 16 sits in the height-2 mountain (leaves 16..19).
    let proof = mmr.prove_membership(16);
    assert!(Mmr::<F, H, MSIZE>::is_member(&state, F::from(16), &proof));

    let mut hinted = proof;
    hinted.leaf_index |= (!0u64 << proof.height) & ((1u64 << MSIZE) - 1);
    assert!(
        Mmr::<F, H, MSIZE>::is_member(&state, F::from(16), &hinted),
        "high bits of leaf_index are not free"
    );

    let mut over = proof;
    over.leaf_index = (1u64 << MSIZE) + 1;
    assert!(!Mmr::<F, H, MSIZE>::is_member(&state, F::from(16), &over));

    // Bits at or above the assigned width are ignored off-circuit exactly as
    // the gadget ignores them, so an index carrying one still verifies.
    let mut high = proof;
    high.leaf_index |= 1u64 << MSIZE;
    assert!(Mmr::<F, H, MSIZE>::is_member(&state, F::from(16), &high));
}
