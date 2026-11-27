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

//! The `poseidon` workload: a chain of Poseidon hashes.

use ff::Field;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{AssignmentInstructions, PublicInputInstructions, hash::HashCPU},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::workload::{RelationCase, Workload, relation_workload};

type F = midnight_curves::Fq;

/// The length of the chain. A single hash fits in 2^6 rows, which is too
/// small to say anything about the prover; at 41 rows per hash, this many
/// fill 95% of 2^14 rows.
const CHAIN_LEN: usize = 380;

/// Knowledge of `(x, a, b)` such that the public digest is `h_CHAIN_LEN`,
/// where `h_0 = x` and `h_{i+1} = Poseidon(h_i, a, b)`.
#[derive(Clone, Default)]
pub struct PoseidonChain;

/// The digest that [`PoseidonChain`] makes public.
fn chain_digest([x, a, b]: [F; 3]) -> F {
    (0..CHAIN_LEN).fold(x, |h, _| {
        <PoseidonChip<F> as HashCPU<F, F>>::hash(&[h, a, b])
    })
}

impl Relation for PoseidonChain {
    type Instance = F;

    type Witness = [F; 3];

    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let [x, a, b]: [_; 3] = std_lib
            .assign_many(layouter, &witness.transpose_array())?
            .try_into()
            .expect("three assigned cells");
        let mut h = x;
        for _ in 0..CHAIN_LEN {
            h = std_lib.poseidon(layouter, &[h, a.clone(), b.clone()])?;
        }
        std_lib.constrain_as_public_input(layouter, &h)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonChain)
    }
}

fn build() -> RelationCase<PoseidonChain> {
    let mut rng = ChaCha8Rng::seed_from_u64(0x9053);
    let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
    RelationCase {
        relation: PoseidonChain,
        instance: chain_digest(witness),
        witness,
        k: None,
    }
}

/// The workloads defined in this module.
pub fn workloads() -> Vec<Box<dyn Workload>> {
    vec![relation_workload("poseidon", build)]
}

#[cfg(test)]
mod tests {
    use crate::workload::Pcs;

    /// Proves and verifies every workload under `pcs`, and checks that
    /// building it again gives the same circuit.
    fn check(pcs: Pcs) {
        for workload in super::workloads() {
            let name = workload.name();
            assert!(
                workload.supported_pcs().contains(&pcs),
                "{name} under {pcs}"
            );
            let mut prepared = workload.setup(pcs);
            let proof = prepared.prove();
            assert!(prepared.verify(&proof), "{name} under {pcs}");
            assert_eq!(
                prepared.vk_hash(),
                workload.setup(pcs).vk_hash(),
                "{name} under {pcs}"
            );
        }
    }

    #[test]
    fn kzg() {
        check(Pcs::Kzg);
    }

    #[test]
    #[ignore = "takes over a minute"]
    fn fflonk() {
        check(Pcs::FflonkT4);
        check(Pcs::FflonkT16);
    }
}
