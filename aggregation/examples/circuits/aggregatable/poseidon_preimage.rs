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

//! Aggregation-compatible Poseidon preimage circuit.
//!
//! Given a Poseidon digest `x`, proves knowledge of a 3-element field
//! preimage `w` such that `Poseidon(w) = x`.
//!
//! This circuit already produces a single public input (the Poseidon
//! digest), so it is natively compatible with the multi-circuit aggregation
//! framework.

use ff::Field;
use midnight_aggregation::multi_circuit_aggregator::AggregableRelation;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::rngs::OsRng;

type F = midnight_curves::Fq;

#[derive(Clone, Debug, Default)]
pub struct PoseidonPreimageCircuit;

impl AggregableRelation for PoseidonPreimageCircuit {}

impl Relation for PoseidonPreimageCircuit {
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
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonPreimageCircuit)
    }
}

/// Samples a random instance–witness pair for the Poseidon preimage circuit.
pub fn random_instance() -> (F, [F; 3]) {
    let preimage: [F; 3] = std::array::from_fn(|_| F::random(OsRng));
    let digest = <PoseidonChip<F> as HashCPU<F, F>>::hash(&preimage);
    (digest, preimage)
}
