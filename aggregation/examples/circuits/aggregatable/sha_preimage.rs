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

//! Aggregation-compatible SHA-256 preimage circuit.
//!
//! Given a SHA-256 digest `x`, proves knowledge of a 192-bit preimage `w`
//! such that `SHA-256(w) = x`.
//!
//! Unlike `sha_preimage` this circuit exposes a single public input: the
//! Poseidon hash of the digest bytes. This makes it compatible with the
//! multi-circuit aggregation framework, which requires exactly one public input
//! per inner circuit.

use midnight_aggregation::multi_circuit_aggregator::AggregableRelation;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
    types::{AssignedByte, Instantiable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::{rngs::OsRng, Rng};
use sha2::Digest;

type F = midnight_curves::Fq;

#[derive(Clone, Debug, Default)]
pub struct AggregatableShaPreimageCircuit;

impl AggregableRelation for AggregatableShaPreimageCircuit {}

impl Relation for AggregatableShaPreimageCircuit {
    type Instance = [u8; 32];
    type Witness = [u8; 24]; // 192 = 24 * 8
    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        let byte_pis: Vec<F> =
            instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect();
        Ok(vec![<PoseidonChip<F> as HashCPU<F, F>>::hash(&byte_pis)])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let witness_bytes = witness.transpose_array();
        let assigned_input = std_lib.assign_many(layouter, &witness_bytes)?;
        let output = std_lib.sha2_256(layouter, &assigned_input)?;

        // Hash the digest bytes in-circuit and expose the hash as the single
        // public input.
        let output_pis: Vec<_> = output
            .iter()
            .map(|b| std_lib.as_public_input(layouter, b))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect();

        let hash = std_lib.poseidon(layouter, &output_pis)?;
        std_lib.constrain_as_public_input(layouter, &hash)
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
        Ok(AggregatableShaPreimageCircuit)
    }
}

/// Samples a random instance–witness pair.
pub fn random_instance() -> ([u8; 32], [u8; 24]) {
    let preimage: [u8; 24] = OsRng.gen();
    let digest: [u8; 32] = sha2::Sha256::digest(preimage).into();
    (digest, preimage)
}
