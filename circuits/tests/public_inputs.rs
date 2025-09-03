// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

//! Unit tests on the number of public inputs in a circuit.
//!
//! We expect a proof verification to fail if the number of provided public
//! inputs does not match the exact number of constrained instance cells in the
//! circuit. This property is not necessarily enforced by halo2, but we require
//! compact_std_lib to satisfy it.

use ff::Field;
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib},
    hash::poseidon::PoseidonChip,
    instructions::{
        hash::HashCPU, AssertionInstructions, AssignmentInstructions, PublicInputInstructions,
    },
    testing_utils::plonk_api::filecoin_srs,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

type F = midnight_curves::Fq;

#[derive(Clone)]
struct PIsCircuit {
    nb_public_inputs: u32,
}

impl Relation for PIsCircuit {
    type Instance = Vec<F>;

    type Witness = Vec<F>;

    fn format_instance(x: &Self::Instance) -> Vec<F> {
        x.clone()
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        // The following is not the most idiomatic way of assigning values,
        // but it is definitely a valid way that we use here to exhibit the
        // problem of using more public inputs than the ones that are
        // actually declared in [circuit].
        //
        // A better way to load the inputs would be the following:
        //
        //   let inputs = instance
        //     .transpose_vec(self.nb_public_inputs as usize)
        //     .into_iter()
        //     .map(|input| std_lib.assign_as_public_input(layouter, input))
        //     .collect::<Result<Vec<_>, Error>>()?;
        //
        // however, that would not allow us to test the issue that we are
        // concerned about here.
        let mut inputs = vec![F::ZERO; self.nb_public_inputs as usize];
        instance.map(|v| inputs = v[..self.nb_public_inputs as usize].to_vec());
        let inputs = inputs
            .into_iter()
            .map(|input| std_lib.assign_as_public_input(layouter, Value::known(input)))
            .collect::<Result<Vec<_>, Error>>()?;

        let preimage_values = witness.transpose_vec(self.nb_public_inputs as usize);
        let preimages = std_lib.assign_many(layouter, &preimage_values)?;

        let hashes = preimages
            .into_iter()
            .map(|preimage| std_lib.poseidon(layouter, &[preimage]))
            .collect::<Result<Vec<_>, Error>>()?;

        for (input, hash) in inputs.iter().zip(hashes.iter()) {
            std_lib.assert_equal(layouter, input, hash)?;
        }

        Ok(())
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.nb_public_inputs.to_le_bytes())
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut bytes = [0u8; 4];
        reader.read_exact(&mut bytes)?;
        Ok(PIsCircuit {
            nb_public_inputs: u32::from_le_bytes(bytes),
        })
    }
}

fn pi_test(nb_public_inputs: u32, extra_pi: bool) {
    let srs = filecoin_srs(12);

    let relation = PIsCircuit { nb_public_inputs };
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    let mut rng = ChaCha8Rng::from_entropy();

    let witness = (0..nb_public_inputs)
        .map(|_| F::random(&mut rng))
        .collect::<Vec<_>>();

    let mut instance = witness
        .iter()
        .map(|w| <PoseidonChip<F> as HashCPU<F, F>>::hash(&[*w]))
        .collect::<Vec<_>>();

    if extra_pi {
        instance.push(F::ONE);
    }

    let proof = compact_std_lib::prove::<PIsCircuit, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, rng,
    )
    .expect("Proof generation should not fail");

    assert!(compact_std_lib::verify::<PIsCircuit, blake2b_simd::State>(
        &srs.verifier_params(),
        &vk,
        &instance,
        &proof
    )
    .is_ok())
}

#[test]
fn public_inputs_test() {
    for n in [0, 1, 2, 10, 32, 33] {
        pi_test(n, false);
    }
}

#[test]
#[should_panic]
fn extra_public_inputs_test() {
    let mut rng = ChaCha8Rng::from_entropy();
    let n: u8 = rng.gen_range(0..=20);
    pi_test(n as u32, true);
}
