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

//! The `aggregation` workloads: a proof that a batch of proofs is valid.
//!
//! The aggregation circuit verifies `BATCH_SIZE` proofs of a SHA-256
//! preimage circuit in-circuit. It exposes their statements and the
//! accumulator of their verification, whose pairing check is left to the
//! verifier.
//!
//! The inner proofs are committed with fflonk, the cheapest scheme to verify
//! in-circuit. The scheme under benchmark is the one of the outer proof.

use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{AssignedByte, Instantiable},
    verifier::{self, Accumulator, AssignedAccumulator, AssignedVk, InCircuitTranscript},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, ConstraintSystem, Error},
    poly::EvaluationDomain,
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::{FflonkKZG, MidnightVK, Relation, ZkStdLib, ZkStdLibArch};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

use crate::{
    srs,
    workload::{RelationCase, Workload, relation_workload},
};

type E = midnight_curves::Bls12;
type F = midnight_curves::Fq;

/// The commitment scheme of the inner proofs.
type InnerPcs = FflonkKZG<4>;

/// The number of inner proofs that the circuit aggregates.
const BATCH_SIZE: usize = 2;

/// The logarithm of the number of rows of the aggregation circuit, the
/// smallest size that fits it.
const K: u32 = 16;

/// The logarithm of the number of rows of the inner circuit.
const INNER_K: u32 = 13;

/// The number of public inputs of the inner circuit: the bytes of a digest.
const INNER_NB_PUBLIC_INPUTS: usize = 32;

/// The workloads defined in this module.
pub fn workloads() -> Vec<Box<dyn Workload>> {
    vec![relation_workload("aggregation", aggregation)]
}

/// Proves [`BATCH_SIZE`] fixed statements of the inner circuit and builds the
/// circuit that aggregates them.
fn aggregation() -> RelationCase<Aggregation> {
    let mut rng = ChaCha8Rng::seed_from_u64(0);

    let params = srs::load::<InnerPcs>(INNER_K);
    let vk = midnight_zk_stdlib::setup_vk::<_, InnerPcs>(&params, &ShaPreimage);
    let pk = midnight_zk_stdlib::setup_pk(&ShaPreimage, &vk);
    let fixed_bases = verifier::fixed_bases::<E, InnerPcs>(vk.vk());

    let mut statements = Vec::with_capacity(BATCH_SIZE);
    let mut proofs = Vec::with_capacity(BATCH_SIZE);
    let mut accs = Vec::with_capacity(BATCH_SIZE);
    for _ in 0..BATCH_SIZE {
        let preimage: [u8; 24] = rng.r#gen();
        let digest: [u8; 32] = sha2::Sha256::digest(preimage).into();
        let proof = midnight_zk_stdlib::prove::<ShaPreimage, PoseidonState<F>, InnerPcs>(
            &params,
            &pk,
            &ShaPreimage,
            &digest,
            preimage,
            &mut rng,
        )
        .expect("proving a satisfied relation cannot fail");

        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&proof);
        let dual_msm = plonk::prepare::<F, InnerPcs, CircuitTranscript<PoseidonState<F>>>(
            vk.vk(),
            &[],
            &[
                &[],
                &ShaPreimage::format_instance(&digest).expect("valid instance"),
            ],
            &mut transcript,
        )
        .expect("the inner proof is well-formed");

        statements.push(digest);
        proofs.push(proof);
        accs.push(Accumulator::from_dual_msm(dual_msm, &fixed_bases));
    }

    let mut acc = Accumulator::accumulate::<PoseidonChip<F>>(&accs);
    acc.collapse();
    assert!(
        acc.check(&params.verifier_params(), &fixed_bases),
        "the inner proofs are valid"
    );

    let mut cs = ConstraintSystem::default();
    let arch = ShaPreimage.used_chips();
    ZkStdLib::configure(&mut cs, (arch, arch.range_check_bit_len(INNER_K)));
    let relation = Aggregation {
        inner_domain: EvaluationDomain::new(cs.degree() as u32, INNER_K),
        inner_vk: vk,
    };

    RelationCase {
        relation,
        instance: (statements, acc),
        witness: proofs,
        k: Some(K),
    }
}

/// Knowledge of a 192-bit preimage of a public SHA-256 digest.
#[derive(Clone, Debug, Default)]
struct ShaPreimage;

impl Relation for ShaPreimage {
    type Instance = [u8; 32];
    type Witness = [u8; 24];
    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let preimage = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let digest = std_lib.sha2_256(layouter, &preimage)?;
        digest.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ShaPreimage)
    }
}

/// The validity of [`BATCH_SIZE`] proofs of [`ShaPreimage`], up to the pairing
/// check of the accumulator in the instance.
#[derive(Clone, Debug)]
struct Aggregation {
    inner_domain: EvaluationDomain<F>,
    inner_vk: MidnightVK<InnerPcs>,
}

impl Relation for Aggregation {
    /// The inner statements and the accumulator of their verification.
    type Instance = (Vec<[u8; 32]>, Accumulator<E>);
    /// The inner proofs.
    type Witness = Vec<Vec<u8>>;
    type Error = Error;

    fn format_instance((statements, acc): &Self::Instance) -> Result<Vec<F>, Error> {
        let mut pis = Vec::new();
        for statement in statements {
            pis.extend(ShaPreimage::format_instance(statement)?);
        }
        pis.extend(AssignedAccumulator::<E>::as_public_input(acc));
        Ok(pis)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let verifier = std_lib.verifier::<InnerPcs>();

        let inner_vk: AssignedVk<F, InnerPcs> = verifier.assign_fixed_vk(
            layouter,
            &self.inner_domain,
            self.inner_vk.vk().cs(),
            self.inner_vk.vk().transcript_repr(),
        )?;

        let mut accs = Vec::with_capacity(BATCH_SIZE);
        for i in 0..BATCH_SIZE {
            let statement = instance
                .as_ref()
                .map(|(statements, _)| {
                    ShaPreimage::format_instance(&statements[i]).expect("valid instance")
                })
                .transpose_vec(INNER_NB_PUBLIC_INPUTS);
            let statement = std_lib.assign_many(layouter, &statement)?;
            statement
                .iter()
                .try_for_each(|x| std_lib.constrain_as_public_input(layouter, x))?;

            let mut transcript = std_lib.verifier_transcript();
            transcript
                .init_with_proof(layouter, witness.as_ref().map(|proofs| proofs[i].clone()))?;
            accs.push(verifier.prepare(
                layouter,
                &inner_vk,
                &[],
                &[&[], &statement],
                &mut transcript,
            )?);
        }

        let mut acc = AssignedAccumulator::accumulate(
            layouter,
            std_lib.bls12_381(),
            std_lib.bls12_381().scalar_field_chip(),
            std_lib.poseidon_chip(),
            &accs,
        )?;
        acc.collapse(
            layouter,
            std_lib.bls12_381(),
            std_lib.bls12_381().scalar_field_chip(),
        )?;
        acc.constrain_as_public_input(
            layouter,
            std_lib.bls12_381(),
            std_lib.bls12_381().scalar_field_chip(),
        )
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            bls12_381: true,
            nb_range_check_groups: 1,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        unimplemented!("the benchmarks do not serialize the aggregation circuit")
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        unimplemented!("the benchmarks do not serialize the aggregation circuit")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::workloads::ivc::check_workload;

    #[test]
    #[ignore = "slow: generates the keys of the aggregation circuit twice"]
    fn aggregation_proves_repeatedly() {
        check_workload(workloads()[0].as_ref());
    }
}
