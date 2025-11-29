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

//! Import of the keccak variant of SHA, implementation from [Alexandros Zacharakis](https://github.com/alexandroszacharakis8).

use ff::PrimeField;
#[cfg(test)]
use keccak::packed_chip::{PackedConfig, PACKED_ADVICE_COLS, PACKED_FIXED_COLS};
use keccak::{packed_chip::PackedChip, sha3_256_gadget::Keccak256, KECCAK_SQUEEZE_BYTES};
#[cfg(test)]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

#[cfg(test)]
use crate::testing_utils::FromScratch;
use crate::{
    external::{unsafe_convert_to_bytes, NG},
    instructions::AssertionInstructions,
    types::{AssignedByte, InnerValue},
};

/// The chip for the external implementation of Keccak.
pub type KeccakChip<F> = Keccak256<F, PackedChip<F>>;

/// Wrapper for the main method of Keccak.
pub fn digest<F: PrimeField>(
    chip: &KeccakChip<F>,
    native_gadget: &NG<F>,
    layouter: &mut impl Layouter<F>,
    input: &[AssignedByte<F>],
) -> Result<[AssignedByte<F>; KECCAK_SQUEEZE_BYTES], Error> {
    // The Keccak implementation requires `Value<u8>` inputs, instead of assigned
    // bytes. We extract these values from `input`, and bridge the broken link with
    // `assert_equal` below.
    let raw_input = input.iter().map(|b| b.value()).collect::<Vec<Value<u8>>>();
    let (reassigned_input, digest) = chip.digest(layouter, &raw_input)?;

    // Rebuilding the broken link between the re-assigned input and the original
    // one. The unsafe conversion is sound since we are processing Keccak bytes.
    let reassigned_input = unsafe_convert_to_bytes(layouter, native_gadget, &reassigned_input)?;
    for (original_byte, reassigned_byte) in input.iter().zip(reassigned_input.iter()) {
        native_gadget.assert_equal(layouter, original_byte, reassigned_byte)?
    }
    // This check should not be necessary to put in-circuit, as it should be
    // reflected in the verification process.
    assert!(input.len() == reassigned_input.len());

    let digest = unsafe_convert_to_bytes(layouter, native_gadget, &digest)?;
    Ok(digest.try_into().unwrap())
}

#[cfg(test)]
impl<F: PrimeField> FromScratch<F> for KeccakChip<F> {
    type Config = PackedConfig;

    fn new_from_scratch(config: &Self::Config) -> Self {
        KeccakChip::new(PackedChip::new(config))
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        _instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let advice_cols = (0..PACKED_ADVICE_COLS).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let fixed_cols = (0..PACKED_FIXED_COLS).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let constant_column = meta.fixed_column();

        keccak::packed_chip::PackedChip::configure(
            meta,
            constant_column,
            advice_cols[..PACKED_ADVICE_COLS].try_into().unwrap(),
            fixed_cols[..PACKED_FIXED_COLS].try_into().unwrap(),
        )
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.chip.load_table(layouter)
    }
}

// The set of preimage tests from the Keccak repo, but applied to our wrapper.
#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use ff::PrimeField;
    use keccak::{
        instructions::Keccackf1600Instructions,
        packed_chip::{PackedChip, PackedConfig},
        KECCAK_SQUEEZE_BYTES,
    };
    use midnight_curves::Fq;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;
    use sha3::{Digest, Keccak256 as KeccakCpu};

    use crate::{
        external::keccak::KeccakChip,
        field::{decomposition::chip::P2RDecompositionConfig, NativeGadget},
        instructions::{AssignmentInstructions, PublicInputInstructions},
        testing_utils::FromScratch,
        types::AssignedByte,
    };

    struct TestPreimage<F: PrimeField> {
        preimage: Vec<u8>,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField> Circuit<F> for TestPreimage<F> {
        // we use an instance column to witness the expected result
        type Config = (P2RDecompositionConfig, PackedConfig);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            let instances = &[committed_instance_column, instance_column];
            let native_config = NativeGadget::configure_from_scratch(meta, instances);
            let keccak_config = KeccakChip::configure_from_scratch(meta, instances);
            (native_config, keccak_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // Creating the chip.
            let native_gadget = NativeGadget::new_from_scratch(&config.0);
            let keccak_chip = KeccakChip::new_from_scratch(&config.1);

            // Assigning the input.
            let preimage =
                self.preimage.iter().map(|b| Value::known(b).cloned()).collect::<Vec<_>>();
            let preimage_assigned: Vec<AssignedByte<F>> =
                native_gadget.assign_many(&mut layouter, &preimage)?;

            // Computing the digest.
            let output = super::digest(
                &keccak_chip,
                &native_gadget,
                &mut layouter,
                &preimage_assigned,
            )?;

            // Assigning the digest bytes as public input.
            output.iter().try_for_each(|output_byte| {
                native_gadget.constrain_as_public_input(&mut layouter, output_byte)
            })?;

            keccak_chip.load_from_scratch(&mut layouter)?;
            native_gadget.load_from_scratch(&mut layouter)
        }
    }

    #[test]
    fn test_keccak_preimage() {
        const KECCAK_ABSORB_BYTES: usize = 136;
        let mut rng = ChaCha8Rng::from_entropy();

        // tested sizes
        let sizes = [
            0usize,
            1,
            100,
            KECCAK_ABSORB_BYTES - 2,
            KECCAK_ABSORB_BYTES - 1,
            KECCAK_ABSORB_BYTES,
            KECCAK_ABSORB_BYTES + 1,
            KECCAK_ABSORB_BYTES + 2,
            3 * KECCAK_ABSORB_BYTES,
            3 * KECCAK_ABSORB_BYTES + 1,
            3 * KECCAK_ABSORB_BYTES + 100,
            3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES - 2,
            3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES - 1,
            3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES,
            3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES + 1,
            3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES + 2,
            rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
            rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
            rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
            rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
            rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
            rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
            rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
        ];

        // Sample random inputs for the above sizes.
        let inputs = sizes
            .iter()
            .map(|&size| (0..size).map(|_| rng.gen()).collect::<Vec<u8>>())
            .collect::<Vec<_>>();

        // Generating the corresponding outputs (off-circuit).
        let test_vectors = inputs.iter().map(|input| {
            let result = {
                let mut hasher = KeccakCpu::new();
                hasher.update(input);
                hasher.finalize()
            };
            let output: [u8; KECCAK_SQUEEZE_BYTES] = result.into();
            (input, output)
        });

        // run the proof for each input/output pair
        test_vectors.for_each(|(preimage, digest)| {
            println!(
                "> [Keccak] Preimage test circuit: h({:?}) = {:?}",
                preimage, digest
            );
            let circuit = TestPreimage::<Fq> {
                preimage: preimage.clone(),
                _marker: PhantomData,
            };

            let k = PackedChip::<Fq>::min_k(preimage.len());

            let digest_converted = digest.iter().map(|b| Fq::from(*b as u64)).collect::<Vec<_>>();
            let prover = match MockProver::run(k, &circuit, vec![vec![], digest_converted]) {
                Ok(prover) => prover,
                Err(e) => panic!("{e:#?}"),
            };
            prover.assert_satisfied();
            println!("... test passed!")
        });
    }
}
