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

//! Import of the blake2b hash implementation from [Eryx](https://github.com/eryxcoop).

#[cfg(test)]
use blake2b::blake2b::blake2b_chip::Blake2bConfig;
#[cfg(test)]
use blake2b::blake2b::NB_BLAKE2B_ADVICE_COLS;
use blake2b::{blake2b::blake2b_chip::Blake2bChip, types::byte::Byte};
use ff::PrimeField;
#[cfg(test)]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};
use midnight_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};

#[cfg(test)]
use crate::testing_utils::FromScratch;
use crate::{
    external::{unsafe_convert_to_bytes, NG},
    field::AssignedNative,
    types::AssignedByte,
};

/// Blake2b hash.
pub fn hash<F: PrimeField>(
    chip: &Blake2bChip<F>,
    native_gadget: &NG<F>,
    layouter: &mut impl Layouter<F>,
    input: &[AssignedByte<F>],
    key: &[AssignedByte<F>],
    output_size: usize,
) -> Result<[AssignedByte<F>; 64], Error> {
    let input = &input.iter().map(AssignedNative::from).collect::<Vec<_>>();
    let key = &key.iter().map(AssignedNative::from).collect::<Vec<_>>();
    let output = &chip.hash(layouter, input, key, output_size)?.map(AssignedCell::<Byte, F>::from);
    Ok(unsafe_convert_to_bytes(layouter, native_gadget, output)?.try_into().unwrap())
}

#[cfg(test)]
impl<F: PrimeField> FromScratch<F> for Blake2bChip<F> {
    type Config = Blake2bConfig;

    fn new_from_scratch(config: &Self::Config) -> Self {
        Blake2bChip::new(config)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let advice_cols =
            (0..NB_BLAKE2B_ADVICE_COLS).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let constant_column = meta.fixed_column();

        Blake2bChip::configure(
            meta,
            constant_column,
            advice_cols[0],
            advice_cols[1..NB_BLAKE2B_ADVICE_COLS].try_into().unwrap(),
            instance_columns[1],
        )
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.load(layouter)
    }
}

// A small subset of the preimage tests from the Blake2b repo, applied to our
// wrapper.
#[cfg(test)]
mod test {
    use blake2b::blake2b::blake2b_chip::{Blake2bChip, Blake2bConfig};
    use ff::PrimeField;
    use halo2curves::bn256::Fr;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };

    use crate::{
        external::unsafe_convert_to_bytes,
        field::{decomposition::chip::P2RDecompositionConfig, NativeGadget},
        instructions::{AssignmentInstructions, PublicInputInstructions},
        testing_utils::FromScratch,
    };

    struct TestPreimage<F: PrimeField> {
        preimage: Vec<Value<F>>,
        key: Vec<Value<F>>,
        output_size: usize,
    }

    impl<F: PrimeField> Circuit<F> for TestPreimage<F> {
        // we use an instance column to witness the expected result
        type Config = (P2RDecompositionConfig, Blake2bConfig);
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
            let blake2b_config = Blake2bChip::configure_from_scratch(meta, instances);
            (native_config, blake2b_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // Creating the chip.
            let native_gadget = NativeGadget::new_from_scratch(&config.0);
            let blake2b_chip = Blake2bChip::new_from_scratch(&config.1);

            // Assigning the input.
            let preimage = native_gadget.assign_many(&mut layouter, &self.preimage)?;
            let preimage = unsafe_convert_to_bytes(&mut layouter, &native_gadget, &preimage)?;
            let key = native_gadget.assign_many(&mut layouter, &self.key)?;
            let key = unsafe_convert_to_bytes(&mut layouter, &native_gadget, &key)?;

            // Computing the digest.
            let output = super::hash(
                &blake2b_chip,
                &native_gadget,
                &mut layouter,
                &preimage,
                &key,
                self.output_size,
            )?;

            // Assigning the hash bytes as public input.
            output.iter().try_for_each(|output_byte| {
                native_gadget.constrain_as_public_input(&mut layouter, output_byte)
            })?;

            blake2b_chip.load_from_scratch(&mut layouter)?;
            native_gadget.load_from_scratch(&mut layouter)
        }
    }

    /// Interpretation of test vectors as actual data. Returns the circuit and
    /// the expected output.
    fn extract_test_vector(input: &str, key: &str, output: &str) -> (TestPreimage<Fr>, [Fr; 64]) {
        let param =
            blake2b::usage_utils::circuit_runner::CircuitRunner::prepare_parameters_for_test(
                &input.to_string(),
                &key.to_string(),
                &output.to_string(),
            );
        (
            TestPreimage {
                preimage: param.0,
                key: param.2,
                output_size: param.5,
            },
            param.4,
        )
    }

    #[test]
    fn test_blake2b_preimage() {
        let test_vectors = TEST_VECTORS.map(|(a, b, c)| extract_test_vector(a, b, c));

        // run the proof for each input/output pair
        test_vectors.iter().zip(TEST_VECTORS).for_each(
            |((circuit, output), (printable_preimage, printable_key, printable_output))| {
                println!(
                    "> [Blake2b] Preimage test circuit: h({:?}, {:?}) = {:?}",
                    printable_preimage, printable_key, printable_output
                );
                let circuit = TestPreimage::<Fr> {
                    preimage: circuit.preimage.clone(),
                    key: circuit.key.clone(),
                    output_size: circuit.output_size,
                };

                let prover = match MockProver::run(17, &circuit, vec![vec![], output.to_vec()]) {
                    Ok(prover) => prover,
                    Err(e) => panic!("{e:#?}"),
                };
                prover.assert_satisfied();
                println!("... test passed!")
            },
        );
    }

    /// A small random selection from test vectors (input, key, output) from the
    /// blake2b repo.
    const TEST_VECTORS: [(&str, &str, &str); 11] = [
        // 0
        ("", "", "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"),

        // 1
        ("00010203040506070809", "", "29102511d749db3cc9b4e335fa1f5e8faca8421d558f6a3f3321d50d044a248ba595cfc3efd3d2adc97334da732413f5cbf4751c362ba1d53862ac1e8dabeee8"),

        // 2
        ("000102030405060708090a0b0c", "", "dea9101cac62b8f6a3c650f90eea5bfae2653a4eafd63a6d1f0f132db9e4f2b1b662432ec85b17bcac41e775637881f6aab38dd66dcbd080f0990a7a6e9854fe"),

        // 3
        ("000102030405060708090a0b0c0d", "", "441ffaa08cd79dff4afc9b9e5b5620eec086730c25f661b1d6fbfbd1cec3148dd72258c65641f2fca5eb155fadbcabb13c6e21dc11faf72c2a281b7d56145f19"),

        // 4
        ("000102030405060708090a0b0c0d0e", "", "444b240fe3ed86d0e2ef4ce7d851edde22155582aa0914797b726cd058b6f45932e0e129516876527b1dd88fc66d7119f4ab3bed93a61a0e2d2d2aeac336d958"),

        // 5
        ("000102030405060708090a0b0c0d0e0f", "", "bfbabbef45554ccfa0dc83752a19cc35d5920956b301d558d772282bc867009168e9e98606bb5ba73a385de5749228c925a85019b71f72fe29b3cd37ca52efe6"),

        // 6
        ("000102030405060708090a0b0c0d0e", "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", "6fbf31b45ab0c0b8dad1c0f5f4061379912dde5aa922099a030b725c73346c524291adef89d2f6fd8dfcda6d07dad811a9314536c2915ed45da34947e83de34e"),

        // 7
        ("000102030405060708090a0b0c0d0e0f", "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", "a0c65bddde8adef57282b04b11e7bc8aab105b99231b750c021f4a735cb1bcfab87553bba3abb0c3e64a0b6955285185a0bd35fb8cfde557329bebb1f629ee93"),

        // 8
        ("000102030405060708090a0b0c0d0e0f10", "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", "f99d815550558e81eca2f96718aed10d86f3f1cfb675cce06b0eff02f617c5a42c5aa760270f2679da2677c5aeb94f1142277f21c7f79f3c4f0cce4ed8ee62b1"),

        // 9
        ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60616263", "", "6f793eb4374a48b0775acaf9adcf8e45e54270c9475f004ad8d5973e2aca52747ff4ed04ae967275b9f9eb0e1ff75fb4f794fa8be9add7a41304868d103fab10"),

        // 10
        ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60616263646566676869", "", "467a33fbadf5ebc52596ef86aaaefc6faba8ee651b1ce04de368a03a5a9040ef2835e00adb09abb3fbd2bce818a2413d0b0253b5bda4fc5b2f6f85f3fd5b55f2"),
    ];
}
