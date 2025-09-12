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

//! Hashing instructions interface.
//!
//! It provides functions for (in-circuit) hashing from a specified input type
//! to another output one.

use std::fmt::Debug;

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::types::{AssignedVector, InnerValue, Vectorizable};

/// The set of off-circuit instructions for hashing operations.
pub trait HashCPU<Input, Output>: Clone + Debug {
    /// Hash the given input into the designated output type.
    fn hash(inputs: &[Input]) -> Output;
}

/// The set of circuit instructions for hashing operations.
pub trait HashInstructions<F, Input, Output>: HashCPU<Input::Element, Output::Element>
where
    F: PrimeField,
    Input: InnerValue,
    Output: InnerValue,
{
    /// Hash the given input into the designated output type.
    fn hash(&self, layouter: &mut impl Layouter<F>, inputs: &[Input]) -> Result<Output, Error>;
}

/// The set of circuit instructions for variable length hashing operations.
pub trait VarHashInstructions<F, const MAX_LEN: usize, Input, Output, const A: usize>:
    HashCPU<<Input as InnerValue>::Element, Output::Element>
where
    F: PrimeField,
    Input: Vectorizable,
    Output: InnerValue,
{
    /// Hash the given input into the designated output type.
    fn varhash(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &AssignedVector<F, Input, MAX_LEN, A>,
    ) -> Result<Output, Error>;
}

#[cfg(test)]
#[allow(missing_docs)]
pub mod tests {
    use std::{fmt::Debug, marker::PhantomData};

    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha12Rng;

    use super::*;
    use crate::{
        field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::{FromScratch, Sampleable},
        utils::circuit_modeling::circuit_to_json,
        vec::vector_gadget::VectorGadget,
    };

    #[derive(Clone, Debug, Default)]
    struct TestCircuit<F, Input, Output, HashChip, AssignChip>
    where
        Input: InnerValue,
        Output: InnerValue,
    {
        inputs: Vec<Vec<Input::Element>>,
        _marker: PhantomData<(F, Output, HashChip, AssignChip)>,
    }

    impl<F, Input, Output, HashChip, AssignChip> Circuit<F>
        for TestCircuit<F, Input, Output, HashChip, AssignChip>
    where
        F: PrimeField,
        Input: InnerValue,
        Output: InnerValue,
        HashChip: HashInstructions<F, Input, Output> + FromScratch<F>,
        AssignChip:
            AssignmentInstructions<F, Input> + AssertionInstructions<F, Output> + FromScratch<F>,
    {
        type Config = (
            <HashChip as FromScratch<F>>::Config,
            <AssignChip as FromScratch<F>>::Config,
        );
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            let instance_columns = [committed_instance_column, instance_column];
            (
                HashChip::configure_from_scratch(meta, &instance_columns),
                AssignChip::configure_from_scratch(meta, &instance_columns),
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = HashChip::new_from_scratch(&config.0);
            let assign_chip = AssignChip::new_from_scratch(&config.1);

            for input in self.inputs.iter() {
                let vec_input = input
                    .iter()
                    .map(|input| Value::known(input.clone()))
                    .collect::<Vec<_>>();
                let inputs = assign_chip.assign_many(&mut layouter, &vec_input)?;
                let expected_output =
                    <HashChip as HashCPU<Input::Element, Output::Element>>::hash(input);

                let output = chip.hash(&mut layouter, &inputs)?;
                assign_chip.assert_equal_to_fixed(&mut layouter, &output, expected_output)?;
            }

            chip.load_from_scratch(&mut layouter)?;
            assign_chip.load_from_scratch(&mut layouter)
        }
    }

    pub fn test_hash<F, Input, Output, HashChip, AssignChip>(
        cost_model: bool,
        chip_name: &str,
        k: u32,
    ) where
        F: PrimeField + ff::FromUniformBytes<64> + Ord,
        Input: InnerValue + Sampleable,
        Output: InnerValue,
        HashChip: HashInstructions<F, Input, Output> + FromScratch<F>,
        AssignChip:
            AssignmentInstructions<F, Input> + AssertionInstructions<F, Output> + FromScratch<F>,
    {
        // Create a random number generator
        let mut rng = ChaCha12Rng::seed_from_u64(0xf007ba11);

        let inputs = (0..10).map(|_| {
            let random_size: usize = rng.gen_range(1..10);
            (0..random_size)
                .map(|_| Input::sample_inner(&mut rng))
                .collect::<Vec<_>>()
        });

        let circuit = TestCircuit::<F, Input, Output, HashChip, AssignChip> {
            inputs: inputs.collect(),
            _marker: PhantomData,
        };

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(k, chip_name, "hash", 0, circuit);
        }
    }

    type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

    #[derive(Clone, Debug, Default)]
    struct TestVarHashCircuit<F, Input, Output, VarHashChip, const M: usize, const A: usize>
    where
        Input: Vectorizable,
        Output: InnerValue,
    {
        input: Vec<Input::Element>, // TODO This should be Value<>
        _marker: PhantomData<(F, Output, VarHashChip)>,
    }

    impl<F, Input, Output, VarHashChip, const M: usize, const A: usize> Circuit<F>
        for TestVarHashCircuit<F, Input, Output, VarHashChip, M, A>
    where
        F: PrimeField,
        Input: Vectorizable,
        Output: InnerValue,
        VarHashChip: VarHashInstructions<F, M, Input, Output, A> + FromScratch<F>,
        VectorGadget<F>: AssignmentInstructions<F, AssignedVector<F, Input, M, A>>,
        NG<F>: AssignmentInstructions<F, Input> + AssertionInstructions<F, Output>,
    {
        type Config = (
            <VarHashChip as FromScratch<F>>::Config,
            <VectorGadget<F> as FromScratch<F>>::Config,
        );
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            let instance_columns = [committed_instance_column, instance_column];
            (
                VarHashChip::configure_from_scratch(meta, &instance_columns),
                VectorGadget::configure_from_scratch(meta, &instance_columns),
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = VarHashChip::new_from_scratch(&config.0);
            let ng = <NG<F>>::new_from_scratch(&config.1);

            let vg = VectorGadget::new(&ng);

            let assigned_input: AssignedVector<_, _, M, A> =
                vg.assign(&mut layouter, Value::known(self.input.clone()))?;
            let expected_output =
                <VarHashChip as HashCPU<Input::Element, Output::Element>>::hash(&self.input);

            let output = chip.varhash(&mut layouter, &assigned_input)?;
            ng.assert_equal_to_fixed(&mut layouter, &output, expected_output)?;

            chip.load_from_scratch(&mut layouter)?;
            ng.load_from_scratch(&mut layouter)
        }
    }

    pub fn test_varhash<F, Input, Output, VarHashChip, const M: usize, const A: usize>(
        cost_model: bool,
        chip_name: &str,
        size: usize,
        k: u32,
    ) where
        F: PrimeField + ff::FromUniformBytes<64> + Ord,
        Input: Vectorizable + Sampleable,
        Output: InnerValue,
        VarHashChip: VarHashInstructions<F, M, Input, Output, A> + FromScratch<F>,
        VectorGadget<F>: AssignmentInstructions<F, AssignedVector<F, Input, M, A>>,
        NG<F>: AssignmentInstructions<F, Input> + AssertionInstructions<F, Output>,
    {
        let mut rng = ChaCha12Rng::seed_from_u64(0xf007ba11);

        let input = (0..size)
            .map(|_| Input::sample_inner(&mut rng))
            .collect::<Vec<_>>();

        let circuit = TestVarHashCircuit::<F, Input, Output, VarHashChip, M, A> {
            input,
            _marker: PhantomData,
        };

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(k, chip_name, "hash", 0, circuit);
        }
    }
}
