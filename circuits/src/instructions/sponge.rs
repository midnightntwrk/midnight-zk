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

//! Sponge instructions interface.
//!
//! It provides functions for sponge-based hashing from a specified input type
//! to another output one.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::types::InnerValue;

/// The set of off-circuit instructions for sponge-based hashing operations.
pub trait SpongeCPU<Input, Output> {
    /// The assigned sponge state.
    type StateCPU;

    /// Initialize an empty sponge state.
    ///
    /// If an `input_len` is specified, this value must match the number of
    /// inputs that are then absorbed and only 1 call to `squeeze`
    /// will be allowed.
    fn init(input_len: Option<usize>) -> Self::StateCPU;

    /// Add the given input into the state (to be digested).
    fn absorb(state: &mut Self::StateCPU, inputs: &[Input]);

    /// Derive a new output from the state (by digesting it).
    fn squeeze(state: &mut Self::StateCPU) -> Output;
}

/// The set of in-circuit instructions for sponge-based hashing operations.
pub trait SpongeInstructions<F, Input, Output>: SpongeCPU<Input::Element, Output::Element>
where
    F: PrimeField,
    Input: InnerValue,
    Output: InnerValue,
{
    /// The assigned sponge state.
    type State;

    /// Initialize an empty sponge state.
    ///
    /// If an `input_len` is specified, this value must match the number of
    /// inputs that are then absorbed and only 1 call to `squeeze`
    /// will be allowed.
    fn init(
        &self,
        layouter: &mut impl Layouter<F>,
        input_len: Option<usize>,
    ) -> Result<Self::State, Error>;

    /// Add the given input into the state (to be digested).
    fn absorb(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut Self::State,
        inputs: &[Input],
    ) -> Result<(), Error>;

    /// Derive a new output from the state (by digesting it).
    fn squeeze(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut Self::State,
    ) -> Result<Output, Error>;
}

#[cfg(test)]
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
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::{FromScratch, Sampleable},
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug, Default)]
    struct TestCircuit<F, Input, Output, SpongeChip, AssignChip>
    where
        Input: InnerValue,
        Output: InnerValue,
    {
        inputs: Vec<Vec<Input::Element>>,
        sequence: Vec<(usize, usize)>,
        _marker: PhantomData<(F, Output, SpongeChip, AssignChip)>,
    }

    impl<F, Input, Output, SpongeChip, AssignChip> Circuit<F>
        for TestCircuit<F, Input, Output, SpongeChip, AssignChip>
    where
        F: PrimeField,
        Input: InnerValue,
        Output: InnerValue,
        SpongeChip: SpongeInstructions<F, Input, Output> + FromScratch<F>,
        AssignChip:
            AssignmentInstructions<F, Input> + AssertionInstructions<F, Output> + FromScratch<F>,
    {
        type Config = (
            <SpongeChip as FromScratch<F>>::Config,
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
                SpongeChip::configure_from_scratch(meta, &instance_columns),
                AssignChip::configure_from_scratch(meta, &instance_columns),
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = SpongeChip::new_from_scratch(&config.0);
            SpongeChip::load_from_scratch(&mut layouter, &config.0);

            let assign_chip = AssignChip::new_from_scratch(&config.1);
            AssignChip::load_from_scratch(&mut layouter, &config.1);

            let mut input_idx = 0;
            let mut state = chip.init(&mut layouter, None)?;
            let mut cpu_state =
                <SpongeChip as SpongeCPU<Input::Element, Output::Element>>::init(None);

            for step in self.sequence.iter() {
                for _nr_absorb in 0..step.0 {
                    let input_vec = self.inputs[input_idx]
                        .iter()
                        .map(|input| Value::known(input.clone()))
                        .collect::<Vec<_>>();
                    let inputs = assign_chip.assign_many(&mut layouter, &input_vec)?;

                    chip.absorb(&mut layouter, &mut state, &inputs)?;
                    <SpongeChip as SpongeCPU<Input::Element, Output::Element>>::absorb(
                        &mut cpu_state,
                        &self.inputs[input_idx],
                    );

                    input_idx += 1;
                }

                for _nr_squeeze in 0..step.1 {
                    let out = chip.squeeze(&mut layouter, &mut state)?;
                    let expected_out =
                        <SpongeChip as SpongeCPU<Input::Element, Output::Element>>::squeeze(
                            &mut cpu_state,
                        );
                    assign_chip.assert_equal_to_fixed(&mut layouter, &out, expected_out)?;
                }
            }

            Ok(())
        }
    }

    pub fn test_sponge<F, Input, Output, SpongeChip, AssignChip>(
        cost_model: bool,
        chip_name: &str,
        k: u32,
    ) where
        F: PrimeField + ff::FromUniformBytes<64> + Ord,
        Input: InnerValue + Sampleable,
        Output: InnerValue,
        SpongeChip: SpongeInstructions<F, Input, Output> + FromScratch<F>,
        AssignChip:
            AssignmentInstructions<F, Input> + AssertionInstructions<F, Output> + FromScratch<F>,
    {
        // Create a random number generator
        let mut rng = ChaCha12Rng::seed_from_u64(0xf007ba11);

        // The sequence consists of the number of (absorb, squeeze, input_size) calls.
        // Between each call, the hasher is not re-initialised. We test
        let sequence = [(1, 1), (0, 1), (3, 3), (7, 2)];

        let nb_absorb_calls = sequence.iter().map(|s| s.0).sum();
        let inputs = (0..nb_absorb_calls).map(|_| {
            let random_size: usize = rng.gen_range(1..10);
            (0..random_size)
                .map(|_| Input::sample_inner(&mut rng))
                .collect::<Vec<_>>()
        });

        let circuit = TestCircuit::<F, Input, Output, SpongeChip, AssignChip> {
            inputs: inputs.collect(),
            sequence: sequence.to_vec(),
            _marker: PhantomData,
        };

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(k, chip_name, "sponge", 0, circuit);
        }
    }
}
