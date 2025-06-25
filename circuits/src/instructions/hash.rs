//! Hashing instructions interface.
//!
//! It provides functions for (in-circuit) hashing from a specified input type
//! to another output one.

use std::fmt::Debug;

use ff::PrimeField;
use halo2_proofs::{circuit::Layouter, plonk::Error};

use crate::types::InnerValue;

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

#[cfg(test)]
pub mod tests {
    use std::{fmt::Debug, marker::PhantomData};

    use halo2_proofs::{
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
            let instance_column = meta.instance_column();
            (
                HashChip::configure_from_scratch(meta, &instance_column),
                AssignChip::configure_from_scratch(meta, &instance_column),
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = HashChip::new_from_scratch(&config.0);
            HashChip::load_from_scratch(&mut layouter, &config.0);

            let assign_chip = AssignChip::new_from_scratch(&config.1);
            AssignChip::load_from_scratch(&mut layouter, &config.1);

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

            Ok(())
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

        MockProver::run(k, &circuit, vec![vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(k, chip_name, "hash", 0, circuit);
        }
    }
}
