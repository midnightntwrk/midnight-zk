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

//! Public input instructions interface.
//!
//! It provides functions for constraining public inputs.
//!
//! This trait is parametrized by the resulting `Assigned` type (a generic of
//! this trait that must implement [crate::types::InnerValue] and
//! [Instantiable]).

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::types::{AssignedNative, Instantiable};

/// The set of circuit instructions for constraining public inputs.
pub trait PublicInputInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: Instantiable<F>,
{
    /// Returns the cells associated with the given assigned value with the same
    /// format as a public input. This function is the in-circuit analog of
    /// [Instantiable::as_public_input].
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &Assigned,
    ) -> Result<Vec<AssignedNative<F>>, Error>;

    /// Constrains the given assigned value as a public input to the circuit.
    ///
    /// One can think of this function as the composition of
    /// [PublicInputInstructions::as_public_input] with the halo2 constrain
    /// instance mechanism.
    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &Assigned,
    ) -> Result<(), Error>;

    /// Same as [assign](crate::instructions::AssignmentInstructions::assign),
    /// but it immediately constrains the assigned value as a public input.
    /// This allows the implementer of this function to skip some in-circuit
    /// checks on the structure of the assigned value, which will be
    /// guaranteed to hold through the public input bind.
    ///
    /// # WARNING
    /// Declaring public inputs with this function may assume that the verifier
    /// will perform additional off-circuit checks on the public inputs.
    /// **DO NOT** use this function if you are not sure these checks are going
    /// to be enforced. Instead, you can safely use
    /// [assign](crate::instructions::AssignmentInstructions::assign)
    /// followed by
    /// [constrain_as_public_input](PublicInputInstructions::constrain_as_public_input).
    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Assigned::Element>,
    ) -> Result<Assigned, Error>;
}

#[cfg(test)]
pub mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand::{rngs::OsRng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::AssignmentInstructions,
        testing_utils::{FromScratch, Sampleable},
        types::{InnerConstants, InnerValue},
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    enum Operation {
        Constrain,
        Assign,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, Chip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        must_pass: bool,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, Chip)>,
    }

    impl<F, Assigned, Chip> Circuit<F> for TestCircuit<F, Assigned, Chip>
    where
        F: PrimeField,
        Assigned: Instantiable<F> + Sampleable,
        Chip: AssignmentInstructions<F, Assigned>
            + PublicInputInstructions<F, Assigned>
            + FromScratch<F>,
    {
        type Config = <Chip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            Chip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = Chip::new_from_scratch(&config);
            Chip::load_from_scratch(&mut layouter, &config);

            let x_val = if self.must_pass {
                self.x.clone()
            } else {
                Assigned::sample_inner(OsRng)
            };

            let x = match self.operation {
                Operation::Constrain => {
                    let x = chip.assign(&mut layouter, Value::known(x_val.clone()))?;
                    chip.constrain_as_public_input(&mut layouter, &x)?;
                    x
                }

                Operation::Assign => {
                    chip.assign_as_public_input(&mut layouter, Value::known(x_val.clone()))?
                }
            };

            if self.must_pass {
                chip.as_public_input(&mut layouter, &x)?
                    .iter()
                    .zip(Assigned::as_public_input(&x_val))
                    .for_each(|(xi, ci)| {
                        xi.value().map(|v| assert_eq!(*v, ci));
                    });
            }

            Ok(())
        }
    }

    fn run<F, Assigned, Chip>(
        x: &Assigned::Element,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: Instantiable<F> + Sampleable,
        Chip: AssignmentInstructions<F, Assigned>
            + PublicInputInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, Chip> {
            x: x.clone(),
            must_pass,
            operation,
            _marker: PhantomData,
        };

        let log2_nb_rows = 10;
        let pi = Assigned::as_public_input(x);

        match MockProver::run(log2_nb_rows, &circuit, vec![vec![], pi.clone()]) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }

        if cost_model {
            circuit_to_json(log2_nb_rows, chip_name, "public_inputs", pi.len(), circuit);
        }
    }

    pub fn test_public_inputs<F, Assigned, Chip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: Instantiable<F> + InnerConstants + Sampleable,
        Chip: AssignmentInstructions<F, Assigned>
            + PublicInputInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let mut cost_model = true;
        [
            Assigned::sample_inner(&mut rng),
            Assigned::inner_zero(),
            Assigned::inner_one(),
        ]
        .into_iter()
        .for_each(|x| {
            run::<F, Assigned, Chip>(&x, Operation::Constrain, true, cost_model, name);
            cost_model = false;
            run::<F, Assigned, Chip>(&x, Operation::Assign, true, cost_model, name);
            run::<F, Assigned, Chip>(&x, Operation::Constrain, false, cost_model, name);
            run::<F, Assigned, Chip>(&x, Operation::Assign, false, cost_model, name);
        });
    }
}
