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

//! Hash to curve instructions interface
//!
//! The trait is parametrised by the curve, `C`, where the hash is mapped.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use super::EccInstructions;
use crate::{ecc::curves::CircuitCurve, types::InnerValue};

/// Off-circuit instructions for hashing a given input of type `Input` into a
/// point of curve `C`.
pub trait HashToCurveCPU<C, Input>
where
    C: CircuitCurve,
{
    /// Hash the given input into a point on the curve.
    fn hash_to_curve(inputs: &[Input]) -> C::CryptographicGroup;
}

/// In-circuit instructions for hashing a given input of type `Input` into a
/// point of curve `C`, emulated over native field `F`.
pub trait HashToCurveInstructions<F, C, Input, E>: HashToCurveCPU<C, Input::Element>
where
    F: PrimeField,
    C: CircuitCurve,
    Input: InnerValue,
    E: EccInstructions<F, C>,
{
    /// Hash the given input into a point on the curve.
    fn hash_to_curve(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[Input],
    ) -> Result<E::Point, Error>;

    /// A set of ECC instructions for C.
    fn ecc_chip(&self) -> &E;
}

#[cfg(test)]
#[allow(missing_docs)]
pub mod tests {
    use std::marker::PhantomData;

    use ff::{FromUniformBytes, PrimeField};
    use group::Group;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::{HashToCurveCPU, HashToCurveInstructions};
    use crate::{
        ecc::curves::CircuitCurve,
        instructions::{AssignmentInstructions, EccInstructions},
        testing_utils::{FromScratch, Sampleable},
        types::{InnerConstants, InnerValue},
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    struct TestCircuit<F, C, I, EccChip, InputsChip, HashToCurveChip>
    where
        I: InnerValue,
        C: CircuitCurve,
    {
        input: Value<I::Element>,
        expected: C::CryptographicGroup,
        _marker: PhantomData<(F, EccChip, InputsChip, HashToCurveChip)>,
    }

    impl<F, C, I, EccChip, InputsChip, HashToCurveChip> Circuit<F>
        for TestCircuit<F, C, I, EccChip, InputsChip, HashToCurveChip>
    where
        F: PrimeField,
        C: CircuitCurve,
        I: InnerValue,
        I::Element: Clone,
        EccChip: EccInstructions<F, C>,
        InputsChip: AssignmentInstructions<F, I> + FromScratch<F>,
        HashToCurveChip: HashToCurveInstructions<F, C, I, EccChip> + FromScratch<F>,
    {
        type Config = (
            <InputsChip as FromScratch<F>>::Config,
            <HashToCurveChip as FromScratch<F>>::Config,
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
                InputsChip::configure_from_scratch(meta, &instance_columns),
                HashToCurveChip::configure_from_scratch(meta, &instance_columns),
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let inputs_chip = InputsChip::new_from_scratch(&config.0);
            let htc_chip = HashToCurveChip::new_from_scratch(&config.1);

            InputsChip::load_from_scratch(&mut layouter, &config.0);
            HashToCurveChip::load_from_scratch(&mut layouter, &config.1);

            let input = inputs_chip.assign(&mut layouter, self.input.clone())?;
            let res = htc_chip.hash_to_curve(&mut layouter, &[input])?;
            htc_chip
                .ecc_chip()
                .assert_equal_to_fixed(&mut layouter, &res, self.expected)
        }
    }

    fn run<F, C, I, EccChip, InputsChip, HashToCurveChip>(
        input: &I::Element,
        expected: C::CryptographicGroup,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        I: InnerValue,
        I::Element: Clone,
        EccChip: EccInstructions<F, C>,
        InputsChip: AssignmentInstructions<F, I> + FromScratch<F>,
        HashToCurveChip: HashToCurveInstructions<F, C, I, EccChip> + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, C, I, EccChip, InputsChip, HashToCurveChip> {
            input: Value::known(input.clone()),
            expected,
            _marker: PhantomData,
        };
        let log2_nb_rows = 11;
        let public_inputs = vec![vec![], vec![]];
        match MockProver::run(log2_nb_rows, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }

        if cost_model {
            circuit_to_json(log2_nb_rows, chip_name, "hash_to_curve", 0, circuit);
        }
    }

    pub fn test_hash_to_curve<F, C, I, EccChip, InputsChip, HashToCurveChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        I: InnerConstants + Sampleable,
        I::Element: Clone,
        EccChip: EccInstructions<F, C>,
        InputsChip: AssignmentInstructions<F, I> + FromScratch<F>,
        HashToCurveChip: HashToCurveInstructions<F, C, I, EccChip> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        [I::sample_inner(&mut rng), I::inner_zero(), I::inner_one()]
            .iter()
            .for_each(|input| {
                let expected =
                    <HashToCurveChip as HashToCurveCPU<C, I::Element>>::hash_to_curve(&[
                        input.clone()
                    ]);
                let wrong = C::CryptographicGroup::identity();
                run::<F, C, I, EccChip, InputsChip, HashToCurveChip>(
                    input, expected, true, true, name,
                );
                run::<F, C, I, EccChip, InputsChip, HashToCurveChip>(
                    input, wrong, false, false, name,
                );
            })
    }
}
