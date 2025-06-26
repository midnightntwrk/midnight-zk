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

//! Range-check instructions interface.

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::BigUint;

use crate::types::InnerValue;

/// The set of circuit instructions for range-check operations.
pub trait RangeCheckInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: InnerValue,
{
    /// Assigns an element that is immediately range-checked to be strictly
    /// lower than the given bound.
    /// This is potentially more efficient than composing [self.assign] with
    /// [self.assert_lower_than_fixed].
    ///
    ///
    /// The following example will make the circuit unsatisfiable
    /// ```should_panic
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// # use num_bigint::BigUint;
    /// chip.assign_lower_than_fixed(
    ///     &mut layouter,
    ///     Value::known(F::from(837)),
    ///     &BigUint::from(512u16),
    /// )?;
    /// # });
    /// ```
    fn assign_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Assigned::Element>,
        bound: &BigUint,
    ) -> Result<Assigned, Error>;

    /// Asserts that the given assigned element is in the range [0, bound).
    ///
    /// This function is potentially more efficient than calling
    /// [self.lower_than] and asserting that the output is `1`.
    fn assert_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        bound: &BigUint,
    ) -> Result<(), Error>;
}

#[cfg(test)]
pub mod tests {
    use std::{fmt::Debug, marker::PhantomData};

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand::{RngCore, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::AssignmentInstructions, testing_utils::FromScratch, types::InnerConstants,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug, Default)]
    struct TestCircuit<F, Assigned, Chip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        bound: BigUint,
        _marker: PhantomData<(F, Assigned, Chip)>,
    }

    impl<F, Assigned, Chip> Circuit<F> for TestCircuit<F, Assigned, Chip>
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Clone + Debug + InnerConstants,
        Chip: RangeCheckInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
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

            let x = chip.assign(&mut layouter, Value::known(self.x))?;
            chip.assert_lower_than_fixed(&mut layouter, &x, &self.bound)
        }
    }
    fn run<F, Assigned, Chip>(
        x: Assigned::Element,
        bound: BigUint,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Clone + Debug + InnerConstants,
        Chip: RangeCheckInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, Chip> {
            x,
            bound,
            _marker: PhantomData,
        };
        let log2_nb_rows = 10;
        let public_inputs = vec![vec![], vec![]];
        match MockProver::run(log2_nb_rows, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }

        if cost_model {
            circuit_to_json(log2_nb_rows, chip_name, op_name, 0, circuit);
        }
    }

    pub fn test_assert_lower_than_fixed<F, Assigned, Chip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField + From<u64>,
        Assigned: Clone + Debug + InnerConstants,
        Chip: RangeCheckInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let x = rng.next_u64();
        let m = u64::MAX;
        let mut cost_model = true;
        [
            (x, m, true),
            (m - 1, m, true),
            (m, m, false),
            (0, 1, true),
            (0, 2, true),
            (2, 1, false),
            (2, 2, false),
            (2, 3, true),
            (100, 99, false),
            (100, 100, false),
            (100, 101, true),
            ((1 << 20) - 1, 1 << 20, true),
            (1 << 20, 1 << 20, false),
        ]
        .into_iter()
        .for_each(|(x, bound, must_pass)| {
            run::<F, Assigned, Chip>(
                Assigned::Element::from(x),
                BigUint::from(bound),
                must_pass,
                cost_model,
                name,
                "assert_lower_than",
            );
            cost_model = false;
        })
    }
}
