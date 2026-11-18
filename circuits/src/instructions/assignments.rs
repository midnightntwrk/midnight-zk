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

//! Assignment instructions interface.
//!
//! It provides functions for assigning fixed and secret values into the
//! circuit.
//!
//! This trait is parametrized by the resulting `Assigned` type (a generic of
//! this trait that implements [InnerValue]). The assignment functions take an
//! `Assigned::Element` as input and return an `Assigned` value.

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::{CircuitField, types::InnerValue};

/// The set of circuit instructions for assignment operations.
pub trait AssignmentInstructions<F, Assigned>
where
    F: CircuitField,
    Assigned: InnerValue,
{
    /// Assigns an element as a private input to the circuit.
    ///
    /// In the following example, `chip` implements [AssignmentInstructions] for
    /// [AssignedNative](crate::types::AssignedNative).
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// // we load a secret variable into the circuit, only the prover may know its value
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    /// # });
    /// ```
    ///
    /// But `chip` can also implement [AssignmentInstructions] for
    /// [AssignedBit](crate::types::AssignedBit) or
    /// [AssignedByte](crate::types::AssignedByte) and other types.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let bit: AssignedBit<F> = chip.assign(&mut layouter, Value::known(true))?;
    ///
    /// let byte: AssignedByte<F> = chip.assign(&mut layouter, Value::known(42u8))?;
    /// # });
    /// ```
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Assigned::Element>,
    ) -> Result<Assigned, Error>;

    /// Assigns a fixed (constant) element.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// // we load a constant into the circuit, everyone knows the value of `k`
    /// let x: AssignedNative<F> = chip.assign_fixed(&mut layouter, F::ONE)?;
    ///
    /// // we can also assign fixed bits or bytes if the chip supports these types
    /// let bit: AssignedBit<F> = chip.assign_fixed(&mut layouter, false)?;
    /// let byte: AssignedByte<F> = chip.assign_fixed(&mut layouter, 255u8)?;
    /// # });
    /// ```
    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: Assigned::Element,
    ) -> Result<Assigned, Error>;

    /// The constant that the given element is known to encode at
    /// circuit-construction time, if any. `None` does not mean that the
    /// element is not constant.
    fn as_constant(&self, _x: &Assigned) -> Option<Assigned::Element> {
        None
    }

    /// Assigns several elements as private inputs to the circuit.
    ///
    /// This is potentially more efficient than calling
    /// [assign](AssignmentInstructions::assign) multiple times.
    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<Assigned::Element>],
    ) -> Result<Vec<Assigned>, Error> {
        values
            .iter()
            .map(|v| self.assign(layouter, v.clone()))
            .collect::<Result<Vec<Assigned>, Error>>()
    }

    /// Assigns several elements fixed values to the circuit.
    ///
    /// This is potentially more efficient than calling
    /// [assign_fixed](AssignmentInstructions::assign_fixed) multiple times.
    fn assign_many_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Assigned::Element],
    ) -> Result<Vec<Assigned>, Error> {
        values
            .iter()
            .map(|v| self.assign_fixed(layouter, v.clone()))
            .collect::<Result<Vec<Assigned>, Error>>()
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        testing_utils::{FromScratch, Sampleable},
        types::InnerConstants,
    };

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, Chip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        _marker: PhantomData<(F, Assigned, Chip)>,
    }

    impl<F, Assigned, Chip> Circuit<F> for TestCircuit<F, Assigned, Chip>
    where
        F: CircuitField,
        Assigned: InnerValue,
        Assigned::Element: PartialEq + std::fmt::Debug,
        Chip: AssignmentInstructions<F, Assigned> + FromScratch<F>,
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
            Chip::configure_from_scratch(
                meta,
                &mut vec![],
                &mut vec![],
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = Chip::new_from_scratch(&config);

            let fixed = chip.assign_fixed(&mut layouter, self.x.clone())?;
            assert_eq!(chip.as_constant(&fixed), Some(self.x.clone()));

            let witnessed = chip.assign(&mut layouter, Value::known(self.x.clone()))?;
            assert_eq!(chip.as_constant(&witnessed), None);

            chip.load_from_scratch(&mut layouter)
        }
    }

    pub fn test_as_constant<F, Assigned, Chip>(_name: &str)
    where
        F: CircuitField + FromUniformBytes<64> + Ord,
        Assigned: InnerConstants + Sampleable,
        Assigned::Element: PartialEq + std::fmt::Debug,
        Chip: AssignmentInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        [
            Assigned::sample_inner(&mut rng),
            Assigned::inner_zero(),
            Assigned::inner_one(),
        ]
        .into_iter()
        .for_each(|x| {
            let circuit = TestCircuit::<F, Assigned, Chip> {
                x,
                _marker: PhantomData,
            };
            MockProver::run(&circuit, vec![vec![], vec![]])
                .expect("synthesis failed")
                .assert_satisfied();
        });
    }
}
