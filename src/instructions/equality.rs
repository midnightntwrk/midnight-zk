//! Equality instructions interface.
//!
//! It provides functions for checking (dis)equality of assigned values in the
//! circuit.
//!
//! This trait is parametrized by a generic `Assigned` (required to implement
//! [InnerValue]) which defines the type over which we check equality.

use ff::PrimeField;
use halo2_proofs::{circuit::Layouter, plonk::ErrorFront as Error};

use crate::types::{AssignedBit, InnerValue};

/// The set of circuit instructions for equality operations.
pub trait EqualityInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: InnerValue,
{
    /// Returns `1` if the elements are equal, returns `0` otherwise.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::from(1)))?;
    /// let y: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::from(2)))?;
    ///
    /// let x_equals_y = chip.is_equal(&mut layouter, &x, &y)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &x_equals_y, Bit(false))?;
    ///
    /// let x_equals_x = chip.is_equal(&mut layouter, &x, &x)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &x_equals_x, Bit(true))?;
    /// # });
    /// ```
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<AssignedBit<F>, Error>;

    /// Returns `1` iff the given element equals the given constant.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ONE))?;
    ///
    /// let x_equals_2 = chip.is_equal_to_fixed(&mut layouter, &x, F::from(2))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &x_equals_2, Bit(false))?;
    ///
    /// let x_equals_1 = chip.is_equal_to_fixed(&mut layouter, &x, F::ONE)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &x_equals_1, Bit(true))?;
    /// # });
    /// ```
    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        constant: Assigned::Element,
    ) -> Result<AssignedBit<F>, Error>;
}

#[cfg(test)]
pub mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand::rngs::OsRng;

    use super::*;
    use crate::{
        instructions::AssignmentInstructions,
        testing_utils::{FromScratch, Sampleable},
        types::{AssignedNative, InnerConstants},
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug, Default)]
    enum Operation {
        #[default]
        Equal,
        EqToFixed,
    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit<F, Assigned, EqualityChip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        y: Assigned::Element,
        expected: bool,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, EqualityChip)>,
    }

    impl<F, Assigned, EqualityChip> Circuit<F> for TestCircuit<F, Assigned, EqualityChip>
    where
        F: PrimeField,
        Assigned: InnerValue,
        EqualityChip: EqualityInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        type Config = <EqualityChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_column = meta.instance_column();
            let constants_column = meta.fixed_column();
            meta.enable_constant(constants_column);
            EqualityChip::configure_from_scratch(meta, &instance_column)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = EqualityChip::new_from_scratch(&config);
            EqualityChip::load_from_scratch(&mut layouter, &config);

            let x = chip.assign_fixed(&mut layouter, self.x.clone())?;
            let y = chip.assign_fixed(&mut layouter, self.y.clone())?;
            let res = match self.operation {
                Operation::Equal => chip.is_equal(&mut layouter, &x, &y)?,
                Operation::EqToFixed => {
                    chip.is_equal_to_fixed(&mut layouter, &x, self.y.clone())?
                }
            };
            let res_as_value: AssignedNative<F> = res.into();
            layouter.assign_region(
                || "assert contains fixed",
                |mut region| {
                    region.constrain_constant(
                        res_as_value.cell(),
                        if self.expected { F::ONE } else { F::ZERO },
                    )
                },
            )
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run<F, Assigned, EqualityChip>(
        x: &Assigned::Element,
        y: &Assigned::Element,
        expected: bool,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        EqualityChip: EqualityInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, EqualityChip> {
            x: x.clone(),
            y: y.clone(),
            expected,
            operation,
            _marker: PhantomData,
        };
        // We need to use 11 because the lookup table of the
        // native ecc has size 2^10
        let log2_nb_rows = 11;
        let public_inputs = vec![vec![]];
        match MockProver::run(log2_nb_rows, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }

        if cost_model {
            circuit_to_json(log2_nb_rows, chip_name, op_name, &[&[]], circuit);
        }
    }

    pub fn test_is_equal<F, Assigned, EqualityChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerConstants + Sampleable,
        EqualityChip: EqualityInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let zero = Assigned::inner_zero();
        let one = Assigned::inner_one();
        let r = Assigned::sample_inner(OsRng);
        let s = Assigned::sample_inner(OsRng);
        let mut cost_model = true;
        [
            (&zero, &zero, true),
            (&one, &one, true),
            (&zero, &one, false),
            (&r, &r, true),
            (&r, &s, false),
        ]
        .iter()
        .for_each(|(x, y, equal)| {
            run::<F, Assigned, EqualityChip>(
                x,
                y,
                *equal,
                Operation::Equal,
                true,
                cost_model,
                name,
                "is_equal",
            );
            run::<F, Assigned, EqualityChip>(
                x,
                y,
                *equal,
                Operation::EqToFixed,
                true,
                cost_model,
                name,
                "is_equal_to_fixed",
            );
            cost_model = false;
            run::<F, Assigned, EqualityChip>(x, y, !equal, Operation::Equal, false, false, "", "");
            run::<F, Assigned, EqualityChip>(
                x,
                y,
                !equal,
                Operation::EqToFixed,
                false,
                false,
                "",
                "",
            );
        });
    }
}
