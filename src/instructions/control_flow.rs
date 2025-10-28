//! Control flow instructions interface.
//!
//! It provides functions for conditionally selecting and asserting equality a
//! pair of `Assigned` elements.
//!
//! The trait is parametrized by `Assigned` type.

use ff::PrimeField;
use halo2_proofs::{circuit::Layouter, plonk::ErrorFront as Error};

use super::AssertionInstructions;
use crate::types::{AssignedBit, InnerValue};

/// The set of circuit instructions for control flow operations.
pub trait ControlFlowInstructions<F: PrimeField, Assigned>:
    AssertionInstructions<F, Assigned>
where
    Assigned: InnerValue,
{
    /// Returns `x` if `cond = true` and `y` otherwise.
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    /// let y: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ONE))?;
    /// let cond: AssignedBit<F> = chip.assign(&mut layouter, Value::known(Bit(true)))?;
    ///
    /// let choice = chip.select(&mut layouter, &cond, &x, &y)?;
    /// chip.assert_equal(&mut layouter, &choice, &x)?;
    /// # });
    /// ```
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<Assigned, Error>;

    /// Equality assertion only if `cond` is set to `1`.
    fn cond_assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<(), Error> {
        let x = self.select(layouter, cond, x, y)?;
        self.assert_equal(layouter, &x, y)
    }

    /// Swaps two elements `x` and `y` only if `cond` is set to `1`.
    fn cond_swap(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<(Assigned, Assigned), Error> {
        let new_x = self.select(layouter, cond, y, x)?;
        let new_y = self.select(layouter, cond, x, y)?;

        Ok((new_x, new_y))
    }
}

#[cfg(test)]
pub mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, Column, ConstraintSystem, Fixed},
    };
    use rand::rngs::OsRng;

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::{FromScratch, Sampleable},
        types::InnerValue,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug, Default)]
    enum Operation {
        #[default]
        Select,
        CondAssertEqual,
    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit<F, Assigned, ControlFlowChip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        y: Assigned::Element,
        cond: bool,
        expected: Assigned::Element,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, ControlFlowChip)>,
    }

    impl<F, Assigned, ControlFlowChip> Circuit<F> for TestCircuit<F, Assigned, ControlFlowChip>
    where
        F: PrimeField,
        Assigned: InnerValue,
        Assigned::Element: Default,
        ControlFlowChip: ControlFlowInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        type Config = (<ControlFlowChip as FromScratch<F>>::Config, Column<Fixed>);
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_column = meta.instance_column();
            let fixed_column = meta.fixed_column();
            meta.enable_equality(fixed_column);
            (
                ControlFlowChip::configure_from_scratch(meta, &instance_column),
                fixed_column,
            )
        }

        fn synthesize(
            &self,
            (config, fixed_column): Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = ControlFlowChip::new_from_scratch(&config);
            ControlFlowChip::load_from_scratch(&mut layouter, &config);

            let x = chip.assign_fixed(&mut layouter, self.x.clone())?;
            let y = chip.assign_fixed(&mut layouter, self.y.clone())?;
            let cond_value = layouter.assign_region(
                || "Assign fixed",
                |mut region| {
                    region.assign_fixed(
                        || "cond value",
                        fixed_column,
                        0,
                        || Value::known(if self.cond { F::ONE } else { F::ZERO }),
                    )
                },
            )?;

            let cond = AssignedBit(cond_value);

            match self.operation {
                Operation::Select => {
                    let res = chip.select(&mut layouter, &cond, &x, &y)?;
                    chip.assert_equal_to_fixed(&mut layouter, &res, self.expected.clone())
                }
                Operation::CondAssertEqual => chip.cond_assert_equal(&mut layouter, &cond, &x, &y),
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run<F, Assigned, ControlFlowChip>(
        x: &Assigned::Element,
        y: &Assigned::Element,
        cond: bool,
        expected: &Assigned::Element,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default,
        ControlFlowChip: ControlFlowInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, ControlFlowChip> {
            x: x.clone(),
            y: y.clone(),
            cond,
            expected: expected.clone(),
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

    pub fn test_select<F, Assigned, ControlFlowChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue + Sampleable,
        Assigned::Element: Default,
        ControlFlowChip: ControlFlowInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let x = Assigned::sample_inner(OsRng);
        let y = Assigned::sample_inner(OsRng);
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            true,
            &x,
            Operation::Select,
            true,
            true,
            name,
            "select",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            false,
            &y,
            Operation::Select,
            true,
            false,
            "",
            "",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            true,
            &y,
            Operation::Select,
            false,
            false,
            "",
            "",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            false,
            &x,
            Operation::Select,
            false,
            false,
            "",
            "",
        );
    }

    pub fn test_cond_assert_equal<F, Assigned, ControlFlowChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue + Sampleable,
        Assigned::Element: Default,
        ControlFlowChip: ControlFlowInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let x = Assigned::sample_inner(OsRng);
        let y = Assigned::sample_inner(OsRng);
        let none = Assigned::Element::default();
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &x,
            true,
            &none,
            Operation::CondAssertEqual,
            true,
            true,
            name,
            "cond_assert_equal",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &x,
            false,
            &none,
            Operation::CondAssertEqual,
            true,
            false,
            "",
            "",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            false,
            &none,
            Operation::CondAssertEqual,
            true,
            false,
            "",
            "",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            true,
            &none,
            Operation::CondAssertEqual,
            false,
            false,
            "",
            "",
        );
    }
}
