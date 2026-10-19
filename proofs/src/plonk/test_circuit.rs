//! A small circuit shared by the tests of the plonk module.

use ff::Field;
use midnight_curves::Fq;

use super::{
    Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Instance, Selector,
    TableColumn,
};
use crate::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    poly::Rotation,
};

/// Large enough for the circuit below, with a few spare rows.
pub(crate) const K: u32 = 6;
/// Number of rows of the circuit below, and size of its lookup table.
pub(crate) const TABLE_SIZE: u64 = 16;

/// `b = a²` on enabled rows (gate), `a ∈ {1..16}` (lookup), `b` of row 0 is
/// public (copy constraint to the instance column). It exercises every
/// argument of the prover: gates, permutation, lookup.
#[derive(Clone, Copy)]
pub(crate) struct SquareCircuit;

#[derive(Clone, Debug)]
pub(crate) struct SquareConfig {
    s: Selector,
    a: Column<Advice>,
    b: Column<Advice>,
    table: TableColumn,
    instance: Column<Instance>,
}

impl Circuit<Fq> for SquareCircuit {
    type Config = SquareConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        *self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> SquareConfig {
        let config = SquareConfig {
            s: meta.complex_selector(),
            a: meta.advice_column(),
            b: meta.advice_column(),
            table: meta.lookup_table_column(),
            instance: meta.instance_column(),
        };
        meta.enable_equality(config.b);
        meta.enable_equality(config.instance);

        meta.create_gate("square", |meta| {
            let s = meta.query_selector(config.s);
            let a = meta.query_advice(config.a, Rotation::cur());
            let b = meta.query_advice(config.b, Rotation::cur());
            Constraints::without_selector(vec![s * (a.clone() * a - b)])
        });

        meta.lookup("range", None, |meta| {
            let s = meta.query_selector(config.s);
            let a = meta.query_advice(config.a, Rotation::cur());
            vec![(s.clone() * a + (Expression::from(1) - s), config.table)]
        });

        config
    }

    fn synthesize(
        &self,
        config: SquareConfig,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "table",
            |mut table| {
                for row in 0..TABLE_SIZE {
                    let value = Value::known(Fq::from(row + 1));
                    table.assign_cell(|| "t", config.table, row as usize, || value)?;
                }
                Ok(())
            },
        )?;

        let first_b = layouter.assign_region(
            || "squares",
            |mut region| {
                let mut first_b = None;
                for row in 0..TABLE_SIZE {
                    config.s.enable(&mut region, row as usize)?;
                    let a = Fq::from(row + 1);
                    region.assign_advice(|| "a", config.a, row as usize, || Value::known(a))?;
                    let b = region.assign_advice(
                        || "b",
                        config.b,
                        row as usize,
                        || Value::known(a.square()),
                    )?;
                    first_b.get_or_insert(b.cell());
                }
                Ok(first_b.unwrap())
            },
        )?;

        layouter.constrain_instance(first_b, config.instance, 0)
    }
}
