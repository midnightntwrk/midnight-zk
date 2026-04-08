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

use midnight_curves::Fq as Scalar;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::cost_model::circuit_model,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};

// We use a lookup example
#[derive(Clone, Copy)]
struct TestCircuit {}

#[derive(Debug, Clone)]
struct MyConfig {
    selector: Selector,
    table: TableColumn,
    advice: Column<Advice>,
}

impl Circuit<Scalar> for TestCircuit {
    type Config = MyConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {}
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> MyConfig {
        let config = MyConfig {
            selector: meta.complex_selector(),
            table: meta.lookup_table_column(),
            advice: meta.advice_column(),
        };

        meta.lookup("lookup", |meta| {
            let selector = meta.query_selector(config.selector);
            let not_selector = Expression::from(1) - selector.clone();
            let advice = meta.query_advice(config.advice, Rotation::cur());
            vec![(selector * advice + not_selector, config.table)]
        });

        config
    }

    fn synthesize(
        &self,
        config: MyConfig,
        mut layouter: impl Layouter<Scalar>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "8-bit table",
            |mut table| {
                for row in 0u64..(1 << 8) {
                    table.assign_cell(
                        || format!("row {row}"),
                        config.table,
                        row as usize,
                        || Value::known(Scalar::from(row + 1)),
                    )?;
                }

                Ok(())
            },
        )?;

        layouter.assign_region(
            || "assign values",
            |mut region| {
                for offset in 0u64..(1 << 10) {
                    config.selector.enable(&mut region, offset as usize)?;
                    region.assign_advice(
                        || format!("offset {offset}"),
                        config.advice,
                        offset as usize,
                        || Value::known(Scalar::from((offset % 256) + 1)),
                    )?;
                }

                Ok(())
            },
        )
    }
}

fn main() {
    let circuit = TestCircuit {};

    let model = circuit_model::<_, 32, 32>(&circuit);
    println!(
        "Cost of circuit with 8 bit lookup table: \n{}",
        serde_json::to_string_pretty(&model).unwrap()
    );
}
