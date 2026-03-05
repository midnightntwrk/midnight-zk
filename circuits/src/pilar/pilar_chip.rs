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

//! A minimal chip with a single advice column and one arithmetic identity.
//!
//! The gate enforces:
//!
//! ```text
//! q_a · a(X) + q_b · a(ωX) + q_c · a(ω²X) + q_m · a(X) · a(ωX) + q_k = 0
//! ```
//!
//! where `a` is the single advice column and `q_a`, `q_b`, `q_c`, `q_m`, `q_k`
//! are fixed columns. Consecutive rotations (`Rotation(0)`, `Rotation(1)`,
//! `Rotation(2)`) replace multiple advice columns.
//!
//! There is no selector — when all fixed columns are zero the identity is
//! trivially satisfied. This keeps max_degree at 3 (the `q_m · a · a` term).
//!
//! NOTE: Public inputs are not supported yet. They may be added in a future
//! iteration.

use std::marker::PhantomData;

use midnight_proofs::{
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed},
    poly::Rotation,
};

use crate::{utils::ComposableChip, CircuitField};

/// Number of fixed columns used by the Pilar chip.
pub const NB_PILAR_FIXED_COLS: usize = 5;

/// Configuration for [`PilarChip`].
#[derive(Clone, Debug)]
pub struct PilarConfig {
    /// The single advice column.
    pub advice: Column<Advice>,
    /// Fixed column for the coefficient of `a(X)`.
    pub q_a: Column<Fixed>,
    /// Fixed column for the coefficient of `a(ωX)`.
    pub q_b: Column<Fixed>,
    /// Fixed column for the coefficient of `a(ω²X)`.
    pub q_c: Column<Fixed>,
    /// Fixed column for the multiplication coefficient `a(X) · a(ωX)`.
    pub q_m: Column<Fixed>,
    /// Fixed column for the constant term.
    pub q_k: Column<Fixed>,
}

/// A chip with a single advice column and one arithmetic identity.
///
/// See the [module-level documentation](self) for details.
#[derive(Clone, Debug)]
pub struct PilarChip<F: CircuitField> {
    config: PilarConfig,
    _marker: PhantomData<F>,
}

impl<F: CircuitField> Chip<F> for PilarChip<F> {
    type Config = PilarConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: CircuitField> ComposableChip<F> for PilarChip<F> {
    type SharedResources = (Column<Advice>, [Column<Fixed>; NB_PILAR_FIXED_COLS]);
    type InstructionDeps = ();

    fn new(config: &PilarConfig, _sub_chips: &()) -> Self {
        Self {
            config: config.clone(),
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> PilarConfig {
        let advice = shared_res.0;
        let fixed_cols = &shared_res.1;

        let q_a = fixed_cols[0];
        let q_b = fixed_cols[1];
        let q_c = fixed_cols[2];
        let q_m = fixed_cols[3];
        let q_k = fixed_cols[4];

        meta.enable_equality(advice);

        // q_a · a(X) + q_b · a(ωX) + q_c · a(ω²X) + q_m · a(X) · a(ωX) + q_k = 0
        meta.create_gate("pilar_gate", |meta| {
            let a_cur = meta.query_advice(advice, Rotation::cur());
            let a_next = meta.query_advice(advice, Rotation::next());
            let a_next2 = meta.query_advice(advice, Rotation(2));

            let q_a = meta.query_fixed(q_a, Rotation::cur());
            let q_b = meta.query_fixed(q_b, Rotation::cur());
            let q_c = meta.query_fixed(q_c, Rotation::cur());
            let q_m = meta.query_fixed(q_m, Rotation::cur());
            let q_k = meta.query_fixed(q_k, Rotation::cur());

            let identity = q_a * a_cur.clone()
                + q_b * a_next.clone()
                + q_c * a_next2
                + q_m * a_cur * a_next
                + q_k;

            Constraints::without_selector(vec![identity])
        });

        PilarConfig {
            advice,
            q_a,
            q_b,
            q_c,
            q_m,
            q_k,
        }
    }

    fn load(&self, _layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::Circuit,
    };

    type F = midnight_curves::Fq;

    /// Test circuit that assigns advice values and enables Pilar gates at
    /// specified offsets with the given fixed coefficients.
    #[derive(Clone, Debug)]
    struct PilarTestCircuit {
        advice_values: Vec<F>,
        /// Each entry: (offset, q_a, q_b, q_c, q_m, q_k).
        gates: Vec<(usize, F, F, F, F, F)>,
    }

    impl Circuit<F> for PilarTestCircuit {
        type Config = PilarConfig;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();
            let fixed_cols: [Column<Fixed>; NB_PILAR_FIXED_COLS] =
                core::array::from_fn(|_| meta.fixed_column());

            PilarChip::<F>::configure(meta, &(advice, fixed_cols))
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "pilar test region",
                |mut region| {
                    for (offset, value) in self.advice_values.iter().enumerate() {
                        region.assign_advice(
                            || format!("advice[{offset}]"),
                            config.advice,
                            offset,
                            || Value::known(*value),
                        )?;
                    }

                    for &(offset, q_a, q_b, q_c, q_m, q_k) in &self.gates {
                        region.assign_fixed(
                            || "q_a",
                            config.q_a,
                            offset,
                            || Value::known(q_a),
                        )?;
                        region.assign_fixed(
                            || "q_b",
                            config.q_b,
                            offset,
                            || Value::known(q_b),
                        )?;
                        region.assign_fixed(
                            || "q_c",
                            config.q_c,
                            offset,
                            || Value::known(q_c),
                        )?;
                        region.assign_fixed(
                            || "q_m",
                            config.q_m,
                            offset,
                            || Value::known(q_m),
                        )?;
                        region.assign_fixed(
                            || "q_k",
                            config.q_k,
                            offset,
                            || Value::known(q_k),
                        )?;
                    }

                    Ok(())
                },
            )
        }
    }

    fn run_pilar_circuit(
        advice_values: Vec<F>,
        gates: Vec<(usize, F, F, F, F, F)>,
    ) -> Result<(), Vec<midnight_proofs::dev::VerifyFailure>> {
        let k = 5;
        let circuit = PilarTestCircuit {
            advice_values,
            gates,
        };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.verify()
    }

    fn f(x: u64) -> F {
        F::from(x)
    }

    fn neg(x: u64) -> F {
        -F::from(x)
    }

    // ---- Positive tests ----

    #[test]
    fn test_addition() {
        // a + b = c: q_a=1, q_b=1, q_c=-1.
        // 1·3 + 1·5 + (-1)·8 = 0.
        let result = run_pilar_circuit(
            vec![f(3), f(5), f(8)],
            vec![(0, f(1), f(1), neg(1), f(0), f(0))],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_multiplication() {
        // a * b = c: q_m=1, q_c=-1.
        // 1·3·7 + (-1)·21 = 0.
        let result = run_pilar_circuit(
            vec![f(3), f(7), f(21)],
            vec![(0, f(0), f(0), neg(1), f(1), f(0))],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_constant_term() {
        // q_a·a + q_k = 0: a=7, q_a=1, q_k=-7.
        let result = run_pilar_circuit(
            vec![f(7), f(0), f(0)],
            vec![(0, f(1), f(0), f(0), f(0), neg(7))],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_full_identity() {
        // q_a·a + q_b·b + q_c·c + q_m·a·b + q_k = 0.
        // a=2, b=3, c=17, q_a=1, q_b=2, q_c=-1, q_m=1, q_k=3.
        // 1·2 + 2·3 + (-1)·17 + 1·2·3 + 3 = 2 + 6 - 17 + 6 + 3 = 0.
        let result = run_pilar_circuit(
            vec![f(2), f(3), f(17)],
            vec![(0, f(1), f(2), neg(1), f(1), f(3))],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_multiple_gates() {
        // Gate at row 0: addition 3 + 5 = 8.
        // Gate at row 3: multiplication 2 * 4 = 8.
        let result = run_pilar_circuit(
            vec![f(3), f(5), f(8), f(2), f(4), f(8)],
            vec![
                (0, f(1), f(1), neg(1), f(0), f(0)),
                (3, f(0), f(0), neg(1), f(1), f(0)),
            ],
        );
        assert!(result.is_ok());
    }

    // ---- Negative tests ----

    #[test]
    fn test_wrong_addition_fails() {
        // a + b should be 8, but c = 7.
        let result = run_pilar_circuit(
            vec![f(3), f(5), f(7)],
            vec![(0, f(1), f(1), neg(1), f(0), f(0))],
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_wrong_multiplication_fails() {
        // a * b should be 21, but c = 20.
        let result = run_pilar_circuit(
            vec![f(3), f(7), f(20)],
            vec![(0, f(0), f(0), neg(1), f(1), f(0))],
        );
        assert!(result.is_err());
    }
}
