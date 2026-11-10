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

#[doc(hidden)]
#[macro_export]
macro_rules! run_test_native_gadget {
    ($chip:ident, $layouter:ident, $synthesize_body:block) => {
        use midnight_circuits::CircuitField;
        use midnight_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            plonk::{Circuit, ConstraintSystem},
        };
        use midnight_proofs::plonk::Error;
        use midnight_curves::Fq as Scalar;
        use midnight_circuits::{
            types::{AssignedBit, AssignedByte, AssignedNative, ComposableChip},
            instructions::*,
            field::{
                AssignedBounded, NativeChip, NativeGadget, NativeGadgetConfig, RangeCheckChip,
                native::NB_EXTRA_ARITH_FIXED_COLS,
            },
        };

        struct TestCircuit;

        impl<F: CircuitField> Circuit<F> for TestCircuit {
            type Config = NativeGadgetConfig;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                unreachable!()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                const NB_ARITH_COLS: usize = 5;
                const NB_ARITH_FIXED_COLS: usize = NB_ARITH_COLS + NB_EXTRA_ARITH_FIXED_COLS;

                let advice_columns: [_; NB_ARITH_COLS] =
                    core::array::from_fn(|_| meta.advice_column());
                let fixed_columns: [_; NB_ARITH_FIXED_COLS] =
                    core::array::from_fn(|_| meta.fixed_column());
                let committed_instance_column = meta.instance_column();
                let instance_column = meta.instance_column();

                let native_config = NativeChip::configure(
                    meta,
                    &(
                        advice_columns.to_vec(),
                        fixed_columns.to_vec(),
                        [committed_instance_column, instance_column],
                    ),
                );

                let range_check_config = RangeCheckChip::configure(
                    meta,
                    &(advice_columns.to_vec(), fixed_columns[..3].to_vec(), 8),
                );
                NativeGadgetConfig { native_config, range_check_config }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut $layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let native_chip = NativeChip::new(&config.native_config, &());
                let range_check_chip = RangeCheckChip::new(&config.range_check_config, &());
                let $chip = NativeGadget::new(native_chip.clone(), range_check_chip.clone());

                $synthesize_body

                native_chip.load(&mut $layouter)?;
                range_check_chip.load(&mut $layouter)
            }
        }

        assert_eq!(
            MockProver::<Scalar>::run(&TestCircuit, vec![vec![], vec![]])
                .unwrap()
                .verify(),
            Ok(())
        );
    };
}
