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

#[doc(hidden)]
#[macro_export]
macro_rules! run_test_native_gadget {
    ($chip:ident, $layouter:ident, $synthesize_body:block) => {
        use ff::PrimeField;
        use midnight_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            plonk::{Circuit, ConstraintSystem},
        };
        use midnight_proofs::plonk::Error;
        use halo2curves::pasta::Fp;
        use midnight_circuits::{
            types::{AssignedBit, AssignedByte, AssignedNative, ComposableChip},
            instructions::*,
            field::{
                decomposition::{
                    chip::{P2RDecompositionChip, P2RDecompositionConfig},
                    pow2range::Pow2RangeChip,
                },
                AssignedBounded, NativeChip, NativeGadget, native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
            },
        };

        struct TestCircuit<const NB_POW2RANGE_COLS: usize>;

        type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

        impl<F: PrimeField, const NB_POW2RANGE_COLS: usize> Circuit<F> for TestCircuit<NB_POW2RANGE_COLS> {
            type Config = P2RDecompositionConfig;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                unreachable!()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                // We create the needed columns
                let advice_columns: [_; NB_ARITH_COLS] =
                    core::array::from_fn(|_| meta.advice_column());
                let fixed_columns: [_; NB_ARITH_FIXED_COLS] =
                    core::array::from_fn(|_| meta.fixed_column());
                let committed_instance_column = meta.instance_column();
                let instance_column = meta.instance_column();

                let native_config = NativeChip::configure(
                    meta,
                    &(
                        advice_columns,
                        fixed_columns,
                        [committed_instance_column, instance_column],
                    ),
                );

                let pow2range_config =
                    Pow2RangeChip::configure(meta, &advice_columns[1..=NB_POW2RANGE_COLS]);
                P2RDecompositionConfig::new(&native_config, &pow2range_config)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut $layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let max_bit_len = 8;
                let native_chip = NativeChip::new(config.native_config(), &());
                let core_decomposition_chip = P2RDecompositionChip::new(&config, &max_bit_len);
                let $chip = NativeGadget::new(core_decomposition_chip, native_chip);

                let pow2range_config = config.pow2range_config();
                let pow2range_chip = Pow2RangeChip::new(pow2range_config, max_bit_len);
                pow2range_chip.load_table(&mut $layouter);

                $synthesize_body

                Ok(())
            }
        }

        assert_eq!(
            MockProver::<Fp>::run(10, &(TestCircuit::<4> {}), vec![vec![], vec![]])
                .unwrap()
                .verify(),
            Ok(())
        );
    };
}
