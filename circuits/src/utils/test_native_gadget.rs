#[doc(hidden)]
#[macro_export]
macro_rules! run_test_native_gadget {
    ($chip:ident, $layouter:ident, $synthesize_body:block) => {
        use ff::PrimeField;
        use halo2_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            plonk::{Circuit, ConstraintSystem},
        };
        use halo2_proofs::plonk::Error;
        use halo2curves::pasta::Fp;
        use midnight_circuits::{
            types::{AssignedBit, AssignedByte, AssignedNative, Bit, Byte, ComposableChip},
            instructions::*,
            field::{
                decomposition::{
                    chip::{P2RDecompositionChip, P2RDecompositionConfig},
                    pow2range::{Pow2RangeChip, NB_POW2RANGE_COLS},
                },
                AssignedBounded, NativeChip, NativeGadget, native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
            },
        };

        struct TestCircuit {}

        type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

        impl<F: PrimeField> Circuit<F> for TestCircuit {
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
                let instance_column = meta.instance_column();

                let native_config =
                    NativeChip::configure(meta, &(advice_columns, fixed_columns, instance_column));
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
            MockProver::<Fp>::run(10, &(TestCircuit {}), vec![vec![]])
                .unwrap()
                .verify(),
            Ok(())
        );
    };
}
