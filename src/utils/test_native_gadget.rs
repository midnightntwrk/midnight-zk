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
        use halo2_proofs::plonk::ErrorFront as Error;
        use halo2curves::pasta::Fp;
        use midnight_circuits::{
            field::{
                decomposition::chip::P2RDecompositionChip,
                AssignedBounded, NativeChip, NativeGadget,
            },
            types::{AssignedBit, AssignedByte, AssignedNative, Bit, Byte},
            instructions::*,
            testing_utils::FromScratch,
        };

        struct TestCircuit {}

        type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

        impl<F: PrimeField> Circuit<F> for TestCircuit {
            type Config = <NG<F> as FromScratch<F>>::Config;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                unreachable!()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let instance_column = meta.instance_column();
                NG::<F>::configure_from_scratch(meta, &instance_column)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut $layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let $chip = NG::<F>::new_from_scratch(&config);
                NG::<F>::load_from_scratch(&mut $layouter, &config);

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
