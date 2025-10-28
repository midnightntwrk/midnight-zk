#[doc(hidden)]
#[macro_export]
macro_rules! run_test_std_lib {
    ($chip:ident, $layouter:ident, $k:expr, $circuit_body:block) => {
        use ff::{FromUniformBytes, PrimeField};
        use halo2_proofs::{
            circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            plonk::ErrorFront as Error,
        };
        use midnight_circuits::{
            ecc::{
                hash_to_curve::{MapToCurveCPU, MapToEdwardsParams},
                curves::EdwardsCurve,
            },
            field::{
                decomposition::chip::P2RDecompositionChip, foreign::params::MultiEmulationParams,
                AssignedBounded, NativeChip, NativeGadget,
            },
            hash::poseidon::{cpu::Spec, P128Pow5T3},
            instructions::*,
            types::{AssignedBit, AssignedByte, AssignedNative, Bit, Byte},
            compact_std_lib::{MidnightCircuit, Relation, ZkStdLib},
        };

        type F = blstrs::Scalar;

        #[derive(Clone, Default)]
        struct TestCircuit {}

        impl Relation for TestCircuit
        {
            type Witness = ();

            type Instance = ();

            const K: u32 = 10;

            fn from_statement(_instance: &Self::Instance, _witness: &Self::Witness) -> Self {
                TestCircuit {}
            }

            fn format_instance(_instance: &Self::Instance) -> Vec<F> {
                vec![]
            }

            fn circuit(
                &self,
                $chip: &ZkStdLib,
                $layouter: &mut impl Layouter<F>,
            ) -> Result<(), Error> {

                $circuit_body

                Ok(())
            }
        }

        let circuit : MidnightCircuit::<_>= TestCircuit { }.into();

        MockProver::run($k, &circuit, vec![vec![]])
            .expect("Failed to generate proof")
            .assert_satisfied();
    };
}
