#[doc(hidden)]
#[macro_export]
macro_rules! run_test_std_lib {
    ($chip:ident, $layouter:ident, $k:expr, $circuit_body:block) => {
        use ff::{FromUniformBytes, PrimeField};
        use halo2_proofs::{
            circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            plonk::Error,
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
            instructions::*,
            types::{AssignedBit, AssignedByte, AssignedNative, Bit, Byte},
            compact_std_lib::{MidnightCircuit, Relation, ZkStdLib},
        };

        type F = blstrs::Scalar;

        #[derive(Clone)]
        struct TestCircuit;

        impl Relation for TestCircuit
        {
            type Witness = ();

            type Instance = ();

            fn format_instance(_instance: &Self::Instance) -> Vec<F> {
                vec![]
            }

            fn circuit(
                &self,
                $chip: &ZkStdLib,
                $layouter: &mut impl Layouter<F>,
                instance: Value<Self::Instance>,
                witness: Value<Self::Witness>,
            ) -> Result<(), Error> {

                $circuit_body

                Ok(())
            }

            fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
                Ok(())
            }

            fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
                Ok(TestCircuit)
            }
        }

        let circuit = MidnightCircuit::from_relation(&TestCircuit);

        MockProver::run($k, &circuit, vec![vec![]])
            .expect("Failed to generate proof")
            .assert_satisfied();
    };
}
