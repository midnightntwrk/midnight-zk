//! Examples on how to perform ECC operations using the ECC Chip inside of
//! AbcirdInterface.

use blstrs::{ExtendedPoint as Jubjub, Fr as JubjubScalar, G1Affine, SubgroupPoint};
use ff::Field;
use group::Group;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    compact_std_lib::{self, MidnightCircuit, Relation, ZkStdLib},
    ecc::{curves::CircuitCurve, native::ScalarVar},
    instructions::{
        AssignmentInstructions, ConversionInstructions, EccInstructions, PublicInputInstructions,
    },
    testing_utils::real_test_api::{check_vk, filecoin_srs},
    types::{AssignedNativePoint, Instantiable},
};
use rand::rngs::OsRng;

type F = blstrs::Scalar;

#[derive(Clone, Default)]
struct EccExample {
    scalar: Value<JubjubScalar>,
}

impl Relation for EccExample {
    type Instance = SubgroupPoint;

    type Witness = JubjubScalar;

    const K: u32 = 12;

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        AssignedNativePoint::<Jubjub>::as_public_input(instance)
    }

    fn from_statement(_instance: &Self::Instance, witness: &Self::Witness) -> Self {
        EccExample {
            scalar: Value::known(*witness),
        }
    }

    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let scalar = std_lib.jubjub().assign(layouter, self.scalar)?;

        // We can also assign a scalar from an assigned native element.
        let native_value = std_lib.assign(layouter, Value::known(F::default()))?;
        let scalar_from_native: ScalarVar<Jubjub> =
            std_lib.jubjub().convert(layouter, &native_value)?;

        // Now we witness a point and create one with H2C.
        // NOTE: careful with this generator, it is NOT the generator of the subgroup,
        // despite the fact that the Group trait states it should be.
        let generator: AssignedNativePoint<Jubjub> = std_lib
            .jubjub()
            .assign_fixed(layouter, <SubgroupPoint as Group>::generator())?;

        let one = std_lib.assign_fixed(layouter, <Jubjub as CircuitCurve>::Base::ONE)?;
        let extra_base = std_lib.hash_to_curve(layouter, &one)?;

        let result = std_lib.jubjub().msm(
            layouter,
            &[scalar, scalar_from_native],
            &[generator, extra_base],
        )?;

        std_lib
            .jubjub()
            .constrain_as_public_input(layouter, &result)
    }
}

fn main() {
    let srs = filecoin_srs(EccExample::K);
    let vk = compact_std_lib::setup_vk::<EccExample>(&srs);

    if cfg!(feature = "check_vk") {
        check_vk::<G1Affine, MidnightCircuit<EccExample>>(&vk);
        return;
    }

    let pk = compact_std_lib::setup_pk::<EccExample>(&srs, &vk);

    let witness = JubjubScalar::random(&mut OsRng);
    let instance = SubgroupPoint::generator() * witness;

    let proof = compact_std_lib::prove::<EccExample>(&srs, &pk, &instance, &witness);

    compact_std_lib::verify::<EccExample>(&srs, &vk, &instance, proof)
}
