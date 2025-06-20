//! Examples on how to perform ECC operations using the ECC Chip inside of
//! ZkStdLib.

use blstrs::{Fr as JubjubScalar, JubjubExtended as Jubjub, JubjubSubgroup};
use ff::Field;
use group::Group;
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    ecc::{curves::CircuitCurve, native::ScalarVar},
    instructions::{
        AssignmentInstructions, ConversionInstructions, EccInstructions, PublicInputInstructions,
    },
    testing_utils::plonk_api::filecoin_srs,
    types::{AssignedNativePoint, Instantiable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::rngs::OsRng;

type F = blstrs::Fq;

#[derive(Clone, Default)]
pub struct EccExample;

impl Relation for EccExample {
    type Instance = JubjubSubgroup;

    type Witness = JubjubScalar;

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        AssignedNativePoint::<Jubjub>::as_public_input(instance)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let scalar = std_lib.jubjub().assign(layouter, witness)?;

        // We can also assign a scalar from an assigned native element.
        let native_value = std_lib.assign(layouter, Value::known(F::default()))?;
        let scalar_from_native: ScalarVar<Jubjub> =
            std_lib.jubjub().convert(layouter, &native_value)?;

        // Now we witness a point and create one with H2C.
        // NOTE: careful with this generator, it is NOT the generator of the subgroup,
        // despite the fact that the Group trait states it should be.
        let generator: AssignedNativePoint<Jubjub> = std_lib
            .jubjub()
            .assign_fixed(layouter, <JubjubSubgroup as Group>::generator())?;

        let one = std_lib.assign_fixed(layouter, <Jubjub as CircuitCurve>::Base::ONE)?;
        let extra_base = std_lib.hash_to_curve(layouter, &[one])?;

        let result = std_lib.jubjub().msm(
            layouter,
            &[scalar, scalar_from_native],
            &[generator, extra_base],
        )?;

        std_lib
            .jubjub()
            .constrain_as_public_input(layouter, &result)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: true,
            poseidon: true,
            sha256: None,
            secp256k1: false,
            bls12_381: false,
            base64: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(EccExample)
    }
}

fn main() {
    const K: u32 = 11;
    let srs = filecoin_srs(K);

    let relation = EccExample;
    let vk = compact_std_lib::setup_vk(&srs, &relation);

    let pk = compact_std_lib::setup_pk(&relation, &vk);

    const N: usize = 5;

    let mut vks = vec![];
    let mut pis = vec![];
    let mut proofs = vec![];

    for _ in 0..N {
        let witness = JubjubScalar::random(&mut OsRng);
        let instance = JubjubSubgroup::generator() * witness;
        let proof = compact_std_lib::prove(&srs, &pk, &relation, &instance, witness, OsRng)
            .expect("Proof generation should not fail");

        vks.push(vk.clone());
        pis.push(EccExample::format_instance(&instance));
        proofs.push(proof);
    }

    assert!(
        compact_std_lib::batch_verify(&vec![srs.verifier_params(); N], &vks, &pis, &proofs).is_ok()
    )
}
