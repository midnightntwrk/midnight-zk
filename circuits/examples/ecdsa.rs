//! Example of proving ECDSA over SECP256k1

use ff::Field;
use halo2curves::secp256k1::{Fq as secp256k1Scalar, Secp256k1};
use midnight_circuits::{
    compact_std_lib::{self, MidnightCircuit, Relation, ZkStdLib, ZkStdLibArch},
    field::foreign::{params::MultiEmulationParams as MEP, AssignedField},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
    },
    testing_utils::{
        ecdsa::{ECDSASig, Ecdsa},
        plonk_api::filecoin_srs,
    },
    types::{AssignedForeignPoint, Instantiable},
};
use midnight_curves::Fq as Scalar;
use midnight_proofs::{
    circuit::{Layouter, Value},
    dev::cost_model::from_circuit_to_circuit_model,
    plonk::Error,
};
use rand::{rngs::OsRng, SeedableRng};
use rand_chacha::ChaCha8Rng;

type F = Scalar;

type PK = Secp256k1;
type MsgHash = secp256k1Scalar;

#[derive(Clone, Default)]
pub struct SecpECDSA;

impl Relation for SecpECDSA {
    // The actual message should be hashed by the verifier. Since this example
    // is "public message", we work directly with its hash for simplicity.
    type Instance = MsgHash;

    type Witness = (PK, ECDSASig);

    fn format_instance(msg_hash: &Self::Instance) -> Vec<F> {
        AssignedField::<F, secp256k1Scalar, MEP>::as_public_input(msg_hash)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1_curve();
        let secp256k1_scalar = std_lib.secp256k1_scalar();
        let secp256k1_base = secp256k1_curve.base_field_chip();

        // Assign the message hash as a public input.
        let msg_hash = secp256k1_scalar.assign_as_public_input(layouter, instance)?;

        for _ in 0..1 {
            // Assign the PK and constrain it as public inputs.
            let pk: AssignedForeignPoint<_, _, _> =
                secp256k1_curve.assign(layouter, witness.unzip().0)?;

            // Assigned public key with known signature asserting
            let s_inv = secp256k1_scalar.assign(
                layouter,
                witness.unzip().1.map(|sig| sig.get_s().invert().unwrap()),
            )?;

            let r_as_le_bytes = std_lib.assign_many(
                layouter,
                &witness.unzip().1.map(|v| v.get_r()).transpose_array(),
            )?;
            let r_as_scalar = secp256k1_scalar.assigned_from_le_bytes(layouter, &r_as_le_bytes)?;
            let r_as_base = secp256k1_base.assigned_from_le_bytes(layouter, &r_as_le_bytes)?;

            let k = {
                let bases: Vec<AssignedForeignPoint<_, _, _>> = vec![
                    secp256k1_curve.assign_fixed(layouter, Secp256k1::generator())?,
                    pk.clone(),
                ];

                let scalars = vec![
                    secp256k1_scalar.mul(layouter, &msg_hash, &s_inv, None)?,
                    secp256k1_scalar.mul(layouter, &r_as_scalar, &s_inv, None)?,
                ];

                // const WS: usize = 8;
                // let scalar_in_chunks = secp256k1_scalar.assigned_to_le_chunks(
                //     layouter,
                //     &msg_hash,
                //     WS,
                //     Some(256usize.div_ceil(WS)),
                // )?;

                // // let foo = secp256k1_curve.fixed_base_mul::<WS>(
                // //     layouter,
                // //     &scalar_in_chunks,
                // //     Secp256k1::generator(),
                // // )?;
                // let foo = secp256k1_curve.fixed_base_mul::<WS>(
                //     layouter,
                //     &scalar_in_chunks,
                //     Secp256k1::generator(),
                // )?;
                // use halo2curves::group::Curve;
                // use midnight_circuits::types::InnerValue;
                // dbg!(foo.value().zip(witness).map(|(p, _)| p.to_affine()));

                secp256k1_curve.msm(layouter, &scalars, &bases)
            }?;

            let k_point_x = secp256k1_curve.x_coordinate(&k);
            secp256k1_base.assert_equal(layouter, &k_point_x, &r_as_base)?;
        }
        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: None,
            secp256k1: true,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 4,
            automaton: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(SecpECDSA)
    }
}

fn main() {
    const K: u32 = 17;
    let srs = filecoin_srs(K);

    let relation = SecpECDSA;

    dbg!(from_circuit_to_circuit_model::<_, _, 48, 32>(
        Some(K),
        &MidnightCircuit::from_relation(&relation),
        0,
    ));

    let vk = compact_std_lib::setup_vk(&srs, &relation);

    let plonk_pk = compact_std_lib::setup_pk(&relation, &vk);

    // Generate a random instance-witness pair.
    let mut rng = ChaCha8Rng::seed_from_u64(0xba5eba11);
    let msg_hash = secp256k1Scalar::random(&mut rng);

    let key = Ecdsa::keygen(&mut rng);
    let pk = key.0;

    let signature = Ecdsa::sign(&key.1, &msg_hash, &mut rng);

    // Sanity check on the generated signature.
    assert!(Ecdsa::verify(&pk, &msg_hash, &signature));

    let instance = msg_hash;
    let witness = (pk, signature);

    use std::time::Instant;
    let now = Instant::now();
    let proof = compact_std_lib::prove::<SecpECDSA, blake2b_simd::State>(
        &srs, &plonk_pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");
    println!("Elapsed while proving: {:?}", now.elapsed());

    assert!(compact_std_lib::verify::<SecpECDSA, blake2b_simd::State>(
        &srs.verifier_params(),
        &vk,
        &instance,
        &proof
    )
    .is_ok())
}
