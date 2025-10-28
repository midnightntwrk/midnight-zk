//! Example on how to prove knowledge of an RSA signature.
//!
//! Concretely, given an RSA public key (e, m) and a message msg as public
//! inputs, we prove knowledge of an integer s such that s^e = msg (mod m).

use std::ops::Rem;

use blstrs::G1Affine;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    biguint::AssignedBoundedBigUint,
    compact_std_lib::{self, MidnightCircuit, Relation, ZkStdLib},
    instructions::{AssertionInstructions, AssignmentInstructions, PublicInputInstructions},
    testing_utils::real_test_api::{check_vk, filecoin_srs},
    types::Instantiable,
};
use num_bigint::{BigUint, RandBigInt};
use num_traits::{Num, One};

type F = blstrs::Scalar;

type Modulus = BigUint;
type Message = BigUint;
type Signature = BigUint;

/// We assume the RSA public key is of the form (3, m).
const E: u64 = 3;
type PK = Modulus;

const NB_BITS: u32 = 1024;

#[derive(Clone, Default)]
struct RSASignatureCircuit {
    // Public inputs:
    public_key: Value<PK>,
    message: Value<Message>,

    // Witnesses:
    signature: Value<Signature>,
}

impl Relation for RSASignatureCircuit {
    type Instance = (PK, Message);

    type Witness = Signature;

    const K: u32 = 12;

    fn format_instance((pk, msg): &Self::Instance) -> Vec<F> {
        [
            AssignedBoundedBigUint::<F, NB_BITS>::as_public_input(pk),
            AssignedBoundedBigUint::<F, NB_BITS>::as_public_input(msg),
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn from_statement((public_key, message): &Self::Instance, signature: &Self::Witness) -> Self {
        RSASignatureCircuit {
            public_key: Value::known(public_key.clone()),
            message: Value::known(message.clone()),

            signature: Value::known(signature.clone()),
        }
    }

    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let biguint = std_lib.biguint();

        let public_key: AssignedBoundedBigUint<F, NB_BITS> =
            biguint.assign_as_public_input(layouter, self.public_key.clone())?;

        let message: AssignedBoundedBigUint<F, NB_BITS> =
            biguint.assign_as_public_input(layouter, self.message.clone())?;

        let signature: AssignedBoundedBigUint<F, NB_BITS> =
            biguint.assign(layouter, self.signature.clone())?;

        let expected_msg =
            biguint.mod_exp(layouter, &signature.clone().into(), E, &public_key.into())?;

        biguint.assert_equal(layouter, &message.into(), &expected_msg)
    }
}

fn main() {
    let srs = filecoin_srs(RSASignatureCircuit::K);

    let vk = compact_std_lib::setup_vk::<RSASignatureCircuit>(&srs);

    if cfg!(feature = "check_vk") {
        check_vk::<G1Affine, MidnightCircuit<RSASignatureCircuit>>(&vk);
        return;
    }

    let pk = compact_std_lib::setup_pk::<RSASignatureCircuit>(&srs, &vk);

    // Two 512-bit primes.
    let p = BigUint::from_str_radix("81e05798232330a8c7059621c812dc9d2bba37edbd0e79f101eef1db373c12724595480ae6a9dbbf158fa65d6910b8aea7b3be2eede9123ede8d84ec9e8ee907", 16).unwrap();
    let q = BigUint::from_str_radix("acd6fd3c0d70502e8ecefb20259fbf4783a614a0fb1a33701e3adc84947326a754f8a632e5f6cd718a681cde953024b3612bb0646f180b6fd063b1ef4e10d4a5", 16).unwrap();
    let phi = (&p - BigUint::one()) * (&q - BigUint::one());
    let d = BigUint::from(E).modinv(&phi).unwrap();

    let public_key = &p * &q;
    let message = rand::thread_rng()
        .gen_biguint(NB_BITS as u64)
        .rem(&public_key);

    let signature = message.modpow(&d, &public_key);

    let witness = signature;
    let instance = (public_key, message);

    let proof = compact_std_lib::prove::<RSASignatureCircuit>(&srs, &pk, &instance, &witness);

    compact_std_lib::verify::<RSASignatureCircuit>(&srs, &vk, &instance, proof)
}
