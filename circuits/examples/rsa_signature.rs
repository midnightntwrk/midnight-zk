//! Example on how to prove knowledge of an RSA signature.
//!
//! Concretely, given an RSA public key (e, m) and a message msg as public
//! inputs, we prove knowledge of an integer s such that s^e = msg (mod m).

use std::ops::Rem;

use midnight_circuits::{
    biguint::AssignedBigUint,
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    instructions::AssertionInstructions,
    testing_utils::plonk_api::filecoin_srs,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::{BigUint, RandBigInt};
use num_traits::{Num, One};
use rand::rngs::OsRng;

type F = midnight_curves::Fq;

type Modulus = BigUint;
type Message = BigUint;
type Signature = BigUint;

/// We assume the RSA public key is of the form (3, m).
const E: u64 = 3;
type PK = Modulus;

const NB_BITS: u32 = 1024;

#[derive(Clone, Default)]
pub struct RSASignatureCircuit;

impl Relation for RSASignatureCircuit {
    type Instance = (PK, Message);

    type Witness = Signature;

    fn format_instance((pk, msg): &Self::Instance) -> Vec<F> {
        [
            AssignedBigUint::<F>::as_public_input::<NB_BITS>(pk),
            AssignedBigUint::<F>::as_public_input::<NB_BITS>(msg),
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let biguint = std_lib.biguint();

        let public_key = biguint.assign_biguint(
            layouter,
            instance.as_ref().map(|(pk, _)| pk.clone()),
            NB_BITS,
        )?;
        let message = biguint.assign_biguint(layouter, instance.map(|(_, msg)| msg), NB_BITS)?;
        let signature = biguint.assign_biguint(layouter, witness, NB_BITS)?;

        biguint.constrain_as_public_input::<NB_BITS>(layouter, &public_key)?;
        biguint.constrain_as_public_input::<NB_BITS>(layouter, &message)?;

        let expected_msg = biguint.mod_exp(layouter, &signature, E, &public_key)?;

        biguint.assert_equal(layouter, &message, &expected_msg)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: false,
            sha512: false,
            secp256k1: false,
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
        Ok(RSASignatureCircuit)
    }
}

fn main() {
    const K: u32 = 12;
    let srs = filecoin_srs(K);

    let relation = RSASignatureCircuit;
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    // Two 512-bit primes.
    let p = BigUint::from_str_radix("81e05798232330a8c7059621c812dc9d2bba37edbd0e79f101eef1db373c12724595480ae6a9dbbf158fa65d6910b8aea7b3be2eede9123ede8d84ec9e8ee907", 16).unwrap();
    let q = BigUint::from_str_radix("acd6fd3c0d70502e8ecefb20259fbf4783a614a0fb1a33701e3adc84947326a754f8a632e5f6cd718a681cde953024b3612bb0646f180b6fd063b1ef4e10d4a5", 16).unwrap();
    let phi = (&p - BigUint::one()) * (&q - BigUint::one());
    let d = BigUint::from(E).modinv(&phi).unwrap();

    let public_key = &p * &q;
    let message = rand::thread_rng().gen_biguint(NB_BITS as u64).rem(&public_key);

    let signature = message.modpow(&d, &public_key);

    let witness = signature;
    let instance = (public_key, message);

    let proof = compact_std_lib::prove::<RSASignatureCircuit, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    assert!(
        compact_std_lib::verify::<RSASignatureCircuit, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof
        )
        .is_ok()
    )
}
