//! Example of proving knowledge of a Ethereum signature (for a public message
//! and public key) using midnight's ZK std lib.

use group::GroupEncoding;
use midnight_circuits::{
    field::foreign::params::MultiEmulationParams,
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions, ZeroInstructions,
    },
    types::{AssignedByte, AssignedForeignPoint, Instantiable},
    CircuitField,
};
use midnight_curves::k256::{Fq as K256Scalar, K256};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::filecoin_srs, Relation, ZkStdLib, ZkStdLibArch};
use rand::rngs::OsRng;

type F = midnight_curves::Fq;

// Message type (the length is arbitrary).
const MSG_LEN: usize = 32;
type Message = [u8; MSG_LEN];
type PK = K256;

type Signature = (K256Scalar, K256Scalar);

// Prefix used in the Keccak digest of the Ethereum signature of 32-byte
// messages (EIP-191 protocol with a fixed input size assumption).
const PREFIX: &[u8] = b"\x19Ethereum Signed Message:\n32";

#[derive(Clone, Default)]
pub struct EthereumSigExample;

impl Relation for EthereumSigExample {
    type Instance = (PK, Message);

    type Witness = Signature;

    fn format_instance((pk, msg_bytes): &Self::Instance) -> Result<Vec<F>, Error> {
        Ok([
            AssignedForeignPoint::<F, K256, MultiEmulationParams>::as_public_input(pk),
            msg_bytes
                .iter()
                .flat_map(AssignedByte::<F>::as_public_input)
                .collect::<Vec<_>>(),
        ]
        .into_iter()
        .flatten()
        .collect())
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

        // Assign the PK as public input.
        let pk = secp256k1_curve.assign_as_public_input(layouter, instance.map(|(pk, _)| pk))?;

        // Assign the message bytes and constrain it as public input.
        let msg_bytes = std_lib.assign_many(
            layouter,
            &instance.map(|(_, msg_bytes)| msg_bytes).transpose_array(),
        )?;
        msg_bytes
            .iter()
            .try_for_each(|byte| std_lib.constrain_as_public_input(layouter, byte))?;

        // Assign the signature as a witness.
        let (r_val, s_val) = witness.unzip();
        let r = secp256k1_scalar.assign(layouter, r_val)?;
        let s = secp256k1_scalar.assign(layouter, s_val)?;

        // Prepare the Keccak input, i.e., PREFIX || message.
        let keccak_input = (std_lib.assign_many_fixed(layouter, PREFIX)?.into_iter())
            .chain(msg_bytes)
            .collect::<Vec<_>>();

        let keccak_output = std_lib.keccak_256(layouter, &keccak_input)?;

        let keccak_output_bits = (keccak_output.into_iter())
            .map(|byte| std_lib.assigned_to_be_bits(layouter, &byte.into(), Some(8), true))
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let z = secp256k1_scalar.assigned_from_be_bits(layouter, &keccak_output_bits)?;
        let s_inv = secp256k1_scalar.inv(layouter, &s)?;
        let u1 = secp256k1_scalar.mul(layouter, &z, &s_inv, None)?;
        let u2 = secp256k1_scalar.mul(layouter, &r, &s_inv, None)?;

        let gen = secp256k1_curve.assign_fixed(layouter, K256::generator())?;
        let u1_bits = secp256k1_scalar.assigned_to_le_bits(layouter, &u1, None, true)?;
        let u2_bits = secp256k1_scalar.assigned_to_le_bits(layouter, &u2, None, true)?;

        // Computing R = u1 * G + u2 * pk, where u1 = keccak output (as integer) *
        // s^{-1} and u2 = r * s^{-1}.
        let r_point = secp256k1_curve.msm_by_le_bits(layouter, &[u1_bits, u2_bits], &[gen, pk])?;

        // Check the correctness of R:
        //  1. It should not be the identity.
        secp256k1_curve.assert_non_zero(layouter, &r_point)?;

        // 2. r_point.x should be equal to r.
        let r_point_x = secp256k1_curve.x_coordinate(&r_point);
        let r_point_x_bits = secp256k1_base.assigned_to_le_bytes(layouter, &r_point_x, None)?;
        let r_point_x_scalar =
            secp256k1_scalar.assigned_from_le_bytes(layouter, &r_point_x_bits)?;
        secp256k1_scalar.assert_equal(layouter, &r_point_x_scalar, &r)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            keccak_256: true,
            secp256k1: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(EthereumSigExample)
    }
}

/// Example vector generated from the following .js code:
/// ```js
/// import { Wallet, Signature } from "ethers";
///
/// const priv =
///   "0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
///
/// const wallet = new Wallet(priv);
/// const pubkey = wallet.signingKey.publicKey;
/// const x = pubkey.slice(4, 68);
/// const y = pubkey.slice(68);
/// console.log("Public key:");
/// console.log("x:", x);
/// console.log("y:", y);
///
/// const message = "this is really 32 byte long, huh";
/// console.log("\nMessage bytes:");
/// console.log(Buffer.from(message).toString("hex"));
///
/// const sig = await wallet.signMessage(message);
/// const { r, s, _ } = Signature.from(sig);
/// console.log("\nSignature:");
/// console.log("r:", r);
/// console.log("s:", s);
/// ```
fn main() {
    let msg_bytes: Message = *b"this is really 32 byte long, huh";

    let pk_bytes: [[u8; 32]; 2] = [
        hex_literal::hex!("4646ae5047316b4230d0086c8acec687f00b1cd9d1dc634f6cb358ac0a9a8fff"),
        hex_literal::hex!("fe77b4dd0a4bfb95851f3b7355c781dd60f8418fc8a65d14907aff47c903a559"),
    ];

    let sig_bytes: [[u8; 32]; 2] = [
        hex_literal::hex!("3c0fb2cfab098941e41e180c5e83bd270f1d52811a517dbee235219f35935717"),
        hex_literal::hex!("1ce5858264bbdf0afe617da1dc8f3fa94a350e40442eb0363c3c95be9cd0d6d8"),
    ];

    const K: u32 = 15;
    let srs = filecoin_srs(K);

    println!(">> Testing Ethereum signature verification");
    let relation = EthereumSigExample;

    println!(" - Deserialising public key...");
    let instance = (parse_eth_point(&pk_bytes), msg_bytes);
    println!(" - Deserialising signatures...");
    // sig_bytes are in big-endian.
    let witness = (
        K256Scalar::from_bytes_be(&sig_bytes[0]).expect("Secp scalar 0"),
        K256Scalar::from_bytes_be(&sig_bytes[1]).expect("Secp scalar 1"),
    );

    println!(" - Setting up vk...");
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    println!(" - Proof generation...");
    let proof = midnight_zk_stdlib::prove::<EthereumSigExample, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    println!(" - Proof verification...");
    assert!(
        midnight_zk_stdlib::verify::<EthereumSigExample, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof
        )
        .is_ok()
    );
    println!("... Success!");
}

// Computation of an Ethereum public key from raw serialised data.
// Takes BE-encoded x and y coordinates.
fn parse_eth_point(bytes: &[[u8; 32]; 2]) -> K256 {
    // Standard SEC1 compressed encoding: 0x02 (even y) or 0x03 (odd y) + BE x.
    let y_parity = bytes[1][31] % 2;
    let mut sec1_compressed = [0u8; 33];
    sec1_compressed[0] = 0x02 + y_parity;
    sec1_compressed[1..].copy_from_slice(&bytes[0]);

    let repr = sec1_compressed.into();
    K256::from_bytes(&repr).expect("Point parsing failed")
}
