//! Example of proving knowledge of a Bitcoin signature (for a public message
//! and public key) using midnight's ZK std lib. The test vectors were generated
//! using Bitcoin's C library https://github.com/bitcoin-core/secp256k1.

use group::GroupEncoding;
use midnight_circuits::{
    field::foreign::params::MultiEmulationParams,
    instructions::{
        AssertionInstructions, AssignmentInstructions, DecompositionInstructions, EccInstructions,
        PublicInputInstructions, ZeroInstructions,
    },
    types::{AssignedByte, AssignedForeignPoint, Instantiable},
    CircuitField,
};
use midnight_curves::k256::{Fp as K256Base, Fq as K256Scalar, K256};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::filecoin_srs, Relation, ZkStdLib, ZkStdLibArch};
use rand::rngs::OsRng;
use sha2::Digest;

type F = midnight_curves::Fq;

type Message = [u8; 32];
type PK = K256;

type Signature = (K256Base, K256Scalar);

// Prefix used in the SHA digest of the bitcoin signature. The tag corresponds
// to SHA256("BIP0340/nonce"), where the string is encoded as utf-8. The prefix
// consists in prepending twice the digest of this tag_preimage.
const TAG_PREIMAGE: [u8; 17] = [
    0x42, 0x49, 0x50, 0x30, 0x33, 0x34, 0x30, 0x2f, 0x63, 0x68, 0x61, 0x6c, 0x6c, 0x65, 0x6e, 0x67,
    0x65,
];

#[derive(Clone, Default)]
pub struct BitcoinSigExample;

impl Relation for BitcoinSigExample {
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
        let (rx_val, s_val) = witness.unzip();
        let rx = secp256k1_base.assign(layouter, rx_val)?;
        let s = secp256k1_scalar.assign(layouter, s_val)?;

        // Assign the (fixed) SHA tag.
        // TODO: this could be improved by giving a precomputed state to SHA.
        let tag_value: [u8; 32] = sha2::Sha256::digest(TAG_PREIMAGE).into();
        let tag = std_lib.assign_many_fixed(layouter, &tag_value)?;

        let rx_bytes = secp256k1_base.assigned_to_be_bytes(layouter, &rx, None)?;
        let pk_x = secp256k1_curve.x_coordinate(&pk);
        let pk_x_bytes = secp256k1_base.assigned_to_be_bytes(layouter, &pk_x, None)?;

        // Prepare the SHA input with the prefix: (tag || tag || rx || pk_x || msg).
        let sha_input = (tag.clone().into_iter())
            .chain(tag)
            .chain(rx_bytes.clone())
            .chain(pk_x_bytes)
            .chain(msg_bytes)
            .collect::<Vec<_>>();

        let mut sha_output = std_lib.sha2_256(layouter, &sha_input)?;

        // Bitcoin represents scalars in big-endian.
        sha_output.reverse();

        let sha_output_bits = sha_output
            .into_iter()
            .map(|byte| std_lib.assigned_to_le_bits(layouter, &byte.into(), Some(8), true))
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let gen = secp256k1_curve.assign_fixed(layouter, K256::generator())?;
        let s_bits = secp256k1_scalar.assigned_to_le_bits(layouter, &s, None, true)?;
        let neg_pk = secp256k1_curve.negate(layouter, &pk)?;

        let r_point =
            secp256k1_curve.msm_by_le_bits(layouter, &[s_bits, sha_output_bits], &[gen, neg_pk])?;

        // Check the correctness of R:
        //  1. It should not be the identity.
        secp256k1_curve.assert_non_zero(layouter, &r_point)?;

        //  2. It should have an even y coordinate.
        let y = secp256k1_curve.y_coordinate(&r_point);
        let y_sign = secp256k1_base.sgn0(layouter, &y)?;
        std_lib.assert_false(layouter, &y_sign)?;

        // 3. r_point.x should be equal to the rx that was hashed.
        let r_point_x = secp256k1_curve.x_coordinate(&r_point);
        secp256k1_base.assert_equal(layouter, &r_point_x, &rx)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            secp256k1: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(BitcoinSigExample)
    }
}

fn main() {
    let msg_bytes: [u8; 32] = [
        27, 214, 156, 7, 93, 215, 183, 140, 79, 32, 166, 152, 178, 42, 63, 185, 215, 70, 21, 37,
        195, 152, 39, 214, 170, 247, 161, 98, 139, 224, 162, 131,
    ];

    let pk_bytes: [u8; 32] = [
        179, 21, 213, 119, 148, 98, 81, 244, 98, 197, 69, 237, 108, 48, 37, 32, 206, 5, 247, 157,
        67, 110, 22, 104, 179, 49, 214, 89, 58, 147, 58, 98,
    ];

    let sig_bytes: [u8; 64] = [
        130, 202, 167, 37, 68, 100, 97, 250, 64, 31, 112, 100, 84, 155, 189, 94, 44, 183, 164, 69,
        191, 116, 182, 25, 49, 201, 43, 66, 204, 112, 124, 32, 49, 8, 60, 245, 140, 215, 44, 157,
        221, 20, 191, 69, 227, 251, 112, 89, 42, 136, 159, 147, 148, 126, 60, 47, 139, 187, 129,
        58, 59, 239, 164, 80,
    ];

    const K: u32 = 15;
    let srs = filecoin_srs(K);

    let relation = BitcoinSigExample;
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let instance = (parse_bitcoin_point(&pk_bytes), msg_bytes);
    // sig_bytes are in big-endian.
    let witness = (
        K256Base::from_bytes_be(&sig_bytes[..32]).expect("Secp base"),
        K256Scalar::from_bytes_be(&sig_bytes[32..]).expect("Secp scalar"),
    );

    let proof = midnight_zk_stdlib::prove::<BitcoinSigExample, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    assert!(
        midnight_zk_stdlib::verify::<BitcoinSigExample, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof
        )
        .is_ok()
    )
}

// Bitcoin uses points that only have even y coordinates. The input x_coord is
// in big-endian format. This function decompresses to the point with even y.
fn parse_bitcoin_point(x_coord: &[u8; 32]) -> K256 {
    // Standard SEC1 compressed encoding: 0x02 for even y + BE x-bytes.
    let mut sec1_compressed = [0u8; 33];
    sec1_compressed[0] = 0x02;
    sec1_compressed[1..].copy_from_slice(x_coord);

    let repr = sec1_compressed.into();
    K256::from_bytes(&repr).expect("Point parsing failed")
}
