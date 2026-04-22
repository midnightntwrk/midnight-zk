//! Example of proving knowledge of a Cardano (Ed25519) signature for a
//! given public message and public key.
//!
//! The test vectors were generated using the `ed25519-dalek` library
//! https://github.com/dalek-cryptography/curve25519-dalek/tree/main/ed25519-dalek.
//!
//! Notation according to https://eprint.iacr.org/2020/1244.pdf.
//!
//! Let C denote the edwards25519 curve , F_L its scalar field, and G1 the
//! cryptographic subgroup of C.
//!
//! This example uses the *strict* (or *cofactorless* or *unbatched*)
//! verification equation:
//!     R = s * B - h * A,
//! where:
//!   * B is the designated generator of G1 (in C).
//!   * A is the public key (in C).
//!   * σ = (R,s) is the signature, with:
//!     - R the nonce commitment (in C),
//!     - s the signature scalar (in F_L).
//!   * h = SHA-512(R_bytes || A_bytes || M) mod L is the challenge (in F_L),
//!     with:
//!     - R_bytes are the LE bytes of the compressed R,
//!     - A_bytes are the LE bytes of the compressed A,
//!     - M are the message bytes.
//!   * L is the scalar field modulus.
//!   * s_bytes are the LE bytes of s.
//!
//! The relation to prove is (x, w), where:
//!   * x is the instance (A_bytes, M),
//!   * w is the witness (R_bytes, s_bytes),
//!
//! [libsodium](https://github.com/jedisct1/libsodium) uses the following verification criteria in
//! `crypto_sign/ed25519/ref10/open.c`:
//!   * cofactorless verification equation R = s * B - h * A,
//!   * canonicity checks for bytes of s, A,
//!   * subgroup-checks for R, A.
//!
//! This example uses the following verification criteria:
//!   * cofactorless verification R = s * B - h * A,
//!   * in-circuit canonicity checks for bytes of s, R, A,
//!   * in-circuit subgroup-check for R, A.

use ff::Field;
use group::Group;
use midnight_circuits::{
    ecc::foreign::edwards_chip::AssignedForeignEdwardsPoint,
    field::foreign::params::MultiEmulationParams,
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, CanonicityInstructions,
        ConversionInstructions, DecompositionInstructions, EccInstructions, FieldInstructions,
        PublicInputInstructions,
    },
    types::{AssignedBit, AssignedByte, AssignedNative, Instantiable},
};
use midnight_curves::curve25519::{Curve25519, Curve25519Subgroup};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::filecoin_srs, Relation, ZkStdLib, ZkStdLibArch};
use rand::rngs::OsRng;

type F = midnight_curves::Fq;

const MSG_LEN: usize = 86;
type Message = [u8; MSG_LEN];
type PublicKey = [u8; 32]; // A_bytes
type Signature = ([u8; 32], [u8; 32]); // (R_bytes, s_bytes)

#[derive(Clone, Default)]
pub struct CardanoSigExample;

impl Relation for CardanoSigExample {
    type Instance = (PublicKey, Message);
    type Witness = Signature;
    type Error = Error;

    fn format_instance((pk_bytes, msg): &Self::Instance) -> Result<Vec<F>, Error> {
        Ok([
            pk_bytes.iter().flat_map(AssignedByte::<F>::as_public_input).collect::<Vec<_>>(),
            msg.iter().flat_map(AssignedByte::<F>::as_public_input).collect::<Vec<_>>(),
        ]
        .concat())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let curve25519 = std_lib.curve25519();
        let curve25519_scalar = std_lib.curve25519().scalar_field_chip();

        // Assign compressed bytes of A as public inputs.
        let a_bytes: [AssignedByte<F>; 32] = instance
            .map(|(a_bytes, _)| a_bytes)
            .transpose_array()
            .into_iter()
            .map(|b| std_lib.assign_as_public_input(layouter, b))
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .expect("exactly 32 bytes");
        let a = from_canonical_compressed_bytes(
            std_lib,
            layouter,
            &a_bytes,
            instance.map(|(a_bytes, _)| decompress_bytes(&a_bytes)),
        )?;

        // Assign message bytes M as public inputs.
        let m_bytes: Vec<AssignedByte<F>> =
            std_lib.assign_many(layouter, &instance.map(|(_, msg)| msg).transpose_array())?;
        m_bytes
            .iter()
            .try_for_each(|byte| std_lib.constrain_as_public_input(layouter, byte))?;

        // Witness bytes of s and enforce canonicity in-circuit.
        let s_bytes: Vec<AssignedByte<F>> =
            std_lib.assign_many(layouter, &witness.map(|(_, s)| s).transpose_array())?;
        let s_bits: Vec<AssignedBit<F>> = assigned_bytes_to_bits(std_lib, layouter, &s_bytes)?;
        let s_is_canonical =
            curve25519_scalar.le_bits_lower_than(layouter, &s_bits, curve25519_scalar.order())?;
        curve25519_scalar.assert_equal_to_fixed(layouter, &s_is_canonical, true)?;
        let s = curve25519_scalar.assigned_from_le_bits(layouter, &s_bits)?;

        // Witness compressed bytes of R and decompress them in-circuit.
        let r_bytes: [AssignedByte<F>; 32] = std_lib
            .assign_many(layouter, &witness.map(|(r, _)| r).transpose_array())?
            .try_into()
            .expect("exactly 32 bytes");
        let r = from_canonical_compressed_bytes(
            std_lib,
            layouter,
            &r_bytes,
            witness.map(|(r, _)| decompress_bytes(&r)),
        )?;

        // Compute h = SHA512(R_bytes || A_bytes || M).
        let sha_input = (r_bytes.into_iter()).chain(a_bytes).chain(m_bytes).collect::<Vec<_>>();
        let h_bytes = std_lib.sha2_512(layouter, &sha_input)?;
        let h = curve25519_scalar.assigned_from_le_bytes(layouter, &h_bytes)?;

        // Assign generator B as fixed point.
        let b = curve25519.assign_fixed(layouter, Curve25519Subgroup::generator())?;

        // Compute s * B - h * A.
        let neg_h = curve25519_scalar.neg(layouter, &h)?;
        let rhs = curve25519.msm(layouter, &[s, neg_h], &[b, a])?;

        // Assert R = s * B - h * A.
        curve25519.assert_equal(layouter, &r, &rhs)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            curve25519: true,
            sha2_512: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(CardanoSigExample)
    }
}

/// Off-circuit decompression of little-endian compressed bytes.
///
/// # Returns
/// A [Curve25519Subgroup] point guaranteed to lie in the subgroup.
fn decompress_bytes(bytes: &[u8; 32]) -> Curve25519Subgroup {
    let compressed = midnight_curves::curve25519::CompressedEdwardsY(*bytes);
    let edwards = compressed.decompress().expect("y coordinate of curve25519 point");
    Curve25519Subgroup::from_edwards(edwards).expect("curve25519 subgroup point")
}

/// In-circuit conversion of [Vec<AssignedByte<F>>] to [Vec<AssignedBit<F>>].
fn assigned_bytes_to_bits(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    bytes: &[AssignedByte<F>],
) -> Result<Vec<AssignedBit<F>>, Error> {
    let bits = bytes
        .iter()
        .map(|byte| std_lib.assigned_to_le_bits(layouter, &byte.clone().into(), Some(8), false))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect();
    Ok(bits)
}

/// In-circuit decompression of little-endian canonical compressed bytes.
/// Non-canonical bytes do not satisfy the underlying constraints.
///
/// # Returns
/// An [AssignedForeignEdwardsPoint] constrained to lie in the subgroup.
fn from_canonical_compressed_bytes(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    compressed_bytes: &[AssignedByte<F>; 32],
    value: Value<Curve25519Subgroup>,
) -> Result<AssignedForeignEdwardsPoint<F, Curve25519, MultiEmulationParams>, Error> {
    let point = std_lib.curve25519().assign(layouter, value)?;
    let canonical_bytes = to_canonical_compressed_bytes(std_lib, layouter, &point)?;
    compressed_bytes
        .iter()
        .zip(canonical_bytes.iter())
        .try_for_each(|(com_byte, can_byte)| std_lib.assert_equal(layouter, com_byte, can_byte))?;

    Ok(point)
}

/// In-circuit compression into canonical little-endian bytes.
///
/// # Returns
/// An array [AssignedByte<F>; 32] constrained to represent a canonical
/// encoding.
fn to_canonical_compressed_bytes(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    point: &AssignedForeignEdwardsPoint<F, Curve25519, MultiEmulationParams>,
) -> Result<[AssignedByte<F>; 32], Error> {
    let curve25519 = std_lib.curve25519();

    let y_bytes = curve25519.base_field_chip().assigned_to_le_bytes(
        layouter,
        &curve25519.y_coordinate(point),
        None,
    )?;

    let x_bits = curve25519.base_field_chip().assigned_to_le_bits(
        layouter,
        &curve25519.x_coordinate(point),
        Some(255),
        true,
    )?;

    // Encode the sign bit of x (= x mod 2, i.e., the least significant bit of x)
    // into the most significant byte of y: MSB = MSB of y + LSBit of x * 128.
    //
    // (This is safe: y <= p - 1 = 2^255 - 19 - 1, which means MSB of y <= 127;
    // hence, adding 128 causes _no_ overflow.)
    let last_byte: AssignedNative<F> = std_lib.linear_combination(
        layouter,
        &[
            (F::ONE, y_bytes[y_bytes.len() - 1].clone().into()),
            (F::from(128), x_bits[0].clone().into()),
        ],
        F::ZERO,
    )?;

    let last_byte: AssignedByte<F> = std_lib.convert(layouter, &last_byte)?;
    let mut compressed_bytes: Vec<AssignedByte<F>> = y_bytes[..y_bytes.len() - 1].to_vec();
    compressed_bytes.push(last_byte);

    Ok(compressed_bytes.try_into().expect("exactly 32 bytes"))
}

fn main() {
    let m: Message =
        "Bajado ya de los árboles/las altas hierbas lo volvieron erecto/y miró las estrellas."
            .as_bytes()
            .try_into()
            .unwrap();

    // Public key A (compressed, little-endian)
    let a_bytes: [u8; 32] = [
        32, 122, 6, 120, 146, 130, 30, 37, 215, 112, 241, 251, 160, 196, 124, 17, 255, 75, 129, 62,
        84, 22, 46, 206, 158, 184, 57, 224, 118, 35, 26, 182,
    ];

    // Signature nonce commitment R (compressed, little-endian)
    let r_bytes: [u8; 32] = [
        2, 149, 17, 250, 35, 213, 26, 139, 202, 65, 23, 200, 170, 109, 4, 161, 27, 152, 221, 254,
        15, 224, 56, 90, 99, 14, 98, 181, 219, 194, 61, 148,
    ];

    // Signature scalar s (little-endian)
    let s_bytes: [u8; 32] = [
        177, 221, 190, 208, 136, 151, 72, 0, 180, 137, 141, 219, 245, 134, 42, 56, 131, 62, 179,
        20, 55, 27, 59, 125, 238, 4, 12, 14, 25, 231, 21, 12,
    ];

    const K: u32 = 17;
    let srs = filecoin_srs(K);

    let relation = CardanoSigExample;

    let instance = (a_bytes, m);
    let witness = (r_bytes, s_bytes);

    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let proof = midnight_zk_stdlib::prove::<CardanoSigExample, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    assert!(
        midnight_zk_stdlib::verify::<CardanoSigExample, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof
        )
        .is_ok()
    );
}
