//! Example of proving knowledge of a Cardano (Ed25519) signature for a
//! given public message and public key. The test vectors were generated using
//! the `ed25519-dalek` library
//! https://github.com/dalek-cryptography/curve25519-dalek/tree/main/ed25519-dalek.
//!
//! Notation according to https://eprint.iacr.org/2020/1244.pdf.
//!
//! Let C denote the edwards25519 curve , F_L its scalar field, and G1 the
//! cryptographic subgroup of C.
//!
//! This example uses the *strict* (or *cofactorless* or *unbatched*)
//! verification equation:
//!     s * B = R + h * A,
//! where:
//!   * B is the designated generator of G1 (in C).
//!   * A is the public key (in C).
//!   * σ = (R,s) is the signature, with:
//!     - R the nonce commitment (in C),
//!     - s the signature scalar (in F_L).
//!   * h = SHA-512(R_bytes || A_bytes || M_bytes) mod L is the challenge (in
//!     F_L), with:
//!     - R_bytes are the bytes of the compressed R,
//!     - A_bytes are the bytes of the compressed A.
//!     - M_bytes are the bytes for message M
//!   * L is the the scalar field modulus.
//!
//! The relation to prove is (x, w), where:
//!   * x is the instance (A, M),
//!   * w is the witness (R, s).
//!
//! [libsodium](https://github.com/jedisct1/libsodium) uses the following verification criteria in
//! `crypto_sign/ed25519/ref10/open.c`:
//!   * cofactorless verification equation R - s * B - h * A = 0,
//!   * canonicity checks on s, A,
//!   * small-order checks on R, A.
//!
//! This example uses the following verification criteria:
//!   * cofactorless verification s * B = R + h * A,
//!   * canonicity checks on s, A, R,
//!   * small-order checks on R, A.

use ff::Field;
use group::Group;
use midnight_circuits::{
    ecc::foreign::edwards_chip::AssignedForeignEdwardsPoint,
    field::foreign::params::MultiEmulationParams,
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, CanonicityInstructions,
        ConversionInstructions, DecompositionInstructions, EccInstructions,
        PublicInputInstructions,
    },
    types::{AssignedByte, AssignedNative, Instantiable},
};
use midnight_curves::curve25519::{CompressedEdwardsY, Curve25519, Curve25519Subgroup, Scalar};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::filecoin_srs, Relation, ZkStdLib, ZkStdLibArch};
use rand::rngs::OsRng;

type F = midnight_curves::Fq;

const MSG_LEN: usize = 86;
type Message = [u8; MSG_LEN];
type PublicKey = Curve25519Subgroup;
type Signature = (Curve25519Subgroup, Scalar);

#[derive(Clone, Default)]
pub struct CardanoSigExample;

impl Relation for CardanoSigExample {
    type Instance = (PublicKey, Message);
    type Witness = Signature;
    type Error = Error;

    fn format_instance((public_key, msg): &Self::Instance) -> Result<Vec<F>, Error> {
        Ok([
            AssignedForeignEdwardsPoint::<F, Curve25519, MultiEmulationParams>::as_public_input(
                public_key,
            ),
            msg.iter().flat_map(AssignedByte::<F>::as_public_input).collect::<Vec<_>>(),
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
        let curve25519_curve = std_lib.curve25519_curve();
        let curve25519_scalar = std_lib.curve25519_scalar();

        // Assign the public key A as public input.
        let a = curve25519_curve.assign_as_public_input(layouter, instance.map(|(a, _)| a))?;

        // Assign the message bytes M and constrain them as public input.
        let m_bytes: Vec<AssignedByte<F>> =
            std_lib.assign_many(layouter, &instance.map(|(_, msg)| msg).transpose_array())?;
        m_bytes
            .iter()
            .try_for_each(|byte| std_lib.constrain_as_public_input(layouter, byte))?;

        // Decompose witness w = (R, s) and assign (R, s) as curve point and scalar.
        let r_val = witness.map(|(r, _)| r);
        let s_val = witness.map(|(_, s)| s);
        let r = curve25519_curve.assign(layouter, r_val)?;
        let s = curve25519_scalar.assign(layouter, s_val)?;

        // Canonicity check for s.
        let s_bits = curve25519_scalar.assigned_to_le_bits(layouter, &s, None, false)?;
        let canonical = curve25519_scalar.is_canonical(layouter, &s_bits)?;
        curve25519_scalar.assert_equal_to_fixed(layouter, &canonical, true)?;

        // Compress R and A.
        let r_compressed_bytes = compress_edwards_point(std_lib, layouter, &r)?;
        let a_compressed_bytes = compress_edwards_point(std_lib, layouter, &a)?;

        // Compute h = SHA512(R_bytes || A_bytes || M).
        let sha_input = (r_compressed_bytes.into_iter())
            .chain(a_compressed_bytes)
            .chain(m_bytes)
            .collect::<Vec<_>>();
        let h_bytes = std_lib.sha2_512(layouter, &sha_input)?;
        let h = curve25519_scalar.assigned_from_le_bytes(layouter, &h_bytes)?;

        // Assign (fixed) generator B.
        let b = curve25519_curve.assign_fixed(layouter, Curve25519Subgroup::generator())?;

        // Compute lhs = s * B.
        let lhs = curve25519_curve.msm(layouter, &[s], &[b])?;

        // Compute rhs = R + h * A.
        let h_a = curve25519_curve.msm(layouter, &[h], &[a])?;
        let rhs = curve25519_curve.add(layouter, &r, &h_a)?;

        // Assert s * B = R + h * A.
        curve25519_curve.assert_equal(layouter, &lhs, &rhs)
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

// Off-circuit decompression of `CompressedEdwardsY` into
// `Curve25519Subgroup` point.
fn decompress_point(bytes: &[u8; 32]) -> Curve25519Subgroup {
    let compressed = CompressedEdwardsY(*bytes);
    let edwards = compressed.decompress().expect("y coordinate of curve25519 point");

    // The result is guaranteed to lie in the prime-order subgroup.
    Curve25519Subgroup::from_edwards(edwards).expect("curve25519 subgroup point")
}

// In-circuit compression of `AssignedForeignEdwardsPoint` into
// `[AssignedByte<F>; 32]`.
//
// Note: Only points with canonical coordinates satisfy the underlying
// constraints.
fn compress_edwards_point(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    point: &AssignedForeignEdwardsPoint<F, Curve25519, MultiEmulationParams>,
) -> Result<[AssignedByte<F>; 32], Error> {
    let curve25519_curve = std_lib.curve25519_curve();
    let base_chip = curve25519_curve.base_field_chip();

    // 1. Decompose assigned y-coordinate into little-endian bytes.
    // Note: Canonicity is enforced by `assigned_to_le_bytes`.
    let y_bytes =
        base_chip.assigned_to_le_bytes(layouter, &curve25519_curve.y_coordinate(point), None)?;

    // 2. Decompose assigned x-coordinate into little-endian bits.
    // Note: We enforce canonicity.
    let x_bits = base_chip.assigned_to_le_bits(
        layouter,
        &curve25519_curve.x_coordinate(point),
        Some(255),
        true,
    )?;

    // 3. Encoding the sign bit of x-coordinate (= x mod 2, i.e., the least
    //    significant bit) into the most significant byte of the y-coordinate:
    //    compressed_point[31] = y_bytes[31] + x_sign_bit * 128.
    //
    // (This is safe: y <= p = 2^255 - 19 - 1, which means y_bytes[31] <= 127;
    // hence, adding 128 to the most significant byte causes _no_ overflow.)
    let last_byte_with_sign: AssignedNative<F> = std_lib.linear_combination(
        layouter,
        &[
            (F::ONE, y_bytes[31].clone().into()),
            (F::from(128), x_bits[0].clone().into()),
        ],
        F::ZERO,
    )?;

    // 4. Assemble 32 bytes of compressed point.
    let last_byte: AssignedByte<F> = std_lib.convert(layouter, &last_byte_with_sign)?;
    let mut compressed_point: Vec<AssignedByte<F>> = y_bytes[..31].to_vec();
    compressed_point.push(last_byte);

    Ok(compressed_point.try_into().expect("compressed point with 32 bytes"))
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

    // Decompress (and deserialize) curve points and deserialize scalars;
    // a weak public key A (of small order) is ruled out by the type system.
    let a = decompress_point(&a_bytes);
    let r = decompress_point(&r_bytes);
    let s = Scalar::from_canonical_bytes(s_bytes).expect("curve25519 scalar");

    let instance = (a, m);
    let witness = (r, s);

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
