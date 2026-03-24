//! Passport verification circuit (SHA-256 + RSA-2048).
//!
//! Proves in zero-knowledge that the prover holds a valid ICAO 9303
//! biometric passport, without revealing the passport contents beyond
//! what the verifier's predicate requires.
//!
//! # Verification chain
//!
//! The circuit performs the following checks:
//!
//! 1. **SOD parsing**: parse the Security Object Document according to
//!    [`spec::sod_sha256_rsa2048_spec`] to extract eContent, signedAttrs,
//!    messageDigest, tbsCertificate, dsPublicKey, dsSignature, cscaSignature,
//!    and hashDg1.
//!
//! 2. **CSCA signature verification**: hash tbsCertificate with SHA-256, apply
//!    PKCS#1 v1.5 padding, and verify the RSA-2048 signature (cscaSignature)
//!    against the CSCA public key provided in the witness.
//!
//! 3. **CSCA key membership**: prove that the CSCA public key belongs to the
//!    trusted set, represented as a Poseidon Merkle tree whose root is the
//!    public input.
//!
//! 4. **DS signature verification**: hash signedAttrs with SHA-256, apply
//!    PKCS#1 v1.5 padding, and verify the RSA-2048 signature (dsSignature)
//!    against dsPublicKey.
//!
//! 5. **eContent integrity**: hash eContent with SHA-256 and check equality
//!    with messageDigest.
//!
//! 6. **DG1 integrity**: hash the full DG1 (93 bytes) with SHA-256 and check
//!    equality with hashDg1 from the eContent.
//!
//! # Public inputs
//!
//! - The Poseidon Merkle root of the trusted CSCA key set. Each key in the set
//!   is keyed by `SHA-256(modulus_be)` truncated to a field element.
//!
//! # Witness
//!
//! - The full SOD bytes.
//! - The full DG1 bytes (93 bytes).
//! - The CSCA public key (RSA-2048 modulus, big-endian bytes).
//! - The Poseidon Merkle tree of trusted CSCA keys (for the membership proof).

use ff::{Field, PrimeField};
use midnight_circuits::{
    biguint::AssignedBigUint,
    hash::poseidon::PoseidonChip,
    instructions::{
        map::{MapCPU, MapInstructions},
        ArithInstructions, AssertionInstructions, AssignmentInstructions, PublicInputInstructions,
    },
    map::cpu::MapMt,
    types::{AssignedByte, AssignedNative},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};

use super::spec;

type F = midnight_curves::Fq;

// -----------------------------------------------------------------------
// RSA-2048 constants
// -----------------------------------------------------------------------

/// RSA-2048 key size in bits.
const RSA_BITS: u32 = 2048;
/// RSA-2048 key size in bytes.
const RSA_BYTES: usize = (RSA_BITS / 8) as usize;
/// RSA public exponent. Passports commonly use e = 65537.
const RSA_E: u64 = 65537;

// -----------------------------------------------------------------------
// ASN.1 parser sizing constants
// -----------------------------------------------------------------------

/// Max varlen tag bytes. All tags in the passport spec are constant (1-2
/// bytes), so no varlen tags are created.
const TAG_M: usize = 0;

/// Max varlen DER length field bytes. The largest variable length in the SOD is
/// ~2600 bytes, which encodes as 3 bytes (0x82 + 2 bytes, covering lengths up
/// to 65535).
const LEN_M: usize = 3;

/// Max varlen value bytes. Must cover the two varlen extractions:
///
///   - eContent (LDSSecurityObject): up to ~650 bytes (16 data groups, each
///     contributing a 39-byte DataGroupHash entry).
///   - tbsCertificate: up to ~1024 bytes (variable due to issuer/subject
///     Distinguished Names and X.509v3 extensions).
///
/// Must be a multiple of `VAL_A`.
const VAL_M: usize = 1024;

/// Chunk alignment for varlen values. Set to 64 to match SHA-256 block size,
/// since both varlen extractions (eContent, tbsCertificate) are hashed with
/// SHA-256.
const VAL_A: usize = 64;

/// Max total SOD (ContentInfo) size. Variable due to:
///
///   - Number of data group hashes in eContent (+39 bytes per DG).
///   - Issuer/subject DN lengths in the DS certificate.
///   - Certificate extensions.
///   - IssuerAndSerialNumber duplication in SignerInfo.
///
/// Typical: ~1700 bytes. Upper bound with 16 DGs: ~2600 bytes.
const SOD_M: usize = 2688;

/// Chunk alignment for the full SOD input. The full SOD witness is not hashed
/// directly (only extracted parts are), so alignment is 1.
const SOD_A: usize = 1;

// -----------------------------------------------------------------------
// Other constants
// -----------------------------------------------------------------------

/// DG1 size for TD3 documents (tag + length + MRZ).
const DG1_LEN: usize = 93;

/// PKCS#1 v1.5 DigestInfo prefix for SHA-256 (DER-encoded AlgorithmIdentifier +
/// OCTET STRING tag + length).
const PKCS1_SHA256_DIGEST_INFO: [u8; 19] = [
    0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05,
    0x00, 0x04, 0x20,
];

/// Fixed prefix of a DER-encoded RSA-2048 public key inside a BIT STRING. The
/// leading zero byte before the modulus is always present for RSA-2048 since
/// the modulus (product of two ~1024-bit primes) always has its MSB set.
const RSA_PUBKEY_PREFIX: [u8; 10] = [
    0x00, // unused bits
    0x30, 0x82, 0x01, 0x22, // SEQUENCE header (290 bytes)
    0x02, 0x82, 0x01, 0x01, // INTEGER tag + length (257)
    0x00, // leading zero (modulus MSB is always set for RSA-2048)
];

/// Fixed suffix: the exponent INTEGER encoding for e = 65537.
const RSA_PUBKEY_SUFFIX: [u8; 5] = [0x02, 0x03, 0x01, 0x00, 0x01];

/// Sentinel value used in the CSCA Merkle tree map to indicate that a key is
/// present. Any non-default value works.
const CSCA_MAP_PRESENT: u64 = 1;

/// Maximum number of bytes that can be packed into a single native field
/// element without overflow: `floor(F::CAPACITY / 8)`. For BLS12-381
/// scalar field (~255-bit modulus), this is 31 bytes (248 bits).
const BYTES_PER_FIELD_ELEMENT: usize = (F::CAPACITY / 8) as usize;

// -----------------------------------------------------------------------
// Instance and witness types
// -----------------------------------------------------------------------

/// The off-circuit Merkle tree map for CSCA keys.
type CscaMap = MapMt<F, PoseidonChip<F>>;

/// Public inputs: Poseidon Merkle root of trusted CSCA key set.
type Instance = F;

/// Witness: SOD bytes, DG1 bytes, CSCA modulus (big-endian), CSCA map.
type Witness = (Vec<u8>, [u8; DG1_LEN], [u8; RSA_BYTES], CscaMap);

#[derive(Clone, Default)]
pub struct PassportVerification;

impl Relation for PassportVerification {
    type Instance = Instance;
    type Witness = Witness;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let biguint = std_lib.biguint();
        let scanner = std_lib.scanner();

        // -- Assign witness --
        let dg1_bytes = witness.as_ref().map(|(_, dg1, _, _)| *dg1);
        let csca_key_bytes = witness.as_ref().map(|(_, _, m, _)| *m);

        // -- Step 1: Parse SOD --
        let spec = spec::sod_sha256_rsa2048_spec();
        let mut sod_raw_buf: Vec<u8> = Vec::new();
        witness.as_ref().map(|(sod, _, _, _)| sod_raw_buf = sod.clone());
        let mut sod_input: &[u8] = &sod_raw_buf;
        let sod_result = scanner
            .parse_asn1_varlen::<&str, TAG_M, LEN_M, VAL_M, VAL_A, SOD_M, SOD_A>(
                layouter,
                &mut sod_input,
                spec,
            )?;

        // Fixlen extractions:
        let hash_dg1_from_sod = sod_result.get_fixlen(&"hashDg1");
        let message_digest = sod_result.get_fixlen(&"messageDigest");
        let ds_signature_bytes = sod_result.get_fixlen(&"dsSignature");
        let ds_public_key_bytes = sod_result.get_fixlen(&"dsPublicKey");
        let csca_signature_bytes = sod_result.get_fixlen(&"cscaSignature");
        let signed_attrs = sod_result.get_fixlen(&"signedAttrs");

        // Varlen extractions (ScannerVec -> byte vector for hashing):
        let econtent_sv = sod_result.get_varlen_val(&"eContent");
        let econtent_bytes = scanner.scanner_vec_to_byte_vector(layouter, econtent_sv)?;

        let tbs_sv = sod_result.get_varlen_val(&"tbsCertificate");
        let tbs_bytes = scanner.scanner_vec_to_byte_vector(layouter, tbs_sv)?;

        // -- Step 2: CSCA signature verification --
        // Assign the CSCA key from the witness and verify the signature.
        let mut csca_key_assigned =
            std_lib.assign_many(layouter, &csca_key_bytes.transpose_array())?;
        csca_key_assigned.reverse();
        let csca_key_biguint = biguint.from_le_bytes(layouter, &csca_key_assigned)?;

        let tbs_hash = std_lib.sha2_256_varlen(layouter, &tbs_bytes)?;
        // cscaSignature is a BIT STRING (257 bytes): skip the unused-bits byte.
        let csca_sig_raw: &[AssignedByte<F>; RSA_BYTES] =
            csca_signature_bytes[1..].try_into().expect("257 - 1 = 256");
        verify_rsa_pkcs1_sha256(
            std_lib,
            layouter,
            &tbs_hash,
            csca_sig_raw,
            &csca_key_biguint,
        )?;

        // -- Step 3: CSCA key membership --
        // Pack the CSCA key bytes into field elements (31 bytes each) and
        // Poseidon-hash them to derive the map lookup key.
        let csca_packed = pack_bytes_to_field_elements(std_lib, layouter, &csca_key_assigned)?;
        let csca_map_key = std_lib.poseidon(layouter, &csca_packed)?;

        let mut csca_map = std_lib.map_gadget().clone();
        csca_map.init(layouter, witness.map(|(_, _, _, map)| map))?;

        // Public input: the Merkle root of the trusted CSCA key set.
        std_lib.constrain_as_public_input(layouter, &csca_map.succinct_repr())?;

        // Membership check: the value at csca_map_key must be CSCA_MAP_PRESENT.
        let map_value = csca_map.get(layouter, &csca_map_key)?;
        std_lib.assert_equal_to_fixed(layouter, &map_value, F::from(CSCA_MAP_PRESENT))?;

        // -- Step 4: DS signature verification --
        let sa_hash = std_lib.sha2_256(layouter, signed_attrs)?;
        let ds_modulus = parse_rsa_public_key(std_lib, layouter, ds_public_key_bytes)?;
        let ds_sig_raw: &[AssignedByte<F>; RSA_BYTES] =
            ds_signature_bytes.try_into().expect("256 bytes");
        verify_rsa_pkcs1_sha256(std_lib, layouter, &sa_hash, ds_sig_raw, &ds_modulus)?;

        // -- Step 5: eContent integrity --
        let econtent_hash = std_lib.sha2_256_varlen(layouter, &econtent_bytes)?;
        for (computed, expected) in econtent_hash.iter().zip(message_digest.iter()) {
            std_lib.assert_equal(layouter, computed, expected)?;
        }

        // -- Step 6: DG1 integrity --
        let dg1_values: [Value<u8>; DG1_LEN] = dg1_bytes.transpose_array();
        let dg1_assigned = std_lib.assign_many(layouter, &dg1_values)?;
        let dg1_hash = std_lib.sha2_256(layouter, &dg1_assigned)?;
        for (computed, expected) in dg1_hash.iter().zip(hash_dg1_from_sod.iter()) {
            std_lib.assert_equal(layouter, computed, expected)?;
        }

        // At this point, the DG1 bytes are authenticated. The caller
        // can extract MRZ fields using the constants from
        // `passport_spec` (e.g., `DG1_DOB`, `DG1_NAME`).

        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            poseidon: true,
            automaton: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PassportVerification)
    }
}

// -----------------------------------------------------------------------
// CSCA map construction (off-circuit)
// -----------------------------------------------------------------------

/// Builds the off-circuit CSCA Merkle tree map from a list of trusted
/// CSCA keys (RSA-2048, big-endian bytes). Each key is packed into
/// field elements (31 bytes each, little-endian) and Poseidon-hashed
/// to derive the map key.
pub fn build_csca_map(trusted_keys: &[[u8; RSA_BYTES]]) -> CscaMap {
    let mut map = CscaMap::new(&F::ZERO);
    for key_bytes in trusted_keys {
        let map_key = csca_map_key_offcircuit(key_bytes);
        map.insert(&map_key, &F::from(CSCA_MAP_PRESENT));
    }
    map
}

/// Off-circuit computation of the CSCA map key: pack bytes into field
/// elements (31 bytes each, little-endian: `sum(byte[i] * 256^i)`) and
/// Poseidon-hash them. Must match the in-circuit computation in
/// `pack_bytes_to_field_elements` + `poseidon`.
fn csca_map_key_offcircuit(key_bytes: &[u8; RSA_BYTES]) -> F {
    use midnight_circuits::{hash::poseidon::PoseidonChip, instructions::hash::HashCPU};

    let packed: Vec<F> = key_bytes
        .chunks(BYTES_PER_FIELD_ELEMENT)
        .map(|chunk| {
            chunk.iter().enumerate().fold(F::ZERO, |acc, (i, &b)| {
                acc + F::from(b as u64) * F::from(256u64).pow([i as u64])
            })
        })
        .collect();
    PoseidonChip::<F>::hash(&packed)
}

// -----------------------------------------------------------------------
// Helper functions
// -----------------------------------------------------------------------

/// Packs a byte slice into native field elements,
/// [`BYTES_PER_FIELD_ELEMENT`] bytes per element (little-endian,
/// according to field capacity). Used to prepare the CSCA key for
/// Poseidon hashing.
fn pack_bytes_to_field_elements(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    bytes: &[AssignedByte<F>],
) -> Result<Vec<AssignedNative<F>>, Error> {
    bytes
        .chunks(BYTES_PER_FIELD_ELEMENT)
        .map(|chunk| {
            let terms: Vec<(F, AssignedNative<F>)> = chunk
                .iter()
                .enumerate()
                .map(|(i, b)| {
                    // 256^i for little-endian packing.
                    let coeff = F::from(256u64).pow([i as u64]);
                    (coeff, b.clone().into())
                })
                .collect();
            std_lib.linear_combination(layouter, &terms, F::ZERO)
        })
        .collect()
}

/// Verifies an RSA-2048 PKCS#1 v1.5 signature over a SHA-256 hash.
///
/// `signature_bytes` must be exactly 256 bytes of raw signature (big-endian).
/// When the ASN.1 extraction produces a BIT STRING (e.g., cscaSignature,
/// 257 bytes), the caller must skip the leading unused-bits byte (0x00)
/// before calling this function: `&csca_sig[1..]`.
/// When the extraction produces an OCTET STRING (e.g., dsSignature,
/// 256 bytes), the bytes can be passed directly.
///
/// Checks that `signature^e mod modulus` equals the PKCS#1 v1.5
/// padded encoding of `hash`:
///
/// ```text
/// 0x00 0x01 [0xFF; 202] 0x00 <DigestInfo> <hash>
/// ```
fn verify_rsa_pkcs1_sha256(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    hash: &[AssignedByte<F>; 32],
    signature_bytes: &[AssignedByte<F>; RSA_BYTES],
    modulus: &AssignedBigUint<F>,
) -> Result<(), Error> {
    let biguint = std_lib.biguint();

    // Convert signature bytes (big-endian, 256 bytes) to BigUint.
    let sig_le: Vec<AssignedByte<F>> = signature_bytes.iter().rev().cloned().collect();
    let signature_biguint = biguint.from_le_bytes(layouter, &sig_le)?;

    // Compute signature^e mod modulus.
    let recovered = biguint.mod_exp(layouter, &signature_biguint, RSA_E, modulus)?;

    // Build the expected PKCS#1 v1.5 padded message from the hash.
    // Layout (256 bytes, big-endian):
    //   [0x00, 0x01] [0xFF; 202] [0x00] [DigestInfo; 19] [hash; 32]
    // = 2 + 202 + 1 + 19 + 32 = 256 bytes
    let padding_len = RSA_BYTES - 3 - PKCS1_SHA256_DIGEST_INFO.len() - 32; // = 202

    let mut padded_be: Vec<AssignedByte<F>> = Vec::with_capacity(RSA_BYTES);
    padded_be.push(std_lib.assign_fixed(layouter, 0x00u8)?);
    padded_be.push(std_lib.assign_fixed(layouter, 0x01u8)?);
    for _ in 0..padding_len {
        padded_be.push(std_lib.assign_fixed(layouter, 0xFFu8)?);
    }
    padded_be.push(std_lib.assign_fixed(layouter, 0x00u8)?);
    for &b in &PKCS1_SHA256_DIGEST_INFO {
        padded_be.push(std_lib.assign_fixed(layouter, b)?);
    }
    padded_be.extend_from_slice(hash);
    assert_eq!(padded_be.len(), RSA_BYTES);

    // Convert to little-endian and build BigUint.
    padded_be.reverse();
    let expected = biguint.from_le_bytes(layouter, &padded_be)?;

    biguint.assert_equal(layouter, &recovered, &expected)
}

/// Parses the DS public key modulus from the BIT STRING content
/// extracted from SubjectPublicKeyInfo.
///
/// The 269-byte content has a fixed DER structure for RSA-2048:
///
/// ```text
/// 0x00                          -- unused bits
/// 0x30 0x82 0x01 0x22           -- SEQUENCE (290 bytes)
///   0x02 0x82 0x01 0x01 0x00    -- INTEGER (257 bytes, with leading zero)
///     <256 bytes modulus>
///   0x02 0x03 0x01 0x00 0x01    -- INTEGER (65537)
/// ```
fn parse_rsa_public_key(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    bit_string_content: &[AssignedByte<F>],
) -> Result<AssignedBigUint<F>, Error> {
    let biguint = std_lib.biguint();

    assert_eq!(
        bit_string_content.len(),
        spec::RSA2048_BIT_STRING_LEN,
        "unexpected BIT STRING content length for RSA-2048 public key"
    );

    // Verify prefix (fixed DER headers).
    for (assigned, &expected) in bit_string_content.iter().zip(RSA_PUBKEY_PREFIX.iter()) {
        std_lib.assert_equal_to_fixed(layouter, assigned, expected)?;
    }

    // Extract 256-byte modulus (big-endian).
    let modulus_offset = RSA_PUBKEY_PREFIX.len();
    let modulus_be = &bit_string_content[modulus_offset..modulus_offset + RSA_BYTES];

    // Verify suffix (exponent = 65537).
    let suffix_offset = modulus_offset + RSA_BYTES;
    for (assigned, &expected) in
        bit_string_content[suffix_offset..].iter().zip(RSA_PUBKEY_SUFFIX.iter())
    {
        std_lib.assert_equal_to_fixed(layouter, assigned, expected)?;
    }

    // Convert modulus bytes (big-endian) to BigUint (little-endian).
    let modulus_le: Vec<AssignedByte<F>> = modulus_be.iter().rev().cloned().collect();
    biguint.from_le_bytes(layouter, &modulus_le)
}
