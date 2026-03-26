//! Passport verification circuit definition (SHA-256 + RSA-2048). See [module
//! level documentation](super) for more details.
//!
//! # Test data
//!
//! Synthetic test fixtures can be generated with the Python script at
//! `credentials/generate.py`. It produces a fake SOD, DG1, and CSCA
//! key for the SHA-256 + RSA-2048 algorithm pair. MRZ fields (name,
//! DOB, passport number, etc.) are configurable via command-line
//! arguments.
//!
//! ```sh
//! # Setup (once):
//! python3 -m venv venv && venv/bin/pip install cryptography
//!
//! # Generate with defaults:
//! venv/bin/python3 credentials/generate.py
//!
//! # Or with custom fields:
//! venv/bin/python3 credentials/generate.py \
//!     --surname DUPONT --given-names "JEAN MICHEL" --dob 900115
//! ```
//!
//! Output files in `credentials/<name>/`:
//! - `dg1.bin`: 93-byte DG1 (TLV header + 88-byte MRZ)
//! - `sod.der`: DER-encoded CMS ContentInfo (SignedData)
//! - `csca_key.bin`: 256-byte CSCA RSA-2048 modulus (big-endian)

use std::iter::once;

use midnight_circuits::{
    biguint::AssignedBigUint,
    instructions::{AssertionInstructions, AssignmentInstructions, PublicInputInstructions},
    parsing::scanner::asn1::der_encoding::encode_length,
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

/// Max total SOD (ContentInfo) size. Derived from `credential_maximal`
/// (16 DG hashes, 3 extra OU attributes per DN), which produces 2588
/// bytes.
///
/// Size breakdown (approximate):
///   - Fixed overhead (ContentInfo + SignedData framing): ~65 bytes
///   - eContent (LDSSecurityObject): ~20 + 39 * num_DGs bytes
///   - DS certificate: ~780 + DN padding bytes
///   - SignerInfo: ~370 + issuer DN duplication bytes
///   - Signatures (CSCA + DS): 2 * 260 = 520 bytes
///
/// Typical (2 DGs, short DNs): ~1400 bytes.
/// Maximum (16 DGs, padded DNs): ~2600 bytes.
const SOD_M: usize = 2588;

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
    0x30, 0x82, 0x01, 0x0A, // SEQUENCE header (266 bytes)
    0x02, 0x82, 0x01, 0x01, // INTEGER tag + length (257)
    0x00, // leading zero (modulus MSB is always set for RSA-2048)
];

/// Fixed suffix: the exponent INTEGER encoding for e = 65537.
const RSA_PUBKEY_SUFFIX: [u8; 5] = [0x02, 0x03, 0x01, 0x00, 0x01];

// -----------------------------------------------------------------------
// Instance and witness types
// -----------------------------------------------------------------------

/// Dummy CSCA registry with realistic proportions (536 keys, for various
/// algorithms reflecting the proportions observed in the ICAO
/// Public-Key-Directory in March 2026).
pub const CSCA_REGISTRY: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/passport/credentials/csca_public_keys.txt"
));
/// Conservative estimate of the number of bytes necessary to store the registry
/// (cumulative number of key bytes + separators).
const MAX_REGISTRY_SIZE: usize = 160000;

#[derive(Clone, Default)]
pub struct PassportVerification;

impl PassportVerification {
    /// Parses a CSCA key registry file (custom format). The format alternates
    /// comment lines (starting with `#`) and hex-encoded key lines:
    ///
    /// ```text
    /// # key 0: RSA-2048, C=NZ
    /// a1b2c3d4...
    /// # key 1: ECDSA-P256, C=SG
    /// 01020304...
    /// ```
    ///
    /// Returns a `Vec<Vec<u8>>` suitable for use as the circuit's
    /// `Instance`. Keys of all algorithms are included; only RSA-2048
    /// keys (256 bytes) are usable in the current circuit.
    pub fn parse_csca_registry(data: &str) -> Vec<Vec<u8>> {
        data.lines()
            .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
            .map(|hex_line| {
                let hex_line = hex_line.trim();
                assert!(
                    hex_line.len() % 2 == 0,
                    "odd-length hex line in CSCA registry"
                );
                (0..hex_line.len())
                    .step_by(2)
                    .map(|i| {
                        u8::from_str_radix(&hex_line[i..i + 2], 16)
                            .unwrap_or_else(|e| panic!("invalid hex in CSCA registry: {e}"))
                    })
                    .collect()
            })
            .collect()
    }

    /// Checks if `key` is in the CSCA registry. `idx` indicates at which offset
    /// the separator before the entry appears in the formatted registry.
    fn csca_member(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        key: [AssignedByte<F>; RSA_BYTES],
        formatted_registry: [AssignedNative<F>; MAX_REGISTRY_SIZE],
        idx: AssignedNative<F>,
    ) -> Result<(), Error> {
        let pad: AssignedNative<F> = std_lib.assign_fixed(layouter, F::from(256))?;
        let sub = once(pad.clone())
            .chain(key.into_iter().map(AssignedNative::from))
            .chain([pad])
            .collect::<Vec<_>>();
        std_lib.scanner().check_bytes_ext(layouter, &formatted_registry, &idx, &sub)
    }
}

/// Public inputs: List of CSCA keys. Storing all the keys with separators
/// should fit in `MAX_REGISTRY_SIZE` total byte count.
type Instance = Vec<Vec<u8>>;

/// Witness: SOD bytes, DG1 bytes, CSCA modulus (big-endian), the formatted CSCA
/// key registry, and the index at which the (separator before the) public key
/// appear in the registry.
#[derive(Debug, Clone)]
pub struct Witness {
    sod: Vec<u8>,
    dg1: [u8; DG1_LEN],
    pub_key: [u8; RSA_BYTES],
    registry: Vec<F>,
    idx: F,
}

impl PassportVerification {
    /// Formats the instance and returns the index at which the has been found,
    /// if any.
    fn format_csca(
        instance: &<Self as Relation>::Instance,
        pub_key: Option<[u8; RSA_BYTES]>,
    ) -> (Vec<F>, Option<F>) {
        let mut instance_padded: Vec<F> = vec![F::from(256); MAX_REGISTRY_SIZE];
        let mut index = None;
        // Starting at position 1 to have one 256 at the beginning.
        let mut position = 1;
        for key in instance {
            let key64: &[F] = &key.iter().map(|x| F::from(*x as u64)).collect::<Vec<_>>();
            instance_padded[position..position + key.len()].copy_from_slice(key64);
            if let Some(rsa_key) = pub_key {
                if index.is_none() && key == &rsa_key.to_vec() {
                    index = Some(F::from(position as u64 - 1));
                }
            }
            // +1 to insert a 256 between entries.
            position += key.len() + 1;
        }
        // Checks that there is at least one 256 at the end before returning.
        assert!(position < MAX_REGISTRY_SIZE - 1);
        assert!(pub_key.is_none() || index.is_some(), "public key not found");
        (instance_padded, index)
    }

    /// Creates a witness from the passport data, using the stored CSCA list.
    pub fn generate_witness(
        sod: Vec<u8>,
        dg1: [u8; DG1_LEN],
        pub_key: [u8; RSA_BYTES],
    ) -> <Self as Relation>::Witness {
        let parsed_instance = Self::parse_csca_registry(CSCA_REGISTRY);
        let (registry, idx) = Self::format_csca(&parsed_instance, Some(pub_key));
        let idx = idx.expect("unexpected format_csca failure");
        Witness {
            sod,
            dg1,
            pub_key,
            registry,
            idx,
        }
    }
}

impl Relation for PassportVerification {
    type Instance = Instance;
    type Witness = Witness;

    // Instances are formatted in a way that the result always has constant length
    // `MAX_REGISTRY_SIZE` (padded with 256). Separators 256 are also inserted
    // between different keys, as well as at the very beginning and the very end.
    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        let (instance_padded, _) = Self::format_csca(instance, None);
        Ok(instance_padded)
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

        // -- Initialisation --
        // Assign witnesses.
        let dg1_bytes = witness.as_ref().map(|w| w.dg1).transpose_array();
        let dg1_assigned = std_lib.assign_many(layouter, &dg1_bytes)?;
        let csca_key_bytes = witness.as_ref().map(|w| w.pub_key).transpose_array();
        let csca_key_assigned = std_lib.assign_many(layouter, &csca_key_bytes)?;
        let csca_idx_bytes = witness.as_ref().map(|w| w.idx);
        let csca_idx_assigned = std_lib.assign(layouter, csca_idx_bytes)?;

        // Constrain the public CSCA registry.
        let csca_registry =
            witness.as_ref().map(|w| w.registry.clone()).transpose_vec(MAX_REGISTRY_SIZE);
        let csca_registry_assigned = csca_registry
            .into_iter()
            .map(|slot| std_lib.assign_as_public_input(layouter, slot))
            .collect::<Result<Vec<AssignedNative<_>>, Error>>()?;

        // -- Step 1: Parse SOD --
        let spec = spec::sod_sha256_rsa2048_spec();
        let sod_input = witness.as_ref().map(|w| w.sod.clone());
        let sod_result = scanner
            .parse_asn1_varlen::<&str, TAG_M, LEN_M, VAL_M, VAL_A, SOD_M, SOD_A>(
                layouter, sod_input, spec,
            )?;

        // Fixlen extractions.
        let hash_dg1_from_sod = sod_result.get_fixlen(&"hashDg1");
        let message_digest = sod_result.get_fixlen(&"messageDigest");
        let ds_signature_bytes = sod_result.get_fixlen(&"dsSignature");
        let ds_public_key_bytes = sod_result.get_fixlen(&"dsPublicKey");
        let csca_signature_bytes = sod_result.get_fixlen(&"cscaSignature");
        let signed_attrs = sod_result.get_fixlen(&"signedAttrs");

        // Varlen extractions (conversion ScannerVec -> AssignedVector for hashing).
        let econtent_sv = sod_result.get_varlen_val(&"eContent");
        let econtent_bytes = scanner.scanner_vec_to_byte_vector(layouter, econtent_sv)?;

        let tbs_sv = sod_result.get_varlen_val(&"tbsCertificate");
        let tbs_bytes = scanner.scanner_vec_to_byte_vector(layouter, tbs_sv)?;

        // -- Step 2: CSCA signature verification --
        let csca_key_le: Vec<AssignedByte<F>> = csca_key_assigned.iter().rev().cloned().collect();
        let csca_key_biguint = biguint.from_le_bytes(layouter, &csca_key_le)?;

        let tbs_hash = std_lib.sha2_256_varlen(layouter, &tbs_bytes)?;
        let csca_sig_raw: &[AssignedByte<F>; RSA_BYTES] =
            csca_signature_bytes[1..].try_into().expect("257 - 1 = 256");
        verify_rsa_pkcs1_sha256(
            std_lib,
            layouter,
            &tbs_hash,
            csca_sig_raw,
            &csca_key_biguint,
        )?;

        // // -- Step 3: CSCA key membership --
        Self::csca_member(
            std_lib,
            layouter,
            csca_key_assigned.try_into().unwrap(),
            csca_registry_assigned.try_into().unwrap(),
            csca_idx_assigned,
        )?;

        // // -- Step 4: DS signature verification --
        let sa_set_header =
            once(0x31u8).chain(encode_length(signed_attrs.len())).collect::<Vec<_>>();
        let sa_header_assigned = std_lib.assign_many_fixed(layouter, &sa_set_header)?;
        let sa_for_hashing: Vec<AssignedByte<F>> =
            sa_header_assigned.iter().chain(signed_attrs.iter()).cloned().collect();
        let sa_hash = std_lib.sha2_256(layouter, &sa_for_hashing)?;
        let ds_modulus = parse_rsa_public_key(std_lib, layouter, ds_public_key_bytes)?;
        let ds_sig_raw: &[AssignedByte<F>; RSA_BYTES] =
            ds_signature_bytes.try_into().expect("256 bytes");
        verify_rsa_pkcs1_sha256(std_lib, layouter, &sa_hash, ds_sig_raw, &ds_modulus)?;

        // -- Step 5: eContent integrity --
        let econtent_hash = std_lib.sha2_256_varlen(layouter, &econtent_bytes)?;
        assert_bytes_equal(std_lib, layouter, &econtent_hash, message_digest)?;

        // -- Step 6: DG1 integrity --
        let dg1_hash = std_lib.sha2_256(layouter, &dg1_assigned)?;
        assert_bytes_equal(std_lib, layouter, &dg1_hash, hash_dg1_from_sod)?;

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
    let prefix: Vec<u8> = ([0x00, 0x01].into_iter())
        .chain(vec![0xFF; padding_len])
        .chain([0x00])
        .chain(PKCS1_SHA256_DIGEST_INFO)
        .collect();
    let prefix_assigned: Vec<AssignedByte<F>> = std_lib.assign_many_fixed(layouter, &prefix)?;
    padded_be.extend_from_slice(&prefix_assigned);
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
    assert_eq!(
        bit_string_content.len(),
        spec::RSA2048_BIT_STRING_LEN,
        "unexpected BIT STRING content length for RSA-2048 public key"
    );
    let biguint = std_lib.biguint();

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

/// Asserts that two byte slices are element-wise equal.
fn assert_bytes_equal(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    a: &[AssignedByte<F>],
    b: &[AssignedByte<F>],
) -> Result<(), Error> {
    assert_eq!(a.len(), b.len(), "byte slices must have equal length");
    for (x, y) in a.iter().zip(b.iter()) {
        std_lib.assert_equal(layouter, x, y)?;
    }
    Ok(())
}
