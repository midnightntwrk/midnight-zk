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

use ff::{Field, PrimeField};
use midnight_circuits::{
    biguint::AssignedBigUint,
    hash::poseidon::PoseidonChip,
    instructions::{
        hash::HashCPU,
        map::{MapCPU, MapInstructions},
        ArithInstructions, AssertionInstructions, AssignmentInstructions,
        DecompositionInstructions, PublicInputInstructions, RangeCheckInstructions,
    },
    map::cpu::MapMt,
    parsing::{scanner::asn1::der_encoding::encode_length, DateFormat, Separator},
    types::{AssignedByte, AssignedNative},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use num_bigint::BigUint;

use super::{DG1_DOB, DG1_LEN, PKCS1_SHA256_DIGEST_INFO, RSA_BYTES, RSA_E, RSA_PUBKEY_PREFIX};

type F = midnight_curves::Fq;

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
/// directly (only extracted parts are), so alignment can be anything.
const SOD_A: usize = 1;

// -----------------------------------------------------------------------
// Instance and witness types
// -----------------------------------------------------------------------

// Hack to be able to display the path to the CSCA whitelist of issuers, while
// also using it in an `include_str!`.
macro_rules! csca_path {
    () => {
        "credentials/csca_public_keys.txt"
    };
}

/// Dummy CSCA registry with realistic proportions (536 keys, for various
/// algorithms reflecting the proportions observed in the ICAO
/// Public-Key-Directory in March 2026).
pub const CSCA_REGISTRY: &str = include_str!(csca_path!());
/// Path to `CSCA_REGISTRY` from `zk_stdlib`.
pub const CSCA_PATH: &str = concat!("examples/identity/passport/", csca_path!());

/// Sentinel value used in the CSCA Merkle tree map to indicate that a key is
/// present. Any non-default value works.
const CSCA_MAP_PRESENT: u64 = 1;

/// Maximum number of bytes that can be packed into a single native field
/// element without overflow, here BLS12-381 scalar field.
const BYTES_PER_FIELD_ELEMENT: usize = (F::CAPACITY / 8) as usize;

/// The off-circuit Merkle tree map for CSCA keys.
type CscaMap = MapMt<F, PoseidonChip<F>>;

/// Public inputs: CSCA Merkle root + reference date for age verification.
#[derive(Clone, Copy)]
pub(crate) struct Instance {
    /// Poseidon Merkle root of the trusted CSCA key set.
    pub(crate) csca_merkle_root: F,
    /// Reference date (YYYYMMDD encoding) for age verification.
    pub(crate) reference_date: F,
    /// Century base N ∈ [0, 99] for resolving 2-digit years. The MRZ date
    /// of birth YY is interpreted in the window [1900+N, 2000+N).
    pub(crate) century_base: F,
}

/// Witness: SOD bytes, DG1 bytes, CSCA modulus (big-endian), CSCA Merkle map.
#[derive(Clone)]
pub(crate) struct Witness {
    sod: Vec<u8>,
    dg1: [u8; DG1_LEN],
    csca_key: [u8; RSA_BYTES],
    csca_map: CscaMap,
}

impl Witness {
    /// Returns the CSCA Merkle root derived from this witness.
    pub fn csca_merkle_root(&self) -> F {
        self.csca_map.succinct_repr()
    }
}

#[derive(Clone, Default)]
pub(crate) struct PassportVerification;

impl PassportVerification {
    /// Parses a CSCA key registry file (custom format from `CSCA_REGISTRY`).
    /// The format alternates comment lines (starting with `#`) and
    /// hex-encoded key lines:
    ///
    /// ```text
    /// # key 0: RSA-2048, C=NZ
    /// a1b2c3d4...
    /// # key 1: ECDSA-P256, C=SG
    /// 01020304...
    /// ```
    ///
    /// Returns the raw key bytes. All keys are included regardless of the
    /// signing algorithm.
    fn parse_csca_registry(data: &str) -> Vec<Vec<u8>> {
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

    /// Builds the CSCA Merkle tree map from the hardcoded registry.
    /// All keys are included regardless of algorithm; the circuit's
    /// signature verification step will reject unsupported key types.
    fn build_csca_map() -> CscaMap {
        let keys = Self::parse_csca_registry(CSCA_REGISTRY);
        let mut map = CscaMap::new(&F::ZERO);
        for key_bytes in &keys {
            // Packing the key into big-endian bytes.
            let packed: Vec<F> = (key_bytes.chunks(BYTES_PER_FIELD_ELEMENT))
                .map(|chunk| {
                    chunk.iter().fold(F::ZERO, |acc, &b| acc * F::from(256) + F::from(b as u64))
                })
                .collect();
            // Insert the hash in the Merkle tree.
            let map_key = PoseidonChip::<F>::hash(&packed);
            map.insert(&map_key, &F::from(CSCA_MAP_PRESENT));
        }
        map
    }

    /// Creates a witness from the passport data, building the CSCA map
    /// from the hardcoded registry.
    pub(crate) fn generate_witness(
        sod: Vec<u8>,
        dg1: [u8; DG1_LEN],
        csca_key: [u8; RSA_BYTES],
    ) -> Witness {
        let csca_map = Self::build_csca_map();
        Witness {
            sod,
            dg1,
            csca_key,
            csca_map,
        }
    }
}

impl Relation for PassportVerification {
    type Instance = Instance;
    type Witness = Witness;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![
            instance.csca_merkle_root,
            instance.reference_date,
            instance.century_base,
        ])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let biguint = std_lib.biguint();
        let scanner = std_lib.scanner();

        let dg1_bytes = witness.as_ref().map(|w| w.dg1);
        let csca_key_bytes = witness.as_ref().map(|w| w.csca_key);
        let sod_input = witness.as_ref().map(|w| w.sod.clone());
        let csca_map_off_circuit = witness.map(|w| w.csca_map);

        // -- Step 1: Parse SOD --
        let spec = super::sod_sha256_rsa2048_spec();
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
        let csca_key = std_lib.assign_many(layouter, &csca_key_bytes.transpose_array())?;
        let csca_key_biguint = biguint.from_be_bytes(layouter, &csca_key)?;

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

        // -- Step 3: CSCA key membership --
        // Pack the original big-endian bytes, matching the off-circuit packing
        // convention (see `build_csca_map()`).
        let csca_packed = (csca_key.chunks(BYTES_PER_FIELD_ELEMENT))
            .map(|chunk| std_lib.assigned_from_be_bytes(layouter, chunk))
            .collect::<Result<Vec<_>, Error>>()?;
        let map_key = std_lib.poseidon(layouter, &csca_packed)?;

        let mut csca_map = std_lib.map_gadget().clone();
        csca_map.init(layouter, csca_map_off_circuit)?;
        std_lib.constrain_as_public_input(layouter, &csca_map.succinct_repr())?;

        let map_value = csca_map.get(layouter, &map_key)?;
        std_lib.assert_equal_to_fixed(layouter, &map_value, F::from(CSCA_MAP_PRESENT))?;

        // // -- Step 4: DS signature verification --
        let sa_set_header =
            once(0x31u8).chain(encode_length(signed_attrs.len())).collect::<Vec<_>>();
        let sa_header_assigned = std_lib.assign_many_fixed(layouter, &sa_set_header)?;
        let sa_for_hashing: Vec<AssignedByte<F>> =
            sa_header_assigned.iter().chain(signed_attrs.iter()).cloned().collect();
        let sa_hash = std_lib.sha2_256(layouter, &sa_for_hashing)?;
        let ds_modulus = biguint.from_be_bytes(
            layouter,
            &ds_public_key_bytes[RSA_PUBKEY_PREFIX.len()..RSA_PUBKEY_PREFIX.len() + RSA_BYTES],
        )?;
        let ds_sig_raw: &[AssignedByte<F>; RSA_BYTES] =
            ds_signature_bytes.try_into().expect("256 bytes");
        verify_rsa_pkcs1_sha256(std_lib, layouter, &sa_hash, ds_sig_raw, &ds_modulus)?;

        // -- Step 5: eContent integrity --
        let econtent_hash = std_lib.sha2_256_varlen(layouter, &econtent_bytes)?;
        scanner.assert_equal_fixlen(layouter, &econtent_hash, message_digest)?;

        // -- Step 6: DG1 integrity --
        let dg1_assigned: Vec<AssignedByte<F>> =
            std_lib.assign_many(layouter, &dg1_bytes.transpose_array())?;
        let dg1_hash = std_lib.sha2_256(layouter, &dg1_assigned)?;
        scanner.assert_equal_fixlen(layouter, &dg1_hash, hash_dg1_from_sod)?;

        // -- Step 7: Age verification (18+) --
        let reference_date: AssignedNative<F> =
            std_lib.assign_as_public_input(layouter, instance.map(|i| i.reference_date))?;
        let century_base: AssignedNative<F> =
            std_lib.assign_as_public_input(layouter, instance.map(|i| i.century_base))?;
        std_lib.assert_lower_than_fixed(layouter, &century_base, &BigUint::from(100u64))?;

        let dob_bytes = &dg1_assigned[DG1_DOB.start..DG1_DOB.end];
        assert_age_over(
            std_lib,
            layouter,
            dob_bytes,
            &reference_date,
            &century_base,
            18,
        )?;

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

/// Asserts that a 6-byte YYMMDD MRZ date of birth represents a person who is
/// at least `age_years` old on `reference_date` (an assigned YYYYMMDD value,
/// typically a public input). Century resolution is parameterised by
/// `century_base` (see [`DateFormat::YYMMDD`]).
fn assert_age_over(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    dob_yymmdd: &[AssignedByte<F>],
    reference_date: &AssignedNative<F>,
    century_base: &AssignedNative<F>,
    age_years: u16,
) -> Result<(), Error> {
    let format = (DateFormat::YYMMDD, Separator::NoSep);
    let dob_full =
        std_lib.parser().date_to_int(layouter, dob_yymmdd, format, Some(century_base))?;

    // diff = reference_date - age_years * 10_000 - dob_full.
    //   - If the person is old enough, the value is a small field element.
    //   - If the person is too young, the negative value wraps to a huge field
    //     element.
    // The range check reflects this situation. The bound 2^20 > 1_001_130 (max date
    // span in YYYYMMDD encoding) is a cheap power-of-2 check.
    let diff = std_lib.linear_combination(
        layouter,
        &[(F::ONE, reference_date.clone()), (-F::ONE, dob_full)],
        -F::from(age_years as u64 * 10_000),
    )?;
    std_lib.assert_lower_than_fixed(layouter, &diff, &BigUint::from(1u64 << 20))?;

    Ok(())
}
