//! Zero-knowledge passport verification (ICAO 9303).
//!
//! This module implements a ZK circuit that proves possession of a valid
//! biometric passport without revealing its contents. The current
//! implementation targets the **SHA-256 + RSA-2048** algorithm pair.
//!
//! # Overview
//!
//! An ICAO 9303 biometric passport stores identity data in numbered
//! Data Groups (DG1 for the MRZ, DG2 for the photo, etc.) on an NFC
//! chip. A Security Object Document (SOD) contains hashes of all DGs,
//! signed by the issuing country's Document Signer (DS) certificate,
//! which is in turn signed by the Country Signing CA (CSCA).
//!
//! # Verification chain (in-circuit)
//!
//! 1. **Parse the SOD** to extract: eContent, signedAttrs, messageDigest,
//!    tbsCertificate, dsPublicKey, dsSignature, cscaSignature, and hashDg1.
//!
//! 2. **Verify the CSCA signature** on the DS certificate:
//!    `SHA-256(tbsCertificate)` + PKCS#1 v1.5 + RSA-2048.
//!
//! 3. **Prove CSCA key membership**: the CSCA key used in step 2 belongs to the
//!    trusted set (a Poseidon Merkle tree whose root is a public input).
//!
//! 4. **Verify the DS signature** on the signed attributes:
//!    `SHA-256(signedAttrs)` + PKCS#1 v1.5 + RSA-2048.
//!
//! 5. **Verify eContent integrity**: `SHA-256(eContent) == messageDigest`.
//!
//! 6. **Verify DG1 integrity**: `SHA-256(DG1) == hashDg1`.
//!
//! 7. **Age verification**: the DG1 date of birth is at least 18 years before
//!    the reference date (public input), with configurable century
//!    disambiguation for 2-digit MRZ years.
//!
//! Using **committed instances**, this proof pipieline can be made more
//! modular. E.g., by performing step 1. to 6. only once, and generating proofs
//! for step 7. later, on demand, depending on the attribute to be disclosed
//! (age, citizenship...).
//!
//! # Inputs
//!
//! **Public input (instance):**
//! - Poseidon Merkle root of the trusted CSCA key set.
//! - Reference date (YYYYMMDD encoding) for age verification.
//! - Century base N in \[0, 99\]: the 2-digit MRZ year YY is interpreted in the
//!   window \[1900+N, 2000+N\).
//!
//! **Private input (witness):**
//! - The full SOD bytes (DER-encoded CMS ContentInfo, typically ~1700 bytes).
//! - The full DG1 bytes (93 bytes for TD3: TLV header + 88-byte MRZ).
//! - The CSCA public key (RSA-2048 modulus, 256 bytes big-endian).
//! - The Poseidon Merkle tree of trusted CSCA keys (for the membership proof
//!   path).
//!
//! In practice, the private input data are obtained by reading the passport
//! chip via NFC. The white list of CSCA-allowed keys is available online via
//! the ICAO Public Key Directory. In order to avoid having real passport data
//! stored in the repository, we made up our own dummy credentials, and
//! therefore use a made-up CSCA white list. It mimicks the size and algorithm
//! representation of the real one, as of March 2026.
//!
//! # Scope and limitations
//!
//! This example performs **passive authentication** only: it verifies
//! the SOD signature chain (CSCA -> DS -> SOD -> DG hashes) and checks
//! a property of the authenticated DG1 (age). This proves that the
//! **data** is genuine (signed by a trusted issuing authority), but does
//! **not** prove that the prover is the legitimate owner of the passport.
//! Anyone who obtained a copy of the SOD and DG1 (e.g., via NFC
//! skimming) could generate the same proof.
//!
//! Production applications should address this missing **proof of
//! ownership** based on their workflow and trust assumptions. ICAO 9303
//! defines two chip authentication mechanisms for this purpose:
//!
//! - **Active Authentication (AA)**, stored in **DG15** (an older mechanism
//!   with declining adoption). The passport chip holds a private key and signs
//!   a challenge from the reader. To bring this into a ZK proof, one would: (1)
//!   extend the `Asn1Spec` to extract `hashDg15`, (2) hash DG15 in-circuit and
//!   check it against the SOD, (3) verify the AA signature over a verifier
//!   chosen challenge in-circuit.
//!
//!   Developers however have to decide where they wish to verify this
//!   signature. Is it done off-circuit? Is it done once, in-circuit? Is it done
//!   at each verification? Each solution implies different assumptions on
//!   relation between the proving and verifying device, in when it is
//!   acceptable to have access to the passport to perform an AA...
//!
//! - **Chip Authentication (CA)**, stored in **DG14** (more common in recent
//!   passports, particularly in the EU). The chip and reader perform an ECDH
//!   key agreement (typically on brainpoolP256r1 or P-256). A successful
//!   exchange proves the chip holds the private key matching the public key in
//!   DG14. In-circuit, this amounts to a scalar multiplication on the relevant
//!   curve.
//!
//!   Similarly to AA, the questions of when to perform this authentication, and
//!   how, are left to the developers and the specific context of their
//!   application's deployment.
//!
//! - Not all passports support AA or CA; some only implement BAC/PACE for
//!   access control with no chip authentication at all. In those cases,
//!   alternative binding mechanisms (e.g., linking the proof to a
//!   holder-controlled key pair, as in the JWT enrollment example) may be
//!   considered. Or, simply, using the passport number and app-level mechanisms
//!   involving it (e.g., hashing it with a salt the app would store somehwere).
//!   The latter type of solutions are typically more lightweight, but do not
//!   offer unlinkability (i.e., the verifier knows when they verify two
//!   different statements from the same user).

pub mod circuit;

use std::ops::Range;

use midnight_circuits::parsing::scanner::asn1::Asn1Spec;

// -----------------------------------------------------------------------
// OIDs used in the spec
// -----------------------------------------------------------------------

/// OID 1.2.840.113549.1.7.2:CMS signedData.
const OID_SIGNED_DATA: &[u32] = &[1, 2, 840, 113549, 1, 7, 2];

/// OID 2.16.840.1.101.3.4.2.1:SHA-256.
const OID_SHA256: &[u32] = &[2, 16, 840, 1, 101, 3, 4, 2, 1];

/// OID 2.23.136.1.1.1:LDSSecurityObject (ICAO).
const OID_LDS_SECURITY_OBJECT: &[u32] = &[2, 23, 136, 1, 1, 1];

/// OID 1.2.840.113549.1.9.3:contentType (CMS attribute).
const OID_CONTENT_TYPE: &[u32] = &[1, 2, 840, 113549, 1, 9, 3];

/// OID 1.2.840.113549.1.9.4:messageDigest (CMS attribute).
const OID_MESSAGE_DIGEST: &[u32] = &[1, 2, 840, 113549, 1, 9, 4];

/// OID 1.2.840.113549.1.1.11:SHA-256 with RSA encryption.
const OID_SHA256_RSA: &[u32] = &[1, 2, 840, 113549, 1, 1, 11];

/// OID 1.2.840.113549.1.1.1:RSA encryption.
const OID_RSA: &[u32] = &[1, 2, 840, 113549, 1, 1, 1];

// -----------------------------------------------------------------------
// RSA related constants
// -----------------------------------------------------------------------

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

/// RSA-2048 key size in bits.
const RSA_BITS: u32 = 2048;

/// RSA-2048 key size in bytes.
const RSA_BYTES: usize = (RSA_BITS / 8) as usize;

/// RSA public exponent. Passports commonly use e = 65537.
const RSA_E: u64 = 65537;

/// BIT STRING content size for an RSA-2048 public key.
const RSA2048_BIT_STRING_LEN: usize = RSA_PUBKEY_PREFIX.len() + RSA_BYTES + RSA_PUBKEY_SUFFIX.len();

/// RSA-2048 signature size: always exactly 256 bytes. BIT STRING
/// content = 1 (unused bits) + 256 = 257 bytes.
const RSA2048_SIG_BIT_STRING_LEN: usize = 257;

/// RSA-2048 signature size as OCTET STRING content: 256 bytes.
const RSA2048_SIG_OCTET_STRING_LEN: usize = 256;

// -----------------------------------------------------------------------
// DG1 layout (TD3, 93 bytes total)
// -----------------------------------------------------------------------
//
// The hash of DG1 covers the entire 93-byte TLV (tag + length + MRZ).
//
// ```text
// 61 5B                     -- Application 1, constructed, length 91
//   5F1F 58                 -- Application 31, primitive, length 88
//     <line 1: 44 bytes>    -- document type, country, name
//     <line 2: 44 bytes>    -- passport number, DOB, sex, expiry, etc.
// ```
//
// Ranges for common fields are made explicit below.

/// DG1 size for TD3 documents (tag + length + MRZ).
const DG1_LEN: usize = 93;

/// Document type (e.g., "P<"). 2 bytes.
pub(crate) const DG1_DOC_TYPE: Range<usize> = 5..7;

/// Issuing state or organization (ISO 3166-1 alpha-3). 3 bytes.
pub(crate) const DG1_ISSUING_COUNTRY: Range<usize> = 7..10;

/// Surname and given names (separated by `<<`, padded with `<`). 39 bytes.
pub(crate) const DG1_NAME: Range<usize> = 10..49;

/// Passport number. 9 bytes.
pub(crate) const DG1_PASSPORT_NUMBER: Range<usize> = 49..58;

/// Nationality (ISO 3166-1 alpha-3). 3 bytes.
pub(crate) const DG1_NATIONALITY: Range<usize> = 59..62;

/// Date of birth (YYMMDD). 6 bytes.
pub(crate) const DG1_DOB: Range<usize> = 62..68;

/// Sex (M, F, or <). 1 byte.
pub(crate) const DG1_SEX: Range<usize> = 69..70;

/// Date of expiry (YYMMDD). 6 bytes.
pub(crate) const DG1_EXPIRY: Range<usize> = 70..76;

// -----------------------------------------------------------------------
// SOD spec (SHA-256 + RSA-2048)
// -----------------------------------------------------------------------

/// Builds the SOD spec for a SHA-256 + RSA-2048 passport.
///
/// Assumptions: single DigestAlgorithm (SHA-256), single SignerInfo,
/// single certificate, DG1 is the first DataGroupHash entry,
/// RSA-2048 keys.
///
/// ```text
/// SEQUENCE (ContentInfo)
///   OID signedData
///   [0] CONSTRUCTED
///     SEQUENCE (SignedData)
///       INTEGER 3
///       SET { AlgId(SHA-256, NULL) }
///       SEQUENCE (encapContentInfo)
///         OID ldsSecurityObject
///         [0] CONSTRUCTED
///           OCTET STRING (eContent)             -- EXTRACT
///       [0] IMPLICIT (certificates)
///         SEQUENCE (Certificate)
///           SEQUENCE (tbsCertificate)           -- EXTRACT
///             [0] { INTEGER 2 }                 -- version v3 (fixed)
///             INTEGER serialNumber
///             AlgId(SHA256-RSA, NULL)            -- fixed
///             Name issuer
///             SEQUENCE validity
///             Name subject
///             SEQUENCE (subjectPublicKeyInfo)
///               AlgId(RSA, NULL)                -- fixed
///               BIT STRING (269 bytes)          -- EXTRACT
///           AlgId(SHA256-RSA, NULL)             -- fixed
///           BIT STRING (257 bytes)              -- EXTRACT
///       SET (signerInfos)
///         SEQUENCE (SignerInfo)
///           INTEGER 1
///           SEQUENCE (issuerAndSerialNumber)
///           AlgId(SHA-256, NULL)                -- fixed
///           [0] (signedAttrs)                   -- EXTRACT
///             SEQUENCE { contentType attr }
///             SEQUENCE { messageDigest attr }   -- EXTRACT
///           AlgId(SHA256-RSA, NULL)             -- fixed
///           OCTET STRING (256 bytes)            -- EXTRACT
/// ```
fn sod_sha256_rsa2048_spec() -> Asn1Spec<&'static str> {
    let econtent =
        Asn1Spec::new().read_octet_string(lds_security_object_spec().mark_full("eContent"));

    let signed_data = Asn1Spec::new().read_sequence(
        Asn1Spec::new()
            .read_integer_const(3)
            .read_set(Asn1Spec::new().read_algid_null(OID_SHA256))
            .read_sequence(Asn1Spec::new().read_oid(OID_LDS_SECURITY_OBJECT).read_ctx(0, econtent))
            .read_ctx(0, x509_certificate_spec())
            .read_set(signer_info_spec()),
    );

    Asn1Spec::new()
        .read_sequence(Asn1Spec::new().read_oid(OID_SIGNED_DATA).read_ctx(0, signed_data))
}

// -----------------------------------------------------------------------
// Sub-specs
// -----------------------------------------------------------------------

/// LDSSecurityObject (the eContent payload), SHA-256 variant.
///
/// Extracts `HashDg1`. The DG1 DataGroupHash is parsed explicitly;
/// any additional DG hashes (DG2, DG14, etc.) are consumed as the
/// tail of the `dataGroupHashValues` SEQUENCE.
fn lds_security_object_spec() -> Asn1Spec<&'static str> {
    let dg1_hash = Asn1Spec::new().read_sequence(
        Asn1Spec::new()
            .read_integer_const(1)
            .read_octet_string(Asn1Spec::new().read_bytes(32).mark_last("hashDg1")),
    );

    Asn1Spec::new().read_sequence(
        Asn1Spec::new()
            .read_integer_const(0)
            .read_algid_null(OID_SHA256)
            .read_sequence(dg1_hash.read_trail()),
    )
}

/// X.509 certificate spec (RSA-2048). Extracts `TbsCertificate`,
/// `DsPublicKey`, and `CscaSignature`.
fn x509_certificate_spec() -> Asn1Spec<&'static str> {
    Asn1Spec::new().read_sequence(
        Asn1Spec::new()
            .read_sequence(tbs_certificate_spec())
            .mark_last("tbsCertificate")
            .read_algid_null(OID_SHA256_RSA) // signatureAlgorithm (fixed)
            .read_bit_string(
                // signatureValue (fixed 257 bytes)
                Asn1Spec::new()
                    .read_bytes(RSA2048_SIG_BIT_STRING_LEN)
                    .mark_last("cscaSignature"),
            ),
    )
}

/// tbsCertificate inner structure (RSA-2048). Extracts `DsPublicKey`.
///
/// **Limitation:** optional fields after `subjectPublicKeyInfo`
/// (extensions, etc.) are not described. The defensive check in
/// the parser will panic if extensions are present.
fn tbs_certificate_spec() -> Asn1Spec<&'static str> {
    let spki = Asn1Spec::new().read_sequence(
        Asn1Spec::new()
            .read_algid_null(OID_RSA) // algorithm (fixed)
            .read_bit_string(
                // publicKey (fixed 269 bytes)
                Asn1Spec::new().read_bytes(RSA2048_BIT_STRING_LEN).mark_last("dsPublicKey"),
            ),
    );

    Asn1Spec::new()
        .read_ctx(0, Asn1Spec::new().read_integer_const(2)) // version v3 (fixed)
        .read_integer(Asn1Spec::new().read_trail()) // serialNumber
        .read_algid_null(OID_SHA256_RSA) // signature (fixed)
        .read_sequence(Asn1Spec::new().read_trail()) // issuer
        .read_sequence(Asn1Spec::new().read_trail()) // validity
        .read_sequence(Asn1Spec::new().read_trail()) // subject
        .then(spki)
        .read_trail() // optional extensions ([3] EXPLICIT)
}

/// SignerInfo spec (SHA-256 + RSA-2048). Extracts `SignedAttrs`,
/// `MessageDigest`, and `DsSignature`.
fn signer_info_spec() -> Asn1Spec<&'static str> {
    Asn1Spec::new().read_sequence(
        Asn1Spec::new()
            .read_integer_const(1) // version
            .read_sequence(Asn1Spec::new().read_trail()) // issuerAndSerialNumber
            .read_algid_null(OID_SHA256) // digestAlgorithm (fixed)
            .read_ctx(0, signed_attrs_spec().mark_full("signedAttrs"))
            .read_algid_null(OID_SHA256_RSA) // signatureAlgorithm (fixed)
            .read_octet_string(
                // signature (fixed 256 bytes)
                Asn1Spec::new()
                    .read_bytes(RSA2048_SIG_OCTET_STRING_LEN)
                    .mark_last("dsSignature"),
            ),
    )
}

/// Signed attributes inner structure. Extracts `MessageDigest`.
fn signed_attrs_spec() -> Asn1Spec<&'static str> {
    let content_type_attr = Asn1Spec::new().read_sequence(
        Asn1Spec::new()
            .read_oid(OID_CONTENT_TYPE)
            .read_set(Asn1Spec::new().read_oid(OID_LDS_SECURITY_OBJECT)),
    );

    let message_digest_attr = Asn1Spec::new().read_sequence(
        Asn1Spec::new().read_oid(OID_MESSAGE_DIGEST).read_set(
            Asn1Spec::new()
                .read_octet_string(Asn1Spec::new().read_bytes(32).mark_last("messageDigest")),
        ),
    );

    content_type_attr.then(message_digest_attr)
}
