//! ICAO 9303 biometric passport structures for zero-knowledge proofs.
//!
//! - **DG1**: Fixed-layout Machine Readable Zone (MRZ). Not parsed via
//!   `Asn1Spec`:field offsets are given as constants.
//! - **SOD**: Security Object Document (CMS SignedData), parsed via `Asn1Spec`
//!   to extract the fields needed for the verification chain.
//!
//! This module targets the **SHA-256 + RSA-2048** algorithm pair.

use std::ops::Range;

use midnight_circuits::parsing::scanner::asn1::Asn1Spec;

// -----------------------------------------------------------------------
// Well-known OIDs
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

/// BIT STRING content size for an RSA-2048 public key:
/// 1 byte (unused bits = 0x00) + DER(SEQUENCE { INTEGER(256+overhead),
/// INTEGER(3+overhead) }). The SEQUENCE is: 30 82 01 0A  02 82 01 01 00 <256
/// bytes modulus> 02 03 01 00 01 = 4 + 259 + 5 = 268 content bytes. BIT STRING
/// content = 1 + 268 = 269 bytes.
pub const RSA2048_BIT_STRING_LEN: usize = 269;

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

/// Document type (e.g., "P<"). 2 bytes.
pub const DG1_DOC_TYPE: Range<usize> = 5..7;

/// Issuing state or organization (ISO 3166-1 alpha-3). 3 bytes.
pub const DG1_ISSUING_COUNTRY: Range<usize> = 7..10;

/// Surname and given names (separated by `<<`, padded with `<`). 39 bytes.
pub const DG1_NAME: Range<usize> = 10..49;

/// Passport number. 9 bytes.
pub const DG1_PASSPORT_NUMBER: Range<usize> = 49..58;

/// Nationality (ISO 3166-1 alpha-3). 3 bytes.
pub const DG1_NATIONALITY: Range<usize> = 59..62;

/// Date of birth (YYMMDD). 6 bytes.
pub const DG1_DOB: Range<usize> = 62..68;

/// Sex (M, F, or <). 1 byte.
pub const DG1_SEX: Range<usize> = 69..70;

/// Date of expiry (YYMMDD). 6 bytes.
pub const DG1_EXPIRY: Range<usize> = 70..76;

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
pub fn sod_sha256_rsa2048_spec() -> Asn1Spec<&'static str> {
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
