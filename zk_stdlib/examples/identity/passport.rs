//! ASN.1 spec definitions for ICAO 9303 biometric passport structures.
//!
//! The main structures are:
//! - **DG1**: The Machine Readable Zone (MRZ), wrapped in a simple TLV.
//! - **SOD**: The Security Object Document (CMS SignedData), containing the
//!   signed hashes of data groups and the DS certificate chain.
//!
//! These specs are designed to be used with [`ScannerChip::parse_asn1`].

use std::{fmt::Debug, hash::Hash};

use super::{
    der_encoding::{self, encode_length, encode_tag, tag, CONSTRUCTED},
    Asn1RawData, Asn1Spec, Asn1Value,
};

// -----------------------------------------------------------------------
// Well-known OIDs (DER-encoded content, without the 0x06 tag + length)
// -----------------------------------------------------------------------

/// OID 1.2.840.113549.1.7.2 — CMS signedData.
const OID_SIGNED_DATA: &[u32] = &[1, 2, 840, 113549, 1, 7, 2];

/// OID 2.16.840.1.101.3.4.2.1 — SHA-256.
const OID_SHA256: &[u32] = &[2, 16, 840, 1, 101, 3, 4, 2, 1];

/// OID 2.23.136.1.1.1 — LDSSecurityObject (ICAO).
const OID_LDS_SECURITY_OBJECT: &[u32] = &[2, 23, 136, 1, 1, 1];

/// OID 1.2.840.113549.1.9.3 — contentType (CMS attribute).
const _OID_CONTENT_TYPE: &[u32] = &[1, 2, 840, 113549, 1, 9, 3];

/// OID 1.2.840.113549.1.9.4 — messageDigest (CMS attribute).
const _OID_MESSAGE_DIGEST: &[u32] = &[1, 2, 840, 113549, 1, 9, 4];

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

/// Builds a fixed tag as `Asn1RawData::fixed`.
fn fixed_tag<Index: Eq + Hash + Debug>(byte: u8) -> Asn1RawData<Index> {
    Asn1RawData::fixed(&[byte])
}

/// Builds a variable-length length field.
fn varlen_length<Index: Eq + Hash + Debug>() -> Asn1RawData<Index> {
    Asn1RawData::any(None)
}

/// Builds a fixed length field from a known value.
fn fixed_length<Index: Eq + Hash + Debug>(len: usize) -> Asn1RawData<Index> {
    Asn1RawData::fixed(&encode_length(len))
}

/// Builds a TLV with a known single-byte tag and variable-length content.
fn tlv_varlen<Index: Eq + Hash + Debug>(
    tag_byte: u8,
    val: impl Into<Asn1Value<Index>>,
) -> Asn1Spec<Index> {
    Asn1Spec::init().read_tlv(fixed_tag(tag_byte), varlen_length(), val)
}

/// Builds a TLV wrapping an OID with known value.
fn tlv_oid<Index: Eq + Hash + Debug>(components: &[u32]) -> Asn1Spec<Index> {
    let encoded = der_encoding::oid(components);
    Asn1Spec::init().read_static(&encoded)
}

/// Builds an AlgorithmIdentifier SEQUENCE with the given OID and NULL params.
fn algorithm_identifier<Index: Eq + Hash + Debug>(oid: &[u32]) -> Asn1Spec<Index> {
    let inner = der_encoding::sequence(&[der_encoding::oid(oid), der_encoding::null()]);
    Asn1Spec::init().read_static(&inner)
}

// -----------------------------------------------------------------------
// Index types
// -----------------------------------------------------------------------

/// Indexes for extracted regions of a DG1 structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dg1Field {
    /// The 88-byte MRZ payload.
    Mrz,
}

/// Indexes for extracted regions of a SOD structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SodField {
    /// The digest algorithm OID from `digestAlgorithms`.
    DigestAlgorithmOid,
    /// The full `eContent` (LDSSecurityObject bytes).
    EContent,
    /// The hash of DG1 inside the LDSSecurityObject.
    HashDg1,
    /// The `signedAttrs` bytes (to be hashed for signature verification).
    SignedAttrs,
    /// The `messageDigest` value from signedAttrs.
    MessageDigest,
    /// The signature algorithm OID from `SignerInfo`.
    SignatureAlgorithmOid,
    /// The DS signature over the signed attributes.
    DsSignature,
    /// The full `tbsCertificate` bytes (to be hashed).
    TbsCertificate,
    /// The DS public key from the X.509 certificate.
    DsPublicKey,
    /// The CSCA signature over the tbsCertificate.
    CscaSignature,
}

// -----------------------------------------------------------------------
// DG1 spec
// -----------------------------------------------------------------------

/// DG1 structure for TD3 passports (93 bytes total):
///
/// ```text
/// 61 5B                     -- Application 1, constructed, length 91
///   5F1F 58                 -- Context 31, primitive, length 88
///     <88 bytes MRZ>
/// ```
pub fn dg1_td3_spec() -> Asn1Spec<Dg1Field> {
    // Inner TLV: tag 5F1F (long-form), length 0x58 (88), value = MRZ
    let mrz_tag_bytes = encode_tag(&der_encoding::Tag {
        class: der_encoding::class::APPLICATION,
        constructed: false,
        number: 31,
    });
    let mrz = Asn1Spec::init().read_tlv(
        Asn1RawData::fixed(&mrz_tag_bytes),
        fixed_length(88),
        Asn1Value::any(Some(88)).mark(Dg1Field::Mrz),
    );

    // Outer TLV: application tag 1 (0x61), wrapping the inner TLV
    let outer_tag_bytes = encode_tag(&der_encoding::Tag {
        class: der_encoding::class::APPLICATION,
        constructed: true,
        number: 1,
    });
    Asn1Spec::init().read_tlv(Asn1RawData::fixed(&outer_tag_bytes), fixed_length(91), mrz)
}

// -----------------------------------------------------------------------
// SOD spec (SHA-256 + ECDSA, PoC version)
// -----------------------------------------------------------------------

/// Builds the SOD spec for a SHA-256 based passport.
///
/// This is a PoC spec: the digest algorithm is fixed to SHA-256, and
/// certain structural assumptions are made (e.g., single DigestAlgorithm
/// in the SET, single SignerInfo, single certificate). Variable-length
/// fields are used where the size depends on key/signature sizes.
///
/// The SOD is a CMS ContentInfo wrapping a SignedData:
///
/// ```text
/// SEQUENCE (ContentInfo)
///   OID signedData
///   [0] CONSTRUCTED (content)
///     SEQUENCE (SignedData)
///       INTEGER 3 (version)
///       SET (digestAlgorithms)
///         SEQUENCE (AlgorithmIdentifier)
///           OID sha256
///           NULL
///       SEQUENCE (encapContentInfo)
///         OID ldsSecurityObject
///         [0] CONSTRUCTED
///           OCTET STRING (eContent = LDSSecurityObject)
///       [0] IMPLICIT (certificates)
///         SEQUENCE (X.509 Certificate)
///           SEQUENCE (tbsCertificate)  -- EXTRACT
///             ...
///             SEQUENCE (subjectPublicKeyInfo)  -- EXTRACT: DS public key
///           SEQUENCE (signatureAlgorithm)
///           BIT STRING (signatureValue)  -- EXTRACT: CSCA signature
///       SET (signerInfos)
///         SEQUENCE (SignerInfo)
///           INTEGER 1 (version)
///           SEQUENCE (issuerAndSerialNumber) -- variable
///           SEQUENCE (digestAlgorithm)
///           [0] IMPLICIT (signedAttrs)  -- EXTRACT
///           SEQUENCE (signatureAlgorithm)  -- EXTRACT OID
///           OCTET STRING (signature)  -- EXTRACT: DS signature
/// ```
pub fn sod_sha256_spec() -> Asn1Spec<SodField> {
    // --- encapContentInfo ---
    // eContent is the DER-encoded LDSSecurityObject inside an OCTET STRING
    // inside a context [0] wrapper.
    let lds_security_object = lds_security_object_sha256_spec();
    let econtent_octet_string = tlv_varlen(tag::OCTET_STRING, lds_security_object);
    let econtent_wrapper = Asn1Spec::init().read_tlv(
        // [0] CONSTRUCTED = 0xA0
        fixed_tag(der_encoding::class::CONTEXT_SPECIFIC | CONSTRUCTED),
        varlen_length(),
        econtent_octet_string,
    );
    let encap_content_info = Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        Asn1Spec::init().then(tlv_oid(OID_LDS_SECURITY_OBJECT)).then(econtent_wrapper),
    );

    // --- certificates [0] IMPLICIT ---
    // Contains a single X.509 certificate.
    let certificate = x509_certificate_spec();
    let certificates = Asn1Spec::init().read_tlv(
        // [0] IMPLICIT CONSTRUCTED = 0xA0
        fixed_tag(der_encoding::class::CONTEXT_SPECIFIC | CONSTRUCTED),
        varlen_length(),
        certificate,
    );

    // --- signerInfos ---
    let signer_info = signer_info_sha256_spec();
    let signer_infos = Asn1Spec::init().read_tlv(fixed_tag(tag::SET), varlen_length(), signer_info);

    // --- digestAlgorithms SET ---
    let digest_algorithms: Asn1Spec<SodField> = Asn1Spec::init().read_tlv(
        fixed_tag(tag::SET),
        varlen_length(),
        algorithm_identifier(OID_SHA256),
    );

    // --- SignedData ---
    let version = Asn1Spec::init().read_static(&der_encoding::integer(3));
    let signed_data_inner = Asn1Spec::cat(vec![
        version,
        digest_algorithms,
        encap_content_info,
        certificates,
        signer_infos,
    ]);
    let signed_data = tlv_varlen(tag::SEQUENCE, signed_data_inner);

    // --- ContentInfo wrapper ---
    let content_wrapper = Asn1Spec::init().read_tlv(
        // [0] CONSTRUCTED = 0xA0
        fixed_tag(der_encoding::class::CONTEXT_SPECIFIC | CONSTRUCTED),
        varlen_length(),
        signed_data,
    );
    Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        Asn1Spec::init().then(tlv_oid(OID_SIGNED_DATA)).then(content_wrapper),
    )
}

// -----------------------------------------------------------------------
// Sub-specs
// -----------------------------------------------------------------------

/// LDSSecurityObject (the eContent payload), SHA-256 variant.
///
/// Extracts the DG1 hash. Assumes a single DataGroupHash for DG1 is
/// present (PoC simplification — production would iterate over all DGs).
fn lds_security_object_sha256_spec() -> Asn1Spec<SodField> {
    let version = Asn1Spec::init().read_static(&der_encoding::integer(0));
    let hash_algorithm: Asn1Spec<SodField> = algorithm_identifier(OID_SHA256);

    // DataGroupHash for DG1:
    //   SEQUENCE { INTEGER 1, OCTET STRING <32 bytes> }
    let dg1_hash = Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        Asn1Spec::init()
            .then(Asn1Spec::init().read_static(&der_encoding::integer(1)))
            .then(Asn1Spec::init().read_tlv(
                fixed_tag(tag::OCTET_STRING),
                fixed_length(32),
                Asn1Value::any(Some(32)).mark(SodField::HashDg1),
            )),
    );

    // dataGroupHashValues: SET OF DataGroupHash
    // We only extract DG1; remaining DGs are consumed as variable-length.
    let data_group_hashes = Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        dg1_hash,
        // TODO: handle additional DG hashes (DG2, DG14, etc.)
    );

    Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        Asn1Spec::cat(vec![version, hash_algorithm, data_group_hashes]),
    )
}

/// Simplified X.509 certificate spec. Extracts tbsCertificate, DS public
/// key, and CSCA signature.
fn x509_certificate_spec() -> Asn1Spec<SodField> {
    // tbsCertificate: variable-length SEQUENCE, extract the whole thing
    let tbs_certificate = Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        // The inner structure is complex (version, serialNumber, issuer, ...,
        // subjectPublicKeyInfo). For PoC, extract the whole tbsCertificate
        // as a blob. The DS public key extraction would require deeper
        // parsing of subjectPublicKeyInfo.
        Asn1Value::any(None).mark(SodField::TbsCertificate),
    );

    // signatureAlgorithm: SEQUENCE (AlgorithmIdentifier)
    let sig_algorithm: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));

    // signatureValue: BIT STRING
    let sig_value = Asn1Spec::init().read_tlv(
        fixed_tag(tag::BIT_STRING),
        varlen_length(),
        Asn1Value::any(None).mark(SodField::CscaSignature),
    );

    Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        Asn1Spec::cat(vec![tbs_certificate, sig_algorithm, sig_value]),
    )
}

/// SignerInfo spec (SHA-256 variant). Extracts signedAttrs, signature
/// algorithm OID, and DS signature.
fn signer_info_sha256_spec() -> Asn1Spec<SodField> {
    // version: INTEGER 1
    let version = Asn1Spec::init().read_static(&der_encoding::integer(1));

    // issuerAndSerialNumber: SEQUENCE (variable, not extracted)
    let issuer_serial: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));

    // digestAlgorithm: AlgorithmIdentifier (SHA-256)
    let digest_alg: Asn1Spec<SodField> = algorithm_identifier(OID_SHA256);

    // signedAttrs: [0] IMPLICIT SET (extract the whole thing)
    let signed_attrs = Asn1Spec::init().read_tlv(
        // [0] IMPLICIT CONSTRUCTED = 0xA0
        fixed_tag(der_encoding::class::CONTEXT_SPECIFIC | CONSTRUCTED),
        varlen_length(),
        Asn1Value::any(None).mark(SodField::SignedAttrs),
    );

    // signatureAlgorithm: SEQUENCE (extract as blob for now)
    let sig_algorithm: Asn1Spec<SodField> = Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        Asn1Value::any(None).mark(SodField::SignatureAlgorithmOid),
    );

    // signature: OCTET STRING
    let signature = Asn1Spec::init().read_tlv(
        fixed_tag(tag::OCTET_STRING),
        varlen_length(),
        Asn1Value::any(None).mark(SodField::DsSignature),
    );

    Asn1Spec::init().read_tlv(
        fixed_tag(tag::SEQUENCE),
        varlen_length(),
        Asn1Spec::cat(vec![
            version,
            issuer_serial,
            digest_alg,
            signed_attrs,
            sig_algorithm,
            signature,
        ]),
    )
}
