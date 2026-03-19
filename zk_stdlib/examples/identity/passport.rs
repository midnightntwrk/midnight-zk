//! ASN.1 spec definitions for ICAO 9303 biometric passport structures.
//!
//! The main structures are:
//! - **DG1**: The Machine Readable Zone (MRZ), wrapped in a simple TLV.
//! - **SOD**: The Security Object Document (CMS SignedData), containing the
//!   signed hashes of data groups and the DS certificate chain.
//!
//! These specs are designed to be used with [`ScannerChip::parse_asn1`].

use std::{fmt::Debug, hash::Hash};

use midnight_circuits::parsing::scanner::asn1::{
    der_encoding::{self, encode_length, encode_tag, tag, CONSTRUCTED},
    Asn1RawData, Asn1Spec, Asn1Value,
};

// -----------------------------------------------------------------------
// Well-known OIDs
// -----------------------------------------------------------------------

/// OID 1.2.840.113549.1.7.2 — CMS signedData.
const OID_SIGNED_DATA: &[u32] = &[1, 2, 840, 113549, 1, 7, 2];

/// OID 2.16.840.1.101.3.4.2.1 — SHA-256.
const OID_SHA256: &[u32] = &[2, 16, 840, 1, 101, 3, 4, 2, 1];

/// OID 2.23.136.1.1.1 — LDSSecurityObject (ICAO).
const OID_LDS_SECURITY_OBJECT: &[u32] = &[2, 23, 136, 1, 1, 1];

/// OID 1.2.840.113549.1.9.3 — contentType (CMS attribute).
const OID_CONTENT_TYPE: &[u32] = &[1, 2, 840, 113549, 1, 9, 3];

/// OID 1.2.840.113549.1.9.4 — messageDigest (CMS attribute).
const OID_MESSAGE_DIGEST: &[u32] = &[1, 2, 840, 113549, 1, 9, 4];

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

/// Builds a complete DER-encoded OID TLV as a static block.
fn tlv_oid<Index: Eq + Hash + Debug>(components: &[u32]) -> Asn1Spec<Index> {
    Asn1Spec::init().read_static(&der_encoding::oid(components))
}

/// Builds an AlgorithmIdentifier SEQUENCE with the given OID and NULL params.
fn algorithm_identifier<Index: Eq + Hash + Debug>(oid: &[u32]) -> Asn1Spec<Index> {
    Asn1Spec::init().read_static(&der_encoding::sequence(&[
        der_encoding::oid(oid),
        der_encoding::null(),
    ]))
}

/// Context-specific constructed tag (0xA0 | number).
fn context_tag<Index: Eq + Hash + Debug>(number: u8) -> Asn1RawData<Index> {
    fixed_tag(der_encoding::class::CONTEXT_SPECIFIC | CONSTRUCTED | number)
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
    /// The full `eContent` bytes (LDSSecurityObject, to be hashed for
    /// step 2 of verification).
    EContent,
    /// The hash of DG1 inside the LDSSecurityObject.
    HashDg1,
    /// The `signedAttrs` bytes (to be hashed for DS signature verification).
    SignedAttrs,
    /// The `messageDigest` value from signedAttrs (hash of eContent).
    MessageDigest,
    /// The DS signature over the signed attributes.
    DsSignature,
    /// The full `tbsCertificate` bytes (to be hashed for CSCA signature
    /// verification).
    TbsCertificate,
    /// The DS public key (BIT STRING content from subjectPublicKeyInfo).
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
///   5F1F 58                 -- Application 31, primitive, length 88
///     <88 bytes MRZ>
/// ```
pub fn dg1_td3_spec() -> Asn1Spec<Dg1Field> {
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
/// PoC assumptions: single DigestAlgorithm (SHA-256), single SignerInfo,
/// single certificate, DG1 is the first DataGroupHash entry.
///
/// ```text
/// SEQUENCE (ContentInfo)
///   OID signedData
///   [0] CONSTRUCTED
///     SEQUENCE (SignedData)
///       INTEGER 3
///       SET { AlgorithmIdentifier(SHA-256) }
///       SEQUENCE (encapContentInfo)
///         OID ldsSecurityObject
///         [0] CONSTRUCTED
///           OCTET STRING (eContent)         -- EXTRACT
///       [0] IMPLICIT (certificates)
///         SEQUENCE (Certificate)
///           SEQUENCE (tbsCertificate)       -- EXTRACT
///             ...
///             SEQUENCE (subjectPublicKeyInfo)
///               AlgorithmIdentifier
///               BIT STRING (publicKey)      -- EXTRACT
///             ...
///           SEQUENCE (signatureAlgorithm)
///           BIT STRING (signatureValue)     -- EXTRACT
///       SET (signerInfos)
///         SEQUENCE (SignerInfo)
///           INTEGER 1
///           SEQUENCE (issuerAndSerialNumber)
///           AlgorithmIdentifier(SHA-256)
///           [0] (signedAttrs)               -- EXTRACT
///             SEQUENCE { OID contentType, SET { OID } }
///             SEQUENCE { OID messageDigest, SET { OCTET STRING } }  -- EXTRACT
///           SEQUENCE (signatureAlgorithm)
///           OCTET STRING (signature)        -- EXTRACT
/// ```
pub fn sod_sha256_spec() -> Asn1Spec<SodField> {
    // --- encapContentInfo ---
    let lds_security_object = lds_security_object_sha256_spec();
    let econtent_octet_string = Asn1Spec::init().read_tlv(
        fixed_tag(tag::OCTET_STRING),
        varlen_length(),
        Asn1Value::from(lds_security_object).mark(SodField::EContent),
    );
    let econtent_wrapper = Asn1Spec::init().read_tlv(
        context_tag(0),
        varlen_length(),
        econtent_octet_string,
    );
    let encap_content_info = tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::init()
            .then(tlv_oid(OID_LDS_SECURITY_OBJECT))
            .then(econtent_wrapper),
    );

    // --- certificates [0] IMPLICIT ---
    let certificates = Asn1Spec::init().read_tlv(
        context_tag(0),
        varlen_length(),
        x509_certificate_spec(),
    );

    // --- signerInfos ---
    let signer_infos = tlv_varlen(tag::SET, signer_info_sha256_spec());

    // --- digestAlgorithms ---
    let digest_algorithms: Asn1Spec<SodField> =
        tlv_varlen(tag::SET, algorithm_identifier(OID_SHA256));

    // --- SignedData ---
    let version = Asn1Spec::init().read_static(&der_encoding::integer(3));
    let signed_data = tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::cat(vec![
            version,
            digest_algorithms,
            encap_content_info,
            certificates,
            signer_infos,
        ]),
    );

    // --- ContentInfo ---
    tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::init()
            .then(tlv_oid(OID_SIGNED_DATA))
            .then(Asn1Spec::init().read_tlv(
                context_tag(0),
                varlen_length(),
                signed_data,
            )),
    )
}

// -----------------------------------------------------------------------
// Sub-specs
// -----------------------------------------------------------------------

/// LDSSecurityObject (the eContent payload), SHA-256 variant.
/// Extracts `HashDg1`. Additional DG hashes after DG1 are consumed as
/// an opaque variable-length blob.
fn lds_security_object_sha256_spec() -> Asn1Spec<SodField> {
    let version = Asn1Spec::init().read_static(&der_encoding::integer(0));
    let hash_algorithm: Asn1Spec<SodField> = algorithm_identifier(OID_SHA256);

    // DataGroupHash for DG1:
    //   SEQUENCE { INTEGER 1, OCTET STRING(32) }
    let dg1_hash = tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::init()
            .then(Asn1Spec::init().read_static(&der_encoding::integer(1)))
            .then(Asn1Spec::init().read_tlv(
                fixed_tag(tag::OCTET_STRING),
                fixed_length(32),
                Asn1Value::any(Some(32)).mark(SodField::HashDg1),
            )),
    );

    // dataGroupHashValues: SEQUENCE OF DataGroupHash.
    // DG1 is first; any remaining DGs are consumed as opaque data.
    let data_group_hashes = tlv_varlen(tag::SEQUENCE, dg1_hash);

    tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::cat(vec![version, hash_algorithm, data_group_hashes]),
    )
}

/// X.509 certificate spec. Extracts `TbsCertificate`, `DsPublicKey`,
/// and `CscaSignature`.
fn x509_certificate_spec() -> Asn1Spec<SodField> {
    let tbs_certificate = tlv_varlen(
        tag::SEQUENCE,
        Asn1Value::from(tbs_certificate_spec()).mark(SodField::TbsCertificate),
    );

    // signatureAlgorithm: AlgorithmIdentifier (not extracted)
    let sig_algorithm: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));

    // signatureValue: BIT STRING
    let sig_value = Asn1Spec::init().read_tlv(
        fixed_tag(tag::BIT_STRING),
        varlen_length(),
        Asn1Value::any(None).mark(SodField::CscaSignature),
    );

    tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::cat(vec![tbs_certificate, sig_algorithm, sig_value]),
    )
}

/// tbsCertificate inner structure. Extracts `DsPublicKey`.
/// Fields before subjectPublicKeyInfo are consumed as opaque blobs.
///
/// ```text
/// SEQUENCE {
///   [0] EXPLICIT { INTEGER version }
///   INTEGER serialNumber
///   AlgorithmIdentifier signature
///   Name issuer
///   SEQUENCE { Time notBefore, Time notAfter } validity
///   Name subject
///   SEQUENCE (subjectPublicKeyInfo)
///     AlgorithmIdentifier algorithm
///     BIT STRING publicKey                    -- EXTRACT
///   ... (optional extensions, ignored)
/// }
/// ```
fn tbs_certificate_spec() -> Asn1Spec<SodField> {
    // version: [0] EXPLICIT { INTEGER }
    let version: Asn1Spec<SodField> =
        Asn1Spec::init().read_tlv(context_tag(0), varlen_length(), Asn1Value::any(None));
    // serialNumber: INTEGER
    let serial: Asn1Spec<SodField> = tlv_varlen(tag::INTEGER, Asn1Value::any(None));
    // signature: AlgorithmIdentifier
    let signature: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));
    // issuer: Name (SEQUENCE)
    let issuer: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));
    // validity: SEQUENCE { Time, Time }
    let validity: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));
    // subject: Name (SEQUENCE)
    let subject: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));

    // subjectPublicKeyInfo: SEQUENCE { AlgorithmIdentifier, BIT STRING }
    let spki_algorithm: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));
    let spki_public_key = Asn1Spec::init().read_tlv(
        fixed_tag(tag::BIT_STRING),
        varlen_length(),
        Asn1Value::any(None).mark(SodField::DsPublicKey),
    );
    let spki = tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::cat(vec![spki_algorithm, spki_public_key]),
    );

    // Remaining fields (issuerUniqueID, subjectUniqueID, extensions) are
    // optional. They will be consumed by the TLV length assertion in
    // process_tlv — process_value's defensive check ensures the inner
    // spec matches the actual byte count. For now, we don't parse them
    // and rely on the enclosing TLV length to delimit.
    Asn1Spec::cat(vec![
        version, serial, signature, issuer, validity, subject, spki,
    ])
}

/// SignerInfo spec (SHA-256 variant). Extracts `SignedAttrs`,
/// `MessageDigest`, and `DsSignature`.
fn signer_info_sha256_spec() -> Asn1Spec<SodField> {
    let version = Asn1Spec::init().read_static(&der_encoding::integer(1));

    // issuerAndSerialNumber: SEQUENCE (not extracted)
    let issuer_serial: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));

    // digestAlgorithm: AlgorithmIdentifier (SHA-256)
    let digest_alg: Asn1Spec<SodField> = algorithm_identifier(OID_SHA256);

    // signedAttrs: [0] IMPLICIT SET — extract the whole blob, and also
    // parse inside to extract the messageDigest value.
    let signed_attrs = Asn1Spec::init().read_tlv(
        context_tag(0),
        varlen_length(),
        Asn1Value::from(signed_attrs_spec()).mark(SodField::SignedAttrs),
    );

    // signatureAlgorithm: AlgorithmIdentifier (not extracted)
    let sig_algorithm: Asn1Spec<SodField> = tlv_varlen(tag::SEQUENCE, Asn1Value::any(None));

    // signature: OCTET STRING
    let signature = Asn1Spec::init().read_tlv(
        fixed_tag(tag::OCTET_STRING),
        varlen_length(),
        Asn1Value::any(None).mark(SodField::DsSignature),
    );

    tlv_varlen(
        tag::SEQUENCE,
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

/// Signed attributes inner structure. Extracts `MessageDigest`.
///
/// ```text
/// SET {
///   SEQUENCE { OID contentType, SET { OID ldsSecurityObject } }
///   SEQUENCE { OID messageDigest, SET { OCTET STRING(32) } }  -- EXTRACT
/// }
/// ```
fn signed_attrs_spec() -> Asn1Spec<SodField> {
    // contentType attribute: SEQUENCE { OID, SET { OID } }
    let content_type_attr: Asn1Spec<SodField> = tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::init()
            .then(tlv_oid(OID_CONTENT_TYPE))
            .then(tlv_varlen(
                tag::SET,
                tlv_oid::<SodField>(OID_LDS_SECURITY_OBJECT),
            )),
    );

    // messageDigest attribute: SEQUENCE { OID, SET { OCTET STRING(32) } }
    let message_digest_attr = tlv_varlen(
        tag::SEQUENCE,
        Asn1Spec::init()
            .then(tlv_oid(OID_MESSAGE_DIGEST))
            .then(Asn1Spec::init().read_tlv(
                fixed_tag(tag::SET),
                varlen_length(),
                Asn1Spec::init().read_tlv(
                    fixed_tag(tag::OCTET_STRING),
                    fixed_length(32),
                    Asn1Value::any(Some(32)).mark(SodField::MessageDigest),
                ),
            )),
    );

    Asn1Spec::cat(vec![content_type_attr, message_digest_attr])
}
