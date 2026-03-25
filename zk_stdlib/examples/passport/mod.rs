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
//! 1. **Parse the SOD** ([`spec::sod_sha256_rsa2048_spec`]) to extract:
//!    eContent, signedAttrs, messageDigest, tbsCertificate, dsPublicKey,
//!    dsSignature, cscaSignature, and hashDg1.
//!
//! 2. **Verify the CSCA signature** on the DS certificate:
//!    `SHA-256(tbsCertificate)` + PKCS#1 v1.5 + RSA-2048.
//!
//! 3. **Prove CSCA key membership**: the CSCA key used in step 2 belongs to the
//!    trusted set (a Poseidon Merkle tree whose root is the public input).
//!
//! 4. **Verify the DS signature** on the signed attributes:
//!    `SHA-256(signedAttrs)` + PKCS#1 v1.5 + RSA-2048.
//!
//! 5. **Verify eContent integrity**: `SHA-256(eContent) == messageDigest`.
//!
//! 6. **Verify DG1 integrity**: `SHA-256(DG1) == hashDg1`.
//!
//! After step 6, the DG1 bytes are authenticated. MRZ fields can be
//! extracted using the byte-range constants in [`spec`] (e.g.,
//! [`spec::DG1_DOB`], [`spec::DG1_NAME`]).
//!
//! # Inputs
//!
//! **Public input (instance):**
//! - The Poseidon Merkle root of the trusted CSCA key set.
//!
//! The verifier builds this root off-circuit from the ICAO PKD master
//! list using [`verification::build_csca_map`]. The root commits to
//! all ~300-400 currently valid CSCA keys worldwide.
//!
//! **Private input (witness):**
//! - The full SOD bytes (DER-encoded CMS ContentInfo, typically ~1700 bytes).
//! - The full DG1 bytes (93 bytes for TD3: TLV header + 88-byte MRZ).
//! - The CSCA public key (RSA-2048 modulus, 256 bytes big-endian).
//! - The Poseidon Merkle tree of trusted CSCA keys (for the membership proof
//!   path).
//!
//! # How to obtain the witness in practice
//!
//! 1. **Read the passport via NFC**: use Basic Access Control (BAC) or Password
//!    Authenticated Connection Establishment (PACE) to establish a secure
//!    channel, then read DG1 and the SOD from the chip.
//!
//! 2. **Extract the CSCA key**: the DS certificate inside the SOD identifies
//!    the issuer. Look up the corresponding CSCA certificate from the ICAO PKD
//!    master list and extract its RSA-2048 modulus.
//!
//! 3. **Build the CSCA map**: call [`verification::build_csca_map`] with all
//!    trusted CSCA moduli from the PKD to obtain the Merkle tree (witness) and
//!    its root (public input).

pub mod circuit;
pub mod spec;
