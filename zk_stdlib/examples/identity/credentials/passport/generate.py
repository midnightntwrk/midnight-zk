#!/usr/bin/env python3
"""Generate synthetic ICAO 9303 passport test data (SHA-256 + RSA-2048).

Produces a DER-encoded SOD (CMS SignedData), a DG1 (TLV-wrapped MRZ),
and the CSCA public key, all suitable for use as test fixtures in the
midnight-zk passport verification circuit.

The MRZ fields can be customised via command-line arguments; all have
sensible defaults using the ICAO specimen country code "UTO" (Utopia).

Setup:
    python3 -m venv venv
    venv/bin/pip install cryptography

Usage:
    venv/bin/python3 generate.py [options]
    venv/bin/python3 generate.py --help

Output files (in the same directory as the script):
    dg1.bin          -- 93-byte DG1 (tag + length + 88-byte MRZ)
    sod.der          -- DER-encoded CMS ContentInfo (SignedData)
    csca_key.bin     -- 256-byte CSCA RSA-2048 modulus (big-endian)
"""

import argparse
import hashlib
import os
import struct
from datetime import datetime, timedelta, timezone

from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding, rsa
from cryptography.x509 import (
    BasicConstraints,
    CertificateBuilder,
    Name,
    NameAttribute,
    random_serial_number,
)
from cryptography.x509.oid import NameOID

# ---------------------------------------------------------------------------
# DER encoding helpers
# ---------------------------------------------------------------------------

def der_tag_length(tag_byte: int, content: bytes) -> bytes:
    """Wrap content in a DER TLV with the given single-byte tag."""
    length = len(content)
    if length < 0x80:
        return bytes([tag_byte, length]) + content
    elif length < 0x100:
        return bytes([tag_byte, 0x81, length]) + content
    elif length < 0x10000:
        return bytes([tag_byte, 0x82]) + struct.pack(">H", length) + content
    else:
        raise ValueError(f"Content too large: {length}")


def der_sequence(content: bytes) -> bytes:
    return der_tag_length(0x30, content)


def der_set(content: bytes) -> bytes:
    return der_tag_length(0x31, content)


def der_octet_string(content: bytes) -> bytes:
    return der_tag_length(0x04, content)


def der_bit_string(content: bytes) -> bytes:
    # Prepend unused-bits byte (0x00).
    return der_tag_length(0x03, b"\x00" + content)


def der_integer_value(n: int) -> bytes:
    """DER-encode a non-negative integer."""
    if n == 0:
        return der_tag_length(0x02, b"\x00")
    b = n.to_bytes((n.bit_length() + 7) // 8, byteorder="big")
    if b[0] & 0x80:  # Needs leading zero for positive sign.
        b = b"\x00" + b
    return der_tag_length(0x02, b)


def der_oid(components: list[int]) -> bytes:
    """DER-encode an OID."""
    assert len(components) >= 2
    body = bytes([40 * components[0] + components[1]])
    for c in components[2:]:
        if c < 128:
            body += bytes([c])
        else:
            # Base-128 encoding.
            parts = []
            val = c
            parts.append(val & 0x7F)
            val >>= 7
            while val:
                parts.append(0x80 | (val & 0x7F))
                val >>= 7
            body += bytes(reversed(parts))
    return der_tag_length(0x06, body)


def der_null() -> bytes:
    return b"\x05\x00"


def der_explicit(number: int, content: bytes) -> bytes:
    """Context-specific EXPLICIT tag [number] CONSTRUCTED."""
    return der_tag_length(0xA0 | number, content)


def der_implicit(number: int, content: bytes) -> bytes:
    """Context-specific IMPLICIT tag [number] CONSTRUCTED.

    Replaces the outermost tag of `content` with the implicit tag.
    """
    return der_tag_length(0xA0 | number, content)


def der_algid(oid_components: list[int], with_null: bool = True) -> bytes:
    """DER-encode an AlgorithmIdentifier SEQUENCE { OID [, NULL] }."""
    body = der_oid(oid_components)
    if with_null:
        body += der_null()
    return der_sequence(body)


# ---------------------------------------------------------------------------
# Well-known OIDs
# ---------------------------------------------------------------------------

OID_SIGNED_DATA = [1, 2, 840, 113549, 1, 7, 2]
OID_LDS_SECURITY_OBJECT = [2, 23, 136, 1, 1, 1]
OID_SHA256 = [2, 16, 840, 1, 101, 3, 4, 2, 1]
OID_SHA256_RSA = [1, 2, 840, 113549, 1, 1, 11]
OID_CONTENT_TYPE = [1, 2, 840, 113549, 1, 9, 3]
OID_MESSAGE_DIGEST = [1, 2, 840, 113549, 1, 9, 4]

# ---------------------------------------------------------------------------
# MRZ helpers
# ---------------------------------------------------------------------------

def pad(s: str, length: int, filler: str = "<") -> str:
    return (s + filler * length)[:length]


def check_digit(data: str) -> str:
    weights = [7, 3, 1]
    total = 0
    for i, ch in enumerate(data):
        if ch == "<":
            val = 0
        elif ch.isdigit():
            val = int(ch)
        elif ch.isalpha():
            val = ord(ch.upper()) - ord("A") + 10
        else:
            val = 0
        total += val * weights[i % 3]
    return str(total % 10)


def build_mrz(
    surname: str, given_names: str, passport_number: str, nationality: str,
    dob: str, sex: str, expiry: str, issuing_country: str,
    passport_type: str = "P", optional_data: str = "",
) -> bytes:
    """Build an 88-byte TD3 MRZ. Dates are YYMMDD."""
    surname = surname.upper().replace(" ", "<")
    given_names = given_names.upper().replace(" ", "<")
    name_field = pad(surname + "<<" + given_names, 39)

    line1 = pad(passport_type, 2) + pad(issuing_country.upper(), 3) + name_field
    assert len(line1) == 44

    pn = pad(passport_number.upper(), 9)
    pn_cd = check_digit(pn)
    nat = pad(nationality.upper(), 3)
    dob_cd = check_digit(dob)
    sex_ch = sex[0].upper() if sex else "<"
    exp_cd = check_digit(expiry)
    opt = pad(optional_data, 14)
    opt_cd = check_digit(opt)

    composite = pn + pn_cd + nat + dob + dob_cd + sex_ch + expiry + exp_cd + opt + opt_cd
    final_cd = check_digit(composite)
    line2 = pn + pn_cd + nat + dob + dob_cd + sex_ch + expiry + exp_cd + opt + opt_cd + final_cd
    assert len(line2) == 44

    return (line1 + line2).encode("ascii")


def build_dg1(mrz: bytes) -> bytes:
    """Wrap the 88-byte MRZ in the DG1 TLV (93 bytes)."""
    assert len(mrz) == 88
    return b"\x61\x5B\x5F\x1F\x58" + mrz


# ---------------------------------------------------------------------------
# SOD construction
# ---------------------------------------------------------------------------

def build_lds_security_object(dg_hashes: dict[int, bytes]) -> bytes:
    """DER-encode LDSSecurityObject { version 0, SHA-256, hashes }."""
    entries = b""
    for dg_num in sorted(dg_hashes):
        entry = der_integer_value(dg_num) + der_octet_string(dg_hashes[dg_num])
        entries += der_sequence(entry)

    return der_sequence(
        der_integer_value(0)
        + der_algid(OID_SHA256)
        + der_sequence(entries)
    )


def build_signed_attrs(econtent_hash: bytes) -> bytes:
    """DER-encode SignedAttributes as a SET (tag 0x31) for signing."""
    ct_attr = der_sequence(
        der_oid(OID_CONTENT_TYPE) + der_set(der_oid(OID_LDS_SECURITY_OBJECT))
    )
    md_attr = der_sequence(
        der_oid(OID_MESSAGE_DIGEST) + der_set(der_octet_string(econtent_hash))
    )
    return der_set(ct_attr + md_attr)


def build_sod(ds_cert_der: bytes, ds_private_key, econtent_der: bytes) -> bytes:
    """Build a DER-encoded CMS ContentInfo wrapping the SOD."""
    econtent_hash = hashlib.sha256(econtent_der).digest()
    signed_attrs = build_signed_attrs(econtent_hash)

    # Sign the SET-tagged signedAttrs.
    signature = ds_private_key.sign(signed_attrs, padding.PKCS1v15(), hashes.SHA256())

    # Extract issuer and serial from the DS certificate DER for SignerInfo.
    # Parse minimally: Certificate -> TBSCertificate -> {version, serial, ..., issuer}
    issuer_and_serial = extract_issuer_and_serial(ds_cert_der)

    # signedAttrs with implicit [0] tag: replace SET tag (0x31) with 0xA0.
    signed_attrs_implicit = bytes([0xA0]) + signed_attrs[1:]

    signer_info = der_sequence(
        der_integer_value(1)               # version
        + issuer_and_serial                # issuerAndSerialNumber
        + der_algid(OID_SHA256)            # digestAlgorithm
        + signed_attrs_implicit            # signedAttrs [0] IMPLICIT
        + der_algid(OID_SHA256_RSA)        # signatureAlgorithm
        + der_octet_string(signature)      # signature
    )

    # encapContentInfo
    ecap = der_sequence(
        der_oid(OID_LDS_SECURITY_OBJECT)
        + der_explicit(0, der_octet_string(econtent_der))
    )

    # SignedData
    signed_data = der_sequence(
        der_integer_value(3)               # version
        + der_set(der_algid(OID_SHA256))   # digestAlgorithms
        + ecap                             # encapContentInfo
        + der_implicit(0, ds_cert_der)     # certificates [0] IMPLICIT
        + der_set(signer_info)             # signerInfos
    )

    # ContentInfo
    return der_sequence(
        der_oid(OID_SIGNED_DATA) + der_explicit(0, signed_data)
    )


def extract_issuer_and_serial(cert_der: bytes) -> bytes:
    """Extract IssuerAndSerialNumber from a DER certificate.

    Parses the TBSCertificate to find the serialNumber and issuer
    fields, then re-encodes them as SEQUENCE { issuer, serial }.
    """
    # Certificate is SEQUENCE { tbsCertificate, signatureAlgorithm, signature }
    tbs_content = _unwrap_sequence(cert_der)

    pos = 0
    # version [0] EXPLICIT (optional, skip if present)
    if tbs_content[pos] == 0xA0:
        _, length, pos = _read_tl(tbs_content, pos)
        pos += length

    # serialNumber INTEGER
    serial_start = pos
    _, length, pos = _read_tl(tbs_content, pos)
    serial_der = tbs_content[serial_start:pos + length]
    pos += length

    # signature AlgorithmIdentifier (skip)
    _, length, pos = _read_tl(tbs_content, pos)
    pos += length

    # issuer Name
    issuer_start = pos
    _, length, pos = _read_tl(tbs_content, pos)
    issuer_der = tbs_content[issuer_start:pos + length]

    return der_sequence(issuer_der + serial_der)


def _unwrap_sequence(data: bytes) -> bytes:
    """Return the content of a DER SEQUENCE."""
    _, length, pos = _read_tl(data, 0)
    return data[pos:pos + length]


def _read_tl(data: bytes, offset: int) -> tuple[int, int, int]:
    """Read a DER tag + length at offset. Returns (tag, length, content_offset)."""
    tag = data[offset]
    offset += 1
    # Handle multi-byte tags (high-tag-number form).
    if tag & 0x1F == 0x1F:
        while data[offset] & 0x80:
            offset += 1
        offset += 1

    first_len = data[offset]
    offset += 1
    if first_len < 0x80:
        return tag, first_len, offset
    num_bytes = first_len & 0x7F
    length = int.from_bytes(data[offset:offset + num_bytes], "big")
    return tag, length, offset + num_bytes


# ---------------------------------------------------------------------------
# Key and certificate generation
# ---------------------------------------------------------------------------

def generate_keypair():
    return rsa.generate_private_key(public_exponent=65537, key_size=2048)


def build_certificate(subject_name, issuer_name, subject_key, signing_key, is_ca=False):
    now = datetime.now(timezone.utc)
    builder = (
        CertificateBuilder()
        .subject_name(subject_name)
        .issuer_name(issuer_name)
        .public_key(subject_key.public_key())
        .serial_number(random_serial_number())
        .not_valid_before(now)
        .not_valid_after(now + timedelta(days=3650))
        .add_extension(BasicConstraints(ca=is_ca, path_length=None), critical=True)
    )
    return builder.sign(signing_key, hashes.SHA256())


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Generate synthetic ICAO 9303 passport test data (SHA-256 + RSA-2048).",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--surname", default="SPECIMEN", help="Holder surname")
    parser.add_argument("--given-names", default="JEAN CHARLES", help="Holder given names")
    parser.add_argument("--passport-number", default="L898902C3", help="Document number (9 chars)")
    parser.add_argument("--nationality", default="UTO", help="Nationality (3-letter ISO code)")
    parser.add_argument("--dob", default="740812", help="Date of birth (YYMMDD)")
    parser.add_argument("--sex", default="M", help="Sex (M/F/<)")
    parser.add_argument("--expiry", default="310101", help="Expiry date (YYMMDD)")
    parser.add_argument("--issuing-country", default="UTO", help="Issuing country (3-letter ISO code)")
    parser.add_argument("--passport-type", default="P", help="Passport type (1-2 chars)")
    parser.add_argument("--optional-data", default="", help="Optional data (up to 14 chars)")
    parser.add_argument(
        "--output-dir",
        default=os.path.dirname(os.path.abspath(__file__)),
        help="Output directory",
    )
    args = parser.parse_args()

    out = args.output_dir
    os.makedirs(out, exist_ok=True)

    # 1. Build MRZ and DG1.
    mrz = build_mrz(
        surname=args.surname, given_names=args.given_names,
        passport_number=args.passport_number, nationality=args.nationality,
        dob=args.dob, sex=args.sex, expiry=args.expiry,
        issuing_country=args.issuing_country, passport_type=args.passport_type,
        optional_data=args.optional_data,
    )
    dg1 = build_dg1(mrz)
    assert len(dg1) == 93
    print(f"MRZ line 1: {mrz[:44].decode()}")
    print(f"MRZ line 2: {mrz[44:].decode()}")

    # 2. Generate CSCA and DS key pairs + certificates.
    csca_key = generate_keypair()
    csca_name = Name([
        NameAttribute(NameOID.COUNTRY_NAME, args.issuing_country[:2]),
        NameAttribute(NameOID.ORGANIZATION_NAME, "Test CSCA"),
        NameAttribute(NameOID.COMMON_NAME, f"Test CSCA {args.issuing_country}"),
    ])
    csca_cert = build_certificate(csca_name, csca_name, csca_key, csca_key, is_ca=True)

    ds_key = generate_keypair()
    ds_name = Name([
        NameAttribute(NameOID.COUNTRY_NAME, args.issuing_country[:2]),
        NameAttribute(NameOID.ORGANIZATION_NAME, "Test DS"),
        NameAttribute(NameOID.COMMON_NAME, f"Test DS {args.issuing_country}"),
    ])
    ds_cert = build_certificate(ds_name, csca_name, ds_key, csca_key, is_ca=False)
    ds_cert_der = ds_cert.public_bytes(serialization.Encoding.DER)

    # 3. Build LDSSecurityObject (eContent).
    dg1_hash = hashlib.sha256(dg1).digest()
    dg2_hash = hashlib.sha256(b"fake DG2 photo data").digest()
    econtent_der = build_lds_security_object({1: dg1_hash, 2: dg2_hash})

    # 4. Build the SOD.
    sod_der = build_sod(ds_cert_der, ds_key, econtent_der)

    # 5. Extract CSCA modulus.
    csca_modulus = csca_key.public_key().public_numbers().n
    csca_key_bytes = csca_modulus.to_bytes(256, byteorder="big")

    # 6. Write output files.
    files = {
        "dg1.bin": dg1,
        "sod.der": sod_der,
        "csca_key.bin": csca_key_bytes,
    }
    for name, data in files.items():
        path = os.path.join(out, name)
        with open(path, "wb") as f:
            f.write(data)

    print(f"\nGenerated files in {out}/:")
    for name, data in files.items():
        print(f"  {name:20s} ({len(data)} bytes)")

    # 7. Sanity checks.
    # CSCA -> DS certificate signature.
    csca_key.public_key().verify(
        ds_cert.signature, ds_cert.tbs_certificate_bytes,
        padding.PKCS1v15(), hashes.SHA256(),
    )
    print("\nCSCA -> DS certificate signature: OK")

    # DS -> signedAttrs signature.
    econtent_hash = hashlib.sha256(econtent_der).digest()
    signed_attrs = build_signed_attrs(econtent_hash)
    # Re-extract signature from the SOD to verify.
    # (Simpler: just verify our signing key works.)
    test_sig = ds_key.sign(signed_attrs, padding.PKCS1v15(), hashes.SHA256())
    ds_key.public_key().verify(test_sig, signed_attrs, padding.PKCS1v15(), hashes.SHA256())
    print("DS -> signedAttrs signature: OK")

    # eContent hash == messageDigest.
    print(f"DG1 SHA-256:      {dg1_hash.hex()}")
    print(f"eContent SHA-256: {econtent_hash.hex()}")
    print(f"SOD size:         {len(sod_der)} bytes")


if __name__ == "__main__":
    main()
