//! Off-circuit ASN.1 encoding/decoding utilities: tag/length/value constants,
//! encoding functions, decoding helpers, and typed constructors for common
//! ASN.1 types. The decoders follow the DER wire format but do not enforce
//! minimality (e.g., a long-form length encoding of a value ≤ 127 is accepted).

/// ASN.1 class values for the two high bits of a tag's first byte.
pub mod class {
    /// Universal class (0x00).
    pub const UNIVERSAL: u8 = 0x00;
    /// Application class (0x40).
    pub const APPLICATION: u8 = 0x40;
    /// Context-specific class (0x80).
    pub const CONTEXT_SPECIFIC: u8 = 0x80;
    /// Private class (0xC0).
    pub const PRIVATE: u8 = 0xC0;
}

/// Constructed-form flag (bit 5 of a tag's first byte).
pub const CONSTRUCTED: u8 = 0x20;

/// Common universal-class primitive tags (single-byte, short form).
pub mod tag {
    /// BOOLEAN (0x01).
    pub const BOOLEAN: u8 = 0x01;
    /// INTEGER (0x02).
    pub const INTEGER: u8 = 0x02;
    /// BIT STRING (0x03).
    pub const BIT_STRING: u8 = 0x03;
    /// OCTET STRING (0x04).
    pub const OCTET_STRING: u8 = 0x04;
    /// NULL (0x05).
    pub const NULL: u8 = 0x05;
    /// OBJECT IDENTIFIER (0x06).
    pub const OID: u8 = 0x06;
    /// UTF8String (0x0C).
    pub const UTF8_STRING: u8 = 0x0C;
    /// PrintableString (0x13).
    pub const PRINTABLE_STRING: u8 = 0x13;
    /// IA5String (0x16).
    pub const IA5_STRING: u8 = 0x16;
    /// UTCTime (0x17).
    pub const UTC_TIME: u8 = 0x17;
    /// GeneralizedTime (0x18).
    pub const GENERALIZED_TIME: u8 = 0x18;
    /// SEQUENCE (constructed, 0x30).
    pub const SEQUENCE: u8 = 0x30;
    /// SET (constructed, 0x31).
    pub const SET: u8 = 0x31;
}

/// A tag descriptor: class, constructed flag, and tag number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tag {
    /// Class bits (use constants from [`class`]).
    pub class: u8,
    /// Whether this is a constructed (vs primitive) encoding.
    pub constructed: bool,
    /// The tag number.
    pub number: u32,
}

/// Encodes a DER tag from a [`Tag`] descriptor.
///
/// - **Short form** (tag number 0-30): single byte.
/// - **Long form** (tag number >= 31): first byte has `0x1F` in the low 5 bits,
///   followed by base-128 encoded tag number bytes with continuation bits.
pub fn encode_tag(tag: &Tag) -> Vec<u8> {
    let first = tag.class | if tag.constructed { CONSTRUCTED } else { 0 };
    if tag.number <= 30 {
        vec![first | tag.number as u8]
    } else {
        let mut out = vec![first | 0x1F];
        let mut fragments = Vec::new();
        let mut n = tag.number;
        fragments.push((n & 0x7F) as u8);
        n >>= 7;
        while n > 0 {
            fragments.push(0x80 | (n & 0x7F) as u8);
            n >>= 7;
        }
        fragments.reverse();
        out.extend(fragments);
        out
    }
}

/// Encodes a DER length field.
///
/// - **Short form** (0-127): single byte.
/// - **Long form** (>= 128): first byte = `0x80 | N`, then N bytes big-endian.
pub fn encode_length(len: usize) -> Vec<u8> {
    if len <= 127 {
        vec![len as u8]
    } else {
        let be = {
            let mut n = len;
            let mut bytes = Vec::new();
            while n > 0 {
                bytes.push((n & 0xFF) as u8);
                n >>= 8;
            }
            bytes.reverse();
            bytes
        };
        let mut out = vec![0x80 | be.len() as u8];
        out.extend(be);
        out
    }
}

/// Decodes a DER tag from the start of `input`. Returns the number of
/// bytes consumed and the decoded [`Tag`], or `None` if the input is
/// empty or truncated.
///
/// This is the inverse of [`encode_tag`].
pub fn decode_tag(input: &[u8]) -> Option<(usize, Tag)> {
    let &first = input.first()?;
    let class = first & 0xC0;
    let constructed = first & CONSTRUCTED != 0;
    let low5 = first & 0x1F;

    if low5 != 0x1F {
        // Short form: tag number in bits 4–0.
        Some((1, Tag { class, constructed, number: low5 as u32 }))
    } else {
        // Long form: subsequent base-128 bytes with continuation bits.
        let mut number: u32 = 0;
        let mut i = 1;
        loop {
            let &b = input.get(i)?;
            i += 1;
            number = number.checked_shl(7)? | (b & 0x7F) as u32;
            if b & 0x80 == 0 {
                break;
            }
        }
        Some((i, Tag { class, constructed, number }))
    }
}

/// Decodes a DER length from the start of `input`. Returns the number of
/// bytes consumed and the length value, or `None` if the input is empty,
/// truncated, or uses the indefinite form (`0x80`).
///
/// This is the inverse of [`encode_length`].
pub fn decode_length(input: &[u8]) -> Option<(usize, usize)> {
    let &first = input.first()?;
    if first <= 0x7F {
        // Short form.
        Some((1, first as usize))
    } else if first == 0x80 {
        // Indefinite form — forbidden in DER.
        None
    } else {
        // Long form: low 7 bits give the number of big-endian length bytes that follow.
        let n = (first & 0x7F) as usize;
        let mut value: usize = 0;
        for i in 0..n {
            let &b = input.get(1 + i)?;
            value = value.checked_shl(8)? | b as usize;
        }
        Some((1 + n, value))
    }
}

/// Builds a DER-encoded TLV from pre-encoded tag bytes and raw value
/// bytes. The length field is computed automatically from the value.
///
/// The `tag` argument can be a single-byte constant from [`tag`] or the
/// output of [`encode_tag`].
pub fn encode_tlv(tag: &[u8], val: &[u8]) -> Vec<u8> {
    tag.iter()
        .chain(encode_length(val.len()).iter())
        .chain(val.iter())
        .copied()
        .collect()
}

// ---------------------------------------------------------------------------
// Typed DER constructors
// ---------------------------------------------------------------------------

/// Encodes a DER BOOLEAN.
pub fn boolean(value: bool) -> Vec<u8> {
    encode_tlv(&[tag::BOOLEAN], &[if value { 0xFF } else { 0x00 }])
}

/// Encodes a DER INTEGER from a signed value.
pub fn integer(n: i64) -> Vec<u8> {
    let value = encode_integer_value(n);
    encode_tlv(&[tag::INTEGER], &value)
}

/// Encodes a signed integer as minimal DER content bytes (big-endian,
/// two's complement, no superfluous leading 0x00 or 0xFF bytes).
fn encode_integer_value(n: i64) -> Vec<u8> {
    if n == 0 {
        return vec![0x00];
    }
    let be = n.to_be_bytes();
    let skip = if n > 0 {
        be.iter().take_while(|&&b| b == 0x00).count().min(be.len() - 1)
    } else {
        be.iter().take_while(|&&b| b == 0xFF).count().min(be.len() - 1)
    };
    let trimmed = &be[skip..];
    if n > 0 && trimmed[0] & 0x80 != 0 {
        let mut out = vec![0x00];
        out.extend_from_slice(trimmed);
        out
    } else if n < 0 && trimmed[0] & 0x80 == 0 {
        let mut out = vec![0xFF];
        out.extend_from_slice(trimmed);
        out
    } else {
        trimmed.to_vec()
    }
}

/// Encodes a DER NULL.
pub fn null() -> Vec<u8> {
    encode_tlv(&[tag::NULL], &[])
}

/// Encodes a DER OCTET STRING from raw bytes.
pub fn octet_string(bytes: &[u8]) -> Vec<u8> {
    encode_tlv(&[tag::OCTET_STRING], bytes)
}

/// Encodes a DER BIT STRING. `unused_bits` is the number of unused bits in
/// the last byte (0-7); use 0 when the content is byte-aligned.
pub fn bit_string(bytes: &[u8], unused_bits: u8) -> Vec<u8> {
    let mut value = vec![unused_bits];
    value.extend_from_slice(bytes);
    encode_tlv(&[tag::BIT_STRING], &value)
}

/// Encodes a DER OBJECT IDENTIFIER from its dot-notation components.
pub fn oid(components: &[u32]) -> Vec<u8> {
    assert!(components.len() >= 2, "OID must have at least 2 components");
    let mut value = Vec::new();
    value.push((40 * components[0] + components[1]) as u8);
    for &c in &components[2..] {
        encode_base128(&mut value, c);
    }
    encode_tlv(&[tag::OID], &value)
}

/// Encodes a u32 in base-128 with continuation bits (used by OID encoding).
fn encode_base128(out: &mut Vec<u8>, mut n: u32) {
    let mut fragments = Vec::new();
    fragments.push((n & 0x7F) as u8);
    n >>= 7;
    while n > 0 {
        fragments.push(0x80 | (n & 0x7F) as u8);
        n >>= 7;
    }
    fragments.reverse();
    out.extend(fragments);
}

/// Encodes a DER UTF8String.
pub fn utf8_string(s: &str) -> Vec<u8> {
    encode_tlv(&[tag::UTF8_STRING], s.as_bytes())
}

/// Encodes a DER PrintableString.
pub fn printable_string(s: &str) -> Vec<u8> {
    encode_tlv(&[tag::PRINTABLE_STRING], s.as_bytes())
}

/// Encodes a DER IA5String.
pub fn ia5_string(s: &str) -> Vec<u8> {
    encode_tlv(&[tag::IA5_STRING], s.as_bytes())
}

/// Encodes a DER UTCTime from a string like `"250101120000Z"`.
pub fn utc_time(s: &str) -> Vec<u8> {
    encode_tlv(&[tag::UTC_TIME], s.as_bytes())
}

/// Encodes a DER GeneralizedTime from a string like `"20250101120000Z"`.
pub fn generalized_time(s: &str) -> Vec<u8> {
    encode_tlv(&[tag::GENERALIZED_TIME], s.as_bytes())
}

/// Encodes a DER SEQUENCE wrapping pre-built children.
pub fn sequence(children: &[Vec<u8>]) -> Vec<u8> {
    let value: Vec<u8> = children.iter().flatten().copied().collect();
    encode_tlv(&[tag::SEQUENCE], &value)
}

/// Encodes a DER SET wrapping pre-built children.
pub fn set(children: &[Vec<u8>]) -> Vec<u8> {
    let value: Vec<u8> = children.iter().flatten().copied().collect();
    encode_tlv(&[tag::SET], &value)
}

/// Wraps content with a context-specific tag (explicit tagging).
pub fn context(number: u32, inner: &[u8]) -> Vec<u8> {
    let tag = Tag {
        class: class::CONTEXT_SPECIFIC,
        constructed: true,
        number,
    };
    encode_tlv(&encode_tag(&tag), inner)
}

/// Wraps content with an application-class constructed tag.
///
/// Useful for passport-specific tags like DG1 (`application(1, ...)` ->
/// `0x61`).
pub fn application(number: u32, inner: &[u8]) -> Vec<u8> {
    let tag = Tag {
        class: class::APPLICATION,
        constructed: true,
        number,
    };
    encode_tlv(&encode_tag(&tag), inner)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_integer() {
        assert_eq!(integer(0), vec![0x02, 0x01, 0x00]);
        assert_eq!(integer(127), vec![0x02, 0x01, 0x7F]);
        assert_eq!(integer(128), vec![0x02, 0x02, 0x00, 0x80]);
        assert_eq!(integer(8697587), vec![0x02, 0x04, 0x00, 0x84, 0xB6, 0xF3]);
        assert_eq!(integer(-1), vec![0x02, 0x01, 0xFF]);
        assert_eq!(integer(-128), vec![0x02, 0x01, 0x80]);
        assert_eq!(integer(-129), vec![0x02, 0x02, 0xFF, 0x7F]);
    }

    #[test]
    fn test_boolean() {
        assert_eq!(boolean(true), vec![0x01, 0x01, 0xFF]);
        assert_eq!(boolean(false), vec![0x01, 0x01, 0x00]);
    }

    #[test]
    fn test_null() {
        assert_eq!(null(), vec![0x05, 0x00]);
    }

    #[test]
    fn test_octet_string() {
        assert_eq!(octet_string(&[0xDE, 0xAD]), vec![0x04, 0x02, 0xDE, 0xAD]);
        let enc = octet_string(&[0xAA; 256]);
        assert_eq!(enc[0], 0x04);
        assert_eq!(&enc[1..4], &[0x82, 0x01, 0x00]);
        assert_eq!(enc.len(), 1 + 3 + 256);
    }

    #[test]
    fn test_oid() {
        assert_eq!(
            oid(&[1, 2, 840, 113549]),
            vec![0x06, 0x06, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D],
        );
        assert_eq!(oid(&[2, 5, 4, 3]), vec![0x06, 0x03, 0x55, 0x04, 0x03],);
    }

    #[test]
    fn test_sequence() {
        let seq = sequence(&[integer(1), boolean(true)]);
        assert_eq!(seq, vec![0x30, 0x06, 0x02, 0x01, 0x01, 0x01, 0x01, 0xFF]);
    }

    #[test]
    fn test_context_and_application() {
        let tagged = context(0, &integer(42));
        assert_eq!(tagged[0], 0xA0);
        assert_eq!(tagged, vec![0xA0, 0x03, 0x02, 0x01, 0x2A]);

        let app = application(1, &octet_string(&[0x01]));
        assert_eq!(app[0], 0x61);
    }

    #[test]
    fn test_string_types() {
        assert_eq!(utf8_string("AB"), vec![0x0C, 0x02, 0x41, 0x42]);
        assert_eq!(printable_string("AB"), vec![0x13, 0x02, 0x41, 0x42]);
    }

    #[test]
    fn test_long_form_tag() {
        let tag31 = Tag {
            class: class::APPLICATION,
            constructed: true,
            number: 31,
        };
        assert_eq!(encode_tag(&tag31), vec![0x7F, 0x1F]);

        let tag129 = Tag {
            class: class::APPLICATION,
            constructed: true,
            number: 129,
        };
        assert_eq!(encode_tag(&tag129), vec![0x7F, 0x81, 0x01]);
    }

    #[test]
    fn test_bit_string() {
        assert_eq!(
            bit_string(&[0x04, 0x03], 0),
            vec![0x03, 0x03, 0x00, 0x04, 0x03]
        );
    }

    #[test]
    fn test_decode_tag_short() {
        assert_eq!(
            decode_tag(&[0x30]),
            Some((1, Tag { class: class::UNIVERSAL, constructed: true, number: 16 }))
        );
        assert_eq!(
            decode_tag(&[0x02]),
            Some((1, Tag { class: class::UNIVERSAL, constructed: false, number: 2 }))
        );
        assert_eq!(
            decode_tag(&[0xA0]),
            Some((1, Tag { class: class::CONTEXT_SPECIFIC, constructed: true, number: 0 }))
        );
    }

    #[test]
    fn test_decode_tag_long() {
        assert_eq!(
            decode_tag(&[0x7F, 0x1F]),
            Some((2, Tag { class: class::APPLICATION, constructed: true, number: 31 }))
        );
        assert_eq!(
            decode_tag(&[0x7F, 0x81, 0x01]),
            Some((3, Tag { class: class::APPLICATION, constructed: true, number: 129 }))
        );
    }

    #[test]
    fn test_decode_tag_roundtrip() {
        for number in [0, 1, 30, 31, 127, 128, 129, 16383, 16384] {
            let tag = Tag { class: class::CONTEXT_SPECIFIC, constructed: true, number };
            let encoded = encode_tag(&tag);
            let (consumed, decoded) = decode_tag(&encoded).unwrap();
            assert_eq!(consumed, encoded.len());
            assert_eq!(decoded, tag);
        }
    }

    #[test]
    fn test_decode_length_short() {
        assert_eq!(decode_length(&[0x00]), Some((1, 0)));
        assert_eq!(decode_length(&[0x58]), Some((1, 88)));
        assert_eq!(decode_length(&[0x7F]), Some((1, 127)));
    }

    #[test]
    fn test_decode_length_long() {
        assert_eq!(decode_length(&[0x81, 0x58]), Some((2, 88)));
        assert_eq!(decode_length(&[0x82, 0x01, 0x00]), Some((3, 256)));
    }

    #[test]
    fn test_decode_length_indefinite() {
        assert_eq!(decode_length(&[0x80]), None);
    }

    #[test]
    fn test_decode_length_roundtrip() {
        for len in [0, 1, 127, 128, 255, 256, 65535, 65536] {
            let encoded = encode_length(len);
            let (consumed, decoded) = decode_length(&encoded).unwrap();
            assert_eq!(consumed, encoded.len());
            assert_eq!(decoded, len);
        }
    }

    #[test]
    fn test_decode_tag_empty() {
        assert_eq!(decode_tag(&[]), None);
    }

    #[test]
    fn test_decode_length_empty() {
        assert_eq!(decode_length(&[]), None);
    }

    #[test]
    fn test_decode_tag_truncated_long() {
        assert_eq!(decode_tag(&[0x7F]), None);
        assert_eq!(decode_tag(&[0x7F, 0x81]), None);
    }

    #[test]
    fn test_decode_length_truncated_long() {
        assert_eq!(decode_length(&[0x82, 0x01]), None);
    }
}
