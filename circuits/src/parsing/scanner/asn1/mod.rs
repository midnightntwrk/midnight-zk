//! ASN.1 parsing support: off-circuit encoding helpers, spec descriptor
//! types, and circuit-level structure verification. Follows the DER wire
//! format but does not enforce minimality of tag/length encodings.

pub mod der_encoding;
mod parser;
use std::{fmt::Debug, hash::Hash};

use midnight_proofs::circuit::Value;

use crate::parsing::scanner::asn1::der_encoding::encode_length;

/// Internal representation for [`Asn1RawData`].
#[derive(Debug, Clone)]
enum Asn1RawDataInternal<Index>
where
    Index: Eq + Hash,
{
    /// A constant sequence of bytes.
    Const(Vec<u8>, Option<Index>),
    /// A sequence of bytes with a fixed length.
    Fixlen(usize, Option<Index>),
    /// A sequence of bytes with an implicit maximal length.
    Varlen(Option<Index>),
}

impl<Index: Eq + Hash> Asn1RawDataInternal<Index> {
    fn marker_mut(&mut self) -> &mut Option<Index> {
        match self {
            Asn1RawDataInternal::Const(_, idx) => idx,
            Asn1RawDataInternal::Fixlen(_, idx) => idx,
            Asn1RawDataInternal::Varlen(idx) => idx,
        }
    }
}

/// An ASN.1 TLV (Tag-Length-Value) unit.
#[derive(Debug, Clone)]
struct Asn1Tlv<Index>
where
    Index: Eq + Hash,
{
    tag: Asn1RawData<Index>,
    len: Asn1RawData<Index>,
    val: Asn1Spec<Index>,
}

/// An ASN.1 block: either raw data or a TLV unit.
#[derive(Debug, Clone)]
enum Asn1Block<Index>
where
    Index: Eq + Hash,
{
    /// A constant sequence of bytes.
    Const(Vec<u8>, Option<Index>),
    /// A fixed-length block. The boolean is `true` if the data should be
    /// extracted, `false` if only the length is accounted for.
    Fixlen(usize, Option<Index>),
    /// A TLV unit. The outer `Option<Index>` is a marker for full T+L+V
    /// extraction.
    Tlv(Asn1Tlv<Index>, Option<Index>),
    /// An optional TLV unit: the tag bytes are peeked at during witness
    /// consumption; if they match `expected_tag`, the full T+L+V is consumed,
    /// otherwise nothing is consumed. Both cases produce valid ScannerVecs
    /// (populated or empty with len=0).
    ///
    /// **Limitation:** the value must be a simple (non-recursive) spec.
    OptionalTlv {
        expected_tag: Vec<u8>,
        len: Asn1RawData<Index>,
        val: Asn1Spec<Index>,
    },
    /// A trail block: consumes all remaining bytes in the enclosing TLV
    /// value. Can only appear as the last block in a spec that is used as
    /// a TLV value (panics at parse time if used at top level).
    Varlen(Option<Index>),
}

impl<Index: Eq + Hash> Asn1Block<Index> {
    /// Returns the total byte count of this block if statically known.
    fn known_len(&self) -> Option<usize> {
        match self {
            Asn1Block::Const(v, _) => Some(v.len()),
            Asn1Block::Fixlen(n, _) => Some(*n),
            Asn1Block::Tlv(tlv, _) => {
                let tag_len = tlv.tag.len()?;
                let len_len = tlv.len.len()?;
                let val_len = tlv.val.size()?;
                Some(tag_len + len_len + val_len)
            }
            Asn1Block::OptionalTlv { .. } => None,
            Asn1Block::Varlen(_) => None,
        }
    }
}

fn double_mark<Index: Debug, T>(m1: Index, m2: Index) -> T {
    panic!(
        "attempting to mark some parsed ASN.1 data with two different markers {:?} and {:?}",
        m1, m2
    )
}

/// A raw block of data in an ASN.1 descriptor. Used for the tag and length
/// fields of a TLV. The type is opaque and built with dedicated constructors.
#[derive(Debug, Clone)]
pub struct Asn1RawData<Index>(Asn1RawDataInternal<Index>)
where
    Index: Eq + Hash;

impl<Index: Eq + Hash + Debug> From<der_encoding::Tag> for Asn1RawData<Index> {
    /// Encodes the tag and wraps as a constant block.
    fn from(tag: der_encoding::Tag) -> Self {
        Asn1RawData::bytes_const(&der_encoding::encode_tag(&tag))
    }
}

impl<Index: Eq + Hash + Debug> From<&[u8]> for Asn1RawData<Index> {
    /// Wraps raw bytes as a constant block.
    fn from(bytes: &[u8]) -> Self {
        Asn1RawData::bytes_const(bytes)
    }
}

impl<Index: Eq + Hash + Debug, const N: usize> From<&[u8; N]> for Asn1RawData<Index> {
    /// Wraps raw bytes as a constant block.
    fn from(bytes: &[u8; N]) -> Self {
        Asn1RawData::bytes_const(bytes)
    }
}

impl<Index: Eq + Hash + Debug> From<&Vec<u8>> for Asn1RawData<Index> {
    /// Wraps raw bytes as a constant block.
    fn from(bytes: &Vec<u8>) -> Self {
        Asn1RawData::bytes_const(bytes)
    }
}

impl<Index: Eq + Hash + Debug> From<usize> for Asn1RawData<Index> {
    /// Encodes a length value and wraps as a constant block.
    fn from(len: usize) -> Self {
        Asn1RawData::bytes_const(&encode_length(len))
    }
}

impl<Index: Eq + Hash> Asn1RawData<Index> {
    /// Returns the known byte count of this data block, or `None` for
    /// variable-length blocks.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> Option<usize> {
        match &self.0 {
            Asn1RawDataInternal::Const(v, _) => Some(v.len()),
            Asn1RawDataInternal::Fixlen(n, _) => Some(*n),
            Asn1RawDataInternal::Varlen(_) => None,
        }
    }

    /// Consumes the block and returns the extraction marker, if any.
    fn into_marker(self) -> Option<Index> {
        match self.0 {
            Asn1RawDataInternal::Const(_, idx) => idx,
            Asn1RawDataInternal::Fixlen(_, idx) => idx,
            Asn1RawDataInternal::Varlen(idx) => idx,
        }
    }
}

impl<Index> Asn1RawData<Index>
where
    Index: Eq + Hash + Debug,
{
    /// Constructs a constant (known at spec-build time) raw data block.
    /// The bytes are baked into the circuit as constants and verified
    /// against the witness. Cheap, fixed-length operation.
    pub fn bytes_const(data: &[u8]) -> Self {
        Asn1RawData(Asn1RawDataInternal::Const(data.to_vec(), None))
    }

    /// A sequence of unspecified raw bytes, interpreted from context.
    /// `None` means variable length, `Some(len)` means fixed length.
    /// Parsing is significantly more efficient for fixed length data.
    pub fn any(len: Option<usize>) -> Self {
        match len {
            None => Asn1RawData(Asn1RawDataInternal::Varlen(None)),
            Some(len) => Asn1RawData(Asn1RawDataInternal::Fixlen(len, None)),
        }
    }

    /// Indicates that `self`'s extraction will be referenced as `m`. Extracting
    /// constant data is free (and likely useless). Extracting fixed-len data
    /// incurs an additional cost, and variable-length data adds yet another
    /// overhead.
    ///
    /// # Panics
    ///
    /// If attempts to mark a constant block of bytes.
    pub fn mark(mut self, m: Index) -> Self {
        assert!(
            !matches!(self.0, Asn1RawDataInternal::Const(_, _)),
            "It is useless to mark constant blocks of Asn1Spec's"
        );
        let slot = self.0.marker_mut();
        match slot.take() {
            None => *slot = Some(m),
            Some(m2) => double_mark(m, m2),
        }
        self
    }
}

/// An ASN.1 spec: a complete ASN.1 encoding which may include several
/// blocks at the same level. The internal structure is opaque; use the
/// builder methods to construct instances as chains of instructions.
///
/// The spec caches the total byte count when all blocks have statically
/// known sizes, accessible via [`size`](`Self::size`).
///
/// The third field is the "full marker": when set, extraction of all bytes
/// produced by this spec's blocks is recorded under this index. Used for
/// V-only extraction when a spec serves as a TLV's value.
#[derive(Debug, Clone)]
pub struct Asn1Spec<Index>(Option<usize>, Vec<Asn1Block<Index>>, Option<Index>)
where
    Index: Eq + Hash;

impl<Index: Eq + Hash> Default for Asn1Spec<Index> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Index> Asn1Spec<Index>
where
    Index: Eq + Hash,
{
    /// Creates an empty specification.
    pub fn new() -> Self {
        Self(Some(0), Vec::new(), None)
    }

    /// Returns the total byte count if all blocks have statically known
    /// sizes, or `None` otherwise.
    pub fn size(&self) -> Option<usize> {
        self.0
    }

}

impl<Index> Asn1Spec<Index>
where
    Index: Eq + Hash + Debug,
{
    /// Adds several blocks to the spec, updating the cached size.
    fn add_many_block(mut self, blocks: Vec<Asn1Block<Index>>) -> Self {
        assert!(
            !self.ends_with_varlen(),
            "cannot add blocks after a trail (Varlen) block"
        );
        for block in &blocks {
            self.0 = self.0.and_then(|s| block.known_len().map(|b| s + b));
        }
        self.1.extend(blocks);
        self
    }

    /// Adds 1 block to the spec.
    fn add_block(self, block: Asn1Block<Index>) -> Self {
        self.add_many_block(vec![block])
    }

    /// Appends a constant byte sequence. The bytes are baked into the
    /// circuit as constants and verified against the witness. Cheap,
    /// fixed-length operation.
    ///
    /// Use [`der_encoding`] helpers to build the byte sequence for
    /// standard ASN.1 structures (OIDs, lengths, tags, etc.).
    pub fn read_bytes_const(self, bytes: &[u8]) -> Self {
        self.add_block(Asn1Block::Const(bytes.to_vec(), None))
    }

    /// Appends a block that reads `len` unknown bytes from the input.
    /// The bytes are assigned as witness values. Cheap, fixed-length
    /// operation (costlier than constant blocks when extracted, but
    /// much cheaper than variable-length).
    pub fn read_bytes(self, len: usize) -> Self {
        self.add_block(Asn1Block::Fixlen(len, None))
    }

    /// Adds a TLV node to the spec with explicit tag, length, and value.
    /// Panics if `len` and `val` are inconsistent (e.g. constant length
    /// with unknown-size value, or known-size value with non-constant
    /// length).
    ///
    /// For common ASN.1 types, prefer the dedicated helpers which
    /// automatically compute the length encoding from `val`:
    /// [`read_sequence`](`Self::read_sequence`),
    /// [`read_set`](`Self::read_set`),
    /// [`read_octet_string`](`Self::read_octet_string`),
    /// [`read_bit_string`](`Self::read_bit_string`),
    /// [`read_integer`](`Self::read_integer`),
    /// [`read_ctx`](`Self::read_ctx`).
    ///
    /// # Type conversions
    ///
    /// `tag` and `len` accept several types via `Into`:
    ///
    ///    - `tag`: [`Tag`](der_encoding::Tag) (encoded via
    ///      [`encode_tag`](der_encoding::encode_tag)) or `&[u8]` (pre-encoded
    ///      raw tag bytes).
    ///
    ///   - `len`: `usize` (encoded via [`encode_length`](encode_length), e.g.,
    ///     `88usize` -> `[0x58]`) or `&[u8]` (pre-encoded raw length bytes).
    pub fn read_tlv(
        self,
        tag: impl Into<Asn1RawData<Index>>,
        len: impl Into<Asn1RawData<Index>>,
        val: Asn1Spec<Index>,
    ) -> Self {
        let tag = tag.into();
        let len = len.into();

        Self::check_tlv_spec_consistency("read_tlv", &len, &val);
        self.add_block(Asn1Block::Tlv(Asn1Tlv { tag, len, val }, None))
    }

    /// Adds an optional TLV node to the spec. This is the most expensive
    /// block type (three `ScannerVec`s, automaton validation, conditional
    /// constraints, all variable-length). Produces three variable-length
    /// vectors for each
    /// T+L+V, which are empty (len=0) when the field is not present in
    /// the witness. The verifier does not learn whether the optional
    /// field is present or not.
    ///
    /// When optional fields appear at the end of a TLV value and do not
    /// need individual extraction, [`read_trail`](`Self::read_trail`) is
    /// significantly cheaper: it consumes the remaining bytes in bulk
    /// without per-field parsing.
    ///
    /// # Limitations
    ///
    /// The value `val` must be a simple (non-recursive, single-block) spec.
    pub fn read_tlv_optional(
        self,
        tag: &[u8],
        len: impl Into<Asn1RawData<Index>>,
        val: Asn1Spec<Index>,
    ) -> Self {
        let len = len.into();
        assert!(
            val.1.len() <= 1
                && !matches!(
                    val.1.first(),
                    Some(Asn1Block::Tlv(..) | Asn1Block::OptionalTlv { .. })
                ),
            "read_tlv_optional: only simple (non-recursive) value specs are supported"
        );
        Self::check_tlv_spec_consistency("read_tlv_optional", &len, &val);
        self.add_block(Asn1Block::OptionalTlv {
            expected_tag: tag.to_vec(),
            len,
            val,
        })
    }

    /// Adds another full spec after this one.
    ///
    /// # Panics
    ///
    /// If either spec has a full marker set via
    /// [`mark_full`](`Self::mark_full`).
    pub fn then(self, spec: Asn1Spec<Index>) -> Self {
        assert!(
            self.2.is_none(),
            "then: left-hand spec has a full marker; cannot concatenate"
        );
        assert!(
            spec.2.is_none(),
            "then: right-hand spec has a full marker; cannot concatenate"
        );
        self.add_many_block(spec.1)
    }

    /// Concatenates several specs in order.
    pub fn cat(items: Vec<Self>) -> Self {
        items.into_iter().fold(Self::new(), |acc, spec| acc.then(spec))
    }
}
