//! ASN.1 parsing support: off-circuit encoding helpers, spec descriptor
//! types, and circuit-level structure verification. Follows the DER wire
//! format but does not enforce minimality of tag/length encodings.

pub mod der_encoding;
mod parser;
use std::{fmt::Debug, hash::Hash};

// ---------------------------------------------------------------------------
// Internal enums (not exposed)
// ---------------------------------------------------------------------------

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

/// Internal representation for [`Asn1Value`].
#[derive(Debug, Clone)]
enum Asn1ValueInternal<Index>
where
    Index: Eq + Hash,
{
    /// Terminal block of data.
    Simple(Asn1RawData<Index>),
    /// Recursive: the value is itself parsed as a sequence of blocks.
    Recursive(Asn1Spec<Index>, Option<Index>),
}

/// An ASN.1 TLV (Tag-Length-Value) unit.
#[derive(Debug, Clone)]
struct Asn1Tlv<Index>
where
    Index: Eq + Hash,
{
    tag: Asn1RawData<Index>,
    len: Asn1RawData<Index>,
    val: Asn1Value<Index>,
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
    /// A TLV unit.
    Tlv(Asn1Tlv<Index>, Option<Index>),
    /// An optional TLV unit: the tag bytes are peeked at during witness
    /// consumption; if they match `expected_tag`, the full T+L+V is consumed,
    /// otherwise nothing is consumed. Both cases produce valid ScannerVecs
    /// (populated or empty with len=0).
    ///
    /// **Limitation:** the value must be `Simple` (non-recursive).
    OptionalTlv {
        expected_tag: Vec<u8>,
        len: Asn1RawData<Index>,
        val: Asn1Value<Index>,
    },
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
                let val_len = tlv.val.known_len()?;
                Some(tag_len + len_len + val_len)
            }
            Asn1Block::OptionalTlv { .. } => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

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
        Asn1RawData::fixed(&der_encoding::encode_tag(&tag))
    }
}

impl<Index: Eq + Hash + Debug> From<&[u8]> for Asn1RawData<Index> {
    /// Wraps raw bytes as a constant block.
    fn from(bytes: &[u8]) -> Self {
        Asn1RawData::fixed(bytes)
    }
}

impl<Index: Eq + Hash + Debug, const N: usize> From<&[u8; N]> for Asn1RawData<Index> {
    /// Wraps raw bytes as a constant block.
    fn from(bytes: &[u8; N]) -> Self {
        Asn1RawData::fixed(bytes)
    }
}

impl<Index: Eq + Hash + Debug> From<&Vec<u8>> for Asn1RawData<Index> {
    /// Wraps raw bytes as a constant block.
    fn from(bytes: &Vec<u8>) -> Self {
        Asn1RawData::fixed(bytes)
    }
}

impl<Index: Eq + Hash + Debug> From<usize> for Asn1RawData<Index> {
    /// Encodes a length value and wraps as a constant block.
    fn from(len: usize) -> Self {
        Asn1RawData::fixed(&der_encoding::encode_length(len))
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
    /// Constructs a constant sequence of data.
    pub fn fixed(data: &[u8]) -> Self {
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

    /// Indicates that `self`'s extraction will be referenced as `m`.
    pub fn mark(mut self, m: Index) -> Self {
        let slot = self.0.marker_mut();
        match slot.take() {
            None => *slot = Some(m),
            Some(m2) => double_mark(m, m2),
        }
        self
    }
}

/// The value field of a TLV node.
///
/// Construct with [`Asn1Value::fixed`] for known constant values,
/// [`Asn1Value::any`] for leaf data of known or unknown length, or
/// [`Asn1Value::recursive`] when the value is itself a sequence of TLV
/// blocks.
#[derive(Debug, Clone)]
pub struct Asn1Value<Index>(Asn1ValueInternal<Index>)
where
    Index: Eq + Hash;

impl<Index: Eq + Hash> Asn1Value<Index> {
    /// Returns the total byte count of this value if statically known.
    fn known_len(&self) -> Option<usize> {
        match &self.0 {
            Asn1ValueInternal::Simple(raw) => raw.len(),
            Asn1ValueInternal::Recursive(spec, _) => spec.size(),
        }
    }

    /// Consumes the value and returns the extraction marker, if any.
    fn into_marker(self) -> Option<Index> {
        match self.0 {
            Asn1ValueInternal::Simple(raw) => raw.into_marker(),
            Asn1ValueInternal::Recursive(_, idx) => idx,
        }
    }
}

impl<Index> From<Asn1Spec<Index>> for Asn1Value<Index>
where
    Index: Eq + Hash,
{
    /// Interprets an [`Asn1Spec`] as a recursive value without a marker.
    fn from(value: Asn1Spec<Index>) -> Self {
        Asn1Value(Asn1ValueInternal::Recursive(value, None))
    }
}

impl<Index> Asn1Value<Index>
where
    Index: Eq + Hash + Debug,
{
    /// Constructs a constant sequence of data, interpreted as a value.
    pub fn fixed(data: &[u8]) -> Self {
        Asn1Value(Asn1ValueInternal::Simple(Asn1RawData::fixed(data)))
    }

    /// A sequence of unspecified raw bytes. `None` means variable length,
    /// `Some(len)` means fixed length. The `extract` flag controls whether
    /// the parsing circuit extracts the value (`true`) or only checks its
    /// length (`false`).
    pub fn any(len: Option<usize>) -> Self {
        Asn1Value(Asn1ValueInternal::Simple(Asn1RawData::any(len)))
    }

    /// Indicates that `self`'s extraction will be referenced as `m`.
    pub fn mark(self, m: Index) -> Self {
        match self.0 {
            Asn1ValueInternal::Simple(x) => Asn1Value(Asn1ValueInternal::Simple(x.mark(m))),
            Asn1ValueInternal::Recursive(s, None) => {
                Asn1Value(Asn1ValueInternal::Recursive(s, Some(m)))
            }
            Asn1ValueInternal::Recursive(_, Some(m2)) => double_mark(m, m2),
        }
    }
}

/// An ASN.1 spec: a complete ASN.1 encoding which may include several
/// blocks at the same level. The internal structure is opaque; use the
/// builder methods to construct instances as chains of instructions.
///
/// The spec caches the total byte count when all blocks have statically
/// known sizes, accessible via [`size`](`Self::size`).
#[derive(Debug, Clone)]
pub struct Asn1Spec<Index>(Option<usize>, Vec<Asn1Block<Index>>)
where
    Index: Eq + Hash;

impl<Index: Eq + Hash> Asn1Spec<Index> {
    /// Creates an empty specification.
    pub fn empty() -> Self {
        Self(Some(0), Vec::new())
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

    /// Validates that the `len` and `val` parts of a TLV spec are consistent:
    /// - If `len` is constant, its decoded value must match `val`'s known size.
    /// - If `val` has a known size, `len` should be constant for efficiency.
    ///
    /// `caller` is used in panic messages for diagnostics.
    fn check_tlv_spec_consistency(caller: &str, len: &Asn1RawData<Index>, val: &Asn1Value<Index>) {
        let val_known = val.known_len();
        match &len.0 {
            Asn1RawDataInternal::Const(len_bytes, _) => {
                let (_, decoded) = der_encoding::decode_length(len_bytes).unwrap_or_else(|| {
                    panic!("{caller}: constant length bytes are not valid DER")
                });
                match val_known {
                    None => panic!(
                        "{caller}: length is constant ({decoded} bytes) but value \
                         has unknown size. The spec is likely inconsistent."
                    ),
                    Some(n) if n != decoded => panic!(
                        "{caller}: constant length says {decoded} bytes but value \
                         has known size {n}. The spec is inconsistent."
                    ),
                    _ => {}
                }
            }
            Asn1RawDataInternal::Fixlen(..) | Asn1RawDataInternal::Varlen(_) => {
                if let Some(n) = val_known {
                    panic!(
                        "{caller}: value has known size ({n} bytes) but length is \
                         not specified as constant. Use a fixed length for better \
                         efficiency (you may compute it automatically via \
                         `Asn1Spec::size()`)."
                    );
                }
            }
        }
    }

    /// Adds an instruction reading a fixed sequence of bytes from the input.
    pub fn read_fixed(self, bytes: &[u8]) -> Self {
        self.add_block(Asn1Block::Const(bytes.to_vec(), None))
    }

    /// Adds an instruction reading `len` bytes from the input.
    pub fn read_bytes(self, len: usize) -> Self {
        self.add_block(Asn1Block::Fixlen(len, None))
    }

    /// Adds a TLV node to the spec. The caller is responsible for ensuring
    /// consistency between the variability of `tag`, `len`, and `val`.
    ///
    /// # Type conversions
    ///
    /// `tag`, `len`, and `val` accept several types via `Into`:
    ///
    ///    - `tag`: [`Tag`](der_encoding::Tag) (encoded via
    ///      [`encode_tag`](der_encoding::encode_tag)) or `&[u8]` (pre-encoded
    ///      raw tag bytes).
    ///
    ///   - `len`: `usize` (encoded via
    ///     [`encode_length`](der_encoding::encode_length), e.g., `88usize` ->
    ///     `[0x58]`) or `&[u8]` (pre-encoded raw length bytes).
    ///
    ///   - `val`: [`Asn1Value`] directly, or [`Asn1Spec`] for recursive
    ///     structures.
    pub fn read_tlv(
        self,
        tag: impl Into<Asn1RawData<Index>>,
        len: impl Into<Asn1RawData<Index>>,
        val: impl Into<Asn1Value<Index>>,
    ) -> Self {
        let tag = tag.into();
        let len = len.into();
        let val = val.into();

        Self::check_tlv_spec_consistency("read_tlv", &len, &val);
        self.add_block(Asn1Block::Tlv(Asn1Tlv { tag, len, val }, None))
    }

    /// Adds an optional TLV node to the spec. When the witness starts with
    /// `tag` the full T+L+V is consumed; otherwise nothing is consumed and
    /// all three ScannerVecs are empty (len=0).
    ///
    /// # Limitations
    ///
    /// - The value must be `Simple` (non-recursive). Recursive optional
    ///   values are not supported.
    pub fn read_tlv_optional(
        self,
        tag: &[u8],
        len: impl Into<Asn1RawData<Index>>,
        val: impl Into<Asn1Value<Index>>,
    ) -> Self {
        let len = len.into();
        let val = val.into();
        assert!(
            matches!(val.0, Asn1ValueInternal::Simple(_)),
            "read_tlv_optional: recursive values are not supported for optional TLV fields"
        );
        Self::check_tlv_spec_consistency("read_tlv_optional", &len, &val);
        self.add_block(Asn1Block::OptionalTlv {
            expected_tag: tag.to_vec(),
            len,
            val,
        })
    }

    /// Adds another full spec after this one.
    pub fn then(self, spec: Asn1Spec<Index>) -> Self {
        self.add_many_block(spec.1)
    }

    /// Concatenates several specs in order.
    pub fn cat(items: Vec<Self>) -> Self {
        items.into_iter().fold(Self::empty(), |acc, spec| acc.then(spec))
    }

    // -------------------------------------------------------------------
    // Common ASN.1 structure helpers
    //
    // All take `self` and append to the current spec via `read_tlv` or
    // `read_fixed`, for uniform chaining.
    // -------------------------------------------------------------------

    /// Returns the appropriate length field for a value: a fixed
    /// `usize` if the value's byte count is known, or `Asn1RawData::any(None)`
    /// (varlen) otherwise.
    fn auto_len(val: &Asn1Value<Index>) -> Asn1RawData<Index> {
        match val.known_len() {
            Some(n) => n.into(),
            None => Asn1RawData::any(None),
        }
    }

    /// Appends a SEQUENCE TLV. Uses a fixed-length encoding when the
    /// value's byte count is statically known.
    pub fn read_sequence(self, val: impl Into<Asn1Value<Index>>) -> Self {
        let val = val.into();
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::SEQUENCE], len, val)
    }

    /// Appends a SET TLV. Uses a fixed-length encoding when the value's
    /// byte count is statically known.
    pub fn read_set(self, val: impl Into<Asn1Value<Index>>) -> Self {
        let val = val.into();
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::SET], len, val)
    }

    /// Appends an OCTET STRING TLV. Uses a fixed-length encoding when
    /// the value's byte count is statically known.
    pub fn read_octet_string(self, val: impl Into<Asn1Value<Index>>) -> Self {
        let val = val.into();
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::OCTET_STRING], len, val)
    }

    /// Appends a BIT STRING TLV. Uses a fixed-length encoding when the
    /// value's byte count is statically known.
    pub fn read_bit_string(self, val: impl Into<Asn1Value<Index>>) -> Self {
        let val = val.into();
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::BIT_STRING], len, val)
    }

    /// Appends an INTEGER TLV. Uses a fixed-length encoding when the
    /// value's byte count is statically known.
    pub fn read_integer(self, val: impl Into<Asn1Value<Index>>) -> Self {
        let val = val.into();
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::INTEGER], len, val)
    }

    /// Appends a context-specific constructed TLV (`[number] CONSTRUCTED`).
    /// Uses a fixed-length encoding when the value's byte count is
    /// statically known.
    pub fn read_ctx(self, number: u32, val: impl Into<Asn1Value<Index>>) -> Self {
        let val = val.into();
        let len = Self::auto_len(&val);
        let ctx_tag = der_encoding::Tag {
            class: der_encoding::class::CONTEXT_SPECIFIC,
            constructed: true,
            number,
        };
        self.read_tlv(ctx_tag, len, val)
    }

    /// Appends a complete DER-encoded OID as a fixed block.
    pub fn read_oid(self, components: &[u32]) -> Self {
        self.read_fixed(&der_encoding::oid(components))
    }

    /// Appends a fixed DER-encoded INTEGER value as a static block.
    /// For a variable-length INTEGER, use
    /// [`read_integer`](`Self::read_integer`).
    pub fn read_integer_fixed(self, n: i64) -> Self {
        self.read_fixed(&der_encoding::integer(n))
    }

    /// Appends an AlgorithmIdentifier SEQUENCE with explicit NULL
    /// parameters: `SEQUENCE { OID, NULL }`.
    ///
    /// Used for algorithms whose ASN.1 definition requires a NULL
    /// parameter field, such as SHA-256 (`2.16.840.1.101.3.4.2.1`) or
    /// RSA (`1.2.840.113549.1.1.1`).
    ///
    /// For algorithms with absent parameters (e.g., ECDSA), use
    /// [`read_algid`](`Self::read_algid`) instead.
    pub fn read_algid_null(self, oid_components: &[u32]) -> Self {
        self.read_fixed(&der_encoding::sequence(&[
            der_encoding::oid(oid_components),
            der_encoding::null(),
        ]))
    }

    /// Appends an AlgorithmIdentifier SEQUENCE with no parameters:
    /// `SEQUENCE { OID }`.
    ///
    /// Used for algorithms whose ASN.1 definition specifies absent
    /// (omitted) parameters, such as ECDSA-SHA256
    /// (`1.2.840.10045.4.3.2`).
    ///
    /// For algorithms that require an explicit NULL parameter (e.g.,
    /// SHA-256, RSA), use [`read_algid_null`](`Self::read_algid_null`)
    /// instead.
    pub fn read_algid(self, oid_components: &[u32]) -> Self {
        self.read_fixed(&der_encoding::sequence(&[der_encoding::oid(
            oid_components,
        )]))
    }

    /// Indicates that the last block of `self`'s extraction will be referenced
    /// as `m`.
    pub fn mark(mut self, m: Index) -> Self {
        let last_block =
            (self.1.last_mut()).unwrap_or_else(|| panic!("no block to mark with index {:?}", m));
        let slot = match last_block {
            Asn1Block::Const(_, idx) => idx,
            Asn1Block::Fixlen(_, idx) => idx,
            Asn1Block::Tlv(_, _) => panic!("extraction of full TLVs is not supported. Use `mark` either on the value, or on each T, L, and V components separately."),
            Asn1Block::OptionalTlv { .. } => panic!("extraction of full optional TLVs is not supported. Mark the length or value components individually."),
        };
        match slot.take() {
            None => *slot = Some(m),
            Some(m2) => double_mark(m, m2),
        }
        self
    }
}
