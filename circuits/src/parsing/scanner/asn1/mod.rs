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
        Asn1RawData::bytes_const(&der_encoding::encode_length(len))
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

impl<Index: Eq + Hash> Asn1Spec<Index> {
    /// Creates an empty specification.
    pub fn new() -> Self {
        Self(Some(0), Vec::new(), None)
    }

    /// Creates an empty specification (alias for [`new`](`Self::new`)).
    pub fn empty() -> Self {
        Self::new()
    }

    /// Returns the total byte count if all blocks have statically known
    /// sizes, or `None` otherwise.
    pub fn size(&self) -> Option<usize> {
        self.0
    }

    /// Consumes the spec and separates the full marker from the blocks.
    fn strip_full_marker(self) -> (Self, Option<Index>) {
        let marker = self.2;
        (Asn1Spec(self.0, self.1, None), marker)
    }

    /// Extracts a marker from a simple (single-block or full-marker) spec.
    /// Used by [`OptionalTlv`](`Asn1Block::OptionalTlv`) to retrieve the
    /// value extraction index.
    fn into_single_block_marker(self) -> Option<Index> {
        if self.2.is_some() {
            return self.2;
        }
        if self.1.len() == 1 {
            match self.1.into_iter().next().unwrap() {
                Asn1Block::Const(_, idx) | Asn1Block::Fixlen(_, idx) | Asn1Block::Varlen(idx) => {
                    idx
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Returns `true` if the last block is a `Varlen`.
    fn ends_with_varlen(&self) -> bool {
        matches!(self.1.last(), Some(Asn1Block::Varlen(_)))
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

    /// Validates that the `len` and `val` parts of a TLV spec are consistent:
    /// - If `len` is constant, its decoded value must match `val`'s known size.
    /// - If `val` has a known size, `len` should be constant for efficiency.
    ///
    /// `caller` is used in panic messages for diagnostics.
    fn check_tlv_spec_consistency(caller: &str, len: &Asn1RawData<Index>, val: &Asn1Spec<Index>) {
        let val_known = val.size();
        match &len.0 {
            Asn1RawDataInternal::Const(len_bytes, _) => {
                let (_, decoded) = der_encoding::decode_length(len_bytes)
                    .unwrap_or_else(|| panic!("{caller}: constant length bytes are not valid DER"));
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
    ///   - `len`: `usize` (encoded via
    ///     [`encode_length`](der_encoding::encode_length), e.g., `88usize` ->
    ///     `[0x58]`) or `&[u8]` (pre-encoded raw length bytes).
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
        items.into_iter().fold(Self::empty(), |acc, spec| acc.then(spec))
    }

    // -------------------------------------------------------------------
    // Common ASN.1 structure helpers
    //
    // All take `self` and append to the current spec via `read_tlv` or
    // `read_bytes_const`, for uniform chaining.
    // -------------------------------------------------------------------

    /// Returns the appropriate length field for a value: a fixed
    /// `usize` if the value's byte count is known, or `Asn1RawData::any(None)`
    /// (varlen) otherwise.
    fn auto_len(val: &Asn1Spec<Index>) -> Asn1RawData<Index> {
        match val.size() {
            Some(n) => n.into(),
            None => Asn1RawData::any(None),
        }
    }

    /// Appends a SEQUENCE TLV. The length is automatically derived
    /// from `val`: when `val.size()` is known, the tag and length are
    /// encoded as constants (cheap T+L); otherwise the length is
    /// parsed at variable-length cost.
    pub fn read_sequence(self, val: Asn1Spec<Index>) -> Self {
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::SEQUENCE], len, val)
    }

    /// Appends a SET TLV. The length is automatically derived from
    /// `val`: when `val.size()` is known, the tag and length are
    /// encoded as constants (cheap T+L); otherwise the length is
    /// parsed at variable-length cost.
    pub fn read_set(self, val: Asn1Spec<Index>) -> Self {
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::SET], len, val)
    }

    /// Appends an OCTET STRING TLV. The length is automatically derived
    /// from `val`: when `val.size()` is known, the tag and length are
    /// encoded as constants (cheap T+L); otherwise the length is
    /// parsed at variable-length cost.
    pub fn read_octet_string(self, val: Asn1Spec<Index>) -> Self {
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::OCTET_STRING], len, val)
    }

    /// Appends a BIT STRING TLV. The length is automatically derived
    /// from `val`: when `val.size()` is known, the tag and length are
    /// encoded as constants (cheap T+L); otherwise the length is
    /// parsed at variable-length cost.
    pub fn read_bit_string(self, val: Asn1Spec<Index>) -> Self {
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::BIT_STRING], len, val)
    }

    /// Appends an INTEGER TLV with unknown value. The length is
    /// automatically derived from `val`: when `val.size()` is known,
    /// the tag and length are encoded as constants (cheap T+L);
    /// otherwise the length is parsed at variable-length cost.
    ///
    /// For an INTEGER with a known value, use
    /// [`read_integer_const`](`Self::read_integer_const`).
    pub fn read_integer(self, val: Asn1Spec<Index>) -> Self {
        let len = Self::auto_len(&val);
        self.read_tlv(&[der_encoding::tag::INTEGER], len, val)
    }

    /// Appends a context-specific constructed TLV (`[number] CONSTRUCTED`).
    /// The length is automatically derived from `val`: when
    /// `val.size()` is known, the tag and length are encoded as
    /// constants (cheap T+L); otherwise the length is parsed at
    /// variable cost.
    pub fn read_ctx(self, number: u32, val: Asn1Spec<Index>) -> Self {
        let len = Self::auto_len(&val);
        let ctx_tag = der_encoding::Tag {
            class: der_encoding::class::CONTEXT_SPECIFIC,
            constructed: true,
            number,
        };
        self.read_tlv(ctx_tag, len, val)
    }

    /// Appends a complete DER-encoded OID as a constant block. The
    /// encoding is computed via [`der_encoding::oid`].
    pub fn read_oid(self, components: &[u32]) -> Self {
        self.read_bytes_const(&der_encoding::oid(components))
    }

    /// Appends a DER-encoded INTEGER with a known value as a constant
    /// block. The encoding is computed via [`der_encoding::integer`].
    ///
    /// For an INTEGER with unknown value, use
    /// [`read_integer`](`Self::read_integer`).
    pub fn read_integer_const(self, n: i64) -> Self {
        self.read_bytes_const(&der_encoding::integer(n))
    }

    /// Appends an AlgorithmIdentifier SEQUENCE with explicit NULL
    /// parameters: `SEQUENCE { OID, NULL }`. The entire TLV is
    /// encoded as a single constant block. The encoding is built from
    /// [`der_encoding`] helpers (`sequence`, `oid`, `null`).
    ///
    /// Used for algorithms whose ASN.1 definition requires a NULL
    /// parameter field, such as SHA-256 (`2.16.840.1.101.3.4.2.1`) or
    /// RSA (`1.2.840.113549.1.1.1`).
    ///
    /// For algorithms with absent parameters (e.g., ECDSA), use
    /// [`read_algid`](`Self::read_algid`) instead.
    pub fn read_algid_null(self, oid_components: &[u32]) -> Self {
        self.read_bytes_const(&der_encoding::sequence(&[
            der_encoding::oid(oid_components),
            der_encoding::null(),
        ]))
    }

    /// Appends an AlgorithmIdentifier SEQUENCE with no parameters:
    /// `SEQUENCE { OID }`. The entire TLV is encoded as a single
    /// constant block. The encoding is built from [`der_encoding`]
    /// helpers (`sequence`, `oid`).
    ///
    /// Used for algorithms whose ASN.1 definition specifies absent
    /// (omitted) parameters, such as ECDSA-SHA256
    /// (`1.2.840.10045.4.3.2`).
    ///
    /// For algorithms that require an explicit NULL parameter (e.g.,
    /// SHA-256, RSA), use [`read_algid_null`](`Self::read_algid_null`)
    /// instead.
    pub fn read_algid(self, oid_components: &[u32]) -> Self {
        self.read_bytes_const(&der_encoding::sequence(&[der_encoding::oid(
            oid_components,
        )]))
    }

    /// Marks the last block of this spec for extraction as `m`.
    ///
    /// For `Const` and `Fixlen` blocks, the block's bytes are extracted.
    /// For `Tlv` blocks, the full T+L+V bytes are extracted.
    /// For `Varlen` (trail) blocks, the trail bytes are extracted.
    ///
    /// # Cost
    ///
    /// Extraction is free for constant blocks. For fixed-length witness
    /// blocks it adds a moderate cost (proof of the validity of the
    /// extract). For variable-length or Tlv blocks, this extra cost is
    /// higher due to the management of variable-length extractions.
    ///
    /// # Panics
    ///
    /// - If the spec has no blocks.
    /// - If the last block is `OptionalTlv` (mark components individually).
    /// - If the last block already has a marker.
    pub fn mark_last(mut self, m: Index) -> Self {
        let last_block =
            (self.1.last_mut()).unwrap_or_else(|| panic!("no block to mark with index {:?}", m));
        let slot = match last_block {
            Asn1Block::Const(_, idx) => idx,
            Asn1Block::Fixlen(_, idx) => idx,
            Asn1Block::Tlv(_, idx) => idx,
            Asn1Block::OptionalTlv { .. } => panic!(
                "extraction of full optional TLVs is not supported. \
                 Mark the length or value components individually."
            ),
            Asn1Block::Varlen(idx) => idx,
        };
        match slot.take() {
            None => *slot = Some(m),
            Some(m2) => double_mark(m, m2),
        }
        self
    }

    /// Marks the entire spec for full extraction as `m`. All bytes
    /// produced by this spec's blocks will be extracted under this index.
    ///
    /// Primarily used for V-only extraction when the spec serves as a
    /// TLV's value.
    ///
    /// # Cost
    ///
    /// Adds a moderate cost for fixed-length specs (proof of the
    /// validity of the extract). For specs containing variable-length
    /// blocks, this extra cost is higher due to the management of
    /// variable-length extractions.
    ///
    /// # Panics
    ///
    /// If a full marker is already set.
    pub fn mark_full(mut self, m: Index) -> Self {
        match self.2.take() {
            None => self.2 = Some(m),
            Some(m2) => double_mark(m, m2),
        }
        self
    }

    /// Appends a trail block: consumes all remaining bytes in the
    /// enclosing TLV value without extraction. Variable-length.
    ///
    /// Can only appear as the last block (panics if further blocks are
    /// added after it). At parse time, panics if no enclosing TLV
    /// provides a byte count. Use `.read_trail().mark_last(m)` to
    /// extract the trail bytes.
    pub fn read_trail(self) -> Self {
        self.add_block(Asn1Block::Varlen(None))
    }
}
