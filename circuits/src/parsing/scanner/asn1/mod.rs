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

    /// Returns the known size of this data block, or `None` for
    /// variable length blocks.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> Option<usize> {
        match &self.0 {
            Asn1RawDataInternal::Const(v, _) => Some(v.len()),
            Asn1RawDataInternal::Fixlen(n, _) => Some(*n),
            Asn1RawDataInternal::Varlen(_) => None,
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
#[derive(Debug, Clone)]
pub struct Asn1Spec<Index>(Vec<Asn1Block<Index>>)
where
    Index: Eq + Hash;

impl<Index> Asn1Spec<Index>
where
    Index: Eq + Hash + Debug,
{
    /// Adds several blocks to the spec.
    fn add_many_block(mut self, blocks: Vec<Asn1Block<Index>>) -> Self {
        self.0.extend(blocks);
        self
    }

    /// Adds 1 block to the spec.
    fn add_block(self, block: Asn1Block<Index>) -> Self {
        self.add_many_block(vec![block])
    }

    /// Creates an empty specification.
    pub fn init() -> Self {
        Self(vec![])
    }

    /// Instruction reading a fixed sequence of bytes from the input.
    pub fn read_static(self, bytes: &[u8]) -> Self {
        self.add_block(Asn1Block::Const(bytes.to_vec(), None))
    }

    /// Instruction reading `len` bytes from the input.
    pub fn read_bytes(self, len: usize) -> Self {
        self.add_block(Asn1Block::Fixlen(len, None))
    }

    /// Adds a TLV node to the spec. The caller is responsible for ensuring
    /// consistency between the variability of `tag`, `len`, and `val`. For
    /// recursion, i.e., when `val` is itself a sequence of TLV nodes, it
    /// suffices to instantiate it by an [`Asn1Spec`].
    pub fn read_tlv(
        self,
        tag: Asn1RawData<Index>,
        len: Asn1RawData<Index>,
        val: impl Into<Asn1Value<Index>>,
    ) -> Self {
        self.add_block(Asn1Block::Tlv(
            Asn1Tlv {
                tag,
                len,
                val: val.into(),
            },
            None,
        ))
    }

    /// Adds another full spec after this one.
    pub fn then(self, spec: Asn1Spec<Index>) -> Self {
        self.add_many_block(spec.0)
    }

    /// Concatenates several specs in order.
    pub fn cat(items: Vec<Self>) -> Self {
        items.into_iter().fold(Self::init(), |acc, spec| acc.then(spec))
    }

    /// Indicates that the last block of `self`'s extraction will be referenced
    /// as `m`.
    pub fn mark(mut self, m: Index) -> Self {
        let last_block =
            (self.0.last_mut()).unwrap_or_else(|| panic!("no block to mark with index {:?}", m));
        let slot = match last_block {
            Asn1Block::Const(_, idx) => idx,
            Asn1Block::Fixlen(_, idx) => idx,
            Asn1Block::Tlv(_, _) => panic!("extraction of full TLVs is not supported. Use `mark` either on the value, or on each T, L, and V components separately."),
        };
        match slot.take() {
            None => *slot = Some(m),
            Some(m2) => double_mark(m, m2),
        }
        self
    }
}
