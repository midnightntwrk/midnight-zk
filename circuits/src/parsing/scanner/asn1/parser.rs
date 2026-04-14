use std::{collections::HashMap, fmt::Debug, hash::Hash, iter::repeat_n};

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use super::{
    der_encoding::{decode_length, decode_tag},
    Asn1Block, Asn1RawData, Asn1RawDataInternal, Asn1Spec, Asn1Tlv,
};
use crate::{
    field::AssignedNative,
    instructions::{
        arithmetic::ArithInstructions, assertions::AssertionInstructions,
        assignments::AssignmentInstructions, control_flow::ControlFlowInstructions,
        equality::EqualityInstructions, RangeCheckInstructions, ZeroInstructions,
    },
    parsing::scanner::{varlen::ScannerVec, AutomatonParser, ScannerChip, StdLibParser},
    types::{AssignedByte, InnerValue},
    CircuitField,
};

/// A unit of data extracted during ASN.1 parsing. The const parameters
/// control the sizing of variable-length vectors:
///
/// - `TAG_M`: maximal byte length of a variable-length tag.
/// - `LEN_M`: maximal byte length of a variable-length length field.
/// - `VAL_M`: maximal byte length of a variable-length value.
/// - `VAL_A`: chunk size for variable-length values. Tags and lengths always
///   use chunk size 1.
///
/// Keep in mind that optional fields are always inherently variable-length.
///
/// If the tags (resp. length, values) are always fixed-length, these
/// corresponding parameters are unused and can be set to any value
/// (recommended: 0, which will trigger some safety checks in case of an
/// oversight).
#[derive(Debug, Clone)]
enum Asn1ParsedUnit<
    F: CircuitField,
    const TAG_M: usize,
    const LEN_M: usize,
    const VAL_M: usize,
    const VAL_A: usize,
> {
    Const(Vec<u8>),
    Fixlen(Vec<AssignedByte<F>>),
    VarlenTag(ScannerVec<F, TAG_M, 1>),
    VarlenLen(ScannerVec<F, LEN_M, 1>),
    VarlenVal(ScannerVec<F, VAL_M, VAL_A>),
}

/// Result of [`ScannerChip::parse_asn1_fixlen`]. Wraps the full assigned
/// witness and the extracted regions.
#[derive(Debug, Clone)]
pub struct Asn1FixlenResult<F: CircuitField, Index: Eq + Hash> {
    full_witness: Vec<AssignedByte<F>>,
    extracted: HashMap<Index, Asn1ParsedUnit<F, 0, 0, 0, 0>>,
}

impl<F: CircuitField, Index: Eq + Hash + Debug> Asn1FixlenResult<F, Index> {
    /// Returns the full assigned and constrained witness.
    pub fn witness(&self) -> &[AssignedByte<F>] {
        &self.full_witness
    }

    /// Returns the extracted unit for the given index.
    pub fn get(&self, index: &Index) -> &[AssignedByte<F>] {
        let extr = self
            .extracted
            .get(index)
            .unwrap_or_else(|| panic!("no extraction for index {:?}", index));
        if let Asn1ParsedUnit::Fixlen(v) = extr {
            v.as_slice()
        } else {
            panic!("[parse_asn1_fixlen] should have filtered out const and varlen extractors")
        }
    }
}

/// Result of [`ScannerChip::parse_asn1_varlen`]. Wraps the full assigned
/// witness (as a [`ScannerVec`]) and the extracted regions.
#[derive(Debug, Clone)]
pub struct Asn1VarlenResult<
    F: CircuitField,
    Index: Eq + Hash,
    const TAG_M: usize,
    const LEN_M: usize,
    const VAL_M: usize,
    const VAL_A: usize,
    const M: usize,
    const A: usize,
> {
    full_witness: ScannerVec<F, M, A>,
    extracted: HashMap<Index, Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>>,
}

impl<
        F: CircuitField,
        Index: Eq + Hash + Debug,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
        const M: usize,
        const A: usize,
    > Asn1VarlenResult<F, Index, TAG_M, LEN_M, VAL_M, VAL_A, M, A>
{
    /// Returns the full assigned and constrained witness.
    pub fn witness(&self) -> &ScannerVec<F, M, A> {
        &self.full_witness
    }

    /// Returns a fixed-length extracted region as a byte slice.
    /// Panics if the index is missing or the extraction is not fixed-length.
    pub fn get_fixlen(&self, index: &Index) -> &[AssignedByte<F>] {
        match self.extracted.get(index) {
            Some(Asn1ParsedUnit::Fixlen(v)) => v.as_slice(),
            Some(Asn1ParsedUnit::Const(_)) => {
                unreachable!(
                    "{:?} points to a constant (`mark` should have avoided that)",
                    index
                )
            }
            Some(_) => panic!("extraction {:?} is not Fixlen", index),
            None => panic!("no extraction for index {:?}", index),
        }
    }

    /// Returns an extracted Tag (T of a TLV) as a variable-length
    /// [`ScannerVec`]. Panics if the index is missing or the extraction
    /// is not a varlen tag.
    pub fn get_varlen_tag(&self, index: &Index) -> &ScannerVec<F, TAG_M, 1> {
        match self.extracted.get(index) {
            Some(Asn1ParsedUnit::VarlenTag(sv)) => sv,
            Some(_) => panic!("extraction {:?} is not VarlenTag", index),
            None => panic!("no extraction for index {:?}", index),
        }
    }

    /// Returns an extracted Length (L of a TLV) as a variable-length
    /// [`ScannerVec`]. Panics if the index is missing or the extraction
    /// is not a varlen length.
    pub fn get_varlen_len(&self, index: &Index) -> &ScannerVec<F, LEN_M, 1> {
        match self.extracted.get(index) {
            Some(Asn1ParsedUnit::VarlenLen(sv)) => sv,
            Some(_) => panic!("extraction {:?} is not VarlenLen", index),
            None => panic!("no extraction for index {:?}", index),
        }
    }

    /// Returns an extracted Value (V of a TLV) as a variable-length
    /// [`ScannerVec`]. Panics if the index is missing or the extraction
    /// is not a varlen value.
    pub fn get_varlen_val(&self, index: &Index) -> &ScannerVec<F, VAL_M, VAL_A> {
        match self.extracted.get(index) {
            Some(Asn1ParsedUnit::VarlenVal(sv)) => sv,
            Some(_) => panic!("extraction {:?} is not VarlenVal", index),
            None => panic!("no extraction for index {:?}", index),
        }
    }
}

