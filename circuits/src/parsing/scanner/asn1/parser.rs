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

/// A position in an ASN.1 parsed input, represented as a sum of
/// variable-length assigned values plus a constant offset:
/// `position = sum(vars) + offset`.
#[derive(Debug, Clone)]
struct ParsingPosition<F: CircuitField> {
    vars: Vec<AssignedNative<F>>,
    offset: usize,
}

impl<F: CircuitField> From<usize> for ParsingPosition<F> {
    fn from(offset: usize) -> Self {
        Self {
            vars: Vec::new(),
            offset,
        }
    }
}

impl<F: CircuitField> From<AssignedNative<F>> for ParsingPosition<F> {
    fn from(value: AssignedNative<F>) -> Self {
        Self {
            vars: vec![value],
            offset: 0,
        }
    }
}

impl<F: CircuitField> ParsingPosition<F> {
    /// Advances the position by exactly `n` bytes.
    fn advance_exact(&mut self, n: usize) {
        self.offset += n;
    }

    /// Advances the position by a variable (circuit-assigned) length.
    fn advance_variable(&mut self, assigned_len: AssignedNative<F>) {
        self.vars.push(assigned_len);
    }

    /// Computes how much `self` has advanced compared to `prev`. Assumes
    /// that `prev.vars` is a prefix of `self.vars` (i.e., all variable
    /// advances since `prev` were pushed to `self`).
    fn diff(&self, prev: &Self) -> ParsingPosition<F> {
        assert!(self.vars.len() >= prev.vars.len(), "unexpected diff call");
        ParsingPosition {
            vars: self.vars[prev.vars.len()..].to_vec(),
            offset: self.offset - prev.offset,
        }
    }
}

// -----------------------------------------------------------------------
// Internal state
// -----------------------------------------------------------------------

/// Which TLV component a variable-length raw data block belongs to.
/// Determines which `Asn1ParsedUnit` variant to produce.
enum RawDataRole {
    Tag,
    Len,
}

/// Mutable state threaded through the ASN.1 parsing functions.
struct ParserState<
    F: CircuitField,
    Index: Eq + Hash,
    const TAG_M: usize,
    const LEN_M: usize,
    const VAL_M: usize,
    const VAL_A: usize,
> {
    /// Current parsing position (may be exact or variable).
    position: ParsingPosition<F>,
    /// Number of input bytes consumed so far (off-circuit position).
    real_position: usize,
    /// Extracted regions keyed by user-supplied index.
    extracted: HashMap<Index, Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>>,
    /// Deferred substring checks: (position, content) pairs to verify at the
    /// end against the full input.
    substring_checks: Vec<(
        ParsingPosition<F>,
        Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>,
    )>,
    /// Set to true when any variable-length block is encountered.
    varlen: bool,
}

impl<
        F: CircuitField,
        Index: Eq + Hash,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    > ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>
{
    fn new() -> Self {
        Self {
            position: ParsingPosition::from(0),
            real_position: 0,
            extracted: HashMap::new(),
            substring_checks: Vec::new(),
            varlen: false,
        }
    }

    /// Records an extraction and a substring check (possibly forced).
    /// Uses `self.position` as the substring check position.
    fn record(
        &mut self,
        index: Option<Index>,
        unit: Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>,
        force_substring_check: bool,
    ) {
        self.record_at(index, unit, force_substring_check, &self.position.clone());
    }

    /// Record an extraction with an explicit substring check position. The
    /// substring check is performed if `force_substring_check` is true, or if
    /// `index` is not None.
    ///
    /// This function is used instead of `record` when the current
    /// `self.position` has already advanced past the extraction.
    fn record_at(
        &mut self,
        index: Option<Index>,
        unit: Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>,
        force_substring_check: bool,
        position: &ParsingPosition<F>,
    ) {
        match index {
            None => {
                if force_substring_check {
                    self.substring_checks.push((position.clone(), unit.clone()))
                }
            }
            Some(idx) => {
                self.substring_checks.push((position.clone(), unit.clone()));
                self.extracted.insert(idx, unit);
            }
        }
    }
}

/// Consume `n` bytes from the front of `input`.
fn consume(input: &mut &[u8], n: usize) -> Vec<u8> {
    assert!(
        input.len() >= n,
        "ASN.1 parse: input too short (need {n}, have {})",
        input.len()
    );
    let (head, tail) = input.split_at(n);
    let bytes = head.to_vec();
    *input = tail;
    bytes
}

// -----------------------------------------------------------------------
// Circuit phase
// -----------------------------------------------------------------------

impl<F> ScannerChip<F>
where
    F: CircuitField + Ord + Hash,
{
    /// Convert a [`ParsingPosition`] to an [`AssignedNative`] for use as a
    /// substring check index.
    fn position_to_assigned(
        &self,
        layouter: &mut impl Layouter<F>,
        pos: &ParsingPosition<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let terms: Vec<_> = pos.vars.iter().map(|v| (F::ONE, v.clone())).collect();
        self.native_gadget
            .linear_combination(layouter, &terms, F::from(pos.offset as u64))
    }

    /// Asserts that two parsing positions are equal in circuit. Optimised
    /// for the common cases where one or both sides have no variable
    /// components.
    fn assert_equal_positions(
        &self,
        layouter: &mut impl Layouter<F>,
        p1: &ParsingPosition<F>,
        p2: &ParsingPosition<F>,
    ) -> Result<(), Error> {
        let terms1 = p1.vars.iter().map(|x| (F::ONE, x.clone()));
        let terms2 = p2.vars.iter().map(|x| (-F::ONE, x.clone()));
        let terms: Vec<_> = terms1.chain(terms2).collect();
        if terms.is_empty() {
            // Both fixed: compile-time check (free in-circuit).
            assert_eq!(p1.offset, p2.offset, "fixed positions are not equal");
            Ok(())
        } else if terms.len() == 1 {
            // Single variable: use assert_equal_to_fixed (1 row).
            let (coeff, var) = &terms[0];
            let fixed = if *coeff == F::ONE {
                F::from(p2.offset as u64) - F::from(p1.offset as u64)
            } else {
                F::from(p1.offset as u64) - F::from(p2.offset as u64)
            };
            self.native_gadget.assert_equal_to_fixed(layouter, var, fixed)
        } else {
            // General case: linear_combination + assert_zero (2 rows).
            let z = self.native_gadget.linear_combination(
                layouter,
                &terms,
                F::from(p1.offset as u64) - F::from(p2.offset as u64),
            )?;
            self.native_gadget.assert_zero(layouter, &z)
        }
    }

    /// Reads `v.len()` bytes as fixed constants. Asserts (off-circuit) that
    /// the witness matches `v`. Advances `state.real_position`. The caller is
    /// responsible for advancing `state.position`.
    fn read_const<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        input: &mut &[u8],
        v: &[u8],
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<(), Error> {
        let input_block = consume(input, v.len());
        assert_eq!(
            v, &input_block,
            "ASN.1 parsing error: expected {:?}, got {:?}",
            v, input_block
        );
        state.real_position += v.len();
        Ok(())
    }

    /// Assigns `n` bytes as unconstrained witness values. Advances
    /// `state.real_position`. The caller is responsible for advancing
    /// `state.position`.
    ///
    /// For soundness, these values however need to be subjected to a substring
    /// check, to constrain them to appear in the original credential. The
    /// caller is responsible that.
    fn assign_witness_fixlen<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &mut &[u8],
        n: usize,
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let input_block: Vec<_> = consume(input, n).into_iter().map(Value::known).collect();
        let assigned = self.native_gadget.assign_many(layouter, &input_block)?;
        state.real_position += n;
        Ok(assigned)
    }

    /// Similar to `assign_witness_fixlen`, but also performs dummy assignments
    /// so that it produces the same structure as a call with `n` = `max_n`.
    /// Returns the assigned values, including the dummies.
    fn assign_witness_varlen<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &mut &[u8],
        n: usize,
        max_n: usize,
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        assert!(n <= max_n, "variable length exceeding max capacity");
        let input_block: Vec<_> = (consume(input, n).into_iter().chain(repeat_n(0u8, max_n - n)))
            .map(Value::known)
            .collect();
        let assigned = self.native_gadget.assign_many(layouter, &input_block)?;
        state.real_position += n;
        Ok(assigned)
    }
}

    /// Validates and interprets a fixed-size raw data block based on its
    /// `role`. For `Tag`, validates the encoding and discards the result.
    /// For `Len`, validates and returns the decoded length value.
    fn automaton_validate_fixlen(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
        role: &RawDataRole,
    ) -> Result<Option<AssignedNative<F>>, Error> {
        match role {
            RawDataRole::Tag => {
                self.parse(
                    layouter,
                    AutomatonParser::Static(StdLibParser::Asn1DerTag),
                    bytes,
                )?;
                Ok(None)
            }
            RawDataRole::Len => {
                let length_value = self.parse_asn1_len(layouter, bytes)?;
                Ok(Some(length_value))
            }
        }
    }

    /// Validates a variable-length tag [`ScannerVec`] via the
    /// [`Asn1DerTag`](`StdLibParser::Asn1DerTag`) automaton.
    fn automaton_validate_varlen_tag<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        sv: &ScannerVec<F, M, 1>,
    ) -> Result<(), Error> {
        self.parse_varlen(
            layouter,
            AutomatonParser::Static(StdLibParser::Asn1DerTag),
            sv,
        )?;
        Ok(())
    }

    /// Validates and interprets a variable-length length [`ScannerVec`].
    /// Returns the circuit-decoded length value.
    fn automaton_validate_varlen_len<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        sv: &ScannerVec<F, M, 1>,
    ) -> Result<AssignedNative<F>, Error> {
        self.parse_asn1_len_varlen(layouter, sv)
    }

    /// Assigns raw bytes and records an extraction at the given position.
    /// If `is_varlen`, the extraction produces a `VarlenVal` (ScannerVec);
    /// otherwise it produces a `Fixlen` (assigned bytes).
    fn extract_and_record<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        raw: &[u8],
        is_varlen: bool,
        index: Index,
        position: &ParsingPosition<F>,
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<(), Error> {
        if is_varlen {
            let sv: ScannerVec<F, VAL_M, VAL_A> =
                self.assign_scanner_vec(layouter, Value::known(raw.to_vec()))?;
            state.record_at(Some(index), Asn1ParsedUnit::VarlenVal(sv), false, position);
        } else {
            let values: Vec<_> = raw.iter().map(|&b| Value::known(b)).collect();
            let bytes = self.native_gadget.assign_many(layouter, &values)?;
            state.record_at(Some(index), Asn1ParsedUnit::Fixlen(bytes), false, position);
        }
        Ok(())
    }

    /// Computes the off-circuit tag identity value that the `Asn1DerTag`
    /// automaton would produce for `tag_bytes`:
    /// - Short form: the full first byte (class + constructed + number).
    /// - Long form: `decode_tag().number` (base-128 of continuation bytes).
    fn compute_tag_identity(tag_bytes: &[u8]) -> u64 {
        let (_, tag) = decode_tag(tag_bytes).expect("compute_tag_identity: invalid DER tag");
        if tag_bytes[0] & 0x1F != 0x1F {
            tag_bytes[0] as u64
        } else {
            tag.number as u64
    /// Performs deferred substring checks for a fixed-length input.
    fn do_fixlen_substring_checks<
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned_input: &[AssignedByte<F>],
        checks: Vec<(
            ParsingPosition<F>,
            Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>,
        )>,
    ) -> Result<(), Error> {
        for (pos, unit) in checks {
            match (unit, pos) {
                (Asn1ParsedUnit::Const(bytes), pos) if pos.vars.is_empty() => {
                    let start = pos.offset;
                    assert!(
                        start + bytes.len() <= assigned_input.len(),
                        "parse_asn1_fixlen did not enforce lengths constraints properly"
                    );
                    for (x, c) in assigned_input[start..].iter().zip(bytes.iter()) {
                        self.native_gadget.assert_equal_to_fixed(layouter, x, *c)?
                    }
                }
                (Asn1ParsedUnit::Fixlen(bytes), pos) if pos.vars.is_empty() => {
                    let start = pos.offset;
                    let end = pos.offset + bytes.len();
                    assert!(
                        end <= assigned_input.len(),
                        "parse_asn1_fixlen did not enforce lengths constraints properly"
                    );
                    self.assert_equal_fixlen(layouter, &bytes, &assigned_input[start..end])?;
                }
                _ => unreachable!("unexpected varlen unit in fixed-length input"),
            }
        }
        Ok(())
    }

    /// Performs deferred substring checks for a variable-length input.
    fn do_varlen_substring_checks<
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
        const M: usize,
        const A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        input_vec: &ScannerVec<F, M, A>,
        checks: Vec<(
            ParsingPosition<F>,
            Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>,
        )>,
    ) -> Result<(), Error> {
        for (pos, unit) in checks {
            let idx = self.position_to_assigned(layouter, &pos)?;
            match unit {
                Asn1ParsedUnit::Const(bytes) => {
                    let assigned = self.native_gadget.assign_many_fixed(layouter, &bytes)?;
                    self.check_bytes_varlen_partial(layouter, input_vec, &idx, &assigned)?
                }
                Asn1ParsedUnit::Fixlen(bytes) => {
                    self.check_bytes_varlen_partial(layouter, input_vec, &idx, &bytes)?
                }
                Asn1ParsedUnit::VarlenTag(sv) => {
                    self.check_bytes_varlen(layouter, input_vec, &idx, &sv)?
                }
                Asn1ParsedUnit::VarlenLen(sv) => {
                    self.check_bytes_varlen(layouter, input_vec, &idx, &sv)?
                }
                Asn1ParsedUnit::VarlenVal(sv) => {
                    self.check_bytes_varlen(layouter, input_vec, &idx, &sv)?
                }
            }
        }
        Ok(())
    }
}
