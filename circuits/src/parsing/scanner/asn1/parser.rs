use std::{collections::HashMap, fmt::Debug, hash::Hash};

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
        equality::EqualityInstructions, ZeroInstructions,
    },
    parsing::scanner::{varlen::ScannerVec, AutomatonParser, ScannerChip, StdLibParser},
    types::AssignedByte,
    CircuitField,
};

// -----------------------------------------------------------------------
// Public types
// -----------------------------------------------------------------------

/// A unit of data extracted during ASN.1 parsing. The const parameters
/// control the sizing of variable-length vectors:
/// - `TAG_M`: maximal byte length of a variable-length tag.
/// - `LEN_M`: maximal byte length of a variable-length length field.
/// - `VAL_M`: maximal byte length of a variable-length value.
/// - `VAL_A`: chunk size for variable-length values. Tags and lengths always
///   use chunk size 1.
///
/// If the tags (resp. length, values) are always fixed-length, these
/// corresponding parameters are unused and can be set to any value.
#[derive(Debug, Clone)]
enum Asn1ParsedUnit<
    F: CircuitField,
    const TAG_M: usize,
    const LEN_M: usize,
    const VAL_M: usize,
    const VAL_A: usize,
> {
    // A block of bytes of fixed length.
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
            panic!("[parse_asn1_fixlen] should have filtered out varlen extractors")
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
    /// Bytes assigned so far, in order.
    assigned_input: Vec<AssignedByte<F>>,
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
            assigned_input: Vec::new(),
            extracted: HashMap::new(),
            substring_checks: Vec::new(),
            varlen: false,
        }
    }

    /// Record an extraction and (for non-const data) a substring check.
    /// Uses `self.position` as the substring check position.
    fn record(
        &mut self,
        index: Option<Index>,
        unit: Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>,
        needs_substring_check: bool,
    ) {
        self.record_at(index, unit, needs_substring_check, &self.position.clone());
    }

    /// Record an extraction with an explicit substring check position.
    /// Used when the current `self.position` has already advanced past
    /// the extraction (e.g., full_marker / tlv_marker in `process_tlv`).
    fn record_at(
        &mut self,
        index: Option<Index>,
        unit: Asn1ParsedUnit<F, TAG_M, LEN_M, VAL_M, VAL_A>,
        needs_substring_check: bool,
        position: &ParsingPosition<F>,
    ) {
        if let Some(idx) = index {
            if needs_substring_check {
                self.substring_checks.push((position.clone(), unit.clone()));
            }
            self.extracted.insert(idx, unit);
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

    /// Assigns `v.len()` bytes as fixed constants. Asserts (off-circuit) that
    /// the witness matches `v`. Adds the assigned constants to
    /// `state.assigned_input`. The caller is responsible for advancing
    /// `state.position`.
    fn assign_const<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &mut &[u8],
        v: &[u8],
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let input_block = consume(input, v.len());
        assert_eq!(
            v,
            &input_block[..],
            "ASN.1 parsing error: expected {:?}, got {:?}",
            v,
            input_block
        );
        let assigned = self.native_gadget.assign_many_fixed(layouter, v)?;
        state.assigned_input.extend_from_slice(&assigned);
        Ok(assigned)
    }

    /// Assigns `n` bytes as unconstrained witness values. Adds the assigned
    /// values to `state.assigned_input`. The caller is responsible for
    /// advancing `state.position`.
    /// For soundness, these values however need to be subjected to a substring
    /// check, to constrain them to appear in the original credential. The
    /// caller is responsible that.
    fn assign_witness<
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
        state.assigned_input.extend_from_slice(&assigned);
        Ok(assigned)
    }
}

impl<F> ScannerChip<F>
where
    F: CircuitField + Ord + Hash,
{
    /// Parses a fully fixed-length witness according to a spec. The assigned
    /// and constrained data can be recovered using `Asn1FixlenResult`
    /// associated functions.
    ///
    /// When `input` is `Value::unknown()` (e.g., during keygen), a dummy
    /// byte sequence derived from the spec is used so the circuit
    /// structure is built correctly without a real witness.
    ///
    /// # Panics
    ///
    /// If the spec contains any variable-length blocks (use
    /// [`parse_asn1_varlen`](`Self::parse_asn1_varlen`) instead).
    pub fn parse_asn1_fixlen<Index: Eq + Hash + Debug + Clone>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: Value<Vec<u8>>,
        spec: Asn1Spec<Index>,
    ) -> Result<Asn1FixlenResult<F, Index>, Error> {
        // Getting an explicit input as it greatly simplifies the handling of
        // context-dependent parsing. Since `spec` only contains fixed-length blocks,
        // the generated circuit will always have the same structure.
        let mut input: &[u8] = &spec.get_explicit_input(input);

        // Main call to generate the parsing circuit.
        let mut state = ParserState::<F, Index, 0, 0, 0, 0>::new();
        spec.no_full_marker();
        self.process_blocks(layouter, &mut input, spec, None, &mut state)?;
        assert!(
            !state.varlen,
            "parse_asn1_fixlen: spec cannot contain variable-length blocks. You must call \
            parse_asn1_varlen instead."
        );

        self.assert_equal_positions(
            layouter,
            &state.position,
            &ParsingPosition::from(state.assigned_input.len()),
        )?;
        self.do_fixlen_substring_checks::<0, 0, 0, 0>(
            layouter,
            &state.assigned_input,
            state.substring_checks,
        )?;
        Ok(Asn1FixlenResult {
            full_witness: state.assigned_input,
            extracted: state.extracted,
        })
    }

    /// Parses a witness that may contain variable-length blocks. The assigned
    /// and constrained data can be recovered using `Asn1VarlenResult`
    /// associated functions. The different const parameters stand for (put
    /// an arbitrary value if not applicable):
    ///
    /// - `TAG_M`: maximal length of a variable-length Tag unit in TLV blocks.
    /// - `LEN_M`: maximal length of a variable-length Length unit in TLV
    ///   blocks.
    /// - `VAL_M`: maximal length of a variable-length Value unit in TLV blocks.
    /// - `VAL_A`: `AssignedVector` alignment for variable-length Value units in
    ///   TLV blocks.
    /// - `M`: maximal length of `input`.
    /// - `A`: `AssignedVector` alignment for `input`.
    ///
    /// # Panics
    ///
    /// If the spec contains no variable-length blocks (use
    /// [`parse_asn1_fixlen`](`Self::parse_asn1_fixlen`) instead).
    /// Parses a witness that may contain variable-length blocks. The assigned
    /// and constrained data can be recovered using `Asn1VarlenResult`
    /// associated functions. The different const parameters stand for (put
    /// an arbitrary value if not applicable):
    ///
    /// - `TAG_M`: maximal length of a variable-length Tag unit in TLV blocks.
    /// - `LEN_M`: maximal length of a variable-length Length unit in TLV
    ///   blocks.
    /// - `VAL_M`: maximal length of a variable-length Value unit in TLV blocks.
    /// - `VAL_A`: `AssignedVector` alignment for variable-length Value units in
    ///   TLV blocks.
    /// - `M`: maximal length of `input`.
    /// - `A`: `AssignedVector` alignment for `input`.
    ///
    /// When `input` is `Value::unknown()` (e.g., during keygen), a dummy
    /// byte sequence derived from the spec is used so the circuit
    /// structure is built correctly without a real witness.
    ///
    /// # Panics
    ///
    /// If the spec contains no variable-length blocks (use
    /// [`parse_asn1_fixlen`](`Self::parse_asn1_fixlen`) instead).
    pub fn parse_asn1_varlen<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
        const M: usize,
        const A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        input: Value<Vec<u8>>,
        spec: Asn1Spec<Index>,
    ) -> Result<Asn1VarlenResult<F, Index, TAG_M, LEN_M, VAL_M, VAL_A, M, A>, Error> {
        // Getting an explicit input as it greatly simplifies the handling of
        // context-dependent parsing. The code below ensures that the same circuit
        // structure is produced regardless of the variable-length parts of `spec`.
        let mut input: &[u8] = &spec.get_explicit_input(input);

        let mut state = ParserState::<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>::new();
        spec.no_full_marker();
        self.process_blocks(layouter, &mut input, spec, None, &mut state)?;
        assert!(
            state.varlen,
            "parse_asn1_varlen: spec contains no variable-length blocks. Call the cheaper \
            parse_asn1_fixlen instead."
        );

        let input_vec: ScannerVec<F, M, A> =
            self.scanner_vec_from_assigned(layouter, &state.assigned_input)?;
        let pos_assigned = self.position_to_assigned(layouter, &state.position)?;
        self.native_gadget.assert_equal(layouter, &pos_assigned, input_vec.len())?;
        self.do_varlen_substring_checks::<TAG_M, LEN_M, VAL_M, VAL_A, M, A>(
            layouter,
            &input_vec,
            state.substring_checks,
        )?;
        Ok(Asn1VarlenResult {
            full_witness: input_vec,
            extracted: state.extracted,
        })
    }

    /// Processes the blocks of an [`Asn1Spec`], updating `state`.
    ///
    /// `remaining` is the off-circuit byte count of the enclosing TLV's
    /// value region, or `None` if this is a top-level call. It is required
    /// for `Varlen` (trail) blocks to compute the trail length.
    fn process_blocks<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &mut &[u8],
        spec: Asn1Spec<Index>,
        remaining: Option<usize>,
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<(), Error> {
        let cursor_at_start = state.assigned_input.len();
        let mut blocks = spec.1;
        blocks.reverse();
        while let Some(block) = blocks.pop() {
            match block {
                Asn1Block::Const(v, index) => {
                    let bytes = self.assign_const(layouter, input, &v, state)?;
                    state.record(index, Asn1ParsedUnit::Fixlen(bytes), false);
                    state.position.advance_exact(v.len());
                }
                Asn1Block::Fixlen(n, index) => {
                    let bytes = self.assign_witness(layouter, input, n, state)?;
                    state.record(index, Asn1ParsedUnit::Fixlen(bytes), true);
                    state.position.advance_exact(n);
                }
                Asn1Block::Tlv(tlv, tlv_marker) => {
                    self.process_tlv(layouter, input, tlv, tlv_marker, state)?;
                }
                Asn1Block::OptionalTlv {
                    expected_tag,
                    len,
                    val,
                } => {
                    self.process_optional_tlv(layouter, input, &expected_tag, len, val, state)?;
                }
                Asn1Block::Varlen(index) => {
                    let remaining = remaining.expect(
                        "Varlen (trail) block at top level: trail blocks can only \
                         appear inside a TLV value",
                    );
                    state.varlen = true;
                    let bytes_consumed = state.assigned_input.len() - cursor_at_start;
                    let trail_len = remaining - bytes_consumed;

                    if let Some(trail_idx) = index {
                        // Indexed trail: assign bytes, create ScannerVec, substring check.
                        let trail_raw = consume(input, trail_len);
                        let trail_values: Vec<_> =
                            trail_raw.iter().map(|&b| Value::known(b)).collect();
                        let assigned = self.native_gadget.assign_many(layouter, &trail_values)?;
                        state.assigned_input.extend_from_slice(&assigned);

                        let sv: ScannerVec<F, VAL_M, VAL_A> =
                            self.assign_scanner_vec(layouter, Value::known(trail_raw))?;
                        state.substring_checks.push((
                            state.position.clone(),
                            Asn1ParsedUnit::VarlenVal(sv.clone()),
                        ));
                        state.position.advance_variable(sv.len().clone());
                        state.extracted.insert(trail_idx, Asn1ParsedUnit::VarlenVal(sv));
                    } else {
                        // Non-indexed trail: assign bytes, advance position.
                        self.assign_witness(layouter, input, trail_len, state)?;
                        let trail_len_assigned = self
                            .native_gadget
                            .assign(layouter, Value::known(F::from(trail_len as u64)))?;
                        state.position.advance_variable(trail_len_assigned);
                    }
                }
            }
        }
        Ok(())
    }

    /// Parses an `Asn1RawData` block. For Const/Fixlen, delegates to
    /// [`assign_const`](`Self::assign_const`)/
    /// [`assign_witness`](`Self::assign_witness`). For Varlen, assigns both as
    /// individual bytes and as a `ScannerVec`, using `role` to select
    /// the correct `Asn1ParsedUnit` variant.
    ///
    /// When `role` is `Tag` or `Len`, runs automaton validation and (for `Len`)
    /// verifies the consistency of the DER length encoding. Returns the
    /// circuit-decoded length value for `Len`, `None` otherwise.
    fn process_raw<
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
        data: Asn1RawData<Index>,
        role: RawDataRole,
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<Option<AssignedNative<F>>, Error> {
        match data.0 {
            Asn1RawDataInternal::Const(v, index) => {
                assert_eq!(n, v.len(), "ill-formed raw data in witness");
                let bytes = self.assign_const(layouter, input, &v, state)?;
                let decoded_len = match role {
                    RawDataRole::Len => {
                        let (_, len_value) =
                            decode_length(&v).expect("ill-formed const Length in witness");
                        Some(self.native_gadget.assign_fixed(layouter, F::from(len_value as u64))?)
                    }
                    RawDataRole::Tag => {
                        decode_tag(&v).expect("ill-formed const Tag in witness");
                        None
                    }
                };
                state.record(index, Asn1ParsedUnit::Fixlen(bytes), false);
                state.position.advance_exact(n);
                Ok(decoded_len)
            }
            Asn1RawDataInternal::Fixlen(m, index) => {
                assert_eq!(n, m, "ill-formed raw data in witness");
                let bytes = self.assign_witness(layouter, input, n, state)?;
                let decoded_len = self.automaton_validate_fixlen(layouter, &bytes, &role)?;
                state.record(index, Asn1ParsedUnit::Fixlen(bytes), true);
                state.position.advance_exact(n);
                Ok(decoded_len)
            }
            Asn1RawDataInternal::Varlen(index) => {
                state.varlen = true;

                // Extracts the witness bytes, and assigns them (no constraints so far).
                let raw_bytes = consume(input, n);
                let values: Vec<_> = raw_bytes.iter().copied().map(Value::known).collect();
                let assigned = self.native_gadget.assign_many(layouter, &values)?;
                state.assigned_input.extend_from_slice(&assigned);

                // Constraining the assigned witness depending on the role. Computes the
                // effective (assigned) length of the block, the length encoded in the block in
                // the `RawDataRole::Len` case, and the `Asn1ParsedUnit` corresponding to the
                // block.
                let (assigned_len, decoded_len, parsed_unit) = match role {
                    RawDataRole::Tag => {
                        // Tag role: automaton parsing.
                        let sv: ScannerVec<F, TAG_M, 1> =
                            self.assign_scanner_vec(layouter, Value::known(raw_bytes))?;
                        self.automaton_validate_varlen_tag(layouter, &sv)?;
                        let parsed_unit = Asn1ParsedUnit::VarlenTag(sv.clone());
                        (sv.len().clone(), None, parsed_unit)
                    }
                    RawDataRole::Len => {
                        // Len role: automaton parsing + length decoding.
                        let sv: ScannerVec<F, LEN_M, 1> =
                            self.assign_scanner_vec(layouter, Value::known(raw_bytes))?;
                        let decoded = self.automaton_validate_varlen_len(layouter, &sv)?;
                        let parsed_unit = Asn1ParsedUnit::VarlenLen(sv.clone());
                        (sv.len().clone(), Some(decoded), parsed_unit)
                    }
                };
                state.record(index, parsed_unit, true);
                state.position.advance_variable(assigned_len);
                Ok(decoded_len)
            }
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

    /// Processes a complete TLV: parses tag, length, and value, then
    /// validates the tag/length encodings via automata and asserts that
    /// the decoded length equals the value byte count.
    ///
    /// `tlv_marker`: if set, extracts the full T+L+V bytes under this
    /// index. The value spec's `full_marker` (if any) additionally
    /// extracts V-only bytes.
    fn process_tlv<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &mut &[u8],
        tlv: Asn1Tlv<Index>,
        tlv_marker: Option<Index>,
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<(), Error> {
        // Peek at tag and length off-circuit before consuming.
        let (n_tag, _) = decode_tag(input).expect("failed to decode tag from witness");
        let (n_len, len_value) =
            decode_length(&input[n_tag..]).expect("failed to decode length from witness");
        let value_is_varlen = !matches!(&tlv.len.0, Asn1RawDataInternal::Const(..));

        // Snapshot raw bytes for varlen extractions (before consuming).
        let tlv_total = n_tag + n_len + len_value;
        let tlv_raw =
            (tlv_marker.is_some() && value_is_varlen).then(|| input[..tlv_total].to_vec());
        let full_marker = tlv.val.2.clone();
        let val_raw = (full_marker.is_some() && value_is_varlen)
            .then(|| input[n_tag + n_len..tlv_total].to_vec());

        // Cursor snapshots for fixed-size extraction.
        let tlv_cursor = state.assigned_input.len();
        // Position snapshot for tlv_marker substring check.
        let pos_before_tlv = state.position.clone();

        // Process T, L. Automaton validation happens inside process_raw.
        self.process_raw(layouter, input, n_tag, tlv.tag, RawDataRole::Tag, state)?;
        let decoded_len = self
            .process_raw(layouter, input, n_len, tlv.len, RawDataRole::Len, state)?
            .expect("process_raw with RawDataRole::Len must return a decoded length");
        let expected_len = ParsingPosition::from(decoded_len);

        let pos_before_val = state.position.clone();
        let val_cursor = state.assigned_input.len();

        // Process V blocks.
        self.process_blocks(layouter, input, tlv.val, Some(len_value), state)?;

        let effective_len = state.position.diff(&pos_before_val);

        // Assert decoded length equals effective value length.
        self.assert_equal_positions(layouter, &effective_len, &expected_len)?;

        // Handle full_marker (V-only extraction).
        // The V bytes start at `pos_before_val`, not at `state.position`
        // (which has already advanced past V).
        if let Some(idx) = full_marker {
            match val_raw {
                None => {
                    // Fixed-size extraction.
                    let v_bytes = state.assigned_input[val_cursor..].to_vec();
                    state.record_at(
                        Some(idx),
                        Asn1ParsedUnit::Fixlen(v_bytes),
                        true,
                        &pos_before_val,
                    );
                }
                Some(raw) => {
                    // Variable-size extraction.
                    let sv: ScannerVec<F, VAL_M, VAL_A> =
                        self.assign_scanner_vec(layouter, Value::known(raw))?;
                    state.record_at(
                        Some(idx),
                        Asn1ParsedUnit::VarlenVal(sv),
                        true,
                        &pos_before_val,
                    );
                }
            }
        }

        // Handle tlv_marker (full T+L+V extraction).
        // The T+L+V bytes start at `pos_before_tlv`, not at `state.position`
        // (which has already advanced past the entire TLV).
        if let Some(idx) = tlv_marker {
            match tlv_raw {
                None => {
                    // Fixed-size extraction.
                    let tlv_bytes = state.assigned_input[tlv_cursor..].to_vec();
                    state.record_at(
                        Some(idx),
                        Asn1ParsedUnit::Fixlen(tlv_bytes),
                        true,
                        &pos_before_tlv,
                    );
                }
                Some(raw) => {
                    // Variable-size extraction.
                    let sv: ScannerVec<F, VAL_M, VAL_A> =
                        self.assign_scanner_vec(layouter, Value::known(raw))?;
                    state.record_at(
                        Some(idx),
                        Asn1ParsedUnit::VarlenVal(sv),
                        true,
                        &pos_before_tlv,
                    );
                }
            }
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
        }
    }

    /// Processes an optional TLV. If the witness starts with `expected_tag`,
    /// the full T+L+V is consumed; otherwise nothing is consumed and all
    /// three ScannerVecs are empty (len=0). Conditional constraints ensure
    /// tag identity and length consistency when present, and are trivially
    /// satisfied when absent.
    fn process_optional_tlv<
        Index: Eq + Hash + Debug + Clone,
        const TAG_M: usize,
        const LEN_M: usize,
        const VAL_M: usize,
        const VAL_A: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &mut &[u8],
        expected_tag: &[u8],
        len: Asn1RawData<Index>,
        val: Asn1Spec<Index>,
        state: &mut ParserState<F, Index, TAG_M, LEN_M, VAL_M, VAL_A>,
    ) -> Result<(), Error> {
        state.varlen = true;

        // Off-circuit: peek and conditionally consume.
        let (tag_raw, len_raw, val_raw) = if input.starts_with(expected_tag) {
            let tag_raw = consume(input, expected_tag.len());
            let (n_len, len_value) =
                decode_length(input).expect("process_optional_tlv: failed to decode length");
            let len_raw = consume(input, n_len);
            let val_raw = consume(input, len_value);
            (tag_raw, len_raw, val_raw)
        } else {
            (vec![], vec![], vec![])
        };

        // Assign raw bytes to assigned_input.
        let all_raw: Vec<Value<u8>> = tag_raw
            .iter()
            .chain(len_raw.iter())
            .chain(val_raw.iter())
            .map(|&b| Value::known(b))
            .collect();
        let assigned = self.native_gadget.assign_many(layouter, &all_raw)?;
        state.assigned_input.extend_from_slice(&assigned);

        // Assign 3 ScannerVecs (empty vecs produce valid ScannerVecs with len=0).
        let tag_sv: ScannerVec<F, TAG_M, 1> =
            self.assign_scanner_vec(layouter, Value::known(tag_raw))?;
        let len_sv: ScannerVec<F, LEN_M, 1> =
            self.assign_scanner_vec(layouter, Value::known(len_raw))?;
        let val_sv: ScannerVec<F, VAL_M, VAL_A> =
            self.assign_scanner_vec(layouter, Value::known(val_raw))?;

        // Deferred substring checks + position advance.
        state.substring_checks.push((
            state.position.clone(),
            Asn1ParsedUnit::VarlenTag(tag_sv.clone()),
        ));
        state.position.advance_variable(tag_sv.len().clone());

        state.substring_checks.push((
            state.position.clone(),
            Asn1ParsedUnit::VarlenLen(len_sv.clone()),
        ));
        state.position.advance_variable(len_sv.len().clone());

        state.substring_checks.push((
            state.position.clone(),
            Asn1ParsedUnit::VarlenVal(val_sv.clone()),
        ));
        state.position.advance_variable(val_sv.len().clone());

        // Automaton validation (accepts empty via epsilon).
        let decoded_tag = self.parse_asn1_tag_varlen(layouter, &tag_sv)?;
        let decoded_len = self.parse_asn1_len_varlen(layouter, &len_sv)?;

        // Conditional constraints.
        let ng = &self.native_gadget;
        let is_present = ng.is_not_equal_to_fixed(layouter, tag_sv.len(), F::ZERO)?;

        // Tag match: is_present => decoded_tag == expected_tag_identity.
        let expected_tag_id = Self::compute_tag_identity(expected_tag);
        let expected_assigned = ng.assign_fixed(layouter, F::from(expected_tag_id))?;
        let selected_tag = ng.select(layouter, &is_present, &decoded_tag, &expected_assigned)?;
        ng.assert_equal(layouter, &selected_tag, &expected_assigned)?;

        // Length consistency: is_present => decoded_len == val_sv.len().
        let selected_len = ng.select(layouter, &is_present, &decoded_len, val_sv.len())?;
        ng.assert_equal(layouter, &selected_len, val_sv.len())?;

        // Extract markers from len and val.
        if let Some(idx) = len.into_marker() {
            state.extracted.insert(idx, Asn1ParsedUnit::VarlenLen(len_sv));
        }
        if let Some(idx) = val.into_single_block_marker() {
            state.extracted.insert(idx, Asn1ParsedUnit::VarlenVal(val_sv));
        }

        Ok(())
    }

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
            let idx = self.position_to_assigned(layouter, &pos)?;
            match unit {
                Asn1ParsedUnit::Fixlen(bytes) => {
                    self.check_bytes(layouter, assigned_input, &idx, &bytes)?;
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
                Asn1ParsedUnit::Fixlen(bytes) => {
                    self.check_bytes_varlen_partial(layouter, input_vec, &idx, &bytes)?;
                }
                Asn1ParsedUnit::VarlenTag(sv) => {
                    self.check_bytes_varlen(layouter, input_vec, &idx, &sv)?;
                }
                Asn1ParsedUnit::VarlenLen(sv) => {
                    self.check_bytes_varlen(layouter, input_vec, &idx, &sv)?;
                }
                Asn1ParsedUnit::VarlenVal(sv) => {
                    self.check_bytes_varlen(layouter, input_vec, &idx, &sv)?;
                }
            }
        }
        Ok(())
    }
}
