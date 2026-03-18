//! ASN.1 tag and length regex specs for automaton parsing, plus circuit-level
//! interpretation functions. The regexes accept the DER wire format but do not
//! enforce minimality of encodings.

use midnight_proofs::{circuit::Layouter, plonk::Error};

use super::super::regex::{Regex, RegexInstructions};
use crate::{
    field::AssignedNative,
    instructions::{arithmetic::ArithInstructions, assertions::AssertionInstructions},
    parsing::scanner::{varlen::ScannerVec, AutomatonParser, ScannerChip, StdLibParser},
    types::AssignedByte,
    CircuitField,
};

/// Regex formalising the spec of `StdLibParser::Asn1DerTag`.
pub(super) fn spec_asn1_der_tag() -> Regex {
    // Bits 7–6: class (Universal=00, Application=01, Context=10, Private=11).
    // Bit 5: form (Primitive=0, Constructed=1).
    // Bits 4–0: tag number (short form) or 0x1F (long form sentinel).
    //
    // Any combination of class (2 bits) and form (1 bit) yields 8 possible
    // prefixes for the top 3 bits, i.e. byte values 0x00, 0x20, 0x40, ...,
    // 0xE0, before adding the tag number in the low 5 bits.
    let class_form_prefix =
        |tag_lo: u8| -> Vec<u8> { (0u8..8).map(|prefix| (prefix << 5) | tag_lo).collect() };

    // Short-form tag: tag number fits in bits 4–0 (values 0–30).
    // Outputs the full byte value (class + form + tag number).
    let tag_short =
        Regex::byte_from((0u8..=30).flat_map(class_form_prefix)).mark(&|b| Some(b as usize));

    // Long-form tag: bits 4–0 are all 1s (0x1F), signalling continuation.
    // No output: this byte is a sentinel only.
    let tag_long_first = Regex::byte_from(class_form_prefix(0x1F));
    // Continuation bytes (bit 7 = 1): more tag-number bits follow.
    // Outputs the low 7 bits (continuation flag stripped).
    let tag_continuation = Regex::byte_from(0x80u8..=0xFF).mark(&|b| Some((b & 0x7F) as usize));
    // Final tag byte (bit 7 = 0): last fragment of the tag number.
    // Outputs the byte value (bit 7 is already 0).
    let tag_long_last = Regex::byte_from(0x00u8..=0x7F).mark(&|b| Some(b as usize));

    let tag_long = Regex::cat([tag_long_first, tag_continuation.list(), tag_long_last]);

    tag_short.or(tag_long)
}

/// Controls which markers the DER length automaton outputs.
#[derive(Clone, Copy)]
enum DerLengthMarking {
    /// Full output: total byte count on first byte (long form) or byte
    /// value (short form), plus byte values on subsequent bytes.
    Full,
    /// Only the total encoding byte count: 1 for short form, N+1 for
    /// long form. Subsequent bytes output 0. Useful for extracting the
    /// encoding size via a simple sum over the marker buffer.
    TotalBytes,
    /// Only the length value bytes: byte value for short form and
    /// subsequent long-form bytes, 0 for the long-form header. Useful
    /// for extracting the decoded length via big-endian interpretation
    /// of the marker buffer.
    Value,
}

/// Regex formalising the spec of `StdLibParser::Asn1DerLength` (and its
/// restricted variants `Asn1DerLengthTotalBytes` and `Asn1DerLengthValue`).
fn spec_asn1_der_length_with(m: DerLengthMarking) -> Regex {
    let total = matches!(m, DerLengthMarking::Full | DerLengthMarking::TotalBytes);
    let value = matches!(m, DerLengthMarking::Full | DerLengthMarking::Value);

    let short = Regex::byte_from(0x00u8..=0x7F).mark(&|b| Some(if value { b as usize } else { 1 }));
    let long_first =
        Regex::byte_from(0x81u8..=0xFF).mark(&|b| total.then(|| (b & 0x7F) as usize + 1));
    let value_byte = Regex::any_byte().mark(&|b| value.then_some(b as usize));

    // Note: the regex cannot enforce "exactly N bytes follow" since that
    // depends on the runtime value of N. This must be constrained somewhere
    // later in the circuit.
    let long = Regex::cat([long_first, value_byte.non_empty_list()]);

    short.or(long)
}

/// Full-output DER length automaton (used by `StdLibParser::Asn1DerLength`).
pub(super) fn spec_asn1_der_length() -> Regex {
    spec_asn1_der_length_with(DerLengthMarking::Full)
}

/// Total-bytes-only DER length automaton (used by
/// `StdLibParser::Asn1DerLengthTotalBytes`).
pub(super) fn spec_asn1_der_length_total_bytes() -> Regex {
    spec_asn1_der_length_with(DerLengthMarking::TotalBytes)
}

/// Value-only DER length automaton (used by
/// `StdLibParser::Asn1DerLengthValue`).
pub(super) fn spec_asn1_der_length_value() -> Regex {
    spec_asn1_der_length_with(DerLengthMarking::Value)
}

impl<F: CircuitField + Ord> ScannerChip<F> {
    /// Parses a fixed-size DER tag encoding via the `Asn1DerTag` automaton
    /// and returns the decoded tag identity value as a field element.
    pub fn parse_asn1_tag(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<AssignedNative<F>, Error> {
        let markers = self.parse(
            layouter,
            AutomatonParser::Static(StdLibParser::Asn1DerTag),
            bytes,
        )?;
        let terms: Vec<_> = (markers.iter().rev())
            .scan(F::ONE, |coeff, marker| {
                let term = (*coeff, marker.clone());
                *coeff *= F::from(128u64);
                Some(term)
            })
            .collect();
        self.native_gadget.linear_combination(layouter, &terms, F::ZERO)
    }

    /// Variable-length variant of
    /// [`parse_asn1_tag`](`Self::parse_asn1_tag`). Parses via
    /// the `Asn1DerTag` automaton and returns the decoded tag value.
    pub fn parse_asn1_tag_varlen<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &ScannerVec<F, M, 1>,
    ) -> Result<AssignedNative<F>, Error> {
        let markers = self.parse_varlen(
            layouter,
            AutomatonParser::Static(StdLibParser::Asn1DerTag),
            input,
        )?;
        let terms: Vec<_> = (markers.buffer.iter().rev())
            .scan(F::ONE, |coeff, marker| {
                let term = (*coeff, marker.clone());
                *coeff *= F::from(128u64);
                Some(term)
            })
            .collect();
        self.native_gadget.linear_combination(layouter, &terms, F::ZERO)
    }

    /// Parses a fixed-size DER length encoding via the `Asn1DerLength`
    /// automaton. Asserts in-circuit that the total encoding byte count matches
    /// `bytes.len()` and returns the decoded length value.
    pub fn parse_asn1_len(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<AssignedNative<F>, Error> {
        let markers = self.parse(
            layouter,
            AutomatonParser::Static(StdLibParser::Asn1DerLength),
            bytes,
        )?;
        if markers.len() == 1 {
            // Short form: total_bytes = 1 = bytes.len(), trivially true.
            Ok(markers[0].clone())
        } else {
            // Long form: markers[0] = total byte count. Assert it matches.
            self.native_gadget.assert_equal_to_fixed(
                layouter,
                &markers[0],
                F::from(bytes.len() as u64),
            )?;
            let terms: Vec<_> = (markers[1..].iter().rev())
                .scan(F::ONE, |coeff, marker| {
                    let term = (*coeff, marker.clone());
                    *coeff *= F::from(256u64);
                    Some(term)
                })
                .collect();
            self.native_gadget.linear_combination(layouter, &terms, F::ZERO)
        }
    }

    /// Variable-length variant of [`parse_asn1_len`](`Self::parse_asn1_len`).
    ///
    /// Parses the input via [`Asn1DerLengthTotalBytes`] and
    /// [`Asn1DerLengthValue`], asserts that the total encoding byte count
    /// matches `input.len()`, and returns the decoded length value.
    ///
    /// Requires vector alignment `A = 1` so that data is right-aligned in the
    /// buffer, allowing direct big-endian interpretation of the marker buffer.
    /// This is more efficient than a generic approach using
    /// [`padding_flags`](`ScannerVec::padding_flags`).
    pub fn parse_asn1_len_varlen<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &ScannerVec<F, M, 1>,
    ) -> Result<AssignedNative<F>, Error> {
        let ng = &self.native_gadget;

        // Total byte count: sum of TotalBytes automaton markers.
        // Assert it matches the input length.
        let tb_markers = self.parse_varlen(
            layouter,
            AutomatonParser::Static(StdLibParser::Asn1DerLengthTotalBytes),
            input,
        )?;
        let terms_buffer: Vec<_> = tb_markers.buffer.iter().map(|m| (F::ONE, m.clone())).collect();
        let total_bytes = ng.linear_combination(layouter, &terms_buffer, F::ZERO)?;
        ng.assert_equal(layouter, &total_bytes, input.len())?;

        // Decoded length: big-endian interpretation of Value automaton markers.
        let val_markers = self.parse_varlen(
            layouter,
            AutomatonParser::Static(StdLibParser::Asn1DerLengthValue),
            input,
        )?;
        let be_terms = (val_markers.buffer.iter().rev())
            .scan(F::ONE, |coeff, m| {
                let term = (*coeff, m.clone());
                *coeff *= F::from(256u64);
                Some(term)
            })
            .collect::<Vec<_>>();
        ng.linear_combination(layouter, &be_terms, F::ZERO)
    }
}

#[cfg(test)]
fn decode_hex(s: &str) -> Vec<u8> {
    assert!(
        s.len().is_multiple_of(2),
        "hex string must have even length: {s}"
    );
    s.as_bytes()
        .chunks(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

#[cfg(test)]
fn read_hex_lines(content: &str) -> Vec<Vec<u8>> {
    content
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(decode_hex)
        .collect()
}

#[cfg(test)]
pub(super) fn test_asn1(
    spec_library: &rustc_hash::FxHashMap<super::StdLibParser, super::super::automaton::Automaton>,
) {
    use super::StdLibParser;

    let valid_tags = read_hex_lines(include_str!("examples/asn1/valid_tags.txt"));
    let invalid_tags = read_hex_lines(include_str!("examples/asn1/invalid_tags.txt"));

    // Expected output sequences for each valid tag (order matches valid_tags.txt).
    let tag_outputs: &[&[usize]] = &[&[48], &[2], &[4], &[97], &[0, 31], &[0, 97], &[0, 1, 1]];
    let accepted_tags: Vec<super::super::OutputTestVector<'_>> =
        valid_tags.iter().zip(tag_outputs).map(|(b, &o)| (b.as_slice(), o)).collect();
    let rejected_tags: Vec<&[u8]> = invalid_tags.iter().map(|b| b.as_slice()).collect();

    super::tests::specs_one_test_with_outputs(
        spec_library,
        StdLibParser::Asn1DerTag,
        &accepted_tags,
        &rejected_tags,
    );

    let valid_lengths = read_hex_lines(include_str!("examples/asn1/valid_lengths.txt"));
    let invalid_lengths = read_hex_lines(include_str!("examples/asn1/invalid_lengths.txt"));

    // Expected output sequences for each valid length (order matches
    // valid_lengths.txt).
    let length_outputs: &[&[usize]] = &[&[0], &[88], &[127], &[2, 88], &[3, 1, 0]];
    let accepted_lengths: Vec<super::super::OutputTestVector<'_>> = valid_lengths
        .iter()
        .zip(length_outputs)
        .map(|(b, &o)| (b.as_slice(), o))
        .collect();
    let rejected_lengths: Vec<&[u8]> = invalid_lengths.iter().map(|b| b.as_slice()).collect();

    super::tests::specs_one_test_with_outputs(
        spec_library,
        StdLibParser::Asn1DerLength,
        &accepted_lengths,
        &rejected_lengths,
    );

    // TotalBytes variant: short form outputs 1, long form first byte
    // outputs N+1, subsequent bytes output 0.
    // valid_lengths.txt: 00, 58, 7F, 8158, 820100
    let total_bytes_outputs: &[&[usize]] = &[&[1], &[1], &[1], &[2, 0], &[3, 0, 0]];
    let accepted_total_bytes: Vec<super::super::OutputTestVector<'_>> = valid_lengths
        .iter()
        .zip(total_bytes_outputs)
        .map(|(b, &o)| (b.as_slice(), o))
        .collect();
    super::tests::specs_one_test_with_outputs(
        spec_library,
        StdLibParser::Asn1DerLengthTotalBytes,
        &accepted_total_bytes,
        &rejected_lengths,
    );

    // Value variant: short form outputs byte value, long form first byte
    // outputs 0, subsequent bytes output byte values.
    // valid_lengths.txt: 00, 58, 7F, 8158, 820100
    let value_outputs: &[&[usize]] = &[&[0], &[88], &[127], &[0, 88], &[0, 1, 0]];
    let accepted_values: Vec<super::super::OutputTestVector<'_>> = valid_lengths
        .iter()
        .zip(value_outputs)
        .map(|(b, &o)| (b.as_slice(), o))
        .collect();
    super::tests::specs_one_test_with_outputs(
        spec_library,
        StdLibParser::Asn1DerLengthValue,
        &accepted_values,
        &rejected_lengths,
    );
}
