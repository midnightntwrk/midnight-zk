//! A library of parsers, represented as a Hash Map from documented fixed
//! tokens (`StdLibParser`) to deterministic minimal automata (`Automata`).
//! Since these parsers can be relatively costly to generate, the automata are
//! serialized. The tests check in particular the consistency between the
//! serialised data and a freshly computed one.
//!
//! Whenever a new parser has to be added to the parser library, the following
//! steps have to be followed:
//! 1. Add a corresponding entry (and documentation) in the `StdLibParser` type.
//! 2. Define a function `spec_*` returning the `Regex` defining the parser.
//! 3. Create an empty file whose name and location matches the result of
//!    `parser.serialization_file()`, where `parser` is the entry defined at
//!    step 1.
//! 4. Add an entry `(parser, spec, serialization)` in the function
//!    `spec_library_data`, following the format of the other entries. The
//!    `serialization` component is, in particular, an `include_bytes!` of the
//!    file created at step 3.
//! 5. Run the tests of this file from the root of the repository. This will
//!    bootstrap the serialisation file created at step 1.
//! 6. If the serialisation data needs to be updated, truncate the content of
//!    the corresponding serialisation file, and re-run step 5.
//!
//! ```shell
//!    cargo test --lib -p midnight-circuits --release -- --nocapture regex_test automaton_test static_specs_test
//! ```

mod asn1_der_tlv;
mod icao9303_td3_dg1;
mod jwt;

#[cfg(test)]
use std::{fs, path::Path};

use rustc_hash::FxHashMap;

use super::{automaton::Automaton, regex::Regex, serialization::Serialize};

/// Folder where the serialized automata for the standard library will be
/// stored.
#[cfg(test)]
const AUTOMATON_CACHE: &str = "src/parsing/scanner/static_specs/automaton_cache";

/// Explicit names (and documentation) for indexing the various parsing
/// specifications hard-coded in the standard library.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum StdLibParser {
    /// # Description and sources
    ///
    /// A JWT (Json Web Token) credential payload format, in compliance with the
    /// [RFC 7519](https://datatracker.ietf.org/doc/html/rfc7519) of the IETF. It uses
    /// [this data model in the VC field](https://www.w3.org/TR/vc-data-model-2.0/).
    ///
    /// Notes:
    ///   - Compliance with RFC 7519: the optional fields "iat" and "jti" are
    ///     not checked by this credential. The fields "iss", "sub", "nbf" and
    ///     "exp" are required by this credential.
    ///   - The parser only accepts fields *in the same order as below*.
    ///
    /// ```text
    /// {
    ///     iss: string,
    ///     sub: string,
    ///     nbf: number,
    ///     exp: number,
    ///     vc: {
    ///       credentialSchema?: {
    ///         id: string,
    ///         type: string
    ///       }[],
    ///       credentialSubject: {
    ///         nationalId: string, # output "1"
    ///         familyName: string, # output "2"
    ///         givenName: string,  # output "3"
    ///         publicKeyJwk: {
    ///           kty: string,
    ///           crv: string,
    ///           x: string, # output "5"
    ///           y: string  # output "6"
    ///         }
    ///         id: string,
    ///         birthDate: string,  # output "4"
    ///       },
    ///       type: string[],
    ///       @context: string[],
    ///       issuer: string | { id: string, type?: string },
    ///       credentialStatus: {
    ///         statusPurpose: string,
    ///         statusListIndex: number,
    ///         id: string,
    ///         type: string,
    ///         statusListCredential: string
    ///       }
    ///     }
    /// }
    /// ```
    ///
    /// In particular, the `string` token above refers to JSON strings. This
    /// parser notably enforces the low-level requirements of JSON strings,
    /// such as being UTF-8 encoded or correctly escaped, as required in
    /// [RFC 8259](https://datatracker.ietf.org/doc/html/rfc8259) §7.
    ///
    /// # Disclaimer
    ///
    /// This parser is mostly here as a usage example for the automaton chip. In
    /// practice, unless one does not want to trust that the issuer produced a
    /// correctly formed credential, it is sufficient (and more efficient) to
    /// extract the desired fields using substring checks
    /// (`[ScannerChip::check_bytes]`). See for reference the example
    /// `zk_stdlib/examples/identity/jwt/property_check.rs`.
    ///
    /// # Output Behaviour:
    ///
    /// As Specified in the above grammar, the following field contents
    /// (excluding the double quotes) are output as follows:
    ///   - `"nationalId"` -> 1
    ///   - `"familyName"` -> 2
    ///   - `"givenName"` -> 3
    ///   - `"birthDate"` -> 4
    ///   - `"x"` -> 5
    ///   - `"y"` -> 6
    Jwt,

    /// # Description and sources
    ///
    /// Format of the Data Group 1 (DG1) of biometric passports, as specified in
    /// ICAO Doc 9303 for TD3-type documents (machine-readable passports).
    ///
    /// The DG1 contains the Machine Readable Zone (MRZ) printed on the
    /// passport's main page and stored verbatim on the embedded chip. It
    /// encodes key identity attributes such as the (possibly truncated)
    /// holder's name, date of birth, nationality, and passport number,
    /// using a fixed-length ASCII format.
    ///
    /// A typical TD3 MRZ looks as follows on passports:
    ///
    /// ```text
    /// PPFRADUPONT<<JEAN<MICHEL<<<<<<<<<<<<<<<<<<<<
    /// 12AB345678FRA7408122M3101012<<<<<<<<<<<<<<04
    /// ```
    ///
    /// Note that despite being presented as two lines of 44 bytes each, the DG1
    /// is read and parsed *as a single 88-byte line*.
    ///
    /// These 88 bytes, along with the other Data Groups, can be retrieved by
    /// reading the passport's NFC chip. Integrity and authenticity are ensured
    /// via the Security Object Document (SOD), which contains signed hashes of
    /// the Data Groups. These signatures can be verified using public keys
    /// distributed through the ICAO Public Key Directory (PKD).
    ///
    /// Sources:
    /// - [ICAO Doc 9303](https://www.icao.int/publications/doc-series/doc-9303)
    /// - [PKD](https://www.icao.int/icao-pkd)
    ///
    /// # Disclaimer
    ///
    /// In practice, the passport verification chain is so that when Data Groups
    /// must be parsed, they have already been established as coming from
    /// trusted source. Parsing DG1 with an automaton instead of simply
    /// extracting the fields (relevant fields appear at constant offsets) is
    /// only needed if you expect potential mistakes in the input's structure,
    /// and want to reject flawed inputs accordingly.
    ///
    /// # Output behaviour
    ///
    /// In the MRZ format, only uppercase letters, digits, and `<` (representing
    /// special characters such as spaces or dashes, as well as padding and
    /// separators), are used. The following fields are then output as follows;
    /// note that checksum fields are not mentioned, as they get no output and
    /// are not verified by the parser.
    ///  - Passport type (2 bytes; uppercase) -> 1
    ///  - Issuing country code (3 bytes; uppercase) -> 2
    ///    + **Note**: this code is ISO 3166-1 alpha-3 compliant.
    ///  - name field (up to 39 bytes; uppercase and spaces) -> 3 (surname) and
    ///    4 (given names, if any)
    ///    + **Note 1**: mononyms, i.e., people having no given names, are
    ///      ICAO9303 TD3 compliant. In this case, no byte will be output `4`.
    ///    + **Note 2**: if the credential holder has at least one given name,
    ///      the credential must include a `<<` separator between the surname
    ///      and the given names. Names may be truncated if needed to make the
    ///      separator fits. The whole field is also padded with `<` bytes if no
    ///      truncation occurred.
    ///    + **Note 3**: The `<` characters (separator or padding) are not
    ///      output by this parser. This is to avoid an output ambiguity when
    ///      reading the first padding element after the given names.
    ///  - Passport number (9 bytes; uppercase and digits) -> 5
    ///  - Nationality (3 bytes; uppercase) -> 6
    ///  - Date of birth (6 bytes; YYMMDD) -> 7
    ///  - Sex (1 byte; `M` Male, `F` Female, or `<` Other) -> 8
    ///  - Date of expiry (6 bytes; YYMMDD) -> 9
    ///  - Optional data (14 bytes; uppercase, digits, and `<`) -> 10
    Icao9309Td3Dg1,

    /// **Note**: This is an auxiliary automaton performing partial operations.
    /// In most cases, rather than calling [`AutomatonChip::parse`] with this
    /// automaton, you likely need the wrappers [`ScannerChip::parse_asn1_tag`]
    /// or [`ScannerChip::parse_asn1_tag_varlen`] instead.
    ///
    /// # Description and sources
    ///
    /// A single ASN.1 DER tag, as specified in ITU-T X.690.
    ///
    /// A DER tag encodes three pieces of information:
    ///   - The **class** (2 bits): Universal, Application, Context-specific,
    ///     Private.
    ///   - The **form** (1 bit): Primitive or Constructed.
    ///   - The **tag number** (5 bits or more).
    ///
    /// When the tag number fits in 5 bits (0–30), the tag is a single byte
    /// (so-called "short form"):
    ///
    /// ```text
    ///   byte:  [class: 2 bits][form: 1 bit][tag number: 5 bits]
    /// ```
    ///
    /// When the tag number is 31 or more, bits 4–0 of the first byte are all
    /// 1s, and subsequent bytes encode the tag number using 7 bits each. Bit 7
    /// is a continuation flag (1 = more bytes follow, 0 = last byte). This is
    /// called a "long form".
    ///
    /// ```text
    ///   byte 0:  [class: 2 bits][form: 1 bit][1 1 1 1 1]
    ///   byte 1+: [continuation: 1 bit][tag number fragment: 7 bits]
    ///            ...last byte has continuation = 0
    /// ```
    ///
    /// # Output behaviour
    ///
    /// Each byte that carries actual tag identity bits outputs its payload
    /// (the tag-relevant bits), stripping structural overhead:
    ///   - Short form: the full byte value `B` is output when `B` is read (it
    ///     carries class, form, and tag number — all part of the tag identity).
    ///   - Long form: byte 0 produces no output (bits 4–0 are just the `11111`
    ///     sentinel). Each continuation or final byte `B` outputs `B & 0x7F`
    ///     (the low 7 bits; the continuation flag is stripped). The tag number
    ///     can thus be reconstructed by reading the sequence of outputs as a
    ///     big-endian number in base 128.
    ///
    /// Recall that [`ScannerChip::parse_asn1_tag`] and
    /// [`ScannerChip::parse_asn1_tag_varlen`] typically parse a tag with this
    /// automaton, and interpret the result in base 128 in-circuit to return the
    /// actual assigned value of the tag.
    ///
    /// # Unconventional behaviour
    ///
    /// For the purpose of supporting optional fields (common in ASN.1
    /// specifications), this parser also accepts empty inputs.
    Asn1DerTag,

    /// **Note**: This is an auxiliary automaton performing partial operations.
    /// In most cases, rather than calling [`AutomatonChip::parse`] with this
    /// automaton, you likely need the wrappers [`ScannerChip::parse_asn1_len`]
    /// or [`ScannerChip::parse_asn1_len_varlen`] instead.
    ///
    /// # Description and sources
    ///
    /// A single ASN.1 DER length field, as specified in ITU-T X.690.
    ///
    /// The length field follows the tag and indicates the number of bytes in
    /// the value. DER mandates the **definite** form with minimal encoding:
    ///
    /// **Short form** (length 0–127): a single byte whose bit 7 is 0.
    ///
    /// ```text
    ///   byte:  0 | length (7 bits)
    /// ```
    ///
    /// **Long form** (length 128+): the first byte has bit 7 = 1 and bits
    /// 6–0 encode the number N of subsequent bytes. The next N bytes give the
    /// length as a big-endian unsigned integer.
    ///
    /// ```text
    ///   byte 0:        1 | N (7 bits, N >=1)
    ///   bytes 1..=N:   length: N bytes, interpreted big-endian
    /// ```
    ///
    /// This is however, the *theoretical* behaviour. As an automaton cannot
    /// check that exactly `N` bytes are read, trails of arbitrary sizes are
    /// accepted. A circuit using this automaton then has to enforce this length
    /// constraint separately (see [`ScannerChip::parse_asn1_len`] and
    /// [`ScannerChip::parse_asn1_len_varlen`]).
    ///
    /// Note: the indefinite form (byte 0 = 0x80) is forbidden by DER.
    ///
    /// # Output behaviour
    ///
    /// Each byte outputs its length-relevant payload:
    ///   - Short form: the byte value `B` is output (it *is* the length, since
    ///     bit 7 is 0).
    ///   - Long form: byte 0 outputs `(B & 0x7F) + 1` = N + 1 (the total
    ///     encoding byte count). Each of the N subsequent bytes outputs its
    ///     byte value `B`. The length can be reconstructed by reading the
    ///     outputs of bytes 1..=N as a big-endian number in base 256.
    ///
    /// See also [`ScannerChip::parse_asn1_len`] and
    /// [`ScannerChip::parse_asn1_len_varlen`] for circuit-level
    /// interpretation.
    ///
    /// # Unconventional behaviour
    ///
    /// For the purpose of supporting optional fields (common in ASN.1
    /// specifications), this parser also accepts empty inputs.
    Asn1DerLength,

    /// **Note**: This is an auxiliary automaton performing partial operations.
    /// In most cases, rather than calling [`AutomatonChip::parse`] with this
    /// automaton, you likely need the wrappers [`ScannerChip::parse_asn1_len`]
    /// or [`ScannerChip::parse_asn1_len_varlen`] instead.
    ///
    /// Restricted variant of `Asn1DerLength` that only outputs the total
    /// encoding byte count: 1 for short form, N+1 for long form where `N` is
    /// the first byte of the input. Subsequent bytes in long form output 0.
    /// Makes it easier to retrieve this specific field after a
    /// variable-length parsing.
    ///
    /// # Unconventional behaviour
    ///
    /// For the purpose of supporting optional fields (common in ASN.1
    /// specifications), this parser also accepts empty inputs.
    Asn1DerLengthTotalBytes,

    /// **Note**: This is an auxiliary automaton performing partial operations.
    /// In most cases, rather than calling [`AutomatonChip::parse`] with this
    /// automaton, you likely need the wrappers [`ScannerChip::parse_asn1_len`]
    /// or [`ScannerChip::parse_asn1_len_varlen`] instead.
    ///
    /// Restricted variant of `Asn1DerLength` that only outputs the length
    /// value bytes: byte value for short form and for subsequent long-form
    /// bytes, 0 for the long-form header. Makes it easier to retrieve this
    /// specific field after a variable-length parsing.
    ///
    /// # Unconventional behaviour
    ///
    /// For the purpose of supporting optional fields (common in ASN.1
    /// specifications), this parser also accepts empty inputs.
    Asn1DerLengthValue,
}

#[cfg(test)]
impl StdLibParser {
    /// Returns the file name where the parser index is serialised. The path
    /// starts from the root of the repository.
    pub(super) fn serialization_file(&self) -> String {
        format!("{}/{:?}", AUTOMATON_CACHE, self)
    }
}

/// The raw entry of the parsing library. Contains the different parser names
/// (`StdLibParser`), the functions used to generate the corresponding `Regex`
/// (functions typically named `spec_*`), and the serialization bytes.
type LibraryData = &'static [(StdLibParser, &'static dyn Fn() -> Regex, &'static [u8])];

/// A library of parsing automata, computed or deserialised.
pub type ParsingLibrary = FxHashMap<StdLibParser, (Regex, Automaton)>;

/// The basic, non computed data of the parsing library. When serialization is
/// enabled, the automata will be deserialized in `spec_library` from the third
/// components. When serialization is disabled, the automaton will be computed
/// using the second argument.
fn spec_library_data() -> LibraryData {
    &[
        (
            StdLibParser::Jwt,
            &jwt::spec_jwt,
            include_bytes!("automaton_cache/Jwt"),
        ),
        (
            StdLibParser::Icao9309Td3Dg1,
            &icao9303_td3_dg1::spec_icao9303_td3_dg1,
            include_bytes!("automaton_cache/Icao9309Td3Dg1"),
        ),
        (
            StdLibParser::Asn1DerTag,
            &asn1_der_tlv::spec_asn1_der_tag,
            include_bytes!("automaton_cache/Asn1DerTag"),
        ),
        (
            StdLibParser::Asn1DerLength,
            &asn1_der_tlv::spec_asn1_der_length,
            include_bytes!("automaton_cache/Asn1DerLength"),
        ),
        (
            StdLibParser::Asn1DerLengthTotalBytes,
            &asn1_der_tlv::spec_asn1_der_length_total_bytes,
            include_bytes!("automaton_cache/Asn1DerLengthTotalBytes"),
        ),
        (
            StdLibParser::Asn1DerLengthValue,
            &asn1_der_tlv::spec_asn1_der_length_value,
            include_bytes!("automaton_cache/Asn1DerLengthValue"),
        ),
    ]
}

/// All automata that can be used as a parsing basis in the standard library.
/// Exclusively uses serialised data.
pub fn spec_library() -> ParsingLibrary {
    spec_library_data()
            .iter()
            .map(|(name, regex, serialization)| {
                assert!(
                    !serialization.is_empty(),
                    "Empty serialisation data for {:?}. The bootstrapping of the serialisation process has not been conducted. (see documentation of `midnight_circuits::parsing::scanner::static_specs`)",
                    *name
                );
                (*name, (regex(), Automaton::deserialize_unwrap(serialization)))
            })
            .collect::<FxHashMap<_, _>>()
}

#[cfg(test)]
/// Re-serialises the data in `checks`, and:
///
/// 1. If some non-empty serialisation file exists and
///    `AUTOMATON_BREAKING_CHANGE` is set to false, panics if the serialized
///    data is inconsistent.
/// 2. If some empty serialisation file exists, writes the serialised data
///    inside.
/// 3. If the expected serialisation files do not exist, panics.
///
/// Will also panic and request a re-compilation if the serialisation data is
/// updated at any point.
///
/// Note: This function is only available in tests.
fn check_serialization(checks: &ParsingLibrary) {
    // Tracks whether a recompilation is needed so that the serialisation data is in
    // sync.
    let mut recompile = false;
    for (parser, (_, automaton)) in checks {
        let file_name = parser.serialization_file();
        assert!(
                Path::new(&file_name).exists(),
                "serialisation file {file_name} does not exist! Follow the documentation of `midnight_circuits::parsing::scanner::static_specs` for instructions on how to add a new parser to the standard library."
            );
        let previous_data = fs::read(file_name.clone()).unwrap();
        let mut current_data = Vec::new();
        automaton.serialize(&mut current_data);
        if previous_data.is_empty() {
            println!("-> bootstrapping the serialisation of {:?}. Recompilation will be necessary so that the executable contains the correct serialised data.", parser);
            recompile = true;
            fs::write(file_name, &current_data).unwrap();
        } else {
            assert!(
                current_data == previous_data,
                "The serialisation data of the parsing library (parser name: {:?}) is not up to date. If this is intentional, clear the content of {}, and run the test again to replace its content.",
                parser, parser.serialization_file()
            );
            println!("-> serialisation data of {:?} is up to date.", parser)
        }
        println!(">> Serialisation checks completed.\n======");
        assert!(
            !recompile,
            "The executable has to be re-compiled so that the serialisation data is up-to-date."
        );
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use rustc_hash::{FxBuildHasher, FxHashMap};

    use super::{
        super::automaton::Automaton, check_serialization, spec_library, spec_library_data,
        StdLibParser,
    };
    use crate::parsing::{regex::Regex, scanner::MarkerTestVector};

    /// Sets up the serialised library (bootstraps it if empty serialisation
    /// data is found), and performs consistency checks or updates accordingly
    /// to the value of `AUTOMATON_BREAKING_CHANGE`.
    fn configure_serialisation() {
        let lib_data = spec_library_data();

        println!("======\nRecomputing the parsing library automata...");
        let mut lib = FxHashMap::with_capacity_and_hasher(lib_data.len(), FxBuildHasher);
        let start = Instant::now();
        for (name, spec, _) in lib_data {
            let start_local = Instant::now();
            let automaton = spec().to_automaton();
            println!(
                "-> Generated {:?} automaton in {:?}",
                *name,
                start_local.elapsed()
            );
            lib.insert(*name, (spec(), automaton));
        }
        println!(
            ">> Full parsing library re-computed in {:?}!\n======\n>> Now checking the consistency of serialised data.",
            start.elapsed()
        );
        check_serialization(&lib)
    }

    /// Checks that the automaton accepts `input` and returns its raw
    /// output sequence.
    fn check_accepted(
        automaton: &Automaton,
        spec: StdLibParser,
        index: usize,
        input: &[u8],
    ) -> Vec<usize> {
        println!("\n -> accepting test nb. {index}");
        let (v, outputs, interrupted) = automaton.run(input);
        let counter = v.len() - 1;
        assert!(!interrupted,
            "[spec {:?}, accept #{index}] stuck after {counter} transitions, reading byte {} ({:02X}). Partial input:\n\n{}\n\n(bytes {:02X?})",
            spec,
            input[counter],
            input[counter],
            String::from_utf8_lossy(&input[..counter]),
            &input[..counter],
        );
        let state = v[counter];
        assert!(
            automaton.final_states.contains(&state),
            "[spec {:?}, accept #{index}] non-final state {state} after {counter} transitions",
            spec
        );
        outputs
    }

    /// Checks that the automaton rejects `input`.
    fn check_rejected(automaton: &Automaton, spec: StdLibParser, index: usize, input: &[u8]) {
        println!("\n -> rejecting test nb. {index}");
        let (v, outputs, interrupted) = automaton.run(input);
        let counter = v.len() - 1;
        if interrupted {
            println!(
                "... rejected as expected (stuck after {counter} transitions at byte {} ({:02X})).",
                input[counter], input[counter],
            )
        } else {
            let state = v[counter];
            assert!(
                !automaton.final_states.contains(&state),
                "[spec {:?}, reject #{index}] unexpectedly accepted (final state {state} after {counter} transitions). Raw outputs: {:?}",
                spec, outputs
            );
            println!(
                "... rejected as expected (non-final state {state} after {counter} transitions)."
            )
        }
    }

    /// Tests a spec whose automaton uses markers as group identifiers:
    /// input bytes at positions sharing the same non-zero marker are
    /// collected into groups, and each group is compared against the
    /// expected byte sequence.
    pub(super) fn specs_one_test_with_markers(
        spec_library: &FxHashMap<StdLibParser, (Regex, Automaton)>,
        spec: StdLibParser,
        accepted: &[MarkerTestVector<'_>],
        rejected: &[&[u8]],
    ) {
        let (_, automaton) = spec_library.get(&spec).unwrap();
        println!("\n\n** TEST of the spec {:?}", spec);
        for (index, &(input, expected_outputs)) in accepted.iter().enumerate() {
            let output_automaton = check_accepted(automaton, spec, index, input);

            // Gathering outputs.
            let mut outputs = FxHashMap::with_capacity_and_hasher(2, FxBuildHasher);
            for (&o, &i) in output_automaton.iter().zip(input) {
                if o != 0 {
                    outputs.entry(o).or_insert(vec![]).push(i);
                }
            }

            if let Some(n) =
                outputs.iter().find(|&(i, _)| expected_outputs.iter().all(|(j, _)| i != j))
            {
                panic!(
                    "[test of spec {:?}, nb. {index}]: accepted as expected, but has unexpected marker {}.",
                    spec, n.0
                )
            }
            for (i, expected_output_bytes) in expected_outputs {
                match outputs.get(i) {
                    None => panic!(
                        "[test of spec {:?}, nb. {index}]: accepted as expected, but missing marker {i}.",
                        spec
                    ),
                    Some(output_bytes) => {
                        assert!(output_bytes == expected_output_bytes,
                            "[test of spec {:?}, nb. {index}]: output for marker {i} is\n  \"{}\"\ninstead of\n  \"{}\"",
                            spec,
                            String::from_utf8_lossy(output_bytes),
                            String::from_utf8_lossy(expected_output_bytes),
                        );
                    }
                }
            }
            let counter = input.len();
            println!("... accepted with correct outputs ({counter} transitions). The outputs are:");
            for (i, o) in expected_outputs {
                println!("  - {i}: {}", String::from_utf8_lossy(o))
            }
        }
        for (index, input) in rejected.iter().enumerate() {
            check_rejected(automaton, spec, index, input);
        }
    }

    /// Tests a spec whose automaton outputs values directly (one per input
    /// byte). The raw output sequence is compared against the expected
    /// sequence.
    pub(super) fn specs_one_test_with_outputs(
        spec_library: &FxHashMap<StdLibParser, (Regex, Automaton)>,
        spec: StdLibParser,
        accepted: &[super::super::OutputTestVector<'_>],
        rejected: &[&[u8]],
    ) {
        let (_, automaton) = spec_library.get(&spec).unwrap();
        println!("\n\n** TEST of the spec {:?}", spec);
        for (index, &(input, expected)) in accepted.iter().enumerate() {
            let actual = check_accepted(automaton, spec, index, input);
            assert_eq!(
                actual, expected,
                "[spec {:?}, accept #{index}]: output mismatch",
                spec
            );
            println!("... accepted with correct outputs: {actual:?}");
        }
        for (index, input) in rejected.iter().enumerate() {
            check_rejected(automaton, spec, index, input);
        }
    }

    #[test]
    fn specs_test() {
        // Enforces that serialisation data is consistent and up to date.
        configure_serialisation();

        // Performs the tests using the serialised data.
        println!(">> Now configuring the spec library for tests... (using the serialised data)");
        let start = Instant::now();
        let spec_library = spec_library();
        println!(
            ">> Configuration completed in {:?}. Automaton breakdown:",
            start.elapsed()
        );
        let mut total = 0;
        for (name, (_, automaton)) in &spec_library {
            println!(
                "  - {:?}: {} states, {} transitions",
                name,
                automaton.nb_states,
                automaton.transitions.values().map(|m| m.len()).sum::<usize>()
            );
            total += automaton.transitions.values().map(|m| m.len()).sum::<usize>()
                + automaton.final_states.len()
        }
        println!(
            ">> Total nb of lookup rows in the chip: {} ≤ 2^{}",
            total,
            total.next_power_of_two().trailing_zeros()
        );

        super::jwt::test_jwt(&spec_library);
        super::icao9303_td3_dg1::test_dg1(&spec_library);
        super::asn1_der_tlv::test_asn1(&spec_library);
    }
}
