//! A library of parsers, represented as a Hash Map from documented custom
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
//!    cargo test --lib -p midnight-circuits --release -- --nocapture regex_test automaton_test specs_test
//! ```

#[cfg(test)]
use std::{fs, path::Path};

use rustc_hash::FxHashMap;

use super::{
    automaton::Automaton,
    regex::{Regex, RegexInstructions},
};
use crate::parsing::serialization::Serialize;

/// Folder where the serialized automata for the standard library will be
/// stored.
#[cfg(test)]
const AUTOMATON_CACHE: &str = "src/parsing/automaton_cache";

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
    ///         nationalId: string, # marked "1"
    ///         familyName: string, # marked "2"
    ///         givenName: string,  # marked "3"
    ///         publicKeyJwk: {
    ///           kty: string,
    ///           crv: string,
    ///           x: string, # marked "5"
    ///           y: string  # marked "6"
    ///         }
    ///         id: string,
    ///         birthDate: string,  # marked "4"
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
    /// # Output Behaviour:
    ///
    /// As Specified in the above grammar, the following field contents
    /// (excluding the double quotes) are marked as follows:
    ///   - `"nationalId"` -> 1
    ///   - `"familyName"` -> 2
    ///   - `"givenName"` -> 3
    ///   - `"birthDate"` -> 4
    ///   - `"x"` -> 5
    ///   - `"y"` -> 6
    Jwt,
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
type ParsingLibrary = FxHashMap<StdLibParser, Automaton>;

/// The basic, non computed data of the parsing library. When serialization is
/// enabled, the automata will be deserialized in `spec_library` from the third
/// components. When serialization is disabled, the automaton will be computed
/// using the second argument.
fn spec_library_data() -> LibraryData {
    &[(
        StdLibParser::Jwt,
        &spec_jwt as &'static dyn Fn() -> Regex,
        include_bytes!("automaton_cache/Jwt") as &'static [u8],
    )]
}

/// All automata that can be used as a parsing basis in the standard library.
/// Exclusively uses serialised data.
pub fn spec_library() -> ParsingLibrary {
    spec_library_data()
            .iter()
            .map(|(name, _, serialization)| {
                assert!(
                    !serialization.is_empty(),
                    "Empty serialisation data for {:?}. The bootstrapping of the serialisation process has not been conducted. (see documentation of `midnight_circuits::parsing::specs`)",
                    *name
                );
                (*name, Automaton::deserialize_unwrap(serialization))
            })
            .collect::<FxHashMap<_, _>>()
}

// Regex formalising the spec of `StdLIbParser::Jwt`.
fn spec_jwt() -> Regex {
    // Content of a basic field (RFC 8259 JSON string), possibly marked if `marker`
    // is not 0.
    let string = |marker: usize| -> Regex {
        Regex::json_string().replace_markers(&|m| if m == 1 { Some(marker) } else { None })
    };
    // A json field, with possible white spaces.
    let field = |name: &str, content: Regex| -> Regex {
        Regex::spaced_cat([format!("\"{name}\"").into(), ":".into(), content])
    };
    let string_field = |name: &str, marker: usize| -> Regex { field(name, string(marker)) };
    let int_field = |name: &str| -> Regex { field(name, Regex::digit().non_empty_list()) };

    // A collection of regular expressions, delimited by `opening` and `closing`,
    // and separated by commas. Arbitrary white spaces are allowed between the
    // delimiters and the various items.
    let collec = |opening: &str, items: Vec<Regex>, closing: &str| -> Regex {
        Regex::spaced_separated_cat(items, ",".into())
            .spaced_delimited(opening.into(), closing.into())
    };

    // A JSON list of strings.
    let string_list = string(0)
        .spaced_separated_list(",".into())
        .spaced_delimited("[".into(), "]".into());

    // Fields of the credential format.
    let credential_schema = field(
        "credentialSchema",
        collec(
            "{",
            vec![string_field("id", 0), string_field("type", 0)],
            "}",
        )
        .spaced_separated_list(",".into())
        .spaced_delimited("[".into(), "]".into()),
    );
    let public_key_jwk = field(
        "publicKeyJwk",
        collec(
            "{",
            vec![
                string_field("kty", 0),
                string_field("crv", 0),
                string_field("x", 5), // Marked 5.
                string_field("y", 6), // Marked 6.
            ],
            "}",
        ),
    );
    let credential_subject = field(
        "credentialSubject",
        collec(
            "{",
            vec![
                string_field("nationalId", 1), // Marked 1.
                string_field("familyName", 2), // Marked 2.
                string_field("givenName", 3),  // Marked 3.
                public_key_jwk,
                string_field("id", 0),
                string_field("birthDate", 4), // Marked 4.
            ],
            "}",
        ),
    );
    let issuer = field(
        "issuer",
        Regex::union([
            string(0),
            collec(
                "{",
                vec![string_field("id", 0), string_field("type", 0)],
                "}",
            ),
            collec("{", vec![string_field("id", 0)], "}"),
        ]),
    );
    let credential_status = field(
        "credentialStatus",
        collec(
            "{",
            vec![
                string_field("statusPurpose", 0),
                int_field("statusListIndex"),
                string_field("id", 0),
                string_field("type", 0),
                string_field("statusListCredential", 0),
            ],
            "}",
        ),
    );

    collec(
        "{",
        vec![
            string_field("iss", 0),
            string_field("sub", 0),
            int_field("nbf"),
            int_field("exp"),
            field(
                "vc",
                collec(
                    "{",
                    vec![
                        credential_subject.clone().or(Regex::spaced_cat([
                            credential_schema,
                            ",".into(),
                            credential_subject,
                        ])),
                        field("type", string_list.clone()),
                        field("@context", string_list),
                        issuer,
                        credential_status,
                    ],
                    "}",
                ),
            ),
        ],
        "}",
    )
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
    for (parser, automaton) in checks {
        let file_name = parser.serialization_file();
        assert!(
                Path::new(&file_name).exists(),
                "serialisation file {file_name} does not exist! Follow the documentation of `midnight_circuits::parsing::specs` for instructions on how to add a new parser to the standard library."
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
        spec_library_data,
        StdLibParser::{self, Jwt},
    };
    use crate::parsing::{automaton::Automaton, spec_library, specs::check_serialization};

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
            lib.insert(*name, automaton);
        }
        println!(
            ">> Full parsing library re-computed in {:?}!\n======\n>> Now checking the consistency of serialised data.",
            start.elapsed()
        );
        check_serialization(&lib)
    }

    /// Tests whether a given regular expression accepts or rejects two sets of
    /// corresponding strings. For accepted strings, checks the list of outputs
    /// for each markers.
    fn specs_one_test(
        spec_library: &FxHashMap<StdLibParser, Automaton>,
        spec: StdLibParser,
        accepted: &[(&str, &[(usize, &str)])],
        rejected: &[&str],
    ) {
        let automaton = spec_library.get(&spec).unwrap();
        println!("\n\n** TEST of the spec {:?}", spec);
        accepted.iter().enumerate().for_each(|(index,&(s,expected_outputs))| {
            println!("\n -> accepting test nb. {index}");
            let s_bytes = s.as_bytes();

            let (v,output_automaton,interrupted) = automaton.run(s_bytes);
            let counter = v.len() - 1;
            assert!(!interrupted,
                "input was unexpectedly rejected after being stuck after {} transitions, reading character '{}' (byte {}). Partial input read before the interruption:\n\n{}\n\n(i.e., bytes [{:?}])",
                counter,
                s_bytes[counter] as char,
                s_bytes[counter],
                &s[..counter],
                &s_bytes[..counter],
            );

            // Gathering outputs.
            let mut outputs = FxHashMap::with_capacity_and_hasher(2, FxBuildHasher);
            for (&o,&i) in output_automaton.iter().zip(s_bytes) {
                if o != 0 {
                    outputs.entry(o).or_insert(vec![]).push(i);
                }
            }

            let state = v[counter];
            assert!(
                automaton.final_states.contains(&state),
                "input was unexpectedly rejected (automaton run ended up in the non-final state {} after {} transitions)", state, counter
            );
            if let Some(n) = outputs.iter().find(|&(i,_)|
                expected_outputs.iter().all(|(j,_)| i != j)
            ){
                panic!(
                    "[test of spec {:?}, nb. {index}]: the input {s} is accepted as expected, but it has been marked with a {}, which is unexpected\nThe automaton reached the final state {} in {} transitions.",
                    spec, n.0, state, counter
                )
            }
            for (i,expected_output) in expected_outputs {
                let expected_output_bytes = expected_output.as_bytes();
                match outputs.get(i) {
                    None => panic!(
                        "[test of spec {:?}, nb. {index}]: the input {s} is accepted as expected, but it has no marker {i}, which is unexpected\nThe automaton reached the final state {} in {} transitions.",
                        spec, state, counter
                    ),
                    Some(output_bytes) => {
                        assert!(output_bytes == expected_output_bytes,
                            "[test of spec {:?}, nb. {index}]: the input {s} is accepted as expected, but the output marked {i} is\n  \"{}\"\ninstead of\n  \"{}\"\nwhich is unexpected. The automaton reached the final state {} in {} transitions.",
                            spec,
                            String::from_utf8_lossy(output_bytes),
                            String::from_utf8_lossy(expected_output_bytes),
                            state,
                            counter
                        );

                    }
                }
            }
            println!("... which is accepted as expected with the correct outputs (the automaton reached the final state {} in {} transitions). The outputs are:", state, counter);
            for (i,o) in expected_outputs {
                println!("  - {i}: {o}")
            }
        });
        rejected.iter().enumerate().for_each(|(index,s)| {
            println!("\n -> rejecting test nb. {index}");
            let s_bytes = s.as_bytes();
            let (v,output,interrupted) = automaton.run(s_bytes);
            let counter = v.len() - 1;
            if interrupted {
                println!(
                    "... which is rejected as expected. The automaton run was stuck after {} transitions, reading character '{}' (byte {}). Partial input read before the interruption:\n\n{}\n",
                    counter,
                    s_bytes[counter] as char,
                    s_bytes[counter],
                    &s[..counter],
                )
            } else {
                let state = v[counter];
                if automaton.final_states.contains(&state) {
                    // Gathering outputs.
                    let mut outputs = FxHashMap::with_capacity_and_hasher(2, FxBuildHasher);
                    for (&o,&i) in output.iter().zip(s_bytes) {
                        if o != 0 {
                            outputs.entry(o).or_insert(vec![]).push(i);
                        }
                    }
                    let mut outputs_str = String::new();
                    for (i,o) in outputs {
                        outputs_str.push_str(&format!("  - {i}: {}\n", String::from_utf8_lossy(&o)))
                    }
                    panic!(
                        "input was unexpectedly accepted (reached final state {} after {} transitions). The outputs were:\n{}",
                        state, counter, outputs_str
                    )
                }
                println!("... which is rejected as expected (the automaton run ended up in the non-final state {} after {} transitions).", state, counter)
            }
        });
    }

    #[test]
    fn specs_test() {
        // Enforces that serialisation data is consistent and up to date.
        configure_serialisation();

        // Performs the tests using the serialised data.
        println!(">> Now configuring the spec library for tests... (using the serialised data)");
        let start = Instant::now();
        let spec_library = spec_library();
        println!(">> Configuration completed in {:?}", start.elapsed());
        for (name, automaton) in &spec_library {
            println!(
                "  - {:?} automaton: {} states, {} transitions",
                name,
                automaton.nb_states,
                automaton.transitions.len()
            )
        }
        let accepted0: Vec<(&str, &[(usize, &str)])> = vec![
            (
                FULL_INPUT_JWT,
                &[
                    (1, "12345"),
                    (2, "Wonderland"),
                    (3, "Alice"),
                    (4, "2000-11-13"),
                    (5, "S0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8M"),
                    (6, "dux8h-QcIA3aZG9CSPIltDwVvOkf0kfJRJLH7K1KSlQ"),
                ],
            ),
            (
                MINIMAL_JWT,
                &[
                    (1, "id"),
                    (2, "fn"),
                    (3, "gn"),
                    (4, "bd"),
                    (5, "x"),
                    (6, "y"),
                ],
            ),
        ];
        let rejected0: Vec<&str> =
            vec!["hello world", &FULL_INPUT_JWT[..1000], &MINIMAL_JWT[..600]];

        specs_one_test(&spec_library, Jwt, &accepted0, &rejected0);
    }

    const FULL_INPUT_JWT: &str = r#"{
    "iss":"did:prism:954e59ea4c212f4b4be8688bd3fe63dd7079d218ef6282205a70131f87f2887c",
    "sub":"did:prism:73bb516fe88beec5b3b8d283eaec5964d1c13cd54ef8f1784217f4fe42688626:CtQBCtEBEkgKFG15LWF1dGgta2V5LW1pZG5pZ2h0EARKLgoJc2VjcDI1NmsxEiECS0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8MSOwoHbWFzdGVyMBABSi4KCXNlY3AyNTZrMRIhAimWDggNDswAIJWKbexkfDxV0PEa58tcVcS1dk2phkDjGkgKDmFnZW50LWJhc2UtdXJsEhBMaW5rZWRSZXNvdXJjZVYxGiRodHRwOi8vMTkyLjE2OC4xLjg2OjgzMDAvY2xvdWQtYWdlbnQ",
    "nbf":1740482175,
    "exp":1740485775,
    "vc":{
       "credentialSchema":[
          {
             "id":"http:\/\/192.168.1.86:8400\/cloud-agent\/schema-registry\/schemas\/2fcfeeae-9532-3869-ad89-cdf5060c3a3c",
             "type":"CredentialSchema2022"
          }
       ],
       "credentialSubject":{
          "nationalId":"12345",
          "familyName":"Wonderland",
          "givenName":"Alice",
          "publicKeyJwk":{
             "kty":"EC",
             "crv":"secp256k1",
             "x":"S0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8M",
             "y":"dux8h-QcIA3aZG9CSPIltDwVvOkf0kfJRJLH7K1KSlQ"
          },
          "id":"did:prism:73bb516fe88beec5b3b8d283eaec5964d1c13cd54ef8f1784217f4fe42688626:CtQBCtEBEkgKFG15LWF1dGgta2V5LW1pZG5pZ2h0EARKLgoJc2VjcDI1NmsxEiECS0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8MSOwoHbWFzdGVyMBABSi4KCXNlY3AyNTZrMRIhAimWDggNDswAIJWKbexkfDxV0PEa58tcVcS1dk2phkDjGkgKDmFnZW50LWJhc2UtdXJsEhBMaW5rZWRSZXNvdXJjZVYxGiRodHRwOi8vMTkyLjE2OC4xLjg2OjgzMDAvY2xvdWQtYWdlbnQ",
          "birthDate":"2000-11-13"
       },
       "type":[
          "VerifiableCredential"
       ],
       "@context":[
          "https:\/\/www.w3.org\/2018\/credentials\/v1"
       ],
       "issuer":{
          "id":"did:prism:954e59ea4c212f4b4be8688bd3fe63dd7079d218ef6282205a70131f87f2887c",
          "type":"Profile"
       },
       "credentialStatus":{
          "statusPurpose":"Revocation",
          "statusListIndex":3,
          "id":"http:\/\/192.168.1.86:8400\/cloud-agent\/credential-status\/2054e2ea-f191-4640-86dd-6dde6b2f77f7#3",
          "type":"StatusList2021Entry",
          "statusListCredential":"http:\/\/192.168.1.86:8400\/cloud-agent\/credential-status\/2054e2ea-f191-4640-86dd-6dde6b2f77f7"
       }
    }
}"#;

    const MINIMAL_JWT: &str = r#"{
    "iss" : "",
    "sub" : "",
    "nbf" : 0,
    "exp" : 1,
    "vc" : {
       "credentialSubject" : {
          "nationalId" : "id",
          "familyName" : "fn",
          "givenName" : "gn",
          "publicKeyJwk" : {
             "kty" : "",
             "crv" : "",
             "x" : "x",
             "y" : "y"
          },
          "id" : "",
          "birthDate" : "bd"
       },
       "type" : [],
       "@context" : [],
       "issuer" : "",
       "credentialStatus" : {
          "statusPurpose" : "",
          "statusListIndex" : 3,
          "id" : "",
          "type" : "",
          "statusListCredential" : ""
       }
    }
}"#;
}
