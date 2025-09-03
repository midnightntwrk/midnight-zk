use std::collections::HashMap;

use super::{
    automaton::Automaton,
    regex::{Regex, RegexInstructions},
};

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
    ///         nationalId: string,
    ///         familyName: string,
    ///         givenName: string,  # marked "1"
    ///         publicKeyJwk: {
    ///           kty: string,
    ///           crv: string,
    ///           x: string, # marked "3"
    ///           y: string  # marked "4"
    ///         }
    ///         id: string,
    ///         birthDate: string,  # marked "2"
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
    ///   - `"givenName"` -> 1
    ///   - `"birthDate"` -> 2
    ///   - `"x"` -> 3
    ///   - `"y"` -> 4
    Jwt,
}

// Regex formalising the spec of `StdLIbParser::Jwt`.
fn spec_jwt() -> Regex {
    // A json field, with possible white spaces.
    let field = |name: &str, content: Regex| -> Regex {
        Regex::spaced_cat([format!("\"{name}\"").into(), ":".into(), content])
    };
    let string_field =
        |name: &str, marker: usize| -> Regex { field(name, Regex::json_string(marker)) };
    let int_field = |name: &str| -> Regex { field(name, Regex::digit().non_empty_list()) };

    // A collection of regular expressions, delimited by `opening` and `closing`,
    // and separated by commas. Arbitrary white spaces are allowed between the
    // delimiters and the various items.
    let collec = |opening: &str, items: Vec<Regex>, closing: &str| -> Regex {
        Regex::spaced_separated_cat(items, ",".into())
            .spaced_delimited(opening.into(), closing.into())
    };

    // A JSON list of strings.
    let string_list = Regex::json_string(0)
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
                string_field("x", 3),
                string_field("y", 4),
            ],
            "}",
        ),
    );
    let credential_subject = field(
        "credentialSubject",
        collec(
            "{",
            vec![
                string_field("nationalId", 0),
                string_field("familyName", 0),
                string_field("givenName", 1), // Marked 1.
                public_key_jwk,
                string_field("id", 0),
                string_field("birthDate", 2), // Marked 2.
            ],
            "}",
        ),
    );
    let issuer = field(
        "issuer",
        Regex::union([
            Regex::json_string(0),
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

/// All automata that can be used as a parsing basis in the standard
/// library.
pub fn spec_library() -> HashMap<StdLibParser, Automaton> {
    let specs = [(StdLibParser::Jwt, spec_jwt())];
    specs
        .iter()
        .map(|(name, regex)| (*name, regex.to_automaton()))
        .collect::<HashMap<_, _>>()
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, time::Instant};

    use super::{StdLibParser, StdLibParser::Jwt};
    use crate::parsing::{automaton::Automaton, spec_library};

    // Tests whether a given regular expression accepts or rejects two sets of
    // corresponding strings. For accepted strings, checks the list of outputs for
    // each markers.
    fn specs_one_test(
        spec_library: &HashMap<StdLibParser, Automaton>,
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
            let mut outputs = HashMap::new();
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
                    let mut outputs = HashMap::new();
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
        println!(">> Configuring the spec library...");
        if cfg!(debug_assertions) {
            println!("WARNING: Running in debug mode, this may take a while!");
        }
        let start = Instant::now();
        let spec_library = spec_library();
        println!(">> Configuration completed in {:?}", start.elapsed());
        for (name, automaton) in &spec_library {
            println!(
                "  - {:?} automaton: {} states, {} transitions",
                name,
                automaton.state_bound,
                automaton.transitions.len()
            )
        }
        let accepted0: Vec<(&str, &[(usize, &str)])> = vec![
            (
                FULL_INPUT_JWT,
                &[
                    (1, "Alice"),
                    (2, "2000-11-13"),
                    (3, "S0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8M"),
                    (4, "dux8h-QcIA3aZG9CSPIltDwVvOkf0kfJRJLH7K1KSlQ"),
                ],
            ),
            (MINIMAL_JWT, &[(1, "A"), (2, "B"), (3, "x"), (4, "y")]),
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
          "nationalId" : "12345",
          "familyName" : "",
          "givenName" : "A",
          "publicKeyJwk" : {
             "kty" : "",
             "crv" : "",
             "x" : "x",
             "y" : "y"
          },
          "id" : "",
          "birthDate" : "B"
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
