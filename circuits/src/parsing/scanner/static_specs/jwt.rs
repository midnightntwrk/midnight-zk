use super::super::regex::{Regex, RegexInstructions};

/// Regex formalising the spec of `StdLibParser::Jwt`.
pub(super) fn spec_jwt() -> Regex {
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
pub(super) fn test_jwt(
    spec_library: &rustc_hash::FxHashMap<super::StdLibParser, super::super::automaton::Automaton>,
) {
    use super::StdLibParser;

    const FULL_INPUT_JWT: &[u8] = include_str!("examples/jwt/full.txt").as_bytes();
    const MINIMAL_JWT: &[u8] = include_str!("examples/jwt/minimal.txt").as_bytes();
    let accepted: Vec<super::super::MarkerTestVector<'_>> = vec![
        (
            FULL_INPUT_JWT,
            &[
                (1, b"12345"),
                (2, b"Wonderland"),
                (3, b"Alice"),
                (4, b"2000-11-13"),
                (5, b"S0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8M"),
                (6, b"dux8h-QcIA3aZG9CSPIltDwVvOkf0kfJRJLH7K1KSlQ"),
            ],
        ),
        (
            MINIMAL_JWT,
            &[
                (1, b"id"),
                (2, b"fn"),
                (3, b"gn"),
                (4, b"bd"),
                (5, b"x"),
                (6, b"y"),
            ],
        ),
    ];
    let rejected: Vec<&[u8]> = vec![b"hello world", &FULL_INPUT_JWT[..1000], &MINIMAL_JWT[..600]];
    super::tests::specs_one_test_with_markers(
        spec_library,
        StdLibParser::Jwt,
        &accepted,
        &rejected,
    );
}
