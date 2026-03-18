use super::super::regex::{Regex, RegexInstructions};

/// Regex formalising the spec of `StdLibParser::Icao9309Td3Dg1`.
pub(super) fn spec_icao9303_td3_dg1() -> Regex {
    // The list of all tolerated passport types. Consulted at this document, Section
    // 4.4, on Jan. 14, 2026:
    // https://www.icao.int/sites/default/files/publications/DocSeries/9303_p4_cons_en.pdf
    // Marked as 1.
    let passport_type = Regex::union([
        "P<".into(), // Legacy denomination of `PP`, before Jan. 2026.
        "PP".into(), // National/Ordinary passport.
        "PE".into(), // Emergency passport.
        "PD".into(), // Diplomatic passport.
        "PO".into(), // Official/Service passport.
        "PR".into(), // Refugee passport.
        "PT".into(), // Alien passport.
        "PS".into(), // Stateless passport.
        "PL".into(), // Laissez-passez passport.
        "PM".into(), // Military passport.
        "PU".into(), /* Emergency travel document. See: https://www.icao.int/sites/default/files/publications/DocSeries/9303_p8_cons_en.pdf */
    ]).mark(&|_| Some(1));
    // A non-empty sequence of uppercase letters, marked with `marker`.
    let name_block = |marker: usize| -> Regex {
        Regex::uppercase_letter().non_empty_list().mark(&|_| Some(marker))
    };
    // One uppercase letter or a digit, marked with `marker`.
    let alphanum = |marker: usize| -> Regex {
        Regex::byte_from((b'A'..=b'Z').chain(b'0'..=b'9')).mark(&|_| Some(marker))
    };
    // A date marked with marker, in YYMMDD format.
    let date = |marker: usize| -> Regex { Regex::digit().mark(&|_| Some(marker)).repeat(6) };
    // Any passport character.
    let any = Regex::byte_from((b'A'..=b'Z').chain(b'0'..=b'9').chain(std::iter::once(b'<')));

    // Example to illustrate the code below:
    // P<FRADUPONT<<JEAN<MICHEL<<<<<<<<<<<<<<<<<<<<
    // 12AB345678FRA7408122M3101012<<<<<<<<<<<<<<04

    // Mandatory part of the first line of the DG1 (passport type, issuer, surname).
    // The separators `<` are not marked.
    let line1_prefix = Regex::cat([
        passport_type,
        Regex::uppercase_letter().mark(&|_| Some(2)).repeat(3),
        name_block(3).separated_non_empty_list("<".into()),
    ]);
    // Given names in the first line of the DG1, prefixed with the separator. The
    // separators `<` are not marked.
    let given_names = Regex::cat([
        "<<".into(),
        name_block(4).separated_non_empty_list("<".into()),
    ]);
    // The part of the first line following `line1_prefix`. Considers cases where
    // given names are present or not.
    let line1_suffix = given_names.optional().terminated(Regex::word("<").list());
    // The full first line, with the length constraint.
    let line1 = line1_prefix.terminated(line1_suffix).and(any.clone().repeat(44));

    // The second line of the DG1. All fields are length constrained.
    let line2 = Regex::cat([
        alphanum(5).repeat(9),
        Regex::digit(), // Unmarked checksum.
        Regex::uppercase_letter().mark(&|_| Some(6)).repeat(3),
        date(7),
        Regex::digit(), // Unmarked checksum.
        Regex::byte_from([b'<', b'M', b'F']).mark(&|_| Some(8)),
        date(9),
        Regex::digit(), // Unmarked checksum.
        any.repeat(14).mark(&|_| Some(10)),
        Regex::digit().repeat(2), // Unmarked checksum.
    ]);

    // Concatenating the two lines, without a newline character.
    line1.terminated(line2)
}

#[cfg(test)]
pub(super) fn test_dg1(
    spec_library: &rustc_hash::FxHashMap<super::StdLibParser, super::super::automaton::Automaton>,
) {
    use super::StdLibParser;

    let accepted_raw: Vec<&[u8]> = include_str!("examples/icao9303_td3_dg1/valid_credentials.txt")
        .lines()
        .map(|l| l.as_bytes())
        .collect();
    let accepted: Vec<super::super::MarkerTestVector<'_>> = vec![
        (
            accepted_raw[0],
            &[
                (1, b"PP"),
                (2, b"JPN"),
                (3, b"OKABE"),
                (4, b"RINTARO"),
                (5, b"12AB34567"),
                (6, b"JPN"),
                (7, b"911214"),
                (8, b"M"),
                (9, b"310101"),
                (10, b"EL<PSY<CONGROO"),
            ],
        ),
        (
            accepted_raw[1],
            &[
                (1, b"PE"),
                (2, b"ESP"),
                (3, b"DELACRUZ"),
                (4, b"MARIA"),
                (5, b"UH87G9901"),
                (6, b"ESP"),
                (7, b"911214"),
                (8, b"F"),
                (9, b"310101"),
                (10, b"XXV789<<<<<<<<"),
            ],
        ),
        (
            accepted_raw[2],
            &[
                (1, b"PD"),
                (2, b"MDG"),
                (3, b"ANDRIANAMPOINIMERINATOMPOLOINDRINDRA"),
                (4, b"R"),
                (5, b"BDL3820HR"),
                (6, b"FRA"),
                (7, b"450101"),
                (8, b"<"),
                (9, b"600101"),
                (10, b"<<<<<<<<<<<<<<"),
            ],
        ),
        (
            accepted_raw[3],
            &[
                (1, b"PO"),
                (2, b"FRA"),
                (3, b"NOOOWAYIGOTATRUNCATEDMONONYMRIGH"),
                (5, b"AAAAAAAAA"),
                (6, b"FRA"),
                (7, b"990101"),
                (8, b"<"),
                (9, b"300101"),
                (10, b"<<<<<<<<<<<<<<"),
            ],
        ),
        (
            accepted_raw[4],
            &[
                (1, b"PR"),
                (2, b"USA"),
                (3, b"ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ"),
                (5, b"PPPPPPPPP"),
                (6, b"USA"),
                (7, b"990101"),
                (8, b"M"),
                (9, b"300102"),
                (10, b"<<<<<<<<<<<<<<"),
            ],
        ),
    ];
    let rejected: Vec<&[u8]> = include_str!("examples/icao9303_td3_dg1/invalid_credentials.txt")
        .lines()
        .map(|l| l.as_bytes())
        .collect();
    super::tests::specs_one_test_with_markers(
        spec_library,
        StdLibParser::Icao9309Td3Dg1,
        &accepted,
        &rejected,
    );
}
