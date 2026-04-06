// Code used to generate the ICAO9303 TD3 DG1 valid examples. Copy paste in
// static_specs.rs and run cargo test to execute.

#[cfg(test)]
mod gen_exs {
    /// Assigns the value a byte will take in the checksum linear combination.
    fn assign_byte_value(b: u8) -> u8 {
        if b == b'<' {
            0
        } else if b.is_ascii_digit() {
            b - b'0'
        } else if b.is_ascii_uppercase() {
            b - b'A' + 10
        } else {
            panic!("unexpected passport byte")
        }
    }

    /// Computes the checksum associated to a sequence of bytes.
    fn checksum(s: &str) -> String {
        s.bytes()
            .map(assign_byte_value)
            .zip([7, 3, 1].iter().cycle())
            .fold(0, |accu, (byte, weight)| {
                (accu + (byte as usize) * *weight) % 10
            })
            .to_string()
    }

    #[derive(Clone)]
    struct PassportData {
        ptype: String,
        country: String,
        surname: String,
        given_names: String,
        number: String,
        citizenship: String,
        dob: String,
        sex: String,
        expiry: String,
        optional: String,
    }

    fn optional_padded(p: PassportData) -> String {
        assert!(p.optional.len() <= 14);
        let padding = "<".repeat(14 - p.optional.len());
        [p.optional, padding].concat()
    }
    fn generate_line1(p: PassportData) -> String {
        let prefix = [p.ptype, p.country, p.surname].concat();
        assert!(prefix.len() <= 44);
        let sep = if prefix.len() == 44 && p.given_names.is_empty() {
            ""
        } else {
            "<<"
        }
        .to_string();
        let prefix = [prefix, sep, p.given_names].concat();
        assert!(prefix.len() <= 44);
        let padding = "<".repeat(44 - prefix.len());
        [prefix, padding].concat()
    }

    fn generate_line2(p: PassportData) -> String {
        let pos_0_10 = [p.number.clone(), checksum(&p.number)].concat();
        let pos_13_20 = [p.dob.clone(), checksum(&p.dob)].concat();
        let pos_21_28 = [p.expiry.clone(), checksum(&p.expiry)].concat();
        let optional = optional_padded(p.clone());
        let pos_28_43 = [optional.clone(), checksum(&optional)].concat();
        [
            pos_0_10.clone(),
            p.citizenship,
            pos_13_20.clone(),
            p.sex,
            pos_21_28.clone(),
            pos_28_43.clone(),
            checksum(&[pos_0_10, pos_13_20, pos_21_28, pos_28_43].concat()),
        ]
        .concat()
    }

    fn mrz(p: PassportData) {
        println!("{}\n{}", generate_line1(p.clone()), generate_line2(p))
    }

    #[test]
    fn gen_mrz() {
        let p1 = PassportData {
            ptype: "PP".to_string(),
            country: "JPN".to_string(),
            surname: "OKABE".to_string(),
            given_names: "RINTARO".to_string(),
            number: "12AB34567".to_string(),
            citizenship: "JPN".to_string(),
            dob: "911214".to_string(),
            sex: "M".to_string(),
            expiry: "310101".to_string(),
            optional: "EL<PSY<CONGROO".to_string(),
        };
        let p2 = PassportData {
            ptype: "PE".to_string(),
            country: "ESP".to_string(),
            surname: "DE<LA<CRUZ".to_string(),
            given_names: "MARIA".to_string(),
            number: "UH87G9901".to_string(),
            citizenship: "ESP".to_string(),
            dob: "911214".to_string(),
            sex: "F".to_string(),
            expiry: "310101".to_string(),
            optional: "XXV789".to_string(),
        };
        let p3 = PassportData {
            ptype: "PD".to_string(),
            country: "MDG".to_string(),
            surname: "ANDRIANAMPOINIMERINATOMPOLOINDRINDRA".to_string(),
            given_names: "R".to_string(),
            number: "BDL3820HR".to_string(),
            citizenship: "FRA".to_string(),
            dob: "450101".to_string(),
            sex: "<".to_string(),
            expiry: "600101".to_string(),
            optional: "".to_string(),
        };
        let p4 = PassportData {
            ptype: "PO".to_string(),
            country: "FRA".to_string(),
            surname: "NOOO<WAY<I<GOT<A<TRUNCATED<MONONYM<RIGH".to_string(),
            given_names: "".to_string(),
            number: "AAAAAAAAA".to_string(),
            citizenship: "FRA".to_string(),
            dob: "990101".to_string(),
            sex: "<".to_string(),
            expiry: "300101".to_string(),
            optional: "".to_string(),
        };
        let p5 = PassportData {
            ptype: "PR".to_string(),
            country: "USA".to_string(),
            surname: "ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ".to_string(),
            given_names: "".to_string(),
            number: "PPPPPPPPP".to_string(),
            citizenship: "USA".to_string(),
            dob: "990101".to_string(),
            sex: "M".to_string(),
            expiry: "300102".to_string(),
            optional: "".to_string(),
        };
        for p in [p1, p2, p3, p4, p5] {
            mrz(p);
            println!(" ")
        }
    }
}
