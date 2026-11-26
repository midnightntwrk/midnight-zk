//! Builds the delta bases of an SRS, which the KZG prover commits with, and
//! stores them next to the SRS. From then on, `load_srs` reads them instead of
//! having the first proof build them.
//!
//! The SRS is looked for in `$SRS_DIR`, by default `./examples/assets`:
//!
//! ```text
//! cargo run --release --example precompute_delta_bases -- <filecoin|midnight> <k>...
//! ```

use midnight_zk_stdlib::utils::plonk_api::{SrsSource, precompute_delta_bases};

const USAGE: &str = "usage: precompute_delta_bases <filecoin|midnight> <k>...";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [source, ks @ ..] = &args[..] else {
        panic!("{USAGE}")
    };
    assert!(!ks.is_empty(), "{USAGE}");

    for k in ks {
        let k: u32 = k.parse().unwrap_or_else(|_| panic!("{USAGE}"));
        let source = match source.as_str() {
            "filecoin" => SrsSource::Filecoin,
            "midnight" => SrsSource::Midnight,
            _ => panic!("{USAGE}"),
        };
        let path = precompute_delta_bases(source, k);
        println!("Stored the delta bases of the SRS of size 2^{k} at {path}");
    }
}
