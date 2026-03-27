//! Example: passport verification circuit (SHA-256 + RSA-2048).
//!
//! Loads test credentials from `examples/passport/credentials/`,
//! runs the full verification chain, and prints timing information.
//!
//! Usage:
//!     cargo run --example passport_verification --release

use std::{io::Write, path::Path, time::Instant};

use midnight_circuits::instructions::map::MapCPU;
use midnight_zk_stdlib::utils::plonk_api::filecoin_srs;
use rand::rngs::OsRng;

// The passport modules are compiled via #[path] since Cargo examples
// don't use the normal module system.
#[path = "./mod.rs"]
mod passport;

use passport::circuit::PassportVerification;

use crate::passport::{
    circuit::{CSCA_PATH, CSCA_REGISTRY},
    spec::{
        DG1_DOB, DG1_DOC_TYPE, DG1_EXPIRY, DG1_ISSUING_COUNTRY, DG1_NAME, DG1_NATIONALITY,
        DG1_PASSPORT_NUMBER, DG1_SEX,
    },
};

/// Path to the credentials directory, relative to the zk_stdlib crate root.
const CRED_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/examples/passport/credentials");

fn load_credential(name: &str) -> (Vec<u8>, [u8; 93], [u8; 256]) {
    let dir = Path::new(CRED_DIR).join(name);
    let sod = std::fs::read(dir.join("sod.der"))
        .unwrap_or_else(|e| panic!("Failed to read {name}/sod.der: {e}"));
    let dg1: [u8; 93] = std::fs::read(dir.join("dg1.bin"))
        .unwrap_or_else(|e| panic!("Failed to read {name}/dg1.bin: {e}"))
        .try_into()
        .expect("DG1 must be 93 bytes");
    let csca_key: [u8; 256] = std::fs::read(dir.join("csca_key.bin"))
        .unwrap_or_else(|e| panic!("Failed to read {name}/csca_key.bin: {e}"))
        .try_into()
        .expect("CSCA key must be 256 bytes");
    (sod, dg1, csca_key)
}

/// Prints a messahe, run a command, and then display its execution time and
/// returns the function result.
fn perf_run<A>(msg: &str, f: impl FnOnce() -> A) -> A {
    print!("> {msg}...");
    let _ = std::io::stdout().flush();
    let t = Instant::now();
    let res = f();
    println!(" done ({:?})", t.elapsed());
    res
}

fn main() {
    // The full passport circuit is large enough to overflow the default
    // thread stack during synthesis. Run on a thread with a larger stack.
    let builder = std::thread::Builder::new().stack_size(64 * 1024 * 1024);
    let handler = builder.spawn(run).expect("failed to spawn thread");
    handler.join().expect("thread panicked");
}

fn run() {
    // Use credential_1 as the default test case.
    let cred_name = std::env::args().nth(1).unwrap_or_else(|| "credential_1".to_string());
    println!("=== Passport verification example ===");
    println!("Credential: {cred_name}\n");

    let (sod, dg1, csca_key) = load_credential(&cred_name);
    let mrz = &dg1[5..]; // Skip the DG1 TLV header (5 bytes).
    println!(
        "MRZ line 1: {}",
        std::str::from_utf8(&mrz[..44]).unwrap_or("?")
    );
    println!(
        "MRZ line 2: {}",
        std::str::from_utf8(&mrz[44..]).unwrap_or("?")
    );

    // Show extracted MRZ fields using the spec constants.
    let field = |r: std::ops::Range<usize>| std::str::from_utf8(&dg1[r]).unwrap_or("?");
    let name: &str = &field(DG1_NAME).replace("<<", " ").replace("<", " ");
    println!("  Name:        {}", name);
    println!("  DOB:         {}", field(DG1_DOB));
    println!("  Sex:         {}", field(DG1_SEX));
    println!("  Nationality: {}", field(DG1_NATIONALITY));
    println!("  Passport #:  {}", field(DG1_PASSPORT_NUMBER));
    println!("  Doc type:    {}", field(DG1_DOC_TYPE));
    println!("  Issuer:      {}", field(DG1_ISSUING_COUNTRY));
    println!("  Expiry:      {}", field(DG1_EXPIRY));
    println!("SOD size: {} bytes\n", sod.len());

    // Generates the witness, including the CSCA Merkle tree map.
    let witness = perf_run("Generating witness", || {
        PassportVerification::generate_witness(sod, dg1, csca_key)
    });
    println!(
        "  -> NB: Includes a CSCA issuer whitelist ({} entries, from {})",
        CSCA_REGISTRY.lines().count() / 2,
        CSCA_PATH
    );
    let instance = witness.3.succinct_repr();
    let relation = PassportVerification;

    // Setup.
    let k = perf_run("For reference: computing optimal size param k", || {
        midnight_zk_stdlib::optimal_k(&relation)
    });
    println!("  -> k = {k}");
    let srs = perf_run("Loading SRS", || filecoin_srs(k));

    let vk = perf_run("Setting up VK", || {
        midnight_zk_stdlib::setup_vk(&srs, &relation)
    });

    let pk = perf_run("Setting up PK", || {
        midnight_zk_stdlib::setup_pk(&relation, &vk)
    });

    // Proof.
    let proof = perf_run("Generating identity proof", || {
        midnight_zk_stdlib::prove::<PassportVerification, blake2b_simd::State>(
            &srs, &pk, &relation, &instance, witness, OsRng,
        )
        .expect("Proof generation should not fail")
    });

    // Verification.
    perf_run("Verifying credential", || {
        midnight_zk_stdlib::verify::<PassportVerification, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof,
        )
        .expect("Verification should not fail");
    });

    println!("\nAll checks passed!");
}
