//! Midnight ZK Extractor Binary
//!
//! This binary provides extraction functionality for Midnight ZK circuits.
//! Build with: cargo build --release --features extraction

use std::env;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Midnight ZK Extractor");
        eprintln!();
        eprintln!("Usage: {} <command> [options]", args[0]);
        eprintln!();
        eprintln!("Commands:");
        eprintln!("  help     Show this help message");
        eprintln!("  version  Show version information");
        eprintln!();
        eprintln!("This binary is built with extraction support enabled.");
        process::exit(1);
    }

    match args[1].as_str() {
        "help" | "--help" | "-h" => {
            println!("Midnight ZK Extractor");
            println!();
            println!("Usage: {} <command> [options]", args[0]);
            println!();
            println!("Commands:");
            println!("  help     Show this help message");
            println!("  version  Show version information");
        }
        "version" | "--version" | "-v" => {
            println!("midnight-extractor {}", env!("CARGO_PKG_VERSION"));
        }
        cmd => {
            eprintln!("Unknown command: {}", cmd);
            eprintln!("Run '{} help' for usage information", args[0]);
            process::exit(1);
        }
    }
}
