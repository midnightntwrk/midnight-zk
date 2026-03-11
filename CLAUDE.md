# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Midnight ZK implements the zero-knowledge proof system for **Midnight**, built on PLONK with KZG commitments over BLS12-381. It is a Rust workspace with 7 crates organized in a layered architecture.

## Build & Test Commands

**Rust toolchain:** 1.90.0 (pinned in `rust-toolchain.toml`). Formatting uses nightly.

```bash
# Build entire workspace
cargo build --release

# Test individual crates (always use --release for proof system crates)
cargo test -p midnight-curves --release --all-features
cargo test -p midnight-proofs --release
cargo test -p midnight-circuits --release
cargo test -p midnight-zk-stdlib --release -- --skip serialization
cargo test -p midnight-zk-stdlib --release --test serialization -- --test-threads=1
cargo test -p midnight-aggregation --release --all-features
cargo test -p midnight-zkir --release --all-features

# Run a single test
cargo test -p <package> --release <test_name>

# Lint and format
cargo clippy --all-targets --all-features -- -Dwarnings
cargo clippy -p midnight-aggregation --all-targets --all-features -- -Dwarnings
cargo +nightly fmt --all -- --check

# Check docs
cargo doc --workspace --document-private-items --no-deps

# Update goldenfiles (run locally, commit changes)
cargo test -p midnight-zk-stdlib --release -- --ignored

# Run benchmarks (e.g., curves, proofs, circuits, zk_stdlib)
cargo bench -p midnight-curves
cargo bench -p midnight-proofs
```

**CI-specific:** Tests for circuits and zk_stdlib set `RUSTFLAGS=--cfg ci_build` to use portable BLST. zk_stdlib tests require an SRS file at `zk_stdlib/examples/assets/bls_filecoin_2p19`.

## Architecture

**Layer 1 — Curves** (`curves/`, crate: `midnight-curves`):
BLS12-381 pairing curve, JubJub Edwards curve, secp256k1, Curve25519. BN256/Pasta curves available behind `dev-curves` feature. Contains field arithmetic, FFT, and multi-scalar multiplication.

**Layer 2 — Proof System** (`proofs/`, crate: `midnight-proofs`):
PLONK prover/verifier with KZG polynomial commitments, Fiat-Shamir transcript, linearization (reduced proof size), logup lookup tables with selectors, permutation arguments, and committed instances support.

**Layer 3 — Circuits** (`circuits/`, crate: `midnight-circuits`):
Gadgets/chips for field arithmetic (native + foreign), ECC operations, hashing (SHA2, Poseidon, Keccak, Blake2b, RIPEMD), big integers, range checks, base64/automaton parsing, vectors, and maps.

**Layer 4 — Standard Library** (`zk_stdlib/`, crate: `midnight-zk-stdlib`):
Fixed-configuration circuit architecture combining all chips. The fixed config enables recursion (same verification logic) and verifier optimization. Contains example circuits for identity credentials.

**Aggregation** (`aggregation/`, crate: `midnight-aggregation`):
Incremental verifiable computation (IVC) and light aggregation for recursive proof composition.

**ZKIR** (`zkir/`, crate: `midnight-zkir`):
Intermediate representation parser for circuit definitions. Parses ZKIR relations into executable circuits.

**VROOM MSM** (`vroom-msm-sys/`, crate: `vroom-msm-sys`):
C++ FFI wrapper providing an optimized multi-scalar multiplication implementation for benchmarking against the native Rust MSM.

### Dependency Order
```
curves → proofs → circuits → zk_stdlib → aggregation
                                       → zkir
```

## Key Feature Flags

- `dev-curves` — Enables BN256/Pasta test curves
- `truncated-challenges` — Modifies challenge computation in proofs and circuits
- `committed-instances` — Enables committed instance handling in verifier
- `blst/portable` — Portable BLST (used in CI via `--cfg ci_build`)

## Testing Notes

- zk_stdlib serialization tests must run single-threaded (`--test-threads=1`)
- zk_stdlib goldenfiles in `zk_stdlib/goldenfiles/examples/` are regression-checked in CI; regenerate with `cargo test -p midnight-zk-stdlib --release -- --ignored` and commit changes
- proofs benchmarks require `libfontconfig1-dev` on Linux (for chart generation)
- Most tests are slow; always use `--release`
- The workspace Cargo.toml patches `crates-io` and the GitHub remote to use local paths for `midnight-proofs`, `midnight-curves`, and `midnight-circuits` — this ensures all crates resolve to the local workspace versions

## License Header

New source files must include the Apache-2.0 license header:
```
// This file is part of midnight-zk.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
```

## Taking notes

When required to take notes with regard to the conversation, write the conversation contents into a markdown file with the specified name under the folder `./notes`.