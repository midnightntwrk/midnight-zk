# Compact suite

The Compact suite proves real Compact contracts through the same calls that
the Midnight proof server makes. It measures the CPU prover and the GPU prover
on the same jobs and checks every GPU proof with the stock verifier. The
runner and its full reference are in
[`gpu-prover/bench/compact/`](../../gpu-prover/bench/compact/README.md). The results are in
[benchmarks.md](benchmarks.md).

## 1. Programs

[`suite.json`](../../gpu-prover/bench/compact/suite.json) pins every source file by
repository, commit and SHA-256. The suite has 33 programs:

- 30 programs are fetched by [`fetch-suite.sh`](../../gpu-prover/bench/compact/fetch-suite.sh)
  from Apache-2.0 sources: LFDT-Minokawa/compact and the midnightntwrk example
  repositories. The tree holds no copy of their sources.
- 3 programs (`s01-natives`, `s02-foreign`, `s03-language`) were written for
  the suite. They are excluded until they have a license.

`suite.json` also records three programs that are left out for other reasons:
`w01-disclose-vector` (a test that must not compile), `d05-kitties` (GPL-3.0,
and it needs an external library) and `d07-zkloan` (does not compile with
language 0.28.0).

Three fetched files get a small patch after the SHA-256 check
([`patches/README.md`](../../gpu-prover/bench/compact/patches/README.md)). Two change an exact language
pragma to `>=`. One adds a constructor to the election example, so that its
authorized circuits can be proved.

## 2. Circuits and calls

A job is one proof: a proof preimage plus the key material of its circuit. Of
the 30 fetched programs, 24 have at least one accepted proving call. The others
have only pure circuits, or every scenario call fails an assertion. The 24
programs give 133 proofs. Three calls of `x01-composable-outer` are
cross-contract calls: each makes an outer proof and a callee proof.

| Program | Circuits proved | Calls | Proofs | k |
|---|---:|---:|---:|---|
| t01-tiny | 3 | 5 | 5 | 7, 13 |
| t02-counter-example | 1 | 1 | 1 | 6 |
| t03-counter-compiler | 1 | 1 | 1 | 6 |
| t04-welcome | 3 | 6 | 6 | 6, 13 |
| a01-adt-counter | 2 | 2 | 2 | 7, 8 |
| a02-set-field | 1 | 1 | 1 | 8 |
| a03-map-field-field | 1 | 1 | 1 | 8 |
| a04-map-bool-map-counter | 1 | 1 | 1 | 7 |
| a05-list-field | 1 | 1 | 1 | 10 |
| a08-kernel | 1 | 1 | 1 | 8 |
| w02-bboard-testcenter | 2 | 4 | 4 | 13 |
| h03-election-ctor | 5 | 13 | 13 | 13, 14 |
| z01-zerocash | 2 | 4 | 4 | 13, 15 |
| z02-unshielded-tokens | 19 | 19 | 19 | 8, 9, 13, 14, 15 |
| z03-block-time | 4 | 4 | 4 | 7 |
| z04-set-qualified-coin | 2 | 3 | 3 | 9, 14 |
| j02-schnorr | 1 | 2 | 2 | 11 |
| d01-example-bboard | 2 | 4 | 4 | 13 |
| d02-battleship | 5 | 11 | 11 | 13, 14 |
| d03-micro-dao | 7 | 18 | 18 | 13, 14, 15, 16 |
| d04-coracle | 4 | 6 | 6 | 14, 16, 17 |
| d06-nft | 11 | 15 | 15 | 7, 8, 9, 10, 13 |
| x01-composable-outer | 6 | 6 | 9 | 6, 7, 8 |
| x02-composable-inner | 1 | 1 | 1 | 7 |

Programs with no accepted proving call: `a06-merkletree-field` and
`a07-historic-merkletree` (the scenario call fails its assertion),
`h01-election` (no constructor), and `h02-external-hashes`,
`j01-jubjub-point` and `j03-ecdsa` (pure circuits only).

## 3. k distribution

| k | 6 | 7 | 8 | 9 | 10 | 11 | 13 | 14 | 15 | 16 | 17 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Proofs | 7 | 15 | 14 | 9 | 3 | 2 | 47 | 16 | 8 | 11 | 1 |

## 4. Reproduce

The runner is a separate cargo workspace with its own `Cargo.lock` and
`rust-toolchain.toml`. The proof server 9.0.1 stack builds on midnight-proofs
0.8.x and needs rustc 1.95 or newer, so the runner is not a member of the root
workspace.

1. Fetch and build the programs. The script fetches compactc 0.36.0 (language
   0.28.0) as a release archive and checks its SHA-256:

   ```sh
   cd gpu-prover/bench/compact
   ./fetch-suite.sh
   ```

2. Build the CPU runner, and the GPU runner from a hooked midnight-proofs
   0.8.3 and a backend crate:

   ```sh
   scripts/build.sh stock
   scripts/build.sh hooked PATH/TO/midnight-proofs-0.8.3-hooked PATH/TO/compact-bench-gpu
   ```

3. Put the KZG parameters `bls_midnight_2p{k}` for k = 6 to 17 from
   `https://srs.midnight.network/` into one directory.
4. Make the jobs from a call set and check each preimage:

   ```sh
   scripts/make-jobs.py --calls CALLS_DIR --build work/build --out jobs.jsonl
   target/stock/release/compact-bench check --jobs jobs.jsonl --params PARAMS_DIR
   ```

5. Run the timed CPU set, the GPU set and the stock verification of every GPU
   proof, then make the comparison table. The commands are in step 7 of the
   [runner README](../../gpu-prover/bench/compact/README.md#reproduce).

A run is resumable. It skips every repetition that is already in the raw
file. With `--lock FILE` the runner takes the device lock before each proof.

## 5. What is not in the pull request

- **Proof preimages.** The preimages hold witness values, so they are not
  committed. The README gives the format and the steps to make them.
- **The scenario driver.** The scripts that run the calls of each program
  with the generated JavaScript and `@midnight-ntwrk/compact-runtime` 0.21.0
  are not in the tree yet.
- **The 0.8.3 backport.** The hooked midnight-proofs 0.8.3 and its CUDA
  backend are not in the pull request. The pull request carries the same
  design on midnight-proofs 0.9.0-rc.1. `gpu-backend-stub/` gives the backend
  API that `scripts/build.sh` expects.
