# Compact proof benchmark

Real Compact contracts, proved through the same calls that the Midnight proof server makes, on
the CPU (stock midnight-proofs 0.8.3) and with the GPU prover (midnight-proofs 0.8.3 with the
GPU hooks). Every proof is checked with the stock verifier.

This directory is a standalone cargo workspace with its own `Cargo.lock` and
`rust-toolchain.toml`. It is not a member of the root workspace: the proof server 9.0.1 stack
(midnight-ledger tag `proof-server-9.0.1`, midnight-zkir 3.2.0, zk-stdlib 2.4.0) builds on
midnight-proofs 0.8.x, not on the 0.9 crates of this repository, and it needs rustc 1.95 or
newer.

## What is proved

The proof server receives a proof preimage and the key material of a circuit
(`ProvingKeyMaterial`: prover key, verifier key, ZKIR). Its call path is
`ProofPreimage::prove` -> `midnight_zkir::IrSource::prove` -> zk-stdlib `prove` ->
`midnight_proofs::plonk::create_proof`, followed by a self-check with the verifier key.

`compact-bench` makes the same calls in the same order, with three differences that keep fixed
costs out of the timed region:

- It decodes the key material once per proof and initializes the prover key before the clock
  starts (`key_load_s`, reported apart).
- It reads the KZG parameters `bls_midnight_2p{k}` once and keeps them in memory.
- It times the prover call (`IrSource::prove`: witness generation and `create_proof`,
  `prove_s`) and the verification (`verify_s`) separately. Each proof is verified twice: with
  verifier parameters from the `k` file (the proof server's self-check) and with the ledger's
  embedded verifier parameters (`PARAMS_VERIFIER`). `verified` is true only when both accept.

The prover RNG is ChaCha20 seeded from the job name. This does not make every proof
reproducible:

- For 39 of the 133 proofs (k 6 to 10) all repetitions gave the same bytes. The bytes changed
  with `RAYON_NUM_THREADS`; with the same thread count, one k=6 proof gave the same sha256 on
  x86_64 and aarch64.
- For the other 94 proofs (all with k 11 or more, and some with k 7 or 8) the bytes change from
  one repetition to the next, also with one thread. The prover RNG is not the only source of
  randomness: for example, the foreign-curve chip of midnight-circuits 7.3.0
  (`ForeignWeierstrassEccChip::new`) samples a point from `OsRng` for incomplete addition.
  Every proof still verifies.

So the proof sha256 is a byte-identity check between a CPU and a GPU build only for the first
group, with the same thread count. For the other proofs the check is the stock verifier. The
summary prints `varies(n)` for a proof with n different hashes; the raw file has each one.

## Programs

`suite.json` pins every source file by repository, commit and sha256. All programs are
Apache-2.0.

| Program | Source | Proof circuits used | Calls proved | Proofs | k |
|---|---|---:|---:|---:|---|
| t01-tiny | LFDT-Minokawa/compact `examples/tiny.compact` | 3 | 5 | 5 | 7, 13 |
| t02-counter-example | midnightntwrk/example-counter `contract/src/counter.compact` | 1 | 1 | 1 | 6 |
| t03-counter-compiler | LFDT-Minokawa/compact `examples/counter.compact` | 1 | 1 | 1 | 6 |
| t04-welcome | LFDT-Minokawa/compact `test-center/test-contracts/welcome.compact` | 3 | 6 | 6 | 6, 13 |
| a01-adt-counter | LFDT-Minokawa/compact `examples/adt/tests/counter.compact` | 2 | 2 | 2 | 7, 8 |
| a02-set-field | `examples/adt/tests/set_field.compact` | 1 | 1 | 1 | 8 |
| a03-map-field-field | `examples/adt/tests/map_field_field.compact` | 1 | 1 | 1 | 8 |
| a04-map-bool-map-counter | `examples/adt/tests/map_boolean_map_field_counter.compact` | 1 | 1 | 1 | 7 |
| a05-list-field | `examples/adt/tests/list_field.compact` | 1 | 1 | 1 | 10 |
| a06-merkletree-field | `examples/adt/tests/merkletree_field.compact` | 0 | 0 | 0 | (k 15; the scenario call fails its assert) |
| a07-historic-merkletree | `examples/adt/tests/historicmerkletree_field.compact` | 0 | 0 | 0 | (k 15; the scenario call fails its assert) |
| a08-kernel | `examples/adt/tests/kernel.compact` | 1 | 1 | 1 | 8 |
| w02-bboard-testcenter | `test-center/test-contracts/bboard.compact` | 2 | 4 | 4 | 13 |
| h01-election | `examples/election.compact` | 0 | 0 | 0 | (no constructor: every call fails an authorization assert) |
| h02-external-hashes | `examples/external/examples.compact` | 0 | 0 | 0 | (pure circuits only) |
| h03-election-ctor | `examples/election.compact` + patch h03 | 5 | 13 | 13 | 13, 14 |
| z01-zerocash | `examples/zerocash.compact` | 2 | 4 | 4 | 13, 15 |
| z02-unshielded-tokens | `test-center/compact/unshielded-tokens.compact` | 19 | 19 | 19 | 8, 9, 13, 14, 15 |
| z03-block-time | `test-center/compact/block-time.compact` | 4 | 4 | 4 | 7 |
| z04-set-qualified-coin | `examples/adt/tests/set_qualified_coin_info.compact` | 2 | 3 | 3 | 9, 14 |
| j01-jubjub-point | `examples/jubjubpoint/examples.compact` | 0 | 0 | 0 | (pure circuits only) |
| j02-schnorr | `test-center/compact/schnorr.compact` | 1 | 2 | 2 | 11 |
| j03-ecdsa | `examples/ecdsa/example_one.compact` | 0 | 0 | 0 | (pure circuits only) |
| d01-example-bboard | midnightntwrk/example-bboard `contract/src/bboard.compact` + patch d01 | 2 | 4 | 4 | 13 |
| d02-battleship | midnightntwrk/example-battleship `contract/battleship.compact` + patch d02 | 5 | 11 | 11 | 13, 14 |
| d03-micro-dao | LFDT-Minokawa/compact `test-center/test-contracts/micro-dao.compact` | 7 | 18 | 18 | 13, 14, 15, 16 |
| d04-coracle | `test-center/test-contracts/coracle.compact` | 4 | 6 | 6 | 14, 16, 17 |
| d06-nft | midnightntwrk/example-nft-contracts `contracts/nft/src/nft.compact` (+ `modules/Nft.compact`) | 11 | 15 | 15 | 7, 8, 9, 10, 13 |
| x01-composable-outer | LFDT-Minokawa/compact `test-center/composable/Basic/Outer.compact` (+ `Inner.compact`) | 6 | 6 | 9 | 6, 7, 8 |
| x02-composable-inner | `test-center/composable/Basic/Inner.compact` | 1 | 1 | 1 | 7 |

Programs without a repository name are in LFDT-Minokawa/compact. "Proof circuits used" counts
the distinct circuits proved, keyed by the program whose keys prove them. Three x01 calls are
cross-contract calls: each makes an outer proof (x01 keys) and a callee proof (x02 keys), so
x01 has 9 proofs from 6 calls.

Total: 30 programs, 24 of them with at least one accepted proving call, 133 proofs.

k distribution of the 133 proofs:

| k | 6 | 7 | 8 | 9 | 10 | 11 | 13 | 14 | 15 | 16 | 17 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| proofs | 7 | 15 | 14 | 9 | 3 | 2 | 47 | 16 | 8 | 11 | 1 |

Not included:

- s01-natives, s02-foreign, s03-language: written for this suite; excluded until they have a
  license.
- w01-disclose-vector (expected compile error), d05-kitties (GPL-3.0, needs an external
  library), d07-zkloan (does not compile with language 0.28.0).

## Calls

A job is one proof: a proof preimage plus the circuit's key material. The preimages come
from scenario runs: a fixed sequence of calls per program (constructor arguments, witness
values, call arguments), executed with the JavaScript that compactc generates and
`@midnight-ntwrk/compact-runtime` 0.21.0. For each call the run writes a call record
`<program>/transcripts/<label>.json` and, per proof-data entry, the preimage
`<label>.<index>.preimage.bin` (`proofDataIntoSerializedPreimage`, tagged
`midnight:proof-preimage`). The call record gives, per entry, the circuit, the program whose
keys prove it (`zkir_id`), the preimage file name, and the communication commitment `comm`
with its randomness `comm_rand`, as hex of the serialized field elements. Every value is
deterministic: the contract address is the dummy address, and keys, witness values and
`comm_rand` derive from the program id and the call label.

The scenarios and the driver that runs them are not in this directory yet. The preimages
hold witness values, so they are not committed either. To regenerate a call set:

1. Build the programs (`./fetch-suite.sh`).
2. For each program, deploy it with the runtime's dummy address, run its calls in order with
   the generated JavaScript, and for each accepted call write the call record and the
   preimages described above.
3. Check every preimage: `compact-bench check` (below) runs the stock ZKIR check with the
   real `comm` and a control with `comm_rand + 1`, which must be refused.

## Reproduce

```sh
# 1. Programs, patches, compactc 0.36.0 (release archive, sha256 checked), full build with keys.
./fetch-suite.sh                       # WORK=./work by default; COMPACTC=... to use a local compactc

# 2. Runner. CPU baseline:
scripts/build.sh stock                 # target/stock/release/compact-bench
#    GPU build (hooked midnight-proofs 0.8.3 and a backend crate, see patches/README.md):
scripts/build.sh hooked path/to/midnight-proofs-0.8.3-hooked path/to/compact-bench-gpu

# 3. KZG parameters: bls_midnight_2p{k} for k = 6..17 from https://srs.midnight.network/
#    into one directory (the proof server's parameter cache uses the same files).

# 4. Jobs from the call set and the build.
scripts/make-jobs.py --calls CALLS_DIR --build work/build --out jobs.jsonl
target/stock/release/compact-bench check --jobs jobs.jsonl --params PARAMS_DIR

# 5. Timed run: 1 warm-up + 5 timed repetitions per proof, resumable. BENCH_SPLIT=6 runs
#    each of the 6 repetitions in its own process (omit it to run them in one process).
RAYON_NUM_THREADS=$(nproc) BENCH_LOCK=/path/to/gpu.lock BENCH_SPLIT=6 \
  scripts/run-bench.sh target/stock/release/compact-bench jobs.jsonl PARAMS_DIR raw.tsv --reps 5

# 6. One row per proof.
target/stock/release/compact-bench summarize --raw raw.tsv --out results/cpu-<gpu-model>.tsv

# 7. GPU half, same machine and thread count. Statements and reference proofs from the stock
#    build (one run per proof), the timed GPU run with its proofs dumped, then a check of every
#    GPU proof by the stock binary, then the combined table.
scripts/run-bench.sh target/stock/release/compact-bench jobs.jsonl PARAMS_DIR stock-dump.tsv \
  --reps 0 --warmup 1 --dump stock-dump
scripts/run-bench.sh target/hooked/release/compact-bench jobs.jsonl PARAMS_DIR raw-gpu.tsv \
  --reps 5 --dump gpu-dump
target/stock/release/compact-bench verify --jobs jobs.jsonl --params PARAMS_DIR \
  --dump gpu-dump --statements stock-dump --out verify-gpu.tsv
target/hooked/release/compact-bench summarize --raw raw-gpu.tsv --out results/gpu-<gpu-model>.tsv
scripts/compare.py --cpu results/cpu-<gpu-model>.tsv --gpu results/gpu-<gpu-model>.tsv \
  --verify verify-gpu.tsv --out results/compare-<gpu-model>.tsv
```

The comparison rule (`scripts/compare.py`): a proof whose CPU repetitions all give the same
bytes must give the same bytes on the GPU (`bytes-equal`); for every other proof each GPU
repetition must verify under the stock verifier against the statement of the stock run, and
its public inputs must equal that statement (`verified`). The raw GPU rows also count the
device calls per proof (`hits_msm`, `hits_ntt`, `hits_coset`, `hits_quotient`) and the hook
calls that fell back to the CPU (`fallbacks`). A repetition with a fallback is degraded:
`compact-bench prove` writes no row for it and stops with exit code 5.

`compact-bench prove` appends one row per repetition to the raw TSV and skips every
(binary, job, repetition) that is already there, so a stopped run continues where it
stopped. `run-bench.sh` waits for a 1-minute load below `BENCH_MAX_LOAD` (default 2) before
each start, outside any lock. `compact-bench` itself does not wait: it stops with exit code 75
when the load is at or above the gate at start, after a proof during which other processes
kept more than `BENCH_YIELD_FOREIGN` cores busy (default 2), and, with `--lock FILE`, before a
proof when another process holds the lock (it takes the lock before each proof and releases
it after). On exit 75 `run-bench.sh` waits again and resumes. With `BENCH_SPLIT=N` each
repetition runs in its own process (`--rep R`), so other jobs on a shared machine run between
repetitions; a timed repetition alone in a process first runs the job's first proof,
unrecorded, so it sees the same warm state as in a full run. Each row records the load before the proof and `foreign_cores`, the CPU
cores that other processes kept busy during the proof.

## Results

`results/<backend>-<gpu-model>.tsv` holds one row per proof; the file name names the GPU model
of the machine, and the header lines name the CPU model, thread count, rustc, midnight-proofs
source and binary sha256. `results/<backend>-<gpu-model>.raw.tsv` holds every repetition.

Columns of the summary: `program`, `circuit`, `key_program`, `job`, `k`, `n` (timed
repetitions), `median_s`, `min_s`, `max_s` (prover call, timed repetitions), `first_s` (first
run, reported apart), `verify_median_s`, `key_load_s`, `proof_bytes`, `proof_sha256`,
`verified`. Newer builds add the hook columns (`hooks_device`, `hits_msm`, `hits_ntt`,
`hits_coset`, `hits_quotient`, `fallbacks`) and the run-condition columns `load1_after`,
`quiet_gate`, `gpu_driver`, `ready_s`, `device_peak_bytes` and `host_hwm_bytes`.

The published result files (both machines) come from builds made before the run-condition columns existed.
They have no `load1_after`, `quiet_gate`, `gpu_driver`, `ready_s`, `device_peak_bytes` or
`host_hwm_bytes` column, and `summarize` leaves those fields empty for them. A rerun that
only adds these fields needs about 11 one-repetition runs of 10 to 15 minutes on a quiet
machine, and the measured machines were not free for that. The load before each proof and
`foreign_cores` (the CPU cores that other processes kept busy during the proof) are in every
row. The 1-minute load includes the benchmark's own threads, so `foreign_cores` is the
measure of other use. In the RTX 5080 Laptop files, rows with `foreign_cores` above 2 occur
only at k <= 10, where a proof takes less than 0.1 s and the 10 ms CPU tick makes the
measure coarse; no row at k >= 11 has it.


### CPU baseline: Intel Core Ultra 9 290HX Plus, 24 threads (machine with an RTX 5080 Laptop GPU)

`results/cpu-rtx-5080-laptop.tsv`: stock midnight-proofs 0.8.3, rustc 1.99.1, x86_64,
`RAYON_NUM_THREADS=24` (24 cores, one thread per core). One warm-up run and 5 timed
repetitions per proof. The run held the shared GPU lock during each proof and started at a 1-minute
load below 2; the `foreign_cores` column records other CPU use per proof. 133 of 133 proofs verify.

| k | proofs | median of per-proof medians (s) | sum of medians (s) |
|---:|---:|---:|---:|
| 6 | 7 | 0.024 | 0.16 |
| 7 | 15 | 0.026 | 0.39 |
| 8 | 14 | 0.030 | 0.43 |
| 9 | 9 | 0.044 | 0.39 |
| 10 | 3 | 0.064 | 0.20 |
| 11 | 2 | 0.220 | 0.44 |
| 13 | 47 | 0.400 | 19.19 |
| 14 | 16 | 0.754 | 12.01 |
| 15 | 8 | 1.397 | 11.05 |
| 16 | 11 | 2.565 | 28.26 |
| 17 | 1 | 4.726 | 4.73 |
| all | 133 | 0.388 (median), 2.565 (p95) | 77.25 |

The times are the prover call only (witness generation and `create_proof`); key loading and
verification are in their own columns.

### GPU half: RTX 5080 Laptop GPU, same machine and thread count

`results/gpu-rtx-5080-laptop.tsv` (hooked midnight-proofs 0.8.3 with a CUDA backend, sm_120,
`RAYON_NUM_THREADS=24`), `results/gpu-rtx-5080-laptop.verify.tsv` (every GPU repetition
checked by the stock binary) and `results/compare-rtx-5080-laptop.tsv` (one row per proof).
Same jobs, same command, 1 warm-up and 5 timed repetitions per proof. All 798 GPU rows
verify; no hook fell back to the CPU.

| k | proofs | CPU s (median) | GPU s (median) | speed-up (sum) | bytes-equal / verified | proofs with device hits |
|---:|---:|---:|---:|---:|---|---:|
| 6 | 7 | 0.024 | 0.026 | 0.92 | 7 / 0 | 7 |
| 7 | 15 | 0.026 | 0.027 | 0.98 | 9 / 6 | 15 |
| 8 | 14 | 0.030 | 0.031 | 0.99 | 11 / 3 | 14 |
| 9 | 9 | 0.044 | 0.040 | 1.08 | 9 / 0 | 9 |
| 10 | 3 | 0.064 | 0.058 | 1.14 | 3 / 0 | 3 |
| 11 | 2 | 0.220 | 0.202 | 1.08 | 0 / 2 | 2 |
| 13 | 47 | 0.400 | 0.307 | 1.29 | 0 / 47 | 47 |
| 14 | 16 | 0.754 | 0.470 | 1.60 | 0 / 16 | 16 |
| 15 | 8 | 1.397 | 0.673 | 2.06 | 0 / 8 | 8 |
| 16 | 11 | 2.565 | 1.103 | 2.34 | 0 / 11 | 11 |
| 17 | 1 | 4.726 | 1.880 | 2.51 | 0 / 1 | 1 |
| all | 133 | 0.388 | 0.297 | 1.77 | 39 / 94 | 133 |

Sum of per-proof medians: CPU 77.25 s, GPU 43.74 s. p95: CPU 2.565 s, GPU 1.103 s. All 39
reproducible proofs give the same bytes on the GPU as on the CPU. The MSM hook takes only
MSMs of 2^14 terms or more, so below k=14 the device runs the NTT, coset and quotient work
and the CPU runs the commitments; the gain grows with k.

### RTX 5090 Laptop GPU: AMD Ryzen AI Max+ 395, 12 threads

`results/cpu-rtx-5090-laptop.tsv` (stock midnight-proofs 0.8.3), `results/gpu-rtx-5090-laptop.tsv`
(hooked midnight-proofs 0.8.3 with the CUDA backend, sm_120), `results/gpu-rtx-5090-laptop.verify.tsv`
and `results/compare-rtx-5090-laptop.tsv`. The machine runs Linux in a WSL2 virtual machine,
x86_64, rustc 1.99.0, `RAYON_NUM_THREADS=12`. Same jobs and commands as above: 1 warm-up and
5 timed repetitions per proof, both builds on the same machine and thread count.

The stock binary checked all 888 GPU rows (148 jobs, s01 to s03 included) and none failed;
the 798 rows of the 133 published jobs are in the verify file. No hook fell back to the CPU.
133 jobs were measured. 26 of them ran, in at least one repetition, while other processes
kept more than 2 cores busy (`foreign_cores > 2`): 3 in the CPU run and 23 in the GPU run.
Those 26 jobs are contended and excluded: they pass the comparison rule, but the table, the
totals, the median and the p95 below use only the other 107 jobs. The compare file lists them
as `# excluded:` lines, and the raw files keep their rows.

| k | proofs | CPU s (median) | GPU s (median) | speed-up (sum) | bytes-equal / verified | proofs with device hits |
|---:|---:|---:|---:|---:|---|---:|
| 6 | 7 | 0.345 | 0.306 | 1.13 | 7 / 0 | 7 |
| 7 | 15 | 0.349 | 0.311 | 1.13 | 9 / 6 | 15 |
| 8 | 12 | 0.356 | 0.311 | 1.14 | 9 / 3 | 12 |
| 9 | 7 | 0.361 | 0.330 | 1.10 | 7 / 0 | 7 |
| 10 | 3 | 0.378 | 0.338 | 1.11 | 3 / 0 | 3 |
| 11 | 2 | 0.526 | 0.501 | 1.05 | 0 / 2 | 2 |
| 13 | 37 | 0.828 | 0.755 | 1.11 | 0 / 37 | 37 |
| 14 | 8 | 1.212 | 1.005 | 1.19 | 0 / 8 | 8 |
| 15 | 8 | 1.976 | 1.236 | 1.60 | 0 / 8 | 8 |
| 16 | 8 | 3.536 | 1.831 | 1.92 | 0 / 8 | 8 |
| all | 107 | 0.818 | 0.723 | 1.34 | 35 / 72 | 107 |

Sum of per-proof medians: CPU 101.12 s, GPU 75.25 s. p95: CPU 3.524 s, GPU 1.815 s. The only
k=17 job is among the excluded ones, so k=17 has no row.

Contended and excluded (foreign_cores > 2): d01-example-bboard 01-alice-post,
04-alice-takedown, 06-bob-post (CPU run); d03-micro-dao 10-carol-commit-yes,
12-advance-to-reveal, 13-alice-reveal-yes, 16-bob-reveal-no; d04-coracle 03-blue-start,
07-blue-guess-7, 08-red-guess-5, 09-blue-concede, 11-red-withdraw; h03-election-ctor
add-voter-32, add-voter-33, advance-to-commit, advance-to-final; z02-unshielded-tokens
getUnshieldedBalanceLtTest, getUnshieldedBalanceTest, mintShieldedToContractTest,
mintShieldedToSelfTest, mintShieldedToUserTest, mintUnshieldedToContractTest,
mintUnshieldedToSelfTest; z04-set-qualified-coin qualified-roundtrip-again,
qualified-roundtrip, shielded-coin-received (GPU run).

On this machine every prover call costs about 0.3 s more than on the RTX 5080 Laptop
machine, at every k and in both builds: a k=6 proof takes 0.345 s against 0.024 s there.
Verification and key loading do not show this cost. The cause is not established. Because the
cost is the same for both builds, it lowers the speed-up at small k, where it is most of the
time.

## Licenses

The programs are fetched, not vendored. LFDT-Minokawa/compact and the midnightntwrk example
repositories are Apache-2.0. The three patches in `patches/suite/` are under the license of
the file they change.
