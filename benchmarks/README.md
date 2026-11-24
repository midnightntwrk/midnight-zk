# Prover benchmarks

`midnight-benchmarks` times the prover on a fixed set of circuits, so that a
change to the proof system can be measured the same way every time. It
provides:

- a standard set of workloads, from a Schnorr signature at 2^11 rows to a
  JWT credential and a proof aggregation at 2^17 rows;
- a runner that times them under KZG and fflonk with several packing sizes,
  single-threaded and multi-threaded, and writes the results as a table, JSON or markdown;
- with the `profiling` feature, a breakdown of each proof by prover phase and
  kernel (MSM, FFT, polynomial evaluation);
- a comparison of two result files, and a script that measures two commits
  alternately and compares them.

The crate is not published. It replaces the `zswap_output` criterion bench
that `midnight-proofs` used to have.

## Quick start

The workloads need Filecoin's SRS, `bls_filecoin_2p19`, in
`zk_stdlib/examples/assets` or in the directory named by `SRS_DIR`:

```sh
curl -L -o zk_stdlib/examples/assets/bls_filecoin_2p19 \
  https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_filecoin_2p19
```

All commands below run from the root of the repository.

```sh
# The workloads and the schemes each supports.
cargo run -p midnight-benchmarks --release -- list

# Everything: every workload, under every scheme it supports, at 1 thread and
# at all logical cores, 5 timed proofs per case. Takes several minutes.
cargo run -p midnight-benchmarks --release -- run

# A selection.
cargo run -p midnight-benchmarks --release -- run \
  --filter zswap,poseidon --pcs kzg --threads 1,8,max --samples 10

# Results as files.
cargo run -p midnight-benchmarks --release -- run \
  --json results.json --markdown results.md
```

`run` is the default command and can be omitted. Its options:

| option              | meaning                                                                        | default       |
| ------------------- | ------------------------------------------------------------------------------ | ------------- |
| `--filter <SUBSTR>` | workloads whose name contains one of these comma-separated substrings          | all           |
| `--pcs <PCS>`       | comma-separated schemes, see below; unsupported combinations are skipped       | all supported |
| `--threads <N>`     | comma-separated sizes of the rayon pool; `max` is the number of logical cores  | `1,max`       |
| `--samples <N>`     | timed proofs per case                                                          | 5             |
| `--warmup <N>`      | untimed proofs before the timed ones                                           | 1             |
| `--json <PATH>`     | writes the results, including every sample, as JSON                            |               |
| `--markdown <PATH>` | writes the tables as markdown                                                  |               |
| `--no-verify`       | skips the verification of the last proof of each case                          |               |

The schemes are `kzg` and `fflonk-t<T>` for `T` in 2, 4, 8, 16: fflonk over
KZG combining up to `T` polynomials into each commitment. `T` is the `T_MAX`
of the library, so `fflonk-t4` is `FflonkKZG<2>` and `fflonk-t16` is
`FflonkKZG<4>`. KZG commits to every polynomial on its own, which makes it
the `T = 1` baseline:

```sh
cargo run -p midnight-benchmarks --release -- run --pcs kzg,fflonk-t4
```

A case is a (workload, scheme, thread count) triple. For each case the table
gives the median and the minimum of the samples, their median absolute
deviation relative to the median (`±MAD%`), the median time to verify a proof
and the size of the proof. Key generation and witness preparation happen once
per workload and scheme and are not timed. The last proof of each case is
verified once per sample, outside the timed section.

The JSON file also records the commit, the CPU, the number of logical cores
and, per case, the SHA-256 digest of the verifying key. It is the input of
`compare`.

The tests of the crate prove and verify the workloads:

```sh
cargo test -p midnight-benchmarks --release
```

The slowest ones are `#[ignore]`d; add `-- --ignored` to run them.

## On the GPU prover branch

This branch is the GPU prover of #667 merged with the benchmarks, so that the
standard workloads can be proved with and without its changes:

```sh
# The stock prover.
cargo run -p midnight-benchmarks --release -- run --pcs kzg --threads max

# With the parallel CPU paths of the GPU prover and no device.
cargo run -p midnight-benchmarks --release --features prover-par -- run --pcs kzg --threads max

# With the accelerator hooks compiled in.
cargo run -p midnight-benchmarks --release --features gpu -- run --pcs kzg --threads max
```

The last one proves on the CPU until a backend installs its hooks. A workload
builds its parameters and its proving key in `PreparedRelation::new`
(`src/workload.rs`), and `ivc_step` in `PreparedIvc::new`
(`src/workloads/ivc.rs`). That is where a backend registers them, as
`bench/gpu-prover/rc1/metrics.rs` does for the chain circuit.

With `--features profiling` the spans cover the stock kernels. Work that a
hook or the parallel paths take over is counted in its phase, but not always
under a kernel.

## Workloads

| name           | what it proves                                                                                                                                             |        k | schemes             |
| -------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- | -------: | ------------------- |
| `zswap_output` | the output circuit of the Zswap protocol: opens a coin commitment (SHA-256) and a value commitment (a Jubjub MSM over a hash-to-curve base)                |       13 | all                 |
| `poseidon`     | a chain of 380 Poseidon hashes                                                                                                                             |       14 | all                 |
| `sha_preimage` | knowledge of a 24-byte preimage of a public SHA-256 digest                                                                                                 |       13 | all                 |
| `ecdsa`        | knowledge of an Ethereum signature (ECDSA over secp256k1 of a Keccak-256 digest) of a public message under a public key                                    |       15 | all                 |
| `schnorr`      | verification of a Schnorr signature over Jubjub with Poseidon as the hash function                                                                         |       11 | all                 |
| `jwt`          | validity of a 2.5 kB JWT credential signed with ECDSA over secp256k1: issuer signature, Base64 decoding, two JSON attributes, the holder's secret key      |       17 | kzg, fflonk-t2, -t4 |
| `aggregation`  | validity of a batch of 2 fflonk proofs of the SHA-256 preimage circuit (k = 13), verified in-circuit; the pairing check is left to the verifier            |       17 | kzg, fflonk-t2, -t4 |
| `ivc_step`     | one step of an incrementally verifiable computation: the IVC circuit of `midnight-aggregation` verifies its previous proof and runs 50 Poseidon iterations | 16 to 18 | all but fflonk-t16  |

`k` is the logarithm of the number of rows. `fflonk-t<T>` needs an SRS of
`T * 2^k` points and the largest one available has 2^19, so `jwt` and
`aggregation` do not run under `fflonk-t8` and `fflonk-t16`.

The size of the `ivc_step` circuit depends on the scheme, because the circuit
verifies a proof of itself: the fewer polynomials per commitment, the more
commitments the in-circuit verifier combines. The transition is the same
under every scheme, and each runs at the smallest size that fits. `fflonk-t16`
would fit in 2^16 rows but needs an SRS of 2^20 points.

A workload implements `Workload` (see `src/workload.rs`) and is listed in
`workloads::registry()`. Most of them are a `Relation` of the standard
library, wrapped with `relation_workload`.

## Profiling

Built with the `profiling` feature, the runner also reports where the time of
each proof went:

```sh
cargo run -p midnight-benchmarks --release --features profiling -- run --filter zswap --pcs kzg
```

The feature enables `midnight_proofs::profiling` (a re-export of
`midnight_curves::profiling`), which records a span around every MSM, FFT and
polynomial evaluation, and the prover announces each of its phases. The runner
prints one matrix per case, taken from the last timed proof:

```
zswap_output, kzg, k=13, 1 thread
phase                          msm                fft          poly_eval             other         phase total
----------------  ----------------  -----------------  -----------------  ----------------  ------------------
preamble            0.00 ms (0.0%)     1.74 ms (0.3%)     0.00 ms (0.0%)    0.09 ms (0.0%)      1.83 ms (0.3%)
synthesis           0.00 ms (0.0%)     0.00 ms (0.0%)     0.00 ms (0.0%)   42.93 ms (8.0%)     42.93 ms (8.0%)
advice_commit      13.33 ms (2.5%)     0.00 ms (0.0%)     0.00 ms (0.0%)    0.56 ms (0.1%)     13.90 ms (2.6%)
lookups             0.00 ms (0.0%)     0.00 ms (0.0%)     0.55 ms (0.1%)    7.29 ms (1.4%)      7.84 ms (1.5%)
permutation         0.00 ms (0.0%)     0.00 ms (0.0%)     0.00 ms (0.0%)    9.39 ms (1.7%)      9.39 ms (1.7%)
trash               0.00 ms (0.0%)     0.00 ms (0.0%)    29.24 ms (5.4%)    0.71 ms (0.1%)     29.95 ms (5.6%)
arguments_commit   15.38 ms (2.9%)     0.00 ms (0.0%)     0.00 ms (0.0%)    1.29 ms (0.2%)     16.67 ms (3.1%)
quotient           16.98 ms (3.2%)  100.42 ms (18.7%)  259.74 ms (48.4%)    0.69 ms (0.1%)   377.81 ms (70.4%)
evals               0.00 ms (0.0%)     0.00 ms (0.0%)    17.71 ms (3.3%)    0.08 ms (0.0%)     17.79 ms (3.3%)
multi_open          8.13 ms (1.5%)     0.00 ms (0.0%)     2.37 ms (0.4%)    8.08 ms (1.5%)     18.59 ms (3.5%)
total             53.81 ms (10.0%)  102.16 ms (19.0%)  309.60 ms (57.7%)  71.12 ms (13.3%)  536.69 ms (100.0%)
```

How to read it:

- A row is a phase of the prover. `phase total` is the
  wall time of the phase, and the percentages are relative to the wall time of
  the whole proof.
- A kernel column is the wall time during which at least one span of that
  kernel was open: the union of the intervals of its spans, not their sum. A
  kernel that runs on 32 threads for 10 ms counts 10 ms.
- `other` is the wall time of the phase during which no span of any kernel was
  open.
- Spans of different kernels can overlap when they run concurrently, in which
  case the kernel columns of a row add up to more than the phase total minus
  `other`. The four columns therefore do not always add up to 100%.
- `poly_eval` includes the polynomial divisions of the multi-open argument,
  which make up most of its `multi_open` cell.
- Within a thread, time is charged to the innermost open span. Work that is
  not in a span but runs under one is charged to that span, which includes a
  task that a rayon thread steals while its span waits on the pool.
- The `Concurrent calls` line under a table is the time summed over the calls
  of a kernel divided by its wall time. It tells how many calls ran at once,
  not how many threads a call used.

What lands in `other` is the prover work that is not one of the three kernels:
witness synthesis (the whole `synthesis` row), batch inversions, the
permutation products, the division by the vanishing polynomial, the linear
combinations of polynomials in the multi-open argument, and transcript
hashing.

On `zswap_output` and `ecdsa` under KZG, 21 interleaved samples per side
showed no difference between a profiling and a plain build beyond the noise
(under 0.6%). The runner still warns that a profiling build does
not produce reference numbers, and `compare` warns when one of its inputs
comes from such a build. Without the feature, every function of the profiling
module is empty and the prover is unchanged.

With `--json`, the breakdown of each case is stored under `breakdown`, in
nanoseconds: per phase `wall_ns` and `covered_ns` (the time inside any
kernel), and per kernel `wall_ns`, `busy_ns` (the sum of the durations of its
spans, which exceeds `wall_ns` when they run concurrently) and `calls`.

## Comparing two commits

`compare` takes two result files and reports, for every case present in both,
the two medians and the change of the head relative to the base (negative
means the head is faster):

```sh
cargo run -p midnight-benchmarks --release -- compare base.json head.json
```

Its options are `--threshold <percent>` (default 2), `--markdown`, and
`--fail-on-regression`, which makes it exit with status 1 if a case is
significantly slower.

A change is reported as `faster` or `slower` only if it exceeds both the
threshold and the noise of the two sample sets, and as `within noise`
otherwise:

- With at least 5 samples on both sides, the noise is
  `2 * sqrt(s_base^2 + s_head^2)`, where `s = 1.4826 * MAD / median` is the
  robust relative standard deviation of one side.
- With 2 to 4 samples on a side, the `[min, max]` ranges of the two sides must
  not overlap.
- With a single sample on a side there is no noise estimate, and the threshold
  alone decides. The report says so.

The comparison is only meaningful if both sides prove the same circuit.
`compare` checks the digest of the verifying key of each case and prints
`VK HASH MISMATCH` when the two builds disagree, which happens when the change
under test alters the constraint system or the keys. It also warns about a different
`k`, a different proof size, a profiling build, or a different machine. When
both files carry a breakdown, it shows the change of each kernel, without
testing it for significance, since a breakdown describes a single proof.

Two runs taken minutes apart on the same machine can differ by more than the
change under test. `scripts/ab.sh` measures two checkouts alternately instead,
typically two git worktrees:

```sh
git worktree add ../midnight-zk-base "$(git merge-base main HEAD)"
benchmarks/scripts/ab.sh ../midnight-zk-base . --rounds 3 -- --filter zswap --threads 1,max
```

It builds the crate in both checkouts, runs them for `--rounds` rounds
(default 4), alternating which side goes first, merges the samples of each
side with `jq`, and runs `compare` on the result. Arguments after `--` go to
`run` on both sides. The result files are kept in `./ab-results/<timestamp>`
or in the `--out` directory. Both checkouts must contain this crate, and both
read the SRS from `SRS_DIR`, which defaults to the assets of the head
checkout. Set `AB_BUILD_ARGS="--features profiling"` to compare breakdowns.
`ab.sh --help` has the details.

## Reference numbers

Plain build (no profiling), `release` profile, 1 warm-up proof and 5 samples
per case.

- Commit: `4bd101b2b18e`
- CPU: AMD Ryzen 9 9950X 16-Core Processor
- Logical cores: 32
- OS: linux x86_64
- Date: 2026-11-12

### 1 thread

| workload     | pcs        |   k |    median |       min | ±MAD% |   verify | proof bytes |
| ------------ | ---------- | --: | --------: | --------: | ----: | -------: | ----------: |
| zswap_output | kzg        |  13 | 537.55 ms | 537.11 ms |   0.1 |  2.00 ms |        4516 |
| zswap_output | fflonk-t2  |  13 | 555.44 ms | 549.23 ms |   0.6 |  1.88 ms |        4052 |
| zswap_output | fflonk-t4  |  13 | 573.09 ms | 571.89 ms |   0.2 |  1.61 ms |        3828 |
| zswap_output | fflonk-t8  |  13 | 612.73 ms | 604.92 ms |   0.3 |  1.68 ms |        3908 |
| zswap_output | fflonk-t16 |  13 | 685.16 ms | 671.75 ms |   0.2 |  1.76 ms |        3940 |
| poseidon     | kzg        |  14 | 683.46 ms | 680.15 ms |   0.3 |  1.72 ms |        2932 |
| poseidon     | fflonk-t2  |  14 | 703.31 ms | 702.48 ms |   0.1 |  1.49 ms |        2628 |
| poseidon     | fflonk-t4  |  14 | 747.51 ms | 738.14 ms |   0.2 |  1.32 ms |        2436 |
| poseidon     | fflonk-t8  |  14 | 816.42 ms | 808.37 ms |   0.9 |  1.32 ms |        2452 |
| poseidon     | fflonk-t16 |  14 | 922.26 ms | 916.91 ms |   0.6 |  1.42 ms |        2532 |
| sha_preimage | kzg        |  13 | 336.29 ms | 331.99 ms |   0.3 |  2.02 ms |        4020 |
| sha_preimage | fflonk-t2  |  13 | 348.31 ms | 346.04 ms |   0.3 |  1.63 ms |        3668 |
| sha_preimage | fflonk-t4  |  13 | 370.37 ms | 366.99 ms |   0.7 |  1.64 ms |        3588 |
| sha_preimage | fflonk-t8  |  13 | 401.49 ms | 398.36 ms |   0.7 |  1.43 ms |        3476 |
| sha_preimage | fflonk-t16 |  13 | 466.12 ms | 465.06 ms |   0.2 |  1.63 ms |        3460 |
| ecdsa        | kzg        |  15 |   2.942 s |   2.931 s |   0.4 |  2.78 ms |        6100 |
| ecdsa        | fflonk-t2  |  15 |   3.000 s |   2.982 s |   0.1 |  2.19 ms |        5396 |
| ecdsa        | fflonk-t4  |  15 |   3.097 s |   3.089 s |   0.1 |  2.03 ms |        5028 |
| ecdsa        | fflonk-t8  |  15 |   3.238 s |   3.227 s |   0.3 |  1.81 ms |        5012 |
| ecdsa        | fflonk-t16 |  15 |   3.537 s |   3.535 s |   0.0 |  2.35 ms |        6100 |
| schnorr      | kzg        |  11 | 132.16 ms | 130.34 ms |   1.4 |  1.76 ms |        3316 |
| schnorr      | fflonk-t2  |  11 | 134.72 ms | 132.74 ms |   1.5 |  1.49 ms |        2964 |
| schnorr      | fflonk-t4  |  11 | 141.01 ms | 139.05 ms |   1.3 |  1.34 ms |        2756 |
| schnorr      | fflonk-t8  |  11 | 151.22 ms | 149.79 ms |   0.3 |  1.37 ms |        2708 |
| schnorr      | fflonk-t16 |  11 | 168.25 ms | 167.02 ms |   0.7 |  1.41 ms |        2852 |
| jwt          | kzg        |  17 |  13.273 s |  13.119 s |   0.5 |  3.14 ms |        6788 |
| jwt          | fflonk-t2  |  17 |  13.359 s |  13.336 s |   0.2 |  2.48 ms |        5828 |
| jwt          | fflonk-t4  |  17 |  13.711 s |  13.658 s |   0.2 |  2.09 ms |        5348 |
| aggregation  | kzg        |  17 |  13.209 s |  13.165 s |   0.0 |  2.76 ms |        5508 |
| aggregation  | fflonk-t2  |  17 |  13.485 s |  13.453 s |   0.1 |  2.26 ms |        4852 |
| aggregation  | fflonk-t4  |  17 |  13.731 s |  13.719 s |   0.1 |  2.08 ms |        4628 |
| ivc_step     | kzg        |  18 |  28.290 s |  28.279 s |   0.0 | 11.12 ms |        5716 |
| ivc_step     | fflonk-t2  |  17 |  14.252 s |  14.235 s |   0.0 |  7.52 ms |        5076 |
| ivc_step     | fflonk-t4  |  17 |  14.288 s |  14.273 s |   0.1 |  6.22 ms |        4820 |
| ivc_step     | fflonk-t8  |  16 |   7.630 s |   7.606 s |   0.2 |  4.47 ms |        4724 |

### 32 threads

| workload     | pcs        |   k |    median |       min | ±MAD% |   verify | proof bytes |
| ------------ | ---------- | --: | --------: | --------: | ----: | -------: | ----------: |
| zswap_output | kzg        |  13 | 141.37 ms | 137.77 ms |   1.1 |  1.99 ms |        4516 |
| zswap_output | fflonk-t2  |  13 | 150.49 ms | 147.34 ms |   1.3 |  1.69 ms |        4052 |
| zswap_output | fflonk-t4  |  13 | 173.99 ms | 169.44 ms |   1.0 |  1.65 ms |        3828 |
| zswap_output | fflonk-t8  |  13 | 198.15 ms | 195.50 ms |   1.3 |  1.60 ms |        3908 |
| zswap_output | fflonk-t16 |  13 | 257.30 ms | 244.97 ms |   1.5 |  1.71 ms |        3940 |
| poseidon     | kzg        |  14 | 192.60 ms | 190.12 ms |   1.3 |  1.56 ms |        2932 |
| poseidon     | fflonk-t2  |  14 | 209.11 ms | 207.56 ms |   0.1 |  1.46 ms |        2628 |
| poseidon     | fflonk-t4  |  14 | 242.74 ms | 233.50 ms |   0.9 |  1.32 ms |        2436 |
| poseidon     | fflonk-t8  |  14 | 296.13 ms | 291.02 ms |   1.6 |  1.31 ms |        2452 |
| poseidon     | fflonk-t16 |  14 | 373.33 ms | 365.97 ms |   1.0 |  1.38 ms |        2532 |
| sha_preimage | kzg        |  13 |  75.31 ms |  74.71 ms |   0.4 |  1.82 ms |        4020 |
| sha_preimage | fflonk-t2  |  13 |  87.38 ms |  82.76 ms |   4.7 |  1.63 ms |        3668 |
| sha_preimage | fflonk-t4  |  13 | 101.30 ms |  98.46 ms |   2.5 |  1.46 ms |        3588 |
| sha_preimage | fflonk-t8  |  13 | 128.67 ms | 125.51 ms |   2.2 |  1.52 ms |        3476 |
| sha_preimage | fflonk-t16 |  13 | 182.61 ms | 176.38 ms |   2.7 |  1.70 ms |        3460 |
| ecdsa        | kzg        |  15 | 734.35 ms | 729.77 ms |   0.6 |  2.85 ms |        6100 |
| ecdsa        | fflonk-t2  |  15 | 766.00 ms | 757.94 ms |   0.6 |  2.18 ms |        5396 |
| ecdsa        | fflonk-t4  |  15 | 836.99 ms | 826.78 ms |   0.6 |  1.98 ms |        5028 |
| ecdsa        | fflonk-t8  |  15 | 925.81 ms | 914.29 ms |   0.2 |  1.89 ms |        5012 |
| ecdsa        | fflonk-t16 |  15 |   1.147 s |   1.141 s |   0.5 |  2.19 ms |        6100 |
| schnorr      | kzg        |  11 |  67.60 ms |  66.64 ms |   0.9 |  1.75 ms |        3316 |
| schnorr      | fflonk-t2  |  11 |  69.96 ms |  68.80 ms |   1.0 |  1.39 ms |        2964 |
| schnorr      | fflonk-t4  |  11 |  75.44 ms |  72.97 ms |   1.2 |  1.26 ms |        2756 |
| schnorr      | fflonk-t8  |  11 |  83.50 ms |  82.07 ms |   0.6 |  1.23 ms |        2708 |
| schnorr      | fflonk-t16 |  11 |  98.21 ms |  97.00 ms |   1.2 |  1.39 ms |        2852 |
| jwt          | kzg        |  17 |   2.154 s |   2.151 s |   0.1 |  3.23 ms |        6788 |
| jwt          | fflonk-t2  |  17 |   2.286 s |   2.271 s |   0.2 |  2.55 ms |        5828 |
| jwt          | fflonk-t4  |  17 |   2.523 s |   2.497 s |   0.4 |  1.86 ms |        5348 |
| aggregation  | kzg        |  17 |   1.963 s |   1.939 s |   0.4 |  2.76 ms |        5508 |
| aggregation  | fflonk-t2  |  17 |   2.074 s |   2.058 s |   0.5 |  2.19 ms |        4852 |
| aggregation  | fflonk-t4  |  17 |   2.300 s |   2.297 s |   0.1 |  1.98 ms |        4628 |
| ivc_step     | kzg        |  18 |   4.239 s |   4.230 s |   0.1 | 10.09 ms |        5716 |
| ivc_step     | fflonk-t2  |  17 |   2.484 s |   2.444 s |   0.8 |  6.91 ms |        5076 |
| ivc_step     | fflonk-t4  |  17 |   2.415 s |   2.379 s |   0.3 |  5.76 ms |        4820 |
| ivc_step     | fflonk-t8  |  16 |   1.583 s |   1.578 s |   0.3 |  4.51 ms |        4724 |

### Kernel shares

Share of the wall time of one proof spent in each kernel, from a separate run
built with `--features profiling` and 3 samples per case. Each kernel column is its wall time summed
over the phases, `other` is the time outside the kernels, and `synthesis` is
the part of `other` spent in witness synthesis. The kernel columns can
overlap, so a row is not guaranteed to add up to 100%.

| workload     | pcs        | threads |     total | msm % | fft % | poly_eval % | other % | synthesis % |
| ------------ | ---------- | ------: | --------: | ----: | ----: | ----------: | ------: | ----------: |
| zswap_output | kzg        |       1 | 534.03 ms |  10.2 |  18.7 |        57.5 |    13.6 |         8.2 |
| zswap_output | kzg        |      32 | 145.07 ms |  37.6 |   8.7 |        17.3 |    36.4 |        30.4 |
| zswap_output | fflonk-t2  |       1 | 556.09 ms |  11.2 |  18.4 |        56.6 |    13.8 |         7.9 |
| zswap_output | fflonk-t2  |      32 | 148.27 ms |  40.4 |   8.1 |        15.0 |    36.6 |        29.8 |
| zswap_output | fflonk-t4  |       1 | 575.04 ms |  13.0 |  17.6 |        55.3 |    14.1 |         7.6 |
| zswap_output | fflonk-t4  |      32 | 170.64 ms |  43.1 |   7.7 |        16.7 |    32.5 |        26.2 |
| zswap_output | fflonk-t8  |       1 | 612.95 ms |  16.8 |  16.7 |        53.0 |    13.5 |         7.1 |
| zswap_output | fflonk-t8  |      32 | 198.22 ms |  52.8 |   6.1 |        12.9 |    28.2 |        22.1 |
| zswap_output | fflonk-t16 |       1 | 673.70 ms |  21.4 |  15.1 |        50.2 |    13.3 |         6.4 |
| zswap_output | fflonk-t16 |      32 | 248.46 ms |  59.1 |   5.0 |        13.3 |    22.6 |        17.6 |
| poseidon     | kzg        |       1 | 684.75 ms |  16.5 |  24.7 |        50.5 |     8.3 |         2.7 |
| poseidon     | kzg        |      32 | 189.84 ms |  60.5 |  10.8 |        12.9 |    15.9 |         9.6 |
| poseidon     | fflonk-t2  |       1 | 704.63 ms |  17.7 |  23.9 |        49.8 |     8.6 |         2.5 |
| poseidon     | fflonk-t2  |      32 | 211.42 ms |  61.0 |  10.2 |        13.4 |    15.3 |         8.6 |
| poseidon     | fflonk-t4  |       1 | 741.77 ms |  20.8 |  22.6 |        47.8 |     8.8 |         2.4 |
| poseidon     | fflonk-t4  |      32 | 242.08 ms |  64.6 |   9.1 |        12.7 |    13.5 |         7.2 |
| poseidon     | fflonk-t8  |       1 | 815.09 ms |  23.9 |  20.8 |        46.1 |     9.2 |         2.1 |
| poseidon     | fflonk-t8  |      32 | 304.48 ms |  69.5 |   7.5 |        11.7 |    11.3 |         5.8 |
| poseidon     | fflonk-t16 |       1 | 922.75 ms |  29.8 |  18.5 |        42.6 |     9.2 |         1.9 |
| poseidon     | fflonk-t16 |      32 | 374.62 ms |  73.7 |   5.9 |        11.0 |     9.4 |         4.6 |
| sha_preimage | kzg        |       1 | 335.23 ms |  11.9 |  26.2 |        52.8 |     9.1 |         1.3 |
| sha_preimage | kzg        |      32 |  78.85 ms |  54.2 |  14.3 |        17.7 |    13.8 |         5.2 |
| sha_preimage | fflonk-t2  |       1 | 344.56 ms |  13.1 |  25.2 |        52.2 |     9.5 |         1.1 |
| sha_preimage | fflonk-t2  |      32 |  85.15 ms |  52.3 |  12.7 |        19.8 |    15.2 |         4.9 |
| sha_preimage | fflonk-t4  |       1 | 372.11 ms |  16.5 |  23.6 |        50.3 |     9.6 |         1.1 |
| sha_preimage | fflonk-t4  |      32 | 108.40 ms |  63.0 |   9.9 |        14.8 |    12.3 |         3.9 |
| sha_preimage | fflonk-t8  |       1 | 401.45 ms |  21.1 |  21.8 |        47.4 |     9.7 |         1.0 |
| sha_preimage | fflonk-t8  |      32 | 128.19 ms |  65.0 |   8.6 |        15.2 |    11.2 |         3.2 |
| sha_preimage | fflonk-t16 |       1 | 466.21 ms |  28.2 |  18.6 |        43.4 |     9.8 |         0.9 |
| sha_preimage | fflonk-t16 |      32 | 186.01 ms |  71.9 |   6.2 |        14.1 |     7.8 |         2.1 |
| ecdsa        | kzg        |       1 |   2.948 s |   9.2 |  24.2 |        50.5 |    16.0 |         8.8 |
| ecdsa        | kzg        |      32 | 734.94 ms |  37.5 |   8.5 |        13.7 |    40.4 |        35.4 |
| ecdsa        | fflonk-t2  |       1 |   2.995 s |  10.0 |  23.9 |        49.6 |    16.6 |         8.9 |
| ecdsa        | fflonk-t2  |      32 | 760.95 ms |  38.9 |   8.4 |        12.6 |    40.1 |        34.1 |
| ecdsa        | fflonk-t4  |       1 |   3.076 s |  11.3 |  23.3 |        48.9 |    16.5 |         8.7 |
| ecdsa        | fflonk-t4  |      32 | 830.40 ms |  42.9 |   7.4 |        12.5 |    37.2 |        31.2 |
| ecdsa        | fflonk-t8  |       1 |   3.209 s |  13.4 |  22.2 |        48.5 |    15.9 |         8.0 |
| ecdsa        | fflonk-t8  |      32 | 917.02 ms |  47.2 |   6.6 |        12.6 |    33.5 |        28.2 |
| ecdsa        | fflonk-t16 |       1 |   3.528 s |  17.4 |  20.4 |        46.4 |    15.8 |         7.3 |
| ecdsa        | fflonk-t16 |      32 |   1.151 s |  53.8 |   5.4 |        13.2 |    27.5 |        22.5 |
| schnorr      | kzg        |       1 | 132.81 ms |  13.1 |  14.7 |        38.2 |    33.9 |        29.5 |
| schnorr      | kzg        |      32 |  67.64 ms |  23.5 |   5.4 |         7.1 |    64.0 |        59.7 |
| schnorr      | fflonk-t2  |       1 | 134.69 ms |  14.4 |  14.3 |        37.5 |    33.8 |        29.2 |
| schnorr      | fflonk-t2  |      32 |  70.88 ms |  25.0 |   5.7 |         8.8 |    60.5 |        55.6 |
| schnorr      | fflonk-t4  |       1 | 143.59 ms |  15.5 |  13.9 |        37.6 |    33.0 |        28.2 |
| schnorr      | fflonk-t4  |      32 |  75.52 ms |  28.4 |   5.2 |         9.1 |    57.3 |        52.1 |
| schnorr      | fflonk-t8  |       1 | 151.55 ms |  19.8 |  13.1 |        36.0 |    31.2 |        25.9 |
| schnorr      | fflonk-t8  |      32 |  84.47 ms |  37.0 |   4.0 |         8.0 |    51.0 |        46.9 |
| schnorr      | fflonk-t16 |       1 | 170.20 ms |  25.4 |  11.8 |        33.8 |    29.0 |        23.6 |
| schnorr      | fflonk-t16 |      32 |  98.94 ms |  43.9 |   3.7 |         8.0 |    44.4 |        39.9 |
| jwt          | kzg        |       1 |  13.254 s |   7.8 |  29.1 |        54.7 |     8.4 |         0.9 |
| jwt          | kzg        |      32 |   2.161 s |  48.4 |  17.0 |        20.3 |    14.3 |         5.5 |
| jwt          | fflonk-t2  |       1 |  13.723 s |   8.3 |  29.0 |        54.2 |     8.5 |         0.8 |
| jwt          | fflonk-t2  |      32 |   2.267 s |  49.2 |  16.1 |        19.8 |    14.9 |         5.2 |
| jwt          | fflonk-t4  |       1 |  13.773 s |   9.5 |  28.7 |        52.8 |     9.0 |         0.8 |
| jwt          | fflonk-t4  |      32 |   2.515 s |  52.3 |  14.4 |        19.1 |    14.2 |         4.6 |
| aggregation  | kzg        |       1 |  13.233 s |   5.1 |  20.9 |        66.9 |     7.1 |         1.9 |
| aggregation  | kzg        |      32 |   1.973 s |  37.3 |  14.8 |        27.0 |    20.9 |        12.9 |
| aggregation  | fflonk-t2  |       1 |  13.428 s |   6.0 |  20.5 |        66.1 |     7.4 |         1.9 |
| aggregation  | fflonk-t2  |      32 |   2.100 s |  37.7 |  13.8 |        27.6 |    20.9 |        12.0 |
| aggregation  | fflonk-t4  |       1 |  13.712 s |   7.0 |  20.1 |        65.3 |     7.6 |         1.8 |
| aggregation  | fflonk-t4  |      32 |   2.297 s |  42.5 |  12.5 |        25.2 |    19.9 |        11.1 |
| ivc_step     | kzg        |       1 |  28.355 s |   5.0 |  22.6 |        64.9 |     7.5 |         2.2 |
| ivc_step     | kzg        |      32 |   4.213 s |  33.9 |  16.7 |        26.2 |    23.3 |        14.8 |
| ivc_step     | fflonk-t2  |       1 |  14.290 s |   6.8 |  19.9 |        64.7 |     8.6 |         2.8 |
| ivc_step     | fflonk-t2  |      32 |   2.514 s |  39.8 |  12.3 |        22.9 |    25.1 |        16.4 |
| ivc_step     | fflonk-t4  |       1 |  14.299 s |   6.9 |  20.0 |        65.2 |     7.9 |         2.0 |
| ivc_step     | fflonk-t4  |      32 |   2.416 s |  41.6 |  12.9 |        24.6 |    20.9 |        12.1 |
| ivc_step     | fflonk-t8  |       1 |   7.634 s |  10.5 |  17.6 |        63.3 |     8.7 |         2.7 |
| ivc_step     | fflonk-t8  |      32 |   1.582 s |  50.5 |   8.9 |        20.3 |    20.3 |        12.8 |

### Effect of the fflonk packing size

Read from the tables above and from the per-phase breakdowns of the profiling
run:

- Only the multi-open argument changes. Synthesis, the commitments to the
  advice columns and to the arguments, and the quotient take the same time
  under every scheme, within 2% at 1 thread. Fflonk commits to a group with
  one MSM over the interleaved bases, which costs as much as committing to its
  polynomials one by one.
- The multi-open argument runs two MSMs whose size is `T` times the number of
  rows. Their time grows 1.7x to 2x each time `T` doubles: on `zswap_output`
  from 8 ms under KZG to 30 ms at `T = 4` and 103 ms at `T = 16`. The
  polynomial arithmetic of the opening grows at the same rate and is about a
  tenth of the MSM time at 32 threads.
- At 32 threads the proof of a fixed circuit takes 1.03x to 1.16x as long as
  under KZG at `T = 2`, 1.12x to 1.35x at `T = 4` and 1.45x to 2.42x at
  `T = 16`. At 1 thread the rest of the prover weighs more, and the overhead
  is 1.01x to 1.04x, 1.03x to 1.10x and 1.20x to 1.39x.
- Verification gets faster and the proof shorter up to `T = 4` or `T = 8`:
  the proof is 11% to 21% shorter at `T = 4`. Beyond that the gains flatten
  or reverse.
- `ivc_step` goes the other way, because a larger `T` shrinks the circuit:
  its in-circuit verifier takes 178,551 rows under KZG, 83,196 at `T = 4` and
  62,223 at `T = 8`, so the circuit fits in 2^18, 2^17 and 2^16 rows. A step
  takes 4.24 s under KZG, 2.42 s at `T = 4` and 1.58 s at `T = 8` at 32
  threads.

## Caveats

- **The 1-thread configuration only limits the rayon pool.** G1 MSMs are
  executed by blst's `multi_exp_affine`, which uses its own thread pool, so
  MSM time does not shrink at 1 thread, and the "1 thread" numbers are not
  those of a single-core machine. This is a known limitation.
- **The timed section of `ivc_step` is a full `IvcProver::prove_step`**,
  which also verifies the previous proof off-circuit.
- **`aggregation` verifies `fflonk-t16` proofs in-circuit** under every outer
  scheme. Only the scheme of the outer proof varies.
- **`aggregation` is not the `single_circuit_aggregation` example.** It is a
  batch-verification relation: 2 inner SHA-256 preimage proofs verified
  in-circuit. The example needs an SRS larger than the 2^19 one available.
- **`zswap_output` runs at k = 13**, its optimal size. The criterion bench it
  replaces used k = 14, so the numbers of the two are not comparable.
- **The reference numbers are indicative.** They were taken with the `release`
  profile on one machine, described above the tables. Compare commits on your
  own machine, with `scripts/ab.sh`.
- The breakdown of a case describes its last proof only.
- **The witnesses of `ivc_step` and `aggregation` differ across runs.** The
  prover draws some blinding factors from the operating system, so the proofs
  these two workloads verify in-circuit are not reproducible. Their circuits
  and verifying keys are.
- **Use enough samples before trusting a verdict.** With 5 samples per side,
  two runs of the same build are reported as different in about 3% of the
  cases, and a full run has 72 cases. `scripts/ab.sh` gathers 20 per side by
  default.
