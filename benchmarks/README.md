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
phase                           msm                fft          poly_eval            other         phase total
----------------  -----------------  -----------------  -----------------  ---------------  ------------------
preamble             0.00 ms (0.0%)     1.71 ms (0.2%)     0.00 ms (0.0%)   0.06 ms (0.0%)      1.77 ms (0.2%)
synthesis            0.00 ms (0.0%)     0.00 ms (0.0%)     0.00 ms (0.0%)  11.83 ms (1.3%)     11.83 ms (1.3%)
advice_commit     117.92 ms (12.9%)     0.00 ms (0.0%)     0.00 ms (0.0%)   0.53 ms (0.1%)   118.46 ms (13.0%)
lookups              0.00 ms (0.0%)     0.00 ms (0.0%)     0.56 ms (0.1%)   7.31 ms (0.8%)      7.87 ms (0.9%)
permutation          0.00 ms (0.0%)     0.00 ms (0.0%)     0.00 ms (0.0%)   9.19 ms (1.0%)      9.19 ms (1.0%)
trash                0.00 ms (0.0%)     0.00 ms (0.0%)    29.03 ms (3.2%)   0.70 ms (0.1%)     29.73 ms (3.3%)
arguments_commit  138.94 ms (15.2%)     0.00 ms (0.0%)     0.00 ms (0.0%)   1.26 ms (0.1%)   140.20 ms (15.3%)
quotient          135.24 ms (14.8%)   98.30 ms (10.8%)  256.00 ms (28.0%)   0.62 ms (0.1%)   490.16 ms (53.6%)
evals                0.00 ms (0.0%)     0.00 ms (0.0%)    17.68 ms (1.9%)   0.08 ms (0.0%)     17.76 ms (1.9%)
multi_open          76.58 ms (8.4%)     0.00 ms (0.0%)     2.29 ms (0.3%)   7.91 ms (0.9%)     86.77 ms (9.5%)
total             468.68 ms (51.3%)  100.01 ms (10.9%)  305.56 ms (33.4%)  39.49 ms (4.3%)  913.75 ms (100.0%)
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

- Commit: `6053c710695e`
- CPU: AMD Ryzen 9 9950X 16-Core Processor
- Logical cores: 32
- OS: linux x86_64
- Date: 2026-11-24

### 1 thread

| workload     | pcs        |   k |    median |       min | ±MAD% |  verify | proof bytes |
| ------------ | ---------- | --: | --------: | --------: | ----: | ------: | ----------: |
| zswap_output | kzg        |  13 | 915.41 ms | 914.97 ms |   0.0 | 2.20 ms |        4516 |
| zswap_output | fflonk-t2  |  13 | 973.59 ms | 972.60 ms |   0.1 | 1.75 ms |        4052 |
| zswap_output | fflonk-t4  |  13 |   1.081 s |   1.081 s |   0.1 | 1.64 ms |        3828 |
| zswap_output | fflonk-t8  |  13 |   1.282 s |   1.280 s |   0.0 | 1.65 ms |        3908 |
| zswap_output | fflonk-t16 |  13 |   1.710 s |   1.709 s |   0.0 | 1.71 ms |        3940 |
| poseidon     | kzg        |  14 |   1.489 s |   1.487 s |   0.0 | 1.80 ms |        2932 |
| poseidon     | fflonk-t2  |  14 |   1.597 s |   1.596 s |   0.0 | 1.57 ms |        2628 |
| poseidon     | fflonk-t4  |  14 |   1.800 s |   1.798 s |   0.0 | 1.30 ms |        2436 |
| poseidon     | fflonk-t8  |  14 |   2.205 s |   2.203 s |   0.1 | 1.28 ms |        2452 |
| poseidon     | fflonk-t16 |  14 |   2.817 s |   2.814 s |   0.1 | 1.38 ms |        2532 |
| sha_preimage | kzg        |  13 | 621.82 ms | 621.35 ms |   0.1 | 1.94 ms |        4020 |
| sha_preimage | fflonk-t2  |  13 | 678.52 ms | 678.09 ms |   0.1 | 1.53 ms |        3668 |
| sha_preimage | fflonk-t4  |  13 | 787.40 ms | 786.32 ms |   0.1 | 1.55 ms |        3588 |
| sha_preimage | fflonk-t8  |  13 | 959.21 ms | 958.79 ms |   0.0 | 1.46 ms |        3476 |
| sha_preimage | fflonk-t16 |  13 |   1.370 s |   1.370 s |   0.0 | 1.63 ms |        3460 |
| ecdsa        | kzg        |  15 |   4.912 s |   4.891 s |   0.2 | 2.75 ms |        6100 |
| ecdsa        | fflonk-t2  |  15 |   5.151 s |   5.131 s |   0.1 | 2.16 ms |        5396 |
| ecdsa        | fflonk-t4  |  15 |   5.515 s |   5.511 s |   0.0 | 1.93 ms |        5028 |
| ecdsa        | fflonk-t8  |  15 |   6.262 s |   6.259 s |   0.0 | 1.83 ms |        5012 |
| ecdsa        | fflonk-t16 |  15 |   7.919 s |   7.911 s |   0.1 | 2.17 ms |        6100 |
| schnorr      | kzg        |  11 | 216.35 ms | 216.20 ms |   0.1 | 1.69 ms |        3316 |
| schnorr      | fflonk-t2  |  11 | 235.60 ms | 235.26 ms |   0.0 | 1.50 ms |        2964 |
| schnorr      | fflonk-t4  |  11 | 273.23 ms | 273.15 ms |   0.0 | 1.34 ms |        2756 |
| schnorr      | fflonk-t8  |  11 | 328.85 ms | 328.54 ms |   0.0 | 1.24 ms |        2708 |
| schnorr      | fflonk-t16 |  11 | 433.41 ms | 433.09 ms |   0.0 | 1.41 ms |        2852 |
| jwt          | kzg        |  17 |  19.981 s |  19.964 s |   0.1 | 3.01 ms |        6788 |
| jwt          | fflonk-t2  |  17 |  20.910 s |  20.879 s |   0.1 | 2.45 ms |        5828 |
| jwt          | fflonk-t4  |  17 |  22.338 s |  22.317 s |   0.1 | 1.82 ms |        5348 |
| aggregation  | kzg        |  17 |  17.946 s |  17.917 s |   0.0 | 3.10 ms |        5508 |
| aggregation  | fflonk-t2  |  17 |  18.796 s |  18.778 s |   0.0 | 2.40 ms |        4852 |
| aggregation  | fflonk-t4  |  17 |  20.335 s |  20.330 s |   0.0 | 1.93 ms |        4628 |
| ivc_step     | kzg        |  18 |  38.053 s |  38.042 s |   0.0 | 8.95 ms |        5716 |
| ivc_step     | fflonk-t2  |  17 |  21.168 s |  21.159 s |   0.0 | 6.37 ms |        5076 |
| ivc_step     | fflonk-t4  |  17 |  21.178 s |  21.150 s |   0.1 | 4.86 ms |        4820 |
| ivc_step     | fflonk-t8  |  16 |  13.251 s |  13.227 s |   0.1 | 4.11 ms |        4724 |

### 32 threads

| workload     | pcs        |   k |    median |       min | ±MAD% |  verify | proof bytes |
| ------------ | ---------- | --: | --------: | --------: | ----: | ------: | ----------: |
| zswap_output | kzg        |  13 |  96.29 ms |  93.40 ms |   0.7 | 1.94 ms |        4516 |
| zswap_output | fflonk-t2  |  13 | 106.00 ms | 103.63 ms |   2.2 | 1.71 ms |        4052 |
| zswap_output | fflonk-t4  |  13 | 114.44 ms | 112.84 ms |   1.0 | 1.55 ms |        3828 |
| zswap_output | fflonk-t8  |  13 | 132.78 ms | 131.89 ms |   0.7 | 1.62 ms |        3908 |
| zswap_output | fflonk-t16 |  13 | 165.99 ms | 162.91 ms |   0.4 | 1.70 ms |        3940 |
| poseidon     | kzg        |  14 | 157.61 ms | 155.24 ms |   0.5 | 1.58 ms |        2932 |
| poseidon     | fflonk-t2  |  14 | 164.68 ms | 163.08 ms |   0.3 | 1.45 ms |        2628 |
| poseidon     | fflonk-t4  |  14 | 189.80 ms | 181.41 ms |   0.6 | 1.26 ms |        2436 |
| poseidon     | fflonk-t8  |  14 | 213.75 ms | 213.14 ms |   0.3 | 1.28 ms |        2452 |
| poseidon     | fflonk-t16 |  14 | 272.18 ms | 264.38 ms |   1.7 | 1.36 ms |        2532 |
| sha_preimage | kzg        |  13 |  66.12 ms |  65.76 ms |   0.4 | 1.78 ms |        4020 |
| sha_preimage | fflonk-t2  |  13 |  71.96 ms |  69.78 ms |   1.5 | 1.50 ms |        3668 |
| sha_preimage | fflonk-t4  |  13 |  80.21 ms |  79.69 ms |   0.6 | 1.46 ms |        3588 |
| sha_preimage | fflonk-t8  |  13 |  98.42 ms |  95.52 ms |   0.6 | 1.46 ms |        3476 |
| sha_preimage | fflonk-t16 |  13 | 130.03 ms | 128.82 ms |   0.9 | 1.62 ms |        3460 |
| ecdsa        | kzg        |  15 | 657.69 ms | 652.28 ms |   0.5 | 2.73 ms |        6100 |
| ecdsa        | fflonk-t2  |  15 | 685.01 ms | 679.39 ms |   0.5 | 2.11 ms |        5396 |
| ecdsa        | fflonk-t4  |  15 | 725.74 ms | 715.65 ms |   0.2 | 1.94 ms |        5028 |
| ecdsa        | fflonk-t8  |  15 | 785.02 ms | 777.46 ms |   0.7 | 1.80 ms |        5012 |
| ecdsa        | fflonk-t16 |  15 | 916.91 ms | 914.46 ms |   0.3 | 2.23 ms |        6100 |
| schnorr      | kzg        |  11 |  30.45 ms |  29.76 ms |   2.3 | 1.67 ms |        3316 |
| schnorr      | fflonk-t2  |  11 |  33.91 ms |  32.47 ms |   3.4 | 1.41 ms |        2964 |
| schnorr      | fflonk-t4  |  11 |  36.35 ms |  35.61 ms |   0.8 | 1.30 ms |        2756 |
| schnorr      | fflonk-t8  |  11 |  42.86 ms |  41.71 ms |   2.7 | 1.24 ms |        2708 |
| schnorr      | fflonk-t16 |  11 |  51.75 ms |  49.43 ms |   1.7 | 1.45 ms |        2852 |
| jwt          | kzg        |  17 |   1.781 s |   1.774 s |   0.3 | 3.05 ms |        6788 |
| jwt          | fflonk-t2  |  17 |   1.872 s |   1.865 s |   0.2 | 2.52 ms |        5828 |
| jwt          | fflonk-t4  |  17 |   2.037 s |   2.002 s |   1.5 | 1.88 ms |        5348 |
| aggregation  | kzg        |  17 |   1.722 s |   1.715 s |   0.4 | 2.69 ms |        5508 |
| aggregation  | fflonk-t2  |  17 |   1.812 s |   1.802 s |   0.2 | 2.15 ms |        4852 |
| aggregation  | fflonk-t4  |  17 |   1.943 s |   1.929 s |   0.4 | 1.96 ms |        4628 |
| ivc_step     | kzg        |  18 |   3.717 s |   3.706 s |   0.1 | 7.93 ms |        5716 |
| ivc_step     | fflonk-t2  |  17 |   2.135 s |   2.111 s |   0.6 | 6.15 ms |        5076 |
| ivc_step     | fflonk-t4  |  17 |   2.052 s |   2.022 s |   0.5 | 4.96 ms |        4820 |
| ivc_step     | fflonk-t8  |  16 |   1.281 s |   1.274 s |   0.6 | 4.28 ms |        4724 |

### Kernel shares

Share of the wall time of one proof spent in each kernel, from a separate run
built with `--features profiling` and 3 samples per case. Each kernel column is its wall time summed
over the phases, `other` is the time outside the kernels, and `synthesis` is
the part of `other` spent in witness synthesis. The kernel columns can
overlap, so a row is not guaranteed to add up to 100%.

| workload     | pcs        | threads |     total | msm % | fft % | poly_eval % | other % | synthesis % |
| ------------ | ---------- | ------: | --------: | ----: | ----: | ----------: | ------: | ----------: |
| zswap_output | kzg        |       1 | 913.75 ms |  51.3 |  10.9 |        33.4 |     4.3 |         1.3 |
| zswap_output | kzg        |      32 |  96.32 ms |  42.7 |  12.7 |        23.5 |    21.1 |        13.2 |
| zswap_output | fflonk-t2  |       1 | 971.20 ms |  53.7 |  10.3 |        31.7 |     4.3 |         1.2 |
| zswap_output | fflonk-t2  |      32 | 103.20 ms |  44.5 |  11.9 |        21.5 |    22.0 |        12.2 |
| zswap_output | fflonk-t4  |       1 |   1.078 s |  57.6 |   9.2 |        29.1 |     4.1 |         1.1 |
| zswap_output | fflonk-t4  |      32 | 120.84 ms |  46.1 |  10.3 |        24.2 |    19.4 |        10.6 |
| zswap_output | fflonk-t8  |       1 |   1.280 s |  63.4 |   7.7 |        25.1 |     3.8 |         0.9 |
| zswap_output | fflonk-t8  |      32 | 131.84 ms |  50.6 |   9.7 |        21.4 |    18.2 |         9.6 |
| zswap_output | fflonk-t16 |       1 |   1.708 s |  71.2 |   5.8 |        19.7 |     3.2 |         0.7 |
| zswap_output | fflonk-t16 |      32 | 169.31 ms |  59.8 |   7.2 |        18.0 |    15.0 |         7.5 |
| poseidon     | kzg        |       1 |   1.486 s |  62.3 |  11.2 |        23.0 |     3.6 |         1.2 |
| poseidon     | kzg        |      32 | 158.72 ms |  49.9 |  13.6 |        17.3 |    19.2 |        11.7 |
| poseidon     | fflonk-t2  |       1 |   1.594 s |  64.3 |  10.4 |        21.7 |     3.6 |         1.1 |
| poseidon     | fflonk-t2  |      32 | 170.89 ms |  52.2 |  12.5 |        17.0 |    18.3 |        10.8 |
| poseidon     | fflonk-t4  |       1 |   1.795 s |  67.6 |   9.3 |        19.7 |     3.5 |         1.0 |
| poseidon     | fflonk-t4  |      32 | 185.02 ms |  55.5 |  11.4 |        15.3 |    17.8 |         9.9 |
| poseidon     | fflonk-t8  |       1 |   2.198 s |  72.5 |   7.5 |        16.8 |     3.2 |         0.8 |
| poseidon     | fflonk-t8  |      32 | 214.33 ms |  58.9 |   9.8 |        15.6 |    15.7 |         8.5 |
| poseidon     | fflonk-t16 |       1 |   2.811 s |  77.3 |   5.9 |        13.9 |     2.9 |         0.6 |
| poseidon     | fflonk-t16 |      32 | 268.15 ms |  63.1 |   7.8 |        14.9 |    14.2 |         7.0 |
| sha_preimage | kzg        |       1 | 620.07 ms |  53.3 |  13.9 |        28.3 |     4.5 |         0.6 |
| sha_preimage | kzg        |      32 |  65.94 ms |  44.0 |  17.1 |        22.0 |    16.9 |         6.5 |
| sha_preimage | fflonk-t2  |       1 | 679.50 ms |  56.4 |  12.8 |        26.3 |     4.5 |         0.6 |
| sha_preimage | fflonk-t2  |      32 |  76.95 ms |  45.8 |  14.4 |        22.0 |    17.9 |         6.2 |
| sha_preimage | fflonk-t4  |       1 | 786.37 ms |  61.5 |  10.9 |        23.4 |     4.1 |         0.5 |
| sha_preimage | fflonk-t4  |      32 |  82.67 ms |  51.6 |  12.7 |        18.8 |    16.9 |         5.2 |
| sha_preimage | fflonk-t8  |       1 | 963.79 ms |  67.7 |   9.0 |        19.6 |     3.7 |         0.4 |
| sha_preimage | fflonk-t8  |      32 |  96.79 ms |  55.7 |  11.2 |        19.1 |    13.9 |         4.3 |
| sha_preimage | fflonk-t16 |       1 |   1.373 s |  75.9 |   6.3 |        14.7 |     3.1 |         0.3 |
| sha_preimage | fflonk-t16 |      32 | 133.16 ms |  61.5 |   8.4 |        18.9 |    11.2 |         3.1 |
| ecdsa        | kzg        |       1 |   4.894 s |  44.8 |  14.6 |        31.0 |     9.6 |         5.3 |
| ecdsa        | kzg        |      32 | 660.54 ms |  30.4 |   9.4 |        15.7 |    44.5 |        39.2 |
| ecdsa        | fflonk-t2  |       1 |   5.115 s |  46.5 |  13.9 |        30.1 |     9.5 |         5.0 |
| ecdsa        | fflonk-t2  |      32 | 678.77 ms |  30.8 |   9.1 |        14.9 |    45.2 |        38.8 |
| ecdsa        | fflonk-t4  |       1 |   5.515 s |  50.5 |  13.0 |        27.5 |     9.1 |         4.7 |
| ecdsa        | fflonk-t4  |      32 | 725.66 ms |  33.6 |   8.5 |        15.5 |    42.4 |        35.5 |
| ecdsa        | fflonk-t8  |       1 |   6.261 s |  55.5 |  11.4 |        25.0 |     8.1 |         4.1 |
| ecdsa        | fflonk-t8  |      32 | 780.95 ms |  37.3 |   7.9 |        14.9 |    40.0 |        33.0 |
| ecdsa        | fflonk-t16 |       1 |   7.875 s |  63.1 |   9.1 |        20.9 |     7.0 |         3.3 |
| ecdsa        | fflonk-t16 |      32 | 915.50 ms |  42.5 |   6.5 |        16.2 |    34.8 |        28.2 |
| schnorr      | kzg        |       1 | 216.27 ms |  62.2 |   8.8 |        23.2 |     5.8 |         3.3 |
| schnorr      | kzg        |      32 |  32.22 ms |  37.4 |  12.2 |        17.2 |    33.2 |        24.0 |
| schnorr      | fflonk-t2  |       1 | 235.11 ms |  65.0 |   8.1 |        21.5 |     5.5 |         3.0 |
| schnorr      | fflonk-t2  |      32 |  32.46 ms |  39.6 |  10.8 |        15.3 |    34.2 |        23.5 |
| schnorr      | fflonk-t4  |       1 | 273.17 ms |  69.3 |   7.0 |        18.8 |     4.9 |         2.6 |
| schnorr      | fflonk-t4  |      32 |  36.45 ms |  42.7 |  11.2 |        16.0 |    30.1 |        20.8 |
| schnorr      | fflonk-t8  |       1 | 327.68 ms |  73.8 |   5.7 |        16.2 |     4.3 |         2.2 |
| schnorr      | fflonk-t8  |      32 |  41.02 ms |  50.5 |   8.4 |        14.2 |    26.9 |        18.7 |
| schnorr      | fflonk-t16 |       1 | 433.42 ms |  79.0 |   4.4 |        12.9 |     3.7 |         1.6 |
| schnorr      | fflonk-t16 |      32 |  52.14 ms |  57.3 |   6.9 |        13.1 |    22.8 |        14.9 |
| jwt          | kzg        |       1 |  20.020 s |  38.8 |  19.0 |        36.5 |     5.7 |         0.6 |
| jwt          | kzg        |      32 |   1.771 s |  36.1 |  20.5 |        25.0 |    18.4 |         7.4 |
| jwt          | fflonk-t2  |       1 |  20.657 s |  41.0 |  18.4 |        34.7 |     5.8 |         0.6 |
| jwt          | fflonk-t2  |      32 |   1.899 s |  37.5 |  19.3 |        24.8 |    18.4 |         6.6 |
| jwt          | fflonk-t4  |       1 |  22.257 s |  44.7 |  17.2 |        32.5 |     5.5 |         0.6 |
| jwt          | fflonk-t4  |      32 |   2.023 s |  39.4 |  18.5 |        23.8 |    18.3 |         6.2 |
| aggregation  | kzg        |       1 |  17.932 s |  30.3 |  15.3 |        49.1 |     5.2 |         1.4 |
| aggregation  | kzg        |      32 |   1.721 s |  27.1 |  16.9 |        31.6 |    24.3 |        15.0 |
| aggregation  | fflonk-t2  |       1 |  18.771 s |  32.7 |  14.9 |        47.2 |     5.2 |         1.4 |
| aggregation  | fflonk-t2  |      32 |   1.824 s |  27.9 |  15.9 |        30.7 |    25.5 |        14.4 |
| aggregation  | fflonk-t4  |       1 |  20.442 s |  37.3 |  13.9 |        43.7 |     5.1 |         1.2 |
| aggregation  | fflonk-t4  |      32 |   1.939 s |  31.1 |  14.8 |        30.1 |    24.0 |        13.4 |
| ivc_step     | kzg        |       1 |  38.144 s |  30.0 |  16.3 |        48.1 |     5.6 |         1.6 |
| ivc_step     | kzg        |      32 |   3.732 s |  24.4 |  19.0 |        30.0 |    26.5 |        17.0 |
| ivc_step     | fflonk-t2  |       1 |  21.132 s |  36.6 |  13.7 |        43.9 |     5.9 |         2.0 |
| ivc_step     | fflonk-t2  |      32 |   2.150 s |  29.0 |  14.2 |        27.5 |    29.3 |        19.6 |
| ivc_step     | fflonk-t4  |       1 |  21.206 s |  37.1 |  13.5 |        44.0 |     5.3 |         1.4 |
| ivc_step     | fflonk-t4  |      32 |   2.014 s |  31.1 |  14.7 |        29.4 |    24.8 |        14.7 |
| ivc_step     | fflonk-t8  |       1 |  13.296 s |  48.3 |  10.5 |        36.3 |     5.0 |         1.6 |
| ivc_step     | fflonk-t8  |      32 |   1.281 s |  38.9 |  10.3 |        25.6 |    25.2 |        16.2 |

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
  at 32 threads from 5.5 ms under KZG to 18 ms at `T = 4` and 61 ms at
  `T = 16`. The rest of the opening, mostly polynomial arithmetic, is about a
  third of the MSM time at 32 threads and a tenth at 1 thread.
- At 32 threads the proof of a fixed circuit takes 1.04x to 1.11x as long as
  under KZG at `T = 2`, 1.10x to 1.21x at `T = 4` and 1.39x to 1.97x at
  `T = 16`. At 1 thread the two MSMs weigh more, and the overhead is 1.05x to
  1.09x, 1.12x to 1.27x and 1.61x to 2.20x.
- Verification gets faster and the proof shorter up to `T = 4` or `T = 8`:
  the proof is 11% to 21% shorter at `T = 4`. Beyond that the gains flatten
  or reverse.
- `ivc_step` goes the other way, because a larger `T` shrinks the in-circuit
  verifier: the circuit takes 178,311 rows under KZG, 82,988 at `T = 4` and
  62,026 at `T = 8`, so it fits in 2^18, 2^17 and 2^16 rows. A step
  takes 3.72 s under KZG, 2.05 s at `T = 4` and 1.28 s at `T = 8` at 32
  threads.

## Caveats

- **The 1-thread numbers are those of one core.** The commitments use the
  Pippenger of `midnight-curves`, which runs on the rayon pool (#594), so a
  proof at 1 thread keeps one core busy. Numbers taken before that change are
  not comparable: the MSMs then ran on blst's own thread pool, whatever the
  size of the rayon pool.
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
