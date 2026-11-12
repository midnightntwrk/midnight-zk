# Prover benchmarks

`midnight-benchmarks` times the prover on a fixed set of circuits, so that a
change to the proof system can be measured the same way every time. It
provides:

- a standard set of workloads, from a Schnorr signature at 2^11 rows to a
  JWT credential and a proof aggregation at 2^17 rows;
- a runner that times them under KZG and fflonk, single-threaded and
  multi-threaded, and writes the results as a table, JSON or markdown;
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
| `--pcs <PCS>`       | `kzg`, `fflonk` or both, comma-separated; unsupported combinations are skipped | all supported |
| `--threads <N>`     | comma-separated sizes of the rayon pool; `max` is the number of logical cores  | `1,max`       |
| `--samples <N>`     | timed proofs per case                                                          | 5             |
| `--warmup <N>`      | untimed proofs before the timed ones                                           | 1             |
| `--json <PATH>`     | writes the results, including every sample, as JSON                            |               |
| `--markdown <PATH>` | writes the tables as markdown                                                  |               |
| `--no-verify`       | skips the verification of the last proof of each case                          |               |

A case is a (workload, scheme, thread count) triple. For each case the table
gives the median and the minimum of the samples, their median absolute
deviation relative to the median (`±MAD%`), and the size of the proof. Key
generation and witness preparation happen once per workload and scheme and
are not timed. The last proof of each case is verified, outside the timed
section.

The JSON file also records the commit, the CPU, the number of logical cores
and, per case, the SHA-256 digest of the verifying key. It is the input of
`compare`.

The tests of the crate prove and verify the workloads:

```sh
cargo test -p midnight-benchmarks --release
```

The slowest ones are `#[ignore]`d; add `-- --ignored` to run them.

## Workloads

| name           | what it proves                                                                                                                                             |  k | schemes        |
| -------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- | -: | -------------- |
| `zswap_output` | the output circuit of the Zswap protocol: opens a coin commitment (SHA-256) and a value commitment (a Jubjub MSM over a hash-to-curve base)                | 13 | kzg, fflonk<4> |
| `poseidon`     | a chain of 380 Poseidon hashes                                                                                                                             | 14 | kzg, fflonk<4> |
| `sha_preimage` | knowledge of a 24-byte preimage of a public SHA-256 digest                                                                                                 | 13 | kzg, fflonk<4> |
| `ecdsa`        | knowledge of an Ethereum signature (ECDSA over secp256k1 of a Keccak-256 digest) of a public message under a public key                                    | 15 | kzg, fflonk<4> |
| `schnorr`      | verification of a Schnorr signature over Jubjub with Poseidon as the hash function                                                                         | 11 | kzg, fflonk<4> |
| `jwt`          | validity of a 2.5 kB JWT credential signed with ECDSA over secp256k1: issuer signature, Base64 decoding, two JSON attributes, the holder's secret key      | 17 | kzg            |
| `aggregation`  | validity of a batch of 2 fflonk proofs of the SHA-256 preimage circuit (k = 13), verified in-circuit; the pairing check is left to the verifier            | 17 | kzg            |
| `ivc_step`     | one step of an incrementally verifiable computation: the IVC circuit of `midnight-aggregation` verifies its previous proof and runs 50 Poseidon iterations | 16 | fflonk<3>      |

`k` is the logarithm of the number of rows. `fflonk<t>` is fflonk over KZG
with chunks of up to 2^t polynomials (`FflonkKZG<t>` in `midnight-zk-stdlib`),
which needs an SRS of size 2^(k + t). The largest SRS available is 2^19, so
`jwt` and `aggregation` only run under KZG.

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

- Commit: `0e572bdb442d`
- CPU: AMD Ryzen 9 9950X 16-Core Processor
- Logical cores: 32
- OS: linux x86_64
- Date: 2026-11-12

### 1 thread

| workload     | pcs       |   k |    median |       min | ±MAD% | proof bytes |
| ------------ | --------- | --: | --------: | --------: | ----: | ----------: |
| zswap_output | kzg       |  13 | 538.88 ms | 537.33 ms |   0.1 |        4516 |
| zswap_output | fflonk<4> |  13 | 678.53 ms | 671.73 ms |   1.0 |        3940 |
| poseidon     | kzg       |  14 | 682.57 ms | 678.43 ms |   0.2 |        2932 |
| poseidon     | fflonk<4> |  14 | 916.82 ms | 911.36 ms |   0.1 |        2532 |
| sha_preimage | kzg       |  13 | 331.86 ms | 330.60 ms |   0.4 |        4020 |
| sha_preimage | fflonk<4> |  13 | 468.29 ms | 459.53 ms |   0.2 |        3460 |
| ecdsa        | kzg       |  15 |   2.967 s |   2.938 s |   0.4 |        6100 |
| ecdsa        | fflonk<4> |  15 |   3.551 s |   3.541 s |   0.2 |        6100 |
| schnorr      | kzg       |  11 | 132.31 ms | 130.49 ms |   0.8 |        3316 |
| schnorr      | fflonk<4> |  11 | 169.99 ms | 166.99 ms |   0.4 |        2852 |
| jwt          | kzg       |  17 |  13.335 s |  13.261 s |   0.5 |        6788 |
| aggregation  | kzg       |  17 |  13.292 s |  13.266 s |   0.1 |        5508 |
| ivc_step     | fflonk<3> |  16 |   7.697 s |   7.673 s |   0.3 |        4724 |

### 32 threads

| workload     | pcs       |   k |    median |       min | ±MAD% | proof bytes |
| ------------ | --------- | --: | --------: | --------: | ----: | ----------: |
| zswap_output | kzg       |  13 | 141.29 ms | 139.14 ms |   0.4 |        4516 |
| zswap_output | fflonk<4> |  13 | 249.39 ms | 245.30 ms |   1.6 |        3940 |
| poseidon     | kzg       |  14 | 191.87 ms | 189.64 ms |   0.3 |        2932 |
| poseidon     | fflonk<4> |  14 | 370.00 ms | 368.46 ms |   0.3 |        2532 |
| sha_preimage | kzg       |  13 |  75.19 ms |  73.29 ms |   1.6 |        4020 |
| sha_preimage | fflonk<4> |  13 | 180.97 ms | 177.33 ms |   2.0 |        3460 |
| ecdsa        | kzg       |  15 | 734.47 ms | 720.02 ms |   1.8 |        6100 |
| ecdsa        | fflonk<4> |  15 |   1.145 s |   1.142 s |   0.2 |        6100 |
| schnorr      | kzg       |  11 |  68.52 ms |  66.95 ms |   0.6 |        3316 |
| schnorr      | fflonk<4> |  11 |  97.98 ms |  97.12 ms |   0.4 |        2852 |
| jwt          | kzg       |  17 |   2.167 s |   2.146 s |   0.5 |        6788 |
| aggregation  | kzg       |  17 |   1.963 s |   1.921 s |   0.4 |        5508 |
| ivc_step     | fflonk<3> |  16 |   1.605 s |   1.586 s |   0.2 |        4724 |

### Kernel shares

Share of the wall time of one proof spent in each kernel, from a separate run
built with `--features profiling`. Each kernel column is its wall time summed
over the phases, `other` is the time outside the kernels, and `synthesis` is
the part of `other` spent in witness synthesis. The kernel columns can
overlap, so a row is not guaranteed to add up to 100%.

| workload     | pcs       | threads |     total | msm % | fft % | poly_eval % | other % | synthesis % |
| ------------ | --------- | ------: | --------: | ----: | ----: | ----------: | ------: | ----------: |
| zswap_output | kzg       |       1 | 536.69 ms |  10.0 |  19.0 |        57.7 |    13.3 |         8.0 |
| zswap_output | kzg       |      32 | 140.20 ms |  39.8 |   8.5 |        14.6 |    37.1 |        31.4 |
| zswap_output | fflonk<4> |       1 | 683.25 ms |  22.1 |  15.1 |        50.1 |    12.7 |         6.3 |
| zswap_output | fflonk<4> |      32 | 252.49 ms |  59.6 |   4.9 |        13.1 |    22.4 |        17.2 |
| poseidon     | kzg       |       1 | 686.21 ms |  16.3 |  25.2 |        50.3 |     8.2 |         2.7 |
| poseidon     | kzg       |      32 | 191.45 ms |  61.5 |  10.9 |        12.2 |    15.4 |         9.5 |
| poseidon     | fflonk<4> |       1 | 917.29 ms |  29.7 |  18.7 |        42.5 |     9.0 |         1.9 |
| poseidon     | fflonk<4> |      32 | 378.00 ms |  73.6 |   5.6 |        11.1 |     9.7 |         4.9 |
| sha_preimage | kzg       |       1 | 337.85 ms |  11.9 |  25.9 |        52.8 |     9.4 |         1.4 |
| sha_preimage | kzg       |      32 |  80.76 ms |  54.4 |  13.3 |        18.9 |    13.4 |         4.9 |
| sha_preimage | fflonk<4> |       1 | 467.06 ms |  28.0 |  18.8 |        43.4 |     9.9 |         0.8 |
| sha_preimage | fflonk<4> |      32 | 180.70 ms |  73.4 |   6.1 |        12.6 |     7.9 |         2.1 |
| ecdsa        | kzg       |       1 |   2.935 s |   9.2 |  24.5 |        50.0 |    16.4 |         9.1 |
| ecdsa        | kzg       |      32 | 733.98 ms |  37.4 |   8.4 |        14.4 |    39.9 |        35.1 |
| ecdsa        | fflonk<4> |       1 |   3.520 s |  17.5 |  20.5 |        46.4 |    15.6 |         7.3 |
| ecdsa        | fflonk<4> |      32 |   1.148 s |  53.2 |   5.5 |        13.0 |    28.3 |        23.1 |
| schnorr      | kzg       |       1 | 131.99 ms |  12.7 |  15.0 |        38.5 |    33.8 |        29.5 |
| schnorr      | kzg       |      32 |  67.61 ms |  24.5 |   5.3 |         8.0 |    62.3 |        57.8 |
| schnorr      | fflonk<4> |       1 | 166.19 ms |  24.9 |  11.6 |        34.2 |    29.3 |        23.5 |
| schnorr      | fflonk<4> |      32 |  99.93 ms |  43.4 |   4.0 |         8.8 |    43.8 |        39.4 |
| jwt          | kzg       |       1 |  13.323 s |   7.8 |  29.3 |        54.6 |     8.3 |         0.9 |
| jwt          | kzg       |      32 |   2.166 s |  48.6 |  16.8 |        20.0 |    14.5 |         5.4 |
| aggregation  | kzg       |       1 |  13.185 s |   5.3 |  21.0 |        66.6 |     7.1 |         1.9 |
| aggregation  | kzg       |      32 |   1.977 s |  36.6 |  14.7 |        27.6 |    21.1 |        13.0 |
| ivc_step     | fflonk<3> |       1 |   7.627 s |  10.5 |  18.1 |        62.8 |     8.7 |         2.7 |
| ivc_step     | fflonk<3> |      32 |   1.601 s |  50.7 |   8.7 |        20.4 |    20.2 |        12.9 |

## Caveats

- **The 1-thread configuration only limits the rayon pool.** G1 MSMs are
  executed by blst's `multi_exp_affine`, which uses its own thread pool, so
  MSM time does not shrink at 1 thread, and the "1 thread" numbers are not
  those of a single-core machine. This is a known limitation.
- **`ivc_step` is not comparable with the other fflonk cases.** It runs
  `FflonkKZG<3>`, which the IVC library fixes, while the others run
  `FflonkKZG<4>`. Its timed section is a full `IvcProver::prove_step`, which
  also verifies the previous proof off-circuit.
- **`aggregation` is not the `single_circuit_aggregation` example.** It is a
  batch-verification relation: 2 inner SHA-256 preimage proofs verified
  in-circuit. The example needs an SRS larger than the 2^19 one available.
  For the same reason no workload with `k + 4 > 19` runs under fflonk.
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
  cases, and a full run has 26 cases. `scripts/ab.sh` gathers 20 per side by
  default.
