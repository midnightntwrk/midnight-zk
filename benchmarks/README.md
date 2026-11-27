# Prover benchmarks

`midnight-benchmarks` times the prover on a fixed set of circuits, so that a
change to the proof system can be measured the same way every time. It
provides:

- a standard set of workloads, from a Schnorr signature at 2^10 rows to a
  JWT credential at 2^17 rows;
- a runner that times them under KZG and fflonk with several packing sizes,
  single-threaded and multi-threaded, and writes the results as a table, JSON
  or markdown;
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

## Workloads

| name           | what it proves                                                                                                                                             |   k | schemes             |
| -------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- | --: | ------------------- |
| `zswap_output` | the output circuit of the Zswap protocol: opens a coin commitment (SHA-256) and a value commitment (a Jubjub MSM over a hash-to-curve base)                |  13 | all                 |
| `poseidon`     | a chain of 380 Poseidon hashes                                                                                                                             |  14 | all                 |
| `sha_preimage` | knowledge of a 24-byte preimage of a public SHA-256 digest                                                                                                 |  13 | all                 |
| `ecdsa`        | knowledge of an Ethereum signature (ECDSA over secp256k1 of a Keccak-256 digest) of a public message under a public key                                    |  15 | all                 |
| `schnorr`      | verification of a Schnorr signature over Jubjub with Poseidon as the hash function                                                                         |  10 | all                 |
| `jwt`          | validity of a 2.5 kB JWT credential signed with ECDSA over secp256k1: issuer signature, Base64 decoding, two JSON attributes, the holder's secret key      |  17 | kzg, fflonk-t2, -t4 |
| `aggregation`  | validity of a batch of 2 fflonk proofs of the SHA-256 preimage circuit (k = 13), verified in-circuit; the pairing check is left to the verifier            |  16 | all but fflonk-t16  |
| `ivc_step`     | one step of an incrementally verifiable computation: the IVC circuit of `midnight-aggregation` verifies its previous proof and runs 50 Poseidon iterations |  15 | fflonk-t8           |

`k` is the logarithm of the number of rows. `fflonk-t<T>` needs an SRS of
`T * 2^k` points and the largest one available has 2^19, which rules out the
largest packing sizes for `jwt` and `aggregation`.

`ivc_step` runs under the scheme of the IVC itself, `midnight_aggregation::ivc::PCS`.

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
synthesis            0.00 ms (0.0%)     0.00 ms (0.0%)     0.00 ms (0.0%)  12.90 ms (1.4%)     12.90 ms (1.4%)
advice_commit     117.26 ms (12.6%)     0.00 ms (0.0%)     0.00 ms (0.0%)   0.85 ms (0.1%)   118.11 ms (12.7%)
lookups              0.00 ms (0.0%)     0.00 ms (0.0%)     0.77 ms (0.1%)   9.49 ms (1.0%)     10.26 ms (1.1%)
permutation          0.00 ms (0.0%)     0.00 ms (0.0%)     0.00 ms (0.0%)   9.28 ms (1.0%)      9.28 ms (1.0%)
trash                0.00 ms (0.0%)     0.00 ms (0.0%)    29.05 ms (3.1%)   0.70 ms (0.1%)     29.75 ms (3.2%)
arguments_commit  126.69 ms (13.6%)     0.00 ms (0.0%)     0.00 ms (0.0%)   1.26 ms (0.1%)   127.95 ms (13.8%)
quotient          135.31 ms (14.6%)   98.77 ms (10.6%)  278.39 ms (30.0%)   1.02 ms (0.1%)   513.49 ms (55.3%)
evals                0.00 ms (0.0%)     0.00 ms (0.0%)    17.66 ms (1.9%)   0.08 ms (0.0%)     17.74 ms (1.9%)
multi_open          76.58 ms (8.2%)     0.00 ms (0.0%)     2.28 ms (0.2%)   8.25 ms (0.9%)     87.11 ms (9.4%)
total             455.85 ms (49.1%)  100.48 ms (10.8%)  328.15 ms (35.3%)  43.88 ms (4.7%)  928.36 ms (100.0%)
Concurrent calls (busy/wall): msm 1.0x, fft 1.0x, poly_eval 1.0x.
```

How to read it:

- A row is a phase of the prover. `phase total` is the wall time of the
  phase, and the percentages are relative to the wall time of the whole
  proof.
- A kernel column is the wall time during which at least one span of that
  kernel was open: the union of the intervals of its spans, not their sum. A
  kernel that runs on 32 threads for 10 ms counts 10 ms.
- `other` is the wall time of the phase during which no span of any kernel was
  open.
- Spans of different kernels can overlap when they run concurrently, in which
  case the kernel columns of a row add up to more than the phase total minus
  `other`. The four columns therefore do not always add up to 100%.
- `poly_eval` includes the polynomial divisions of the multi-open argument.
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
(under 0.6%). The runner still warns that a profiling build does not produce
reference numbers, and `compare` warns when one of its inputs comes from such
a build. Without the feature, every function of the profiling module is empty
and the prover is unchanged.

With `--json`, the breakdown of each case is stored under `breakdown`, in
nanoseconds: per phase `wall_ns` and `covered_ns` (the time inside any
kernel), and per kernel `wall_ns`, `busy_ns` (the sum of the durations of its
spans, which exceeds `wall_ns` when they run concurrently) and `calls`. Files
written without the feature have no `breakdown` and no `environment.profiling`,
and are read as builds without profiling.

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
under test alters the constraint system or the keys. It also warns about a
different `k`, a different proof size, a profiling build, or a different
machine. When both files carry a breakdown, it shows the change of each
kernel, without testing it for significance, since a breakdown describes a
single proof.

Two runs taken minutes apart on the same machine can differ by more than the
change under test. `scripts/ab.sh` measures two checkouts alternately instead,
typically two git worktrees:

```sh
git worktree add ../midnight-zk-base "$(git merge-base main HEAD)"
benchmarks/scripts/ab.sh ../midnight-zk-base . --rounds 3 -- --filter zswap --threads 1,max
```

It builds the crate in both checkouts, runs them for `--rounds` rounds
(default 4), alternating which side goes first, merges the samples of each
side with `jq`, and runs `compare` on the result. It also writes the
comparison as markdown to `comparison.md`. Arguments after `--` go to `run` on
both sides. The result files are kept in `./ab-results/<timestamp>` or in the
`--out` directory. Both checkouts must contain this crate, and both read the
SRS from `SRS_DIR`, which defaults to the assets of the head checkout. Set
`AB_BUILD_ARGS="--features profiling"` to compare breakdowns. `ab.sh --help`
has the details.

## Measuring a change for a pull request

A pull request that may affect the speed of the prover should state its
effect, measured the same way each time:

1. Add a worktree at the merge base of the branch:

   ```sh
   git worktree add ../midnight-zk-base "$(git merge-base main HEAD)"
   ```

2. On an otherwise idle machine, run from the root of the branch:

   ```sh
   benchmarks/scripts/ab.sh ../midnight-zk-base . --rounds 3 -- \
     --pcs kzg,fflonk-t8 --threads max --samples 5
   ```

   This takes about 25 minutes for all workloads. Add `--filter` after `--`
   to measure only the workloads the change concerns.

3. Paste the `comparison.md` of the output directory into the description of
   the pull request, with the CPU model and the number of cores.

If the comparison reports `VK HASH MISMATCH`, the change alters the circuits
of those workloads, so the two sides do not prove the same thing. Say so in
the pull request.

## Caveats

- **The timed section of `ivc_step` is a full `IvcProver::prove_step`**,
  which also verifies the previous proof off-circuit.
- **`aggregation` verifies `fflonk-t16` proofs in-circuit** under every outer
  scheme. Only the scheme of the outer proof varies.
- **`aggregation` is not the `single_circuit_aggregation` example.** It is a
  batch-verification relation: 2 inner SHA-256 preimage proofs verified
  in-circuit. The example needs an SRS larger than the 2^19 one available.
- **`zswap_output` runs at k = 13**, its optimal size. The criterion bench it
  replaces used k = 14, so the numbers of the two are not comparable.
- The breakdown of a case describes its last proof only.
- **The witnesses of `ivc_step` and `aggregation` differ across runs.** The
  prover draws some blinding factors from the operating system, so the proofs
  these two workloads verify in-circuit are not reproducible. Their circuits
  and verifying keys are.
- **Use enough samples before trusting a verdict.** With 5 samples per side,
  two runs of the same build are reported as different in about 3% of the
  cases, and a full run has 66 cases. `scripts/ab.sh` gathers 20 per side by
  default.
