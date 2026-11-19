# GPU prover against the stock CPU prover

Tree: `ffa83b28` (the PR rebased onto upstream main `4bea43d4`). The CPU column is stock midnight-proofs at that tree, which includes the faster commitment MSM (`commit_msm`, #594). The GPU column is the same tree with the midnight-gpu hooks installed.

Every number is MEASURED. Each k row is one process: 1 cold proof, then 3 warm proofs on the same key and context. The throughput rows are one process per mode: 1 cold proof, then 64 warm proofs. The stock CPU verifier (`prepare` plus the KZG pairing check) accepted every proof.

## Box

- GPU: NVIDIA GeForce RTX 5090 Laptop GPU, 24463 MiB, SM 120, driver 615.78.08, CUDA 13.4 (libcudart.so.13 from the CUDA 13.4 toolkit, checked with `ldd` before the timed runs).
- CPU: Intel Core Ultra 9 275HX, 24 cores. `RAYON_NUM_THREADS=24` in both modes.
- Toolchain: cargo 1.90.0, release profile.
- Each process waits for a one-minute load below 2 before its first proof. No other benchmark ran on the box during the set.

## Circuit

This is the `gpu-prover/bench/rc1` chain circuit: `x[i+1] = x[i]^2 + 3` in the BLS12-381 scalar field, four advice columns, one selector, no lookups. The start and end values are bound to one public instance column. It uses KZG with a public test SRS (`unsafe_setup`, fixed seed), and a Blake2b transcript.

## Head to head (seconds per proof)

| k | CPU cold | GPU cold | CPU warm median (min-max) | GPU warm median (min-max) | Warm speedup | Verified | GPU device peak | GPU declines |
|---|---|---|---|---|---|---|---|---|
| 14 | 0.147 | 0.212 | 0.167 (0.164-0.168) | 0.106 (0.105-0.108) | 1.57x | 4/4 + 4/4 | 42.5 MB | 2 per proof: `msm below-min-k` |
| 16 | 0.556 | 0.338 | 0.562 (0.560-0.566) | 0.217 (0.215-0.220) | 2.59x | 4/4 + 4/4 | 89.9 MB | 0 |
| 18 | 2.050 | 0.887 | 2.109 (2.080-2.345) | 0.690 (0.685-0.698) | 3.06x | 4/4 + 4/4 | 272.3 MB | 0 |
| 20 | 8.548 | 2.490 | 8.584 (8.556-8.612) | 2.352 (2.315-2.747) | 3.65x | 4/4 + 4/4 | 1002.1 MB | 0 |
| 21 | 17.253 | 4.629 | 17.485 (17.403-17.538) | 4.351 (4.292-4.415) | 4.02x | 4/4 + 4/4 | 1975.2 MB | 0 |

- Warm speedup is the CPU warm median divided by the GPU warm median. Each warm median is over 3 proofs.
- Device calls per GPU proof: 11 MSM, 7 NTT (forward and inverse), 1 quotient at k >= 16. At k = 14 there are 9 MSM: two small MSMs fall below the device's minimum size, run on the CPU and are counted as `below-min-k` declines.
- The device peak is the backend's tracked device allocation, sppark buffers included. Driver and context memory are not included.
- k = 16 check after #594: every GPU proof at k = 16 made 11 MSM calls. The hook is still reached through the new `commit_msm` path.
- Device errors: 0 at every k.

## Batch mode

The PR has no multi-proof batch call:

- `create_proof` takes one circuit and its instances, so several circuit instances cannot share one proof.
- `midnight-gpu` and `midnight-gpu-prover` have no `prove_many` or batch entry point.
- The daemon serves one request at a time and holds one more in its queue (`QUEUE_PLACES = 2`). A further request gets `busy` at once.
- "Batched" in the oracle refers to the batched LogUp lookups and the tiled quotient numerator inside one proof.

The benchmark registers the SRS and key once in its process and proves in sequence. The table below shows N sequential warm proofs in one process at k = 16. The N = 1, 4 and 16 rows are the first N warm proofs of the 64-proof run.

| N | GPU proofs/s | GPU median latency (max) | CPU proofs/s | CPU median latency (max) | Throughput ratio |
|---|---|---|---|---|---|
| 1 | 5.01 | 0.200 s (0.200) | 1.67 | 0.598 s (0.598) | 3.0x |
| 4 | 5.07 | 0.197 s (0.201) | 1.74 | 0.568 s (0.598) | 2.9x |
| 16 | 5.09 | 0.197 s (0.202) | 1.73 | 0.566 s (0.643) | 2.9x |
| 64 | 5.07 | 0.196 s (0.219) | 1.74 | 0.567 s (0.646) | 2.9x |

- Proofs/s is N divided by the summed prove time of those N proofs.
- All 65 proofs in each mode verified. GPU device peak was 89.9 MB with 0 fallbacks, and it stays flat across the 64 proofs.

## Test suites

Tree `ffa83b28`, on the same box, counted from the `test result` lines:

- `cargo clippy --workspace --all-targets` with and without `--all-features`, `-D warnings`: clean.
- `midnight-proofs` lib tests with no feature, with `prover-par` and with `gpu-test`, the `gpu_install` and `gpu_msm_crosscheck` tests, and `cargo check -p midnight-proofs --no-default-features`: all passed.
- `midnight-gpu --features cuda,test-fault`: 36 binaries, 85 passed, 0 failed, 10 ignored. With `gpu-test` on, every device-served commitment MSM in these tests is checked against `msm_pippenger`.
- `midnight-gpu-prover --features cuda`: 12 binaries, 97 passed, 0 failed, 2 ignored.
- The ignored tests are child-process helpers and opt-in device checks.

## Commands

From the root of the tree, with `PATH` holding the CUDA 13.4 `bin` directory, `LD_LIBRARY_PATH` holding its `lib64` directory, `MIDNIGHT_GPU_ARCHS=120` and `RAYON_NUM_THREADS=24`:

```sh
export RC1_WORK_DIR=<work dir> RC1_CACHE=<work dir>/key-cache
bash gpu-prover/bench/rc1/scripts/build.sh
export RC1_STOCK_BIN=$RC1_WORK_DIR/bin/rc1-cpu
for k in 16 14 18 20 21; do
  RC1_K=$k $RC1_WORK_DIR/bin/rc1-cpu prepare
  RC1_K=$k RC1_WARM=3 RC1_REP=1 $RC1_WORK_DIR/bin/rc1-cpu run > raw/k$k-cpu.tsv
  RC1_K=$k RC1_WARM=3 RC1_REP=1 $RC1_WORK_DIR/bin/rc1-gpu run > raw/k$k-gpu.tsv
done
RC1_K=16 RC1_WARM=64 RC1_REP=2 $RC1_WORK_DIR/bin/rc1-gpu run > raw/seq16-gpu.tsv
RC1_K=16 RC1_WARM=64 RC1_REP=2 $RC1_WORK_DIR/bin/rc1-cpu run > raw/seq16-cpu.tsv
```

## Files

- `raw/*.tsv`: one row per proof. The columns are those of `gpu-prover/bench/rc1/README.md`.
- `results.json`: the medians, ranges, verification flags and throughput prefixes computed from the TSVs.
- `run.log`: the step log of the run.

## Not covered

- Seeded byte comparison: the bench proves with OS randomness, so proof bytes are not compared. Seeded proofs are deterministic only in the `test-seed` example, which this set did not run.
- There is no daemon run with concurrent clients.
