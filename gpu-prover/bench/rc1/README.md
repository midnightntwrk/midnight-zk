# Public k = 21 prover benchmark

This benchmark measures midnight-proofs 0.9.0-rc.1 on one machine. Both executables use the same circuit, KZG parameters, serialized proving key, transcript, release profile and Rayon thread count. The CUDA build installs the MSM, FFT, inverse FFT and quotient hooks from midnight-gpu directly. The CPU build has the midnight-proofs `gpu` feature off.

## Circuit and inputs

In the BLS12-381 scalar field, start at `x[0] = 7` and iterate `x[i+1] = x[i]^2 + 3`. Each of the first `2^k - 16` rows holds four consecutive values in four advice columns. One selector enables four quadratic constraints, with the fourth reading the first column of the next row. One final cell holds the endpoint. Copy constraints bind the start and endpoint to the two entries of one public instance column. At k = 21 this gives 2,097,136 active rows and 8,388,544 constrained steps. The verifier recomputes the endpoint. There are no lookup tables.

The prover commits the dense advice columns, runs the permutation argument, constructs one quotient and opens the polynomials. The raw rows give the device call counts for this circuit. The workload differs from the private k = 21 circuit used for the 0.8.3 results.

## Running a set

Run the scripts from the repository root on Linux. Set `RC1_WORK_DIR` to the directory for the binaries and results. It defaults to `../rc1-results`. `RC1_CACHE` selects the key cache and defaults to `$RC1_WORK_DIR/key-cache`. Both CPU and GPU processes must use the same cache. Use the root workspace toolchain and lockfile, the offline Cargo registry, and a CUDA toolkit for the GPU build.

```sh
bench=gpu-prover/bench/rc1/scripts
bash "$bench/build.sh"
bash "$bench/prepare.sh"
```

The build uses eight Cargo jobs and defaults to SM 120 for an RTX 5080 Laptop GPU. Set `MIDNIGHT_GPU_ARCHS` to the explicit SM of another device before building. The build requires nvcc to produce the CUDA core. Preparation runs on the CPU. It generates a public benchmark SRS with `ParamsKZG::unsafe_setup` and `StdRng` seeded with `0x524331`. These test parameters have a publicly reproducible setup secret. It serializes the SRS and proving key, including the verifying key, in checked raw format. Every timed process deserializes the same files once before the first proof.

Use three repeats per mode, one prover process per repeat. Run CPU sets with the host otherwise quiet. Run GPU sets through the device scheduler. Use this order to vary which mode goes first.

| Repeat | First command | Second command |
|---|---|---|
| 1 | `bash "$bench/run-cpu.sh" 1` | `bash "$bench/run-gpu.sh" 1` |
| 2 | `bash "$bench/run-gpu.sh" 2` | `bash "$bench/run-cpu.sh" 2` |
| 3 | `bash "$bench/run-cpu.sh" 3` | `bash "$bench/run-gpu.sh" 3` |

Each set performs one cold proof and one warm proof by default (`RC1_WARM=1`). Keep N and `RAYON_NUM_THREADS` (default 8) identical across all six sets. The process samples the one-minute load after key loading, endpoint calculation and host registration of the SRS and key. It waits for a value below 2 (`RC1_MAX_LOAD` sets another bound) immediately before the cold proof. The same process and key serve the warm proof. Device buffers follow the backend's default request cleanup policy between proofs. The GPU wrapper times out at 690 seconds, with a three-second kill grace. A failed or interrupted set leaves the prior raw file intact.

`prove_s` measures transcript initialization, witness synthesis inside `create_proof`, the proof itself and transcript finalization. Each proof uses OS randomness. Setup, the quiet gate, counter reads, end-of-request cleanup and verification are outside this timer. After proving, the process passes the verifying key, verifier parameters and proof bytes to the stock CPU executable. It checks each proof with `prepare` and the KZG pairing check. `verify_s` measures those operations and transcript initialization. The runner publishes a set only after every proof verifies.

## Reading the TSV

The scripts append verified rows to `$RC1_WORK_DIR/box-out/raw-{cpu,gpu}.tsv`. The first proof has index 0. The row includes the repeat, k, Rayon thread count, load at the gate, device model and capacity. Time values are seconds. Memory and transfer sizes are bytes.

- `msm_calls`, `ntt_calls` and `quotient_calls` count completed device calls for that proof. NTT includes forward and inverse transforms. The rc.1 hook interface has no separate coset counter. The public prover API exposes no phase timings.
- `declines` records the `midnight_gpu::declines()` triples of class, reason and count. `hook_declines` records the corresponding proof-layer triples. `fallbacks` sums proof-layer declines, counting a device refusal once when both layers observe it. These counters cover instrumented paths. `device_errors` is the backend's error counter.
- `h2d_*` and `d2h_*` are the copy counts and byte totals from `xfer::stats()`. The `msm_d2h_*` fields report sppark bucket readbacks separately. The `stage` array gives staged copies and bytes, large direct copies and bytes, allocation failures, allocations, bus-bound requests and bounce bytes held at proof end. The first seven entries are per-proof deltas.
- `peak_device_bytes` is the peak of the backend's tracked device allocations, including sppark buffers, between request start and the end of proving. Driver and other process allocations fall outside this metric. A GPU row with a missing device phase or fallbacks needs the accompanying decline counts for interpretation.

Summarize complete sets with the following command. It reports median, minimum and maximum separately for cold and warm samples, pooled over the three processes of each mode. A change in GPU model or capacity, or a GPU row with zero completed device calls, prevents a comparison.

```sh
out="${RC1_WORK_DIR:-../rc1-results}/box-out"
python3 "$bench/summarize.py" "$out/raw-cpu.tsv" "$out/raw-gpu.tsv"
```

For a CPU-only smoke test, build just the stock target and use a smaller k. Smoke mode omits the quiet gate and prints `NA` for the start load.

```sh
export CARGO_BUILD_JOBS=8 RC1_K=8 RC1_WARM=1 RAYON_NUM_THREADS=4
export RC1_CACHE="${RC1_WORK_DIR:-../rc1-results}/smoke-cache"
cargo build --release --locked --offline -p midnight-gpu-prover --bin rc1-bench --features rc1-bench
bin="${CARGO_TARGET_DIR:-target}/release/rc1-bench"
"$bin" prepare
"$bin" smoke
```
