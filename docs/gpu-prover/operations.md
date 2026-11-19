# Operations

This document tells you how to build, configure, run and supervise the GPU
prover, and what to do when it fails. The crate reference is
[gpu-prover/README.md](../../gpu-prover/README.md). The container reference is
[gpu-prover/container/README.md](../../gpu-prover/container/README.md).

## 1. Install

The CPU build needs only the Rust toolchain of `rust-toolchain.toml`. A GPU
build needs these items on the build machine:

- The CUDA toolkit (`nvcc`). The build finds it through `CUDA_PATH`, else
  `CUDA_HOME`, else `nvcc` on `PATH`.
- A C++17 host compiler that `nvcc` accepts.

The machine that runs the prover needs the NVIDIA driver and a device with
compute capability 7.0 or higher and cooperative launch. The build does not
need a device.

## 2. Build

Build the service with the device path:

```sh
MIDNIGHT_GPU_ARCHS=120 MIDNIGHT_GPU_REQUIRE_CUDA=1 \
  cargo build --release -p midnight-gpu-prover --features cuda
```

- Set `MIDNIGHT_GPU_ARCHS` to the SM numbers of your devices to shorten the
  build. Use `native` to compile for the devices of the build machine. Leave
  it unset for the default list (80, 86, 89, 90, 100, 120).
- Set `MIDNIGHT_GPU_REQUIRE_CUDA=1` in release builds. Without it, a missing
  `nvcc` gives a warning and a stub that runs every phase on the CPU.

Build the CPU-only service (no CUDA toolkit needed):

```sh
cargo build --release -p midnight-gpu-prover
```

Use the hooks in your own prover. Enable the feature `gpu` of
`midnight-proofs`, depend on `midnight-gpu` with the feature `cuda`, and install
the hooks once at start:

```rust
midnight_proofs::gpu::install(midnight_proofs::gpu::GpuHooks {
    msm_g1: Some(midnight_gpu::msm_g1),
    fft: Some(midnight_gpu::fft),
    ifft: Some(midnight_gpu::ifft),
    quotient: Some(midnight_gpu::quotient),
});
```

Call `midnight_gpu::end_request()` between proofs. It zeroes and frees every
buffer that held witness values. Treat a `false` result as an unconfirmed
erasure: stop the process.

## 3. Configuration

### 3.1 Build time (`midnight-gpu`)

| Variable | Default | Meaning |
|---|---|---|
| `CUDA_PATH`, `CUDA_HOME` | unset | CUDA toolkit root. Without them, the toolkit of `nvcc` on `PATH`. |
| `MIDNIGHT_GPU_ARCHS` | `80,86,89,90,100,120` (those the `nvcc` supports) | SM numbers to compile (SASS for each, PTX of the highest), or `native`. |
| `MIDNIGHT_GPU_REQUIRE_CUDA` | unset | `1`: a missing `nvcc` or a failed compile is a build error, not a stub. |

### 3.2 Run time (`midnight-gpu`)

| Variable | Default | Meaning |
|---|---|---|
| `MIDNIGHT_GPU` | unset | `off`: use no device. Every call declines. |
| `MIDNIGHT_GPU_MIN_K` | 14 | Smallest log2 size sent to the device (MSM length, transform size, extended quotient size). |
| `MIDNIGHT_GPU_MAX_BYTES` | 90% of the free device memory at the call | Device bytes one quotient may use. Above it the quotient declines. |
| `MIDNIGHT_GPU_QUOTIENT_THREADS` | 512 per multiprocessor | Grid threads of the quotient kernel, a multiple of 256 in `[256, 2^24]`. |
| `MIDNIGHT_GPU_STAGE` | on | `off`: no page-locked bounce buffer for copies of 16 MiB or more. |
| `MIDNIGHT_GPU_STAGE_THREADS` | up to 8 | Host copy threads of the staged copies. |
| `MIDNIGHT_GPU_WIPE_CHECK` | 0 | `1`: read every zeroed region back and compare it with zero (slower). |
| `MIDNIGHT_GPU_FAULT` | unset | Armed test faults, `class:point[:count],...`. Only in a build with the feature `test-fault`. |
| `CUDA_VISIBLE_DEVICES` | unset | Read by the CUDA runtime. The crate uses device 0 of the visible set. |

### 3.3 Daemon (`midnight-gpu-prover`)

Precedence, lowest first: default, JSON file, environment variable,
command-line flag. An unknown key in the file is an error.

| Field | Variable | Default | Meaning |
|---|---|---|---|
| (file) | `MIDNIGHT_GPU_PROVER_CONFIG` | unset | JSON config file (`--config` wins). |
| `max_k` | `MIDNIGHT_GPU_PROVER_MAX_K` | 25 | Largest circuit size (log2 rows). A larger circuit is refused at start. |
| `vk_sha256` | `MIDNIGHT_GPU_PROVER_VK_SHA256` | unset | Expected SHA-256 of the verifying key. A mismatch refuses the start. |
| `device` | `MIDNIGHT_GPU_PROVER_DEVICE` | `auto` | `auto` or `off`. |
| `threads` | `MIDNIGHT_GPU_PROVER_THREADS` | 0 | Prover threads. 0 is one per available CPU. |
| `resident` | `MIDNIGHT_GPU_PROVER_RESIDENT` | `evict` | `evict`: free the key copies before each reply. `keep`: keep them (device with no other user). |
| `wait_s` | `MIDNIGHT_GPU_PROVER_WAIT_S` | 20 | Longest admission wait for another device user, seconds. |
| `margin_mib` | `MIDNIGHT_GPU_PROVER_MARGIN_MIB` | 768 | Reserve added to the computed need, MiB. |
| `lock_path` | `MIDNIGHT_GPU_PROVER_LOCK` | unset | Device lock file. When set, a request uses the device only with a lease. |
| `wsl` | `MIDNIGHT_GPU_PROVER_WSL` | `auto` | WSL2 profile: `auto`, `on` or `off`. |
| `wsl_reserve_mib` | `MIDNIGHT_GPU_PROVER_WSL_RESERVE_MIB` | 4096 | WSL2 budget = device total minus this reserve. |
| `mode` | `MIDNIGHT_GPU_PROVER_MODE` | `production` | `production` or `acceptance`. |
| `zero_check` | `MIDNIGHT_GPU_PROVER_ZERO_CHECK` | 0 | Read every wiped region back. |
| `srs_path` | `MIDNIGHT_GPU_PROVER_SRS` | unset | SRS file (`RawBytesUnchecked`, the format of the Midnight SRS files). |
| `socket` | `MIDNIGHT_GPU_PROVER_SOCKET` | `$XDG_RUNTIME_DIR/midnight-gpu-prover.sock` | Daemon socket. Without `XDG_RUNTIME_DIR`: `/tmp/midnight-gpu-prover-$UID.sock`. |

### 3.4 Client (`midnight-gpu-prover`)

| Field | Variable | Default | Meaning |
|---|---|---|---|
| (file) | `MIDNIGHT_GPU_PROVER_CLIENT_CONFIG` | unset | JSON config file of the client (`--config` wins). |
| `socket` | `MIDNIGHT_GPU_PROVER_SOCKET` | as the daemon | Daemon socket. |
| `cpu_fallback` | `MIDNIGHT_GPU_PROVER_CPU_FALLBACK` | 1 | Prove in-process when the daemon cannot serve. |
| `reply_timeout_s` | `MIDNIGHT_GPU_PROVER_REPLY_TIMEOUT_S` | 3600 | Longest wait for a reply, seconds. |
| `breaker_failures` | `MIDNIGHT_GPU_PROVER_BREAKER_FAILURES` | 3 | Consecutive daemon failures that open the breaker. |
| `breaker_window_s` | `MIDNIGHT_GPU_PROVER_BREAKER_WINDOW_S` | 600 | Window of those failures, seconds. |
| `breaker_cooldown_s` | `MIDNIGHT_GPU_PROVER_BREAKER_COOLDOWN_S` | 600 | Time the open breaker skips the daemon, seconds. |
| `breaker_state` | `MIDNIGHT_GPU_PROVER_BREAKER_STATE` | socket path + `.breaker` | Breaker state file, owner-only. |
| `alert_cmd` | `MIDNIGHT_GPU_PROVER_ALERT_CMD` | unset | Program run once when the breaker opens, with the alert line as its argument. |

### 3.5 Container scripts

| Variable | Default | Meaning |
|---|---|---|
| `MIDNIGHT_GPU_PROVER_HEALTH_CMD` | unset | Replaces the command of `healthcheck.sh`. |
| `CUDA_CACHE_PATH` | set by the systemd unit | Writable directory for the CUDA JIT cache. |

## 4. Run the daemon

The shipped binaries serve the example relation `PoseidonPreimage`. For your
own circuit, write two short binaries that call `daemon::main` and
`client::main` with your relation (see [gpu-prover/README.md](../../gpu-prover/README.md)).

```sh
P=target/release
$P/midnight-gpu-proverd --srs /path/to/srs --socket /run/prover/proverd.sock &
$P/midnight-gpu-prover-client --socket /run/prover/proverd.sock health
$P/midnight-gpu-prover-client --socket /run/prover/proverd.sock prove in.bin proof.bin --srs /path/to/srs
$P/midnight-gpu-prover-client --socket /run/prover/proverd.sock stop
```

- Give the input file mode 600 and the daemon's owner. The daemon refuses any
  other input file.
- Give the client `--srs` for its CPU fallback.
- Use `--insecure-test-srs` only for tests. The process knows the toxic waste
  of that SRS.
- Send `SIGTERM` or a `stop` request for a graceful stop. The daemon serves the
  queued request, then removes its socket file.

**Shared device.** Set `lock_path` when other programs use the device. The
caller takes an exclusive `flock` on the lock file and passes the locked
descriptor with the request (`--lock PATH` or `--lock-fd N`). Without a lease
the request runs on the CPU and is labelled `cpu`.

## 5. Containers

The image builds from the repository root with BuildKit:

```sh
docker buildx build -f gpu-prover/container/Dockerfile -t midnight-gpu-prover:local .
```

The builder sets `MIDNIGHT_GPU_REQUIRE_CUDA=1`, runs offline against the
vendored crates of `Cargo.lock`, and has no `nvptx64` target. The runtime image
holds the daemon, the client and two scripts. It runs as uid 10001.

**NVIDIA Container Toolkit.** Install the toolkit on the host and pass
`--gpus all`. The full command is in the [container README](../../gpu-prover/container/README.md).

**CDI.** Generate the CDI spec, then start the container through
`gpu-prover/container/run-gpu.sh`. The wrapper runs `check-cdi.sh` on every spec
and starts the command only when each spec is current:

```sh
sudo nvidia-ctk cdi generate --output=/etc/cdi/nvidia.yaml
gpu-prover/container/run-gpu.sh docker run -d --device nvidia.com/gpu=all --restart on-failure:3 ... midnight-gpu-prover:local
```

Regenerate the spec after every driver update.

**WSL2 CDI staleness.** On WSL2 the driver directory under
`/usr/lib/wsl/drivers/` changes its name when the Windows driver changes. A
spec from before the update names the old directory, and the container starts
without a working GPU. Start every GPU container through `run-gpu.sh`, which
refuses a stale spec (for a systemd unit, run `check-cdi.sh` as `ExecStartPre=`).
A restart by the `on-failure:3` policy does not pass through the wrapper, so after
a driver update stop the container, regenerate the spec and start it again through
`run-gpu.sh`. `check-cdi.sh` exits 1 when a path in the spec is missing. When
`nvidia-ctk` is installed, it also exits 1 when a spec generated from the live
driver names another directory [GPU-066].

## 6. Supervision

A daemon that keeps failing must stop. The clients then prove on the CPU and do
not wait for a restart loop.

**systemd.** The unit
[`midnight-gpu-proverd.service`](../../gpu-prover/container/midnight-gpu-proverd.service) sets:

```ini
[Unit]
StartLimitIntervalSec=600
StartLimitBurst=3

[Service]
Restart=on-failure
RestartSec=5s
```

systemd starts the daemon at most 3 times in 600 s. Then it refuses the next
start and leaves the unit `failed` with `Result=start-limit-hit`. Clear the
state with `systemctl reset-failed midnight-gpu-proverd`.

**Docker and Compose.** [`compose.yaml`](../../gpu-prover/container/compose.yaml) sets
`restart: on-failure:3` and a health check (`healthcheck.sh` every 30 s, timeout
10 s, start period 120 s, 3 retries). Docker restarts the container at most 3
times, so the container runs 4 times, then stays exited. This cap has no time
window. An unhealthy status does not restart the container. Only an exit does.

**Restart-cap test.** [`restart-cap.test.sh`](../../gpu-prover/container/restart-cap.test.sh) reads
the settings from the unit file and the Compose file and runs a stub that
always exits 1. It needs no GPU. Results on 2026-11-17 (Linux aarch64,
systemd 262, Docker 29.9.3):

| Supervisor | Result |
|---|---|
| systemd (transient user unit) | 3 starts in 600 s, then refused: `NRestarts=3`, `Result=start-limit-hit` |
| Docker | stopped after 3 restarts (4 runs), container `exited`, `RestartCount=3` |

[TESTED.md](../../gpu-prover/container/TESTED.md) records the same Docker cap with the
real image: 4 runs, `RestartCount=3`, and a client proof with label
`cpu-fallback` after the cap.

**Client CPU fallback and circuit breaker.** When the daemon is absent,
refuses, is busy or fails, the client proves in-process and labels the result
`cpu-fallback`. The breaker counts daemon failures:

- A failure is a daemon that cannot be reached, breaks the protocol, fails to
  prove or verify, or has retired.
- `busy` and refusals caused by the request (input, output, degraded, refused)
  are not failures.
- A served reply resets the count.
- After 3 consecutive failures within 600 s the breaker opens. The client skips
  the daemon for 600 s and proves on the CPU.
- When the breaker opens, the client writes one alert line to stderr. When
  `alert_cmd` is set, it runs that program once with the line as its argument.
- The state lives in an owner-only file, so it holds across client processes.

The breaker defaults match the systemd cap: 3 in 600 s.

## 7. Logs and records

- **Start record.** Before it opens the socket, the daemon writes one JSON line
  to stderr. It holds the circuit shape (degree, extended k, column counts,
  the device quotient shape), the device facts (name, compute capability,
  runtime and driver versions, build architectures) and the settings
  (features, policy, computed need, threads, verifying-key hash, key
  generation time, WSL2 flag).
- **Reply records.** After that the daemon writes one JSON line per reply. It
  holds prove and phase seconds, MSM count and seconds, device call counts,
  fallbacks by phase and reason, the admission step, the device peak, the host
  high-water mark, and the SHA-256 of the proof and of the public inputs.
- **Content rule.** No record holds a witness value, a key, a seed, a path or
  any other field of a request [GPU-054].
- **Where.** Under systemd, read them with `journalctl -u midnight-gpu-proverd`.
  In a container, read them with `docker logs midnight-gpu-prover`.
- **Health.** `midnight-gpu-prover-client health` gives the state (`ready`,
  `proving`, `stopping`), the queue, the requests served, the relation, k and
  the verifying-key hash. The daemon answers it during a proof too.

## 8. Troubleshooting

| Symptom | Cause | Action |
|---|---|---|
| Build warning `building the stub that declines every device call` | `nvcc` not found or the compile failed | Set `CUDA_PATH`. Set `MIDNIGHT_GPU_REQUIRE_CUDA=1` to make it an error. |
| Build warning `this nvcc does not support sm_N` | The toolkit is older than the requested architecture | Update the toolkit or remove the number from `MIDNIGHT_GPU_ARCHS`. |
| Start record shows no device | No usable device, `MIDNIGHT_GPU=off`, `device = off`, or a CPU-only build | Check `nvidia-smi`, the container device flags and the features. |
| Every proof labelled `cpu`, reason "the device lock is not held by the caller" | `lock_path` is set and the caller passed no locked descriptor | Pass `--lock PATH`, or unset `lock_path` on a device with no other user. |
| Proofs with step `evict` or `cpu` and a memory reason in `degraded_reasons` | Not enough free device memory | Free the device, lower `margin_mib`, or use a larger device. |
| Request refused in `acceptance` mode | A fallback or a degraded admission | Expected in that mode. Use `production` to serve degraded proofs. |
| Daemon exits with an erasure error | The wipe could not be confirmed | The supervisor restarts it. Check the driver log (`dmesg`) for device errors. |
| Unit `failed`, `Result=start-limit-hit` | 3 exits in 600 s | Read the journal for the cause, then `systemctl reset-failed midnight-gpu-proverd`. |
| Container `exited` after 4 runs | Restart cap of `on-failure:3` | Read `docker logs`, fix the cause, start the container again. |
| Container starts but sees no GPU (WSL2) | Stale CDI spec after a driver update | Regenerate the spec, then start the container again through `run-gpu.sh`. |
| Client alert line, every proof `cpu-fallback` | The breaker is open | Fix the daemon. The breaker skips the daemon until the cooldown ends. |
| Input refused | The file is not mode 600 or not owned by the daemon user | Fix the mode and owner. |
