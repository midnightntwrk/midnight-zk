# midnight-gpu-prover

A resident prover service for Midnight circuits (KZG over BLS12-381). It keeps
the SRS and the proving key in host memory between requests. By default it
frees its device copies of them before each reply (resident policy `evict`).
It sends proof phases to a CUDA device when one is present and has room, and
runs the rest on the CPU.

The crate has three parts:

- `ProverService<R>`: the library. `R` is a ZK standard library `Relation`
  that also implements `ServedRelation` (decode request input bytes into the
  instance and the witness).
- `midnight-gpu-proverd`: a daemon that serves one service on a local Unix
  socket.
- `midnight-gpu-prover-client`: a library API and CLI that call the daemon.
  When the daemon cannot serve, the client proves on the CPU in-process.

The shipped binaries serve the example relation `example::PoseidonPreimage`
(knowledge of a Poseidon preimage of three field elements). A service for
another circuit is two short binaries:

```rust
// src/bin/my-proverd.rs
fn main() {
    std::process::exit(midnight_gpu_prover::daemon::main(MyRelation::new()));
}

// src/bin/my-prover-client.rs
fn main() {
    std::process::exit(midnight_gpu_prover::client::main(MyRelation::new()));
}
```

## What a request does

1. The daemon opens the input file once and checks the open file: a regular
   file, owned by the daemon's user, mode 600 (no group or other access). The
   bytes go into a buffer that is zeroed when it is dropped.
2. Admission. The service computes the device memory the proof needs from the
   loaded key. Resident buffers are counted once. It then takes the first step
   that fits:
   - `gpu`: every configured phase on the device;
   - `wait`: the same, after a wait of at most `wait_s` for another device
     user;
   - `evict`: the resident proving-key copies are freed and the quotient runs
     on the CPU;
   - `cpu`: nothing on the device.

   No phase starts that cannot finish in memory.
3. The proof is made with fresh randomness from the operating system.
4. Every device and staging buffer that held witness-dependent values is
   zeroed and freed. With `zero_check`, each region is read back and compared
   with zero first. If the erasure cannot be confirmed, the daemon replies with
   an error and exits. It takes no further witness.
   Limit: on the host, the service zeroes the input buffer it reads. The
   decoded witness (the relation's own types) and the buffers of the stock
   prover are freed without zeroing, as on any CPU prover.
5. With the default resident policy (`evict`), the proving-key copies and the
   MSM base tables are also freed before the reply; the next request uploads
   them again. `keep` holds them between requests and is meant only for a
   device with no other user.
6. The stock verifier checks the proof. If it refuses, the request fails and
   no output is written.
7. The proof is written owner-only (mode 600) through a temporary file and a
   rename.

The reply holds a record of counts, sizes, times and hashes: prove seconds,
phase seconds, MSM count and seconds, device call counts, fallbacks by phase
and reason, device peak, host high-water mark, and the SHA-256 of the proof
and of the public inputs. It never holds a witness value, a key, a seed, or
any field of the request.

## Labels

| Label | Meaning |
|---|---|
| `gpu` | At least one call ran on the device and none fell back. Expected declines (a call below the device's size threshold, no device) are no fallback. A degraded admission alone (step `evict`, a key the device quotient does not take) does not change the label: its reason is in `degraded_reasons`. |
| `gpu-degraded` | At least one call ran on the device and at least one call fell back to the CPU (reason `shape`, `unreduced`, `memory`, `fault` or `device-error`), or the request was withdrawn from the device (client hung up, lease lost). |
| `cpu` | No call ran on the device: no device phase admitted (no device, step `cpu`, no lock lease), or every device call declined (for example a circuit below the device's size threshold). |
| `cpu-fallback` | The client proved in-process because the daemon could not serve. |

In `acceptance` mode any degraded admission or fallback fails the request, and
no proof is written. Use it for benchmarks and acceptance runs, where a timing
that mixes CPU and device work is false. In `production` mode (the default) the
proof is served and labelled.

## Configuration

Precedence, lowest first: default, JSON config file
(`MIDNIGHT_GPU_PROVER_CONFIG` or `--config`), environment variable,
command-line flag. Unknown keys in the file are an error.

| Field | Environment variable | Default | Meaning |
|---|---|---|---|
| `max_k` | `MIDNIGHT_GPU_PROVER_MAX_K` | 25 | Largest circuit size (log2 rows). A larger circuit is refused at start. |
| `vk_sha256` | `MIDNIGHT_GPU_PROVER_VK_SHA256` | unset | Expected SHA-256 of the verifying key (`RawBytes`). A mismatch refuses the start. |
| `device` | `MIDNIGHT_GPU_PROVER_DEVICE` | `auto` | `auto` (use a detected device) or `off`. `CUDA_VISIBLE_DEVICES` is respected by the CUDA runtime. |
| `threads` | `MIDNIGHT_GPU_PROVER_THREADS` | 0 | Rayon threads of the prover; 0 is one per available CPU. |
| `resident` | `MIDNIGHT_GPU_PROVER_RESIDENT` | `evict` | `evict`: free the proving-key copies and MSM base tables before each reply; the next request uploads them again. `keep`: hold them between requests (opt-in, for a device with no other user). |
| `wait_s` | `MIDNIGHT_GPU_PROVER_WAIT_S` | 20 | Longest admission wait for another device user, seconds. |
| `margin_mib` | `MIDNIGHT_GPU_PROVER_MARGIN_MIB` | 768 | Reserve added to the computed need, MiB. |
| `max_device_peak_mib` | `MIDNIGHT_GPU_PROVER_MAX_DEVICE_PEAK_MIB` | 0 | Bound on the device peak of one request, MiB (0: none). Above it the reply goes out, then the daemon exits 3 so that its supervisor restarts it. |
| `max_host_hwm_mib` | `MIDNIGHT_GPU_PROVER_MAX_HOST_HWM_MIB` | 0 | Bound on the host high-water mark after a request, MiB (0: none). Handled as `max_device_peak_mib`. |
| `lock_path` | `MIDNIGHT_GPU_PROVER_LOCK` | unset | Device lock file. When set, a request uses the device only with a lease (see below). |
| `wsl` | `MIDNIGHT_GPU_PROVER_WSL` | `auto` | WSL2 profile: `auto` (detect `/dev/dxg` or Microsoft in `/proc/version`), `on`, `off`. |
| `wsl_reserve_mib` | `MIDNIGHT_GPU_PROVER_WSL_RESERVE_MIB` | 4096 | WSL2 budget = device total minus this reserve. |
| `mode` | `MIDNIGHT_GPU_PROVER_MODE` | `production` | `production` or `acceptance`. |
| `zero_check` | `MIDNIGHT_GPU_PROVER_ZERO_CHECK` | 0 | Read every wiped region back (slower). |
| `srs_path` | `MIDNIGHT_GPU_PROVER_SRS` | unset | SRS file (`RawBytesUnchecked`, the format of the Midnight and Filecoin SRS files). |
| `socket` | `MIDNIGHT_GPU_PROVER_SOCKET` | `$XDG_RUNTIME_DIR/midnight-gpu-prover.sock` | Daemon socket. Without `XDG_RUNTIME_DIR`: `/tmp/midnight-gpu-prover-$UID.sock`. |

Client (`MIDNIGHT_GPU_PROVER_CLIENT_CONFIG` for its JSON file):

| Field | Environment variable | Default | Meaning |
|---|---|---|---|
| `socket` | `MIDNIGHT_GPU_PROVER_SOCKET` | as above | Daemon socket. |
| `cpu_fallback` | `MIDNIGHT_GPU_PROVER_CPU_FALLBACK` | 1 | Prove in-process when the daemon cannot serve. |
| `reply_timeout_s` | `MIDNIGHT_GPU_PROVER_REPLY_TIMEOUT_S` | 3600 | Longest wait for a reply. |
| `breaker_failures` | `MIDNIGHT_GPU_PROVER_BREAKER_FAILURES` | 3 | Consecutive daemon failures that open the breaker. |
| `breaker_window_s` | `MIDNIGHT_GPU_PROVER_BREAKER_WINDOW_S` | 600 | Window of those failures, seconds. |
| `breaker_cooldown_s` | `MIDNIGHT_GPU_PROVER_BREAKER_COOLDOWN_S` | 600 | Time the open breaker skips the daemon, seconds. |
| `breaker_state` | `MIDNIGHT_GPU_PROVER_BREAKER_STATE` | socket path + `.breaker` | Breaker state file (owner-only). |
| `alert_cmd` | `MIDNIGHT_GPU_PROVER_ALERT_CMD` | unset | Program run once when the breaker opens, with the alert line as its argument. |

The breaker defaults match a supervisor that restarts the daemon at most three
times in ten minutes. A daemon that cannot be reached, breaks the protocol,
fails to prove or verify, or has retired counts as a failure. `busy` and
refusals caused by the request do not count. A served reply resets the count.

## Device lock and WSL2

The service never takes the device lock. When `lock_path` is set, the caller
holds an exclusive `flock` on that file and passes the locked descriptor with
the request (`SCM_RIGHTS`; the CLI does this with `--lock PATH` or
`--lock-fd N`). The daemon accepts the descriptor only if it names the lock
file, the lock is held, and that descriptor's open file description is the
holder. A lock held by another process gives no lease. The daemon keeps its
copy of the descriptor until the request has been wiped, so the lock stays
held even if the client disconnects. Without a lease the request runs on the
CPU and is labelled `cpu`, with the reason.

Under WSL2 the CUDA free-memory query does not see other device users. The
WSL2 profile therefore admits against a fixed budget (device total minus
`wsl_reserve_mib`) with no wait, and refuses `resident = keep`. Set
`lock_path` there; without a lease, no device work runs.

Limit: a device user that ignores the lock is not seen and not protected
against.

## Protocol

Newline-delimited JSON over the Unix socket. One request line and one reply
line per connection. The socket has mode 0600, and only peers with the
daemon's uid are served.

| Request | Effect |
|---|---|
| `{"op":"health"}` | State (`ready`, `proving`, `stopping`), queue, requests served, relation, k, VK hash. Answered at once, also during a proof. |
| `{"op":"prove","input":PATH,"output":PATH,"zero_check":false}` | Prove, verify, write the proof. |
| `{"op":"stats"}` | Start record, requests served, device bytes held. |
| `{"op":"evict","tables":false}` | Free the resident proving-key copies (and with `tables` the MSM tables). |
| `{"op":"stop"}` | Graceful stop: serve what is queued, then exit and remove the socket file. `SIGTERM` and `SIGINT` do the same. |

A reply is `{"ok":true,...}` or `{"ok":false,"error":{"kind":KIND,"message":TEXT}}`.
`KIND` is one of `busy`, `bad-request`, `refused`, `input`, `output`, `prove`,
`verify`, `degraded`, `retired`. One request is served and one waits; a third
gets `busy` at once.

The daemon writes one start record to stderr before it opens the socket:
degree, extended k, column counts, the device quotient shape, device facts
(name, compute capability, runtime and driver versions), features, policy,
computed need, thread count, VK hash, key generation time and the WSL2 flag.
After that it writes one JSON line per reply.

## Example: serve and call

```sh
cargo build --release -p midnight-gpu-prover
P=target/release

# A test SRS is generated in-process. It is insecure: use --srs for real keys.
$P/midnight-gpu-proverd --insecure-test-srs --socket /tmp/demo.sock &

$P/midnight-gpu-prover-client --socket /tmp/demo.sock health

# 96 bytes: three canonical little-endian BLS12-381 scalars. Mode 600.
head -c 32 /dev/zero > in.bin; head -c 32 /dev/zero >> in.bin; head -c 32 /dev/zero >> in.bin
chmod 600 in.bin
$P/midnight-gpu-prover-client --socket /tmp/demo.sock prove in.bin proof.bin --insecure-test-srs

$P/midnight-gpu-prover-client --socket /tmp/demo.sock stop
```

The test `binaries_serve_and_call` in `tests/daemon.rs` runs this round trip,
then proves once more after the stop and checks the `cpu-fallback` label.

## Features

- `cuda`: route phases to a CUDA device through `midnight-gpu`. A build
  without the CUDA toolkit still compiles. Without a detected device every
  phase runs on the CPU.
- `test-seed`: `ProverService::prove_seeded` and the `seeded_prove` example,
  for byte-identity tests. The daemon never takes a seed. A build with this
  feature writes the marker `MIDNIGHT-GPU-PROVER-TEST-SEED-BUILD-NOT-FOR-RELEASE`
  to stderr at start; `container/check-no-test-seed.sh IMAGE` refuses an image
  that holds the marker or a file named `*seeded*`.

`cargo run --release -p midnight-gpu-prover --example seeded_prove --features
test-seed[,cuda] -- OUT_DIR` proves the example input with seed 7 and 8 threads
on the CPU path and, when a device is detected, on the device path. It writes
`OUT_DIR/cpu.proof` and `OUT_DIR/gpu.proof` and prints `PATH SHA256` for each.

Every feature compiles with `--all-features` on a machine without CUDA.

## Tests

`cargo test -p midnight-gpu-prover --all-features` runs the CPU-path tests:
config, admission arithmetic with fake device memory (including the WSL2
budget), lock leases, protocol, socket mode, queue and `busy`, health during a
proof, input refusal, resident policy, fallback labelling, the circuit breaker,
verify-before-return, retirement, and the binaries end to end. The device tests
in `tests/gpu.rs` compile only when the device crates are linked, and skip when
no device is found.
