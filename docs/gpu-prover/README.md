# GPU prover

This pull request adds an optional NVIDIA GPU path to the midnight-proofs
prover. The path moves the heaviest pure functions of a proof to a CUDA
device: the G1 multi-scalar multiplication (MSM), the forward and inverse
NTT, the coset transform and the quotient polynomial. Each device function
returns the exact value of the stock CPU function or declines. On a decline
the stock CPU code runs on the unchanged input. The proof, the transcript and
the random draws are the ones the CPU prover makes.

Without the cargo feature `gpu`, midnight-proofs compiles the release prover
code. Without the CUDA toolkit, the device crate compiles a stub that declines
every call. Upstream CI therefore needs no GPU and no CUDA install.

## How the pieces fit

```text
 caller (wallet, proof server, service)
        |
        v
 midnight-gpu-prover      daemon on a Unix socket, client with CPU fallback,
 (gpu-prover/)            admission ladder, wipe, verify before return
        |
        v
 midnight-proofs          feature `gpu`: hook points in the prover,
 (proofs/src/gpu/)        one hook set per process, stock code on decline
        |
        v
 midnight-gpu             CUDA kernels: sppark MSM and NTT (vendored),
 (gpu/)                   coset transform, quotient interpreter and division,
                          zero-before-free of every witness buffer
```

1. `midnight-proofs` with the feature `gpu` defines the hook points and the
   `install` function. It offers each hooked operation to the installed hook
   first.
2. `midnight-gpu` holds the device code. Its public functions have the
   signatures of the hook fields, so a process installs them as they are.
3. `midnight-gpu-prover` is a resident service. It holds the SRS, the keys and
   the device state between requests. It decides per request which phases run
   on the device, wipes the device buffers, and verifies each proof before it
   returns it.

## Documents

| Document | Content |
|---|---|
| [architecture.md](architecture.md) | Pipeline, hook points and the hook contract, device kernels, resident data, admission, wipe, read-back, daemon and client, fallback levels, build. |
| [operations.md](operations.md) | Install, build, every environment variable, daemon, containers, supervision, CPU fallback and circuit breaker, logs, troubleshooting. |
| [security.md](security.md) | The zero-knowledge argument, the wipe and its limits, permissions, lock leases, threat model, residual risks. |
| [benchmarks.md](benchmarks.md) | The Compact suite (CPU and GPU, 133 proofs), the large-circuit numbers, Preview transactions. |
| [compact-suite.md](compact-suite.md) | The Compact programs, calls and k values, and how to reproduce the suite. |

## Crates and files

| Path | What it is |
|---|---|
| [`proofs/src/gpu/`](../../proofs/src/gpu/mod.rs) | Hook module of midnight-proofs (feature `gpu`, test switches under `gpu-test`). |
| [`gpu/`](../../gpu/src/lib.rs) | `midnight-gpu`: CUDA kernels, [build script](../../gpu/build.rs), [vendored sppark](../../gpu/third_party/sppark/VENDORED.txt). |
| [`gpu-prover/`](../../gpu-prover/README.md) | `midnight-gpu-prover`: library, daemon `midnight-gpu-proverd`, client `midnight-gpu-prover-client`. |
| [`gpu-prover/container/`](../../gpu-prover/container/README.md) | Dockerfile, Compose file, systemd unit, CDI check, restart-cap test, [test record](../../gpu-prover/container/TESTED.md). |
| [`gpu-prover/bench/compact/`](../../gpu-prover/bench/compact/README.md) | Compact proof benchmark: runner, [results](../../gpu-prover/bench/compact/results/compare-rtx-5080-laptop.tsv), [proof server note](../../gpu-prover/bench/compact/PROOF-SERVER.md). |
| [`gpu-prover/bench/large-circuit/`](../../gpu-prover/bench/large-circuit/README.md) | The k = 21 measurements made before the port to 0.9.0-rc.1. |
| [`gpu-spec/`](../../gpu-spec/README.md) | The specification: [requirements](../../gpu-spec/requirements.md) GPU-001 to GPU-072, [design](../../gpu-spec/design.md), [results and open items](../../gpu-spec/RESULTS.md). |
| [`gpu-spec/oracle/`](../../gpu-spec/oracle/Main.lean) | Lean 4 oracle: reference arithmetic, device models and theorems, the request state machine. |
| [`gpu-spec/quint/`](../../gpu-spec/quint/gpu_service.qnt) | Quint model of the request state machine, written from the requirements only. |
| [`gpu-spec/vectors/`](../../gpu-spec/vectors/README.md) | Golden vectors that the Rust tests compare the kernels with. |
| [`scripts/check-generic.sh`](../../scripts/check-generic.sh) | CI check: no machine-local names or paths in the tree. |
| [`docs/gpu-prover-site/`](../gpu-prover-site/index.html) | An illustrated walk through the pipeline, the kernels and the fallback. |

## What the pull request leaves out

- A Rust MSM kernel exists in the earlier work. It needs the `nvptx64` target,
  so it is left out. Only the CUDA (sppark) MSM ships.
- The 0.8.3 backport of the hooks, which the Compact benchmark used, is not in
  the pull request. The pull request carries the same design on
  midnight-proofs 0.9.0-rc.1.
- The Compact proof preimages hold witness data. They are not committed.
