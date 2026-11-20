# gpu-conformance

Tests that check the production GPU code against the formal model in
[`formal/gpu-prover`](../formal/gpu-prover/README.md). The crate has no library code and is
not published; the production crates are only its dev-dependencies.

| Test | What it replays |
|---|---|
| `tests/oracle_arithmetic.rs` | The Lean oracle's golden vectors (MSM, NTT, coset, quotient, gate, threshold, data movement) through the midnight-proofs hooks and midnight-gpu, on the stock CPU code and, with a device, on the device. |
| `tests/readback.rs` | GPU-038: every buffer the device reads back during a proof is a kind the oracle's data-movement policy permits. Needs a CUDA device. |
| `tests/actor_itf.rs` | The Quint model's ITF traces of the device-owner actor through its protocol core. |

The vectors are read from `formal/gpu-prover/vectors`, or from `ORACLE_VECTOR_DIR` when set.
A missing vector directory is a test failure, not a skip.

```sh
# CPU lanes (any machine)
cargo test -p midnight-gpu-conformance
# with a CUDA device (the CUDA core needs nvcc)
MIDNIGHT_GPU_REQUIRE_CUDA=1 cargo test --release -p midnight-gpu-conformance \
    --features midnight-gpu/cuda -- --include-ignored --test-threads=1
```

`gpu/scripts/gpu-gate.sh` runs these tests together with the device tests of midnight-gpu and the
service replay of midnight-gpu-prover.
