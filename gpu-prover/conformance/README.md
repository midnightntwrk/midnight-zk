# gpu-prover conformance

Unit tests of midnight-gpu-prover that replay the formal model in
[`formal/gpu-prover`](../../formal/gpu-prover/README.md) through the proving service:

- `oracle_conformance.rs`: the Lean oracle's service vectors (`vectors/service`) through
  `ProverService` with a test device that supplies memory readings, fault counters and wipe
  confirmations, and the client's fallback and breaker through a reply seam.
- `oracle_itf.rs`: the Quint model's ITF traces of the request state machine through the same
  adapter (`ORACLE_ITF_DIR`).
- `oracle_reader.rs`: a complete prove request through the daemon's reader on a socket pair.

They reach crate-private items, so they are compiled into the crate's unit tests, from this
folder, only with `cfg(all(test, feature = "conformance"))`. No build of the library or the
daemon contains them, and the crate's tests run without `formal/` when the feature is off.

```sh
cargo test -p midnight-gpu-prover --features conformance --lib oracle_conformance
```

The vectors are read from `formal/gpu-prover/vectors`, or from `ORACLE_VECTOR_DIR`; a missing
directory fails the tests. `gpu/scripts/gpu-gate.sh` runs the two gate tests
(`service_oracle_vectors`, `itf::quint_daemon_gate`) with frozen ITF traces.
