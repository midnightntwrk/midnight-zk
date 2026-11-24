# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
* `ProverService<R>`: a resident prover for any ZK standard library `Relation` that implements `ServedRelation`. It holds the SRS, the keys and the device state between requests, checks an optional verifying-key pin at start, admits device phases by the ladder `gpu`, `wait`, `evict`, `cpu` from the device memory need computed from the key, wipes witness-dependent buffers after each request, and verifies every proof with the stock verifier before it returns it
* `midnight-gpu-proverd`: a daemon on a local Unix socket (mode 0600, owner only), with a queue of one, `health`, `stats`, `evict` and graceful `stop`, and a newline-delimited JSON protocol
* `midnight-gpu-prover-client`: a client library and CLI with in-process CPU fallback (`cpu-fallback` label) and a persistent circuit breaker with an alert hook
* Device lock leases passed as file descriptors over the socket, and a WSL2 profile (budget admission, no resident data between requests)
* Configuration through a struct, a JSON file and `MIDNIGHT_GPU_PROVER_*` environment variables
* Features `cuda` and `test-seed`
* `seeded_prove` example (`test-seed` only): seeded proofs on the CPU and device paths, with their SHA-256
* `container/check-no-test-seed.sh`: refuses an image that holds a `test-seed` build
### Changed
### Removed
