# Architecture

This document describes how the GPU path attaches to the midnight-proofs
0.9.0-rc.1 prover and what runs on the device. It also describes the data that
stays on the device between requests, the admission, the wipe and the
fallback.
The requirements are in [gpu-spec/requirements.md](../../gpu-spec/requirements.md).
Requirement IDs appear in brackets.

## 1. Pipeline and hook points

The prover runs the stock phases in the stock order:

1. Commit to the advice columns.
2. Draw the lookup and permutation challenges.
3. Commit to the lookup, permutation and trash polynomials.
4. Compute the quotient `h(X)` and commit to its limbs.
5. Evaluate, and run the multi-open argument.

Every transcript write and
every challenge squeeze stays on the CPU, in the stock order [GPU-015].

With the cargo feature `gpu`, four operations are offered to an installed hook
before the stock code runs:

| Hook field | Hook point (file, function) | Stock code on decline |
|---|---|---|
| `msm_g1` | [`proofs/src/poly/kzg/mod.rs`](../../proofs/src/poly/kzg/mod.rs), `commit_msm` (every commitment); [`proofs/src/poly/kzg/msm.rs`](../../proofs/src/poly/kzg/msm.rs), `msm_specific` | `msm_pippenger` (commitments); blstrs `multi_exp_affine` (`msm_specific`) |
| `fft` | [`proofs/src/poly/domain.rs`](../../proofs/src/poly/domain.rs), `best_fft_with_twiddles` | `midnight_curves::fft::best_fft_with_twiddles` |
| `ifft` | `proofs/src/poly/domain.rs`, `EvaluationDomain::ifft` | the same FFT at the inverse root, then the scaling by the divisor |
| `quotient` | [`proofs/src/plonk/prover.rs`](../../proofs/src/plonk/prover.rs), `finalise_proof`, through `gpu::quotient_coeffs` | `compute_nu_poly`, `divide_by_vanishing_poly`, `extended_to_coeff` |

The hook module is [`proofs/src/gpu/mod.rs`](../../proofs/src/gpu/mod.rs). Only the
BLS12-381 scalar field `Fq` and its G1 group reach a hook. Other fields and
curves never reach one, because each entry point checks the type first.

The quotient hook gets one job, a `QuotientJob`. The job holds the
proving key's `FlatGraphEvaluator` lowered to a `DeviceProgram`. The lowered
program runs the same field operations in the same order as the stock
evaluator, and only renames the storage of intermediate values. The job also
holds the extended-domain constants that `divide_by_vanishing_poly`,
`extended_to_coeff` and the truncation of the quotient use. The hook returns
the first `len` coefficients of `h(X)`.

The prover then commits to them with
`commit_h_coeffs`. `QuotientJob::numerator_reference` is a CPU interpreter of
the job. Unit tests compare it with the stock evaluator.

## 2. The hook contract

Each hook obeys one contract [GPU-007, GPU-008, GPU-009]:

1. A hook returns the exact value of the stock function on the same input, or
   it declines (`None` or `false`).
2. A decline leaves the caller's buffer unchanged. The stock code then runs on
   that buffer.
3. A hook draws no random value and touches no transcript [GPU-014, GPU-016].
4. A process installs one hook set with `gpu::install`. A second call returns
   `false` and keeps the first set [GPU-011].
5. With no hook installed, or without the feature `gpu`, the prover runs only
   the stock code [GPU-001, GPU-002].

The random draws stay where the stock prover makes them. The advice and lookup
blinding values come from the caller's RNG in `compute_trace`, before any
hooked call that uses them. The quotient limb blinding (`blind_quotient_limbs`)
draws from `OsRng` after the quotient hook returns, on the CPU, in the stock
order. A decline therefore cannot shift the random stream. See
[security.md](security.md) for the argument and the oracle theorems.

## 3. Device kernels

The device code is the crate `midnight-gpu` ([`gpu/`](../../gpu/src/lib.rs)). Its CUDA
core is one translation unit, [`gpu/cuda/midnight_gpu.cu`](../../gpu/cuda/midnight_gpu.cu).

**MSM.** The MSM is the Pippenger MSM of sppark
(`msm/pippenger.cuh`). sppark is vendored unmodified at commit
`08033103c14ff3c742e710b9463dde42acc0f058`, with its Apache-2.0 license, in
[`gpu/third_party/sppark/`](../../gpu/third_party/sppark/VENDORED.txt) [GPU-006]. The CUDA core
redirects the sppark device allocations to its own wrappers by macro, in its
own translation unit, so no sppark file changes. The kernel sends no witness
statistic to the host and branches on none.

sppark sums each bucket in one thread. A scalar that repeats many times would
send most points of a window to one bucket. The MSM is therefore computed as
`MSM(s + r) - MSM(r)`, with `r` a fixed public pseudo-random vector that
depends only on the length [GPU-013]. The result is the same group element.

`MSM(r)` is computed once per table and length. This skew mask is a load
balance measure only. It is not a blinding value (see [security.md](security.md)).

**NTT.** The forward and inverse NTT are the sppark NTT in natural order. The
hook takes a size only for the standard root of that size or its inverse. The
inverse transform of sppark includes `1/n`, and the hook corrects for any
other divisor.

**Coset transform.** The coset transform multiplies coefficient `i` by
`[1, zeta, zeta^2]` (by `i mod 3`), pads with zeros to the extended size and
runs the forward NTT. It runs on the device only inside the quotient hook. No
extended-domain vector goes back to the host.

**Quotient.** The quotient hook does these steps on the device:

1. It moves the proof's polynomials to the extended coset.
2. It runs the numerator kernel.
3. It divides by the vanishing polynomial.
4. It runs the inverse extended transform and removes the coset factors.
5. It reads the first `len` coefficients into the caller's buffer.

The numerator
kernel is an interpreter: one device thread evaluates the lowered programs
(gates, permutation, LogUp lookups, trash) at one point of the extended domain
and folds the gate values by powers of `y`. The source is
[`gpu/src/quotient.rs`](../../gpu/src/quotient.rs) and
[`gpu/cuda/quotient.cuh`](../../gpu/cuda/quotient.cuh).

**Size threshold.** Calls below `2^min_k` elements decline (default `min_k` 14,
`MIDNIGHT_GPU_MIN_K`). Below that size, the transfer costs more than the CPU
work.

**Declines.** A device function declines for one of these reasons, and each
decline is counted with its hook class and reason (`midnight_gpu::declines`):

| Reason | Cause |
|---|---|
| `no-device` | Stub build, no usable device, or `MIDNIGHT_GPU=off`. |
| `below-min-k` | The input is smaller than `2^min_k`. |
| `shape` | A length, root, job layout or ABI version the device does not take. |
| `unreduced` | A scalar that is not below the field modulus. |
| `memory` | The device need of the quotient exceeds the limit. |
| `fault` | A test fault (feature `test-fault` only), armed before the device work. |
| `device-error` | A device call failed. |

## 4. Resident data

Two kinds of public data can stay on the device. Both are keyed by a handle
that the registrant holds.

- **SRS tables.** `midnight_gpu::register_srs(bases)` returns an `SrsHandle`.
  Registration is host work only: a copy and a digest. The first MSM on the
  slice, or on a prefix of it, uploads the points into an sppark MSM context.
  Before each use, the table checks the caller's slice against the stored
  points: eight sampled points in a release build, every point in a debug
  build. A slice that fails the check drops its table and takes the one-shot
  path. `end_request` frees every MSM context, because a context holds the
  bucket sums of its last MSM. The registration stays, and the next request
  uploads the points again.
- **Proving-key copies.** `midnight_gpu::register_key(polys)` returns a
  `KeyHandle` for the fixed and permutation polynomials on the extended domain.
  The first quotient makes the device copies. A changed polynomial fails the
  digest check and is uploaded for the call only. Dropping the handle frees
  the copies.

**Eviction policy.** The service policy `resident` decides what stays between
requests [GPU-030]:

- `evict` (the default): the service frees the proving-key copies before each
  reply. With the MSM contexts freed by `end_request`, the device holds no key
  data and no table between requests. The next request uploads both again.
- `keep` (opt-in): the proving-key copies stay for the next request. Use it
  only on a device with no other user. The WSL2 profile refuses `keep`
  [GPU-059].

The `evict` request of the daemon protocol frees the copies on demand, and with
`tables` the MSM contexts too.

## 5. Need and admission

Before any device phase starts, the service computes the device memory the
proof needs from the loaded proving key ([`gpu-prover/src/need.rs`](../../gpu-prover/src/need.rs))
[GPU-025]. The terms are the per-proof extended cosets, the numerator output and
the kernel scratch, the transform scratch, one MSM call, and the resident
copies and MSM tables. A resident buffer that is already on the device is
counted once. The configured margin (`margin_mib`, default 768 MiB) is added.

The admission ladder ([`gpu-prover/src/admission.rs`](../../gpu-prover/src/admission.rs)) takes
the first step that fits:

1. `gpu`: the free memory covers the need of every configured phase. Every
   phase runs on the device.
2. `wait`: the service polls the free memory for at most `wait_s` (default
   20 s) for another device user to free memory. When the need fits, every
   phase runs on the device.
3. `evict`: the service frees the resident proving-key copies and moves the
   quotient to the CPU. MSM and NTT stay on the device. The service checks the
   smaller need of those phases against the free memory again. The proof is
   marked degraded [GPU-027].
4. `cpu`: the smaller need does not fit either. The service frees its MSM
   tables and runs every phase on the CPU. The proof is marked degraded
   [GPU-028].

No device phase starts whose need exceeds the free memory at the decision
[GPU-029]. Freeing the key copies at step `evict` cannot make the full need fit,
because the full need adds the freed copies back. Step `evict` exists for the
smaller need only.

Under WSL2 the free-memory query does not see allocations of the Windows host.
The WSL2 profile admits against a fixed budget (device total minus
`wsl_reserve_mib`) with no wait, and only while the caller holds the device lock
[GPU-056 to GPU-061].

## 6. Wipe

When a request ends, for any reason, the service calls `end_request`
([`gpu/src/wipe.rs`](../../gpu/src/wipe.rs)) before it reads the next request
[GPU-034]. It zeroes, then frees:

- The device buffers of the call: transform scratch, the extended cosets of
  the proof's polynomials, the numerator and the quotient scratch.
- The sppark device buffers (the per-call MSM buffer and the MSM contexts),
  through the zero-before-free allocation wrappers.
- The host staging: the masked MSM scalars (volatile writes), the page-locked
  bounce buffer and the read-back buffer of the CUDA core.

A region whose zeroing or free fails goes into quarantine and is never handed
back with values in it. `end_request` retries the quarantine. If the erasure
cannot be confirmed, the service replies with an error, retires and takes no
further witness [GPU-035]. In zero-check mode every zeroed region is read back
and compared with zero [GPU-036]. [security.md](security.md) states what the wipe does
not cover.

## 7. Read-back set

Only these values go from the device to the host on the proving path
[GPU-038]:

- MSM result points (one G1 point per MSM).
- Base-domain transform outputs (`2^k` values), written into the caller's
  buffer. The CPU prover holds these values at that point too.
- The quotient coefficients, once per proof.
- Counters.

No extended-domain vector goes back. The test
`readback_is_base_transforms_and_quotient` in
[`gpu/tests/prover.rs`](../../gpu/tests/prover.rs) records the size of every
device-to-host result copy of one proof and checks this set. Zero-check
read-backs of zeroed regions are not results and are not recorded.

## 8. Daemon and client

`midnight-gpu-prover` ([`gpu-prover/`](../../gpu-prover/README.md)) holds one relation, its SRS
and its keys between requests. A request runs as follows:

1. The daemon opens the input file once and checks the open file (regular,
   owned by the daemon user, mode 600).
2. The admission ladder chooses the device phases.
3. The service proves with fresh randomness from the operating system.
4. `end_request` zeroes and frees the witness buffers. Under the `evict`
   policy the key copies are freed too.
5. The stock verifier checks the proof. A refused proof is an error, and no
   output is written [GPU-039, GPU-040].
6. The proof is written owner-only through a temporary file and a rename.

The daemon serves newline-delimited JSON on a local Unix socket with mode 0600.
It serves one request and queues one more. A third request gets `busy` at once
[GPU-045, GPU-046]. The client ([`gpu-prover/src/client.rs`](../../gpu-prover/src/client.rs))
calls the daemon and proves in-process on the CPU when the daemon cannot serve.
A circuit breaker stops the calls to a failing daemon. [operations.md](operations.md)
gives the settings.

The service talks to the device through the `Device` trait
([`gpu-prover/src/device.rs`](../../gpu-prover/src/device.rs)). `NoDevice` runs every phase on
the CPU. The CUDA binding installs the `midnight-gpu` hooks and is compiled
only when the build links both crates.

## 9. CPU fallback levels

A fault at one level moves work to the CPU at that level. The proof is the same
in every case.

| Level | Trigger | Effect | Label |
|---|---|---|---|
| Hook call | A device function declines | The stock code runs that call | Counted per class and reason. A failed device call marks the proof `gpu-degraded`. |
| Admission | Not enough device memory | Step `evict` (quotient on the CPU) or `cpu` | Step `evict`: `gpu` with a reason in `degraded_reasons` (`gpu-degraded` only when a call also fell back); step `cpu`: `cpu` |
| Daemon | No device, `device = off`, or no lock lease | Every phase on the CPU in the daemon | `cpu` |
| Client | Daemon absent, busy, failed or retired | The client proves in-process | `cpu-fallback` |
| Breaker | 3 daemon failures in 600 s | The client skips the daemon for 600 s | `cpu-fallback` |
| Supervisor | The daemon exits 3 times in 600 s | The daemon stays stopped | `cpu-fallback` |

In `acceptance` mode a degraded admission or a fallback fails the request, and
no proof is written. Benchmarks use this mode, so a timing that mixes CPU and
device work does not pass as a GPU timing.

## 10. Build

The build script [`gpu/build.rs`](../../gpu/build.rs) compiles the CUDA core
when the feature `cuda` is on and `nvcc` is found:

- The CUDA toolkit is `CUDA_PATH`, else `CUDA_HOME`, else the toolkit of `nvcc`
  on `PATH` [GPU-004].
- `MIDNIGHT_GPU_ARCHS` lists the SM numbers (for example `80,86,120`). Each one
  is compiled to SASS with `-gencode`, and the PTX of the highest one is
  embedded so that a newer device can compile it at load time [GPU-005].
  `native` compiles for the devices of the build machine. The default list is
  80, 86, 89, 90, 100 and 120, filtered to the ones the `nvcc` supports.
- Without `nvcc`, or after a failed compile, the build prints a warning and
  compiles a stub. Every device call of the stub declines, so the prover runs
  the CPU code [GPU-003]. `MIDNIGHT_GPU_REQUIRE_CUDA=1` makes a missing `nvcc` a
  build error. The container image sets it.

`cargo clippy --all-targets --all-features` and `cargo test --all-features`
pass on a machine without CUDA, because every feature falls back to the stub.

The earlier work also has a Rust MSM kernel. It needs the `nvptx64` target, so
the pull request leaves it out. Only the CUDA (sppark) MSM ships.
