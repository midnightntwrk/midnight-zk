# Security and zero knowledge

This document gives the argument that the GPU path keeps the proof and its
zero-knowledge property unchanged. It then states what the service does with
witness data on the device and on the host, what it does not do, and which
risks remain. The full threat model is section 12 of
[gpu-spec/design.md](../../gpu-spec/design.md). The open items are in
[gpu-spec/RESULTS.md](../../gpu-spec/RESULTS.md).

## 1. Where randomness is drawn

The GPU path draws no random value. All randomness of a proof comes from the
places where the stock prover draws it, in the stock order:

| Draw | Location | Source |
|---|---|---|
| Advice blinding rows | `compute_trace`, `parse_advices` ([`proofs/src/plonk/prover.rs`](../../proofs/src/plonk/prover.rs)) | the caller's RNG |
| Lookup and other blinding vectors | `compute_trace`, `sample_blindings`, before the parallel sections | the caller's RNG |
| Quotient limb blinding `t`, `t'` | `blind_quotient_limbs`, after the quotient is computed | `OsRng` |
| Challenges | transcript squeezes | the transcript (deterministic) |

The service passes `OsRng` as the caller's RNG (`ProverService::prove`). Some
circuits also draw randomness during synthesis. For example, the foreign-curve
chip of midnight-circuits samples a point from `OsRng`. That draw is part of
the circuit, not of the prover, and the GPU path does not touch it.

## 2. Why a hook cannot change the proof

The hook contract has three parts (see [architecture.md](architecture.md#2-the-hook-contract)):

1. A hook returns the value of the stock function on the same input, or it
   declines.
2. A decline leaves the input unchanged, and the stock code runs on it.
3. A hook draws no random value and touches no transcript.

The Lean oracle in [`gpu-spec/oracle/`](../../gpu-spec/oracle/Main.lean) states the prover as a
fold over a list of events: hooked calls, random draws and transcript
squeezes. It proves these theorems:

| Theorem | File | Statement |
|---|---|---|
| `resolve_eq` | [`GpuSpec/Hooks.lean`](../../gpu-spec/oracle/GpuSpec/Hooks.lean) | A device that obeys the contract resolves every call to the reference value. |
| `prove_any_schedule` | `GpuSpec/Hooks.lean` | Any two devices that obey the contract give the same transcript and the same number of random draws. |
| `runInPlace_eq` | `GpuSpec/Hooks.lean` | An in-place hook whose decline leaves the buffer unchanged gives the reference value. |
| `msmMasked_eq` | [`GpuSpec/Msm.lean`](../../gpu-spec/oracle/GpuSpec/Msm.lean) | `MSM(s + r) - MSM(r) = MSM(s)` for every `s` and `r` of equal length. |
| `compile_correct`, `deviceNumerator_eq` | [`GpuSpec/Quotient.lean`](../../gpu-spec/oracle/GpuSpec/Quotient.lean) | The compiled stack program computes the tree value of every expression, and the device numerator equals the reference numerator at every point. |

The CPU-only device obeys the contract. By `prove_any_schedule`, every device
schedule therefore gives the transcript of the CPU prover with the same random
stream. The proof is the CPU proof, and its distribution over the random
stream is the distribution of the CPU prover. The zero-knowledge property of
the proof system carries over unchanged.

These theorems are about a model: the MSM is over the toy group `Z_r`, and the
transforms and the numerator are reference definitions. The link from the
model to the CUDA code is made by tests:

- The golden vectors in [`gpu-spec/vectors/`](../../gpu-spec/vectors/README.md) fix the
  expected values of the NTT, the coset transforms, the MSM and the quotient
  numerator. The oracle checks its device models against them.
- [`gpu/tests/prover.rs`](../../gpu/tests/prover.rs) compares whole proofs. `seeded_proofs_equal_cpu`
  checks that seeded proofs with the hooks are byte-equal to the CPU proofs.
  `quotient_fuzz_small` and `quotient_fuzz_10000` compare the device quotient
  with the CPU quotient on random constraint systems [GPU-071].
  `faults_give_valid_proofs` arms device faults and checks that each proof
  still verifies.

In 0.9.0-rc.1 the quotient limb blinding draws from `OsRng`, not from the
caller's RNG. A byte comparison therefore needs the test-only seed of the
feature `gpu-test` (`test_switches::set_quotient_blinding_seed`). That feature
exists for these tests and is never part of a production build.

## 3. The MSM skew mask is not a blinding value

The MSM kernel computes `MSM(s + r) - MSM(r)`, with `r` a fixed public vector
that depends only on the length (see [architecture.md](architecture.md#3-device-kernels)). The
mask spreads the scalars over the buckets so that no bucket is hot when the
witness repeats a value. It hides nothing: `r` is public, so `s + r` gives `s`.
The device sees the witness-derived scalars in either form. The security of
the GPU path does not depend on the mask.

## 4. Read-back set

Only these values go from the device to the host on the proving path
[GPU-038]:

- MSM result points.
- The partial bucket sums of the vendored MSM. It copies them to host memory
  for the final accumulation, counts the transfers and zeroes the host copies
  after use.
- Base-domain transform outputs. The CPU prover holds these values at that
  point too.
- The quotient coefficients, once per proof.
- Counters.

No extended-domain vector goes back to the host. The test
`readback_is_base_transforms_and_quotient` records every device-to-host result
copy of a proof and checks this set.

## 5. Wipe

The wipe zeroes, then frees, every device buffer and host staging buffer of
`midnight-gpu` that held witness-dependent values, before the next request is
read [GPU-034]. [architecture.md](architecture.md#6-wipe) lists the buffers. If the wipe
cannot be confirmed, the daemon replies with an error and exits [GPU-035].

The wipe does not cover these items:

- **Host memory of the prover.** The service zeroes the input buffer it reads.
  The decoded witness (the relation's own types) and the buffers of the stock
  prover are freed without zeroing, as on any CPU prover.
- **A daemon crash.** When the daemon process dies, the driver frees its device
  memory without zeroing it. The wipe cannot run. The next process that
  allocates that memory can read the values until the driver or the device
  clears them.
- **Public data.** Proving-key copies and SRS tables are freed as they are.

Zero-check mode checks each zeroed region on the device [GPU-036]. A kernel
reduces the region and returns the count of non-zero words. Whole chunks are
not read back, so a region that was not zeroed does not reach host memory
through the check.

## 6. Sockets, files and permissions

- The daemon socket has mode 0600. The daemon serves only peers whose uid
  (`SO_PEERCRED`) is the daemon's uid [GPU-043].
- A request line has at most 64 KiB and must arrive within 10 s [GPU-047].
- The daemon opens an input file once, without following a symbolic link. It
  checks the open file: a regular file, owned by the daemon's user, no group
  or other access, at most 1 GiB [GPU-044]. The bytes go into a buffer that is
  zeroed when it is dropped.
- The proof is written with mode 600 to a temporary file and renamed into
  place.
- The breaker state file of the client is owner-only.
- The container runs as a non-root user with a read-only root file system, no
  capabilities and `no-new-privileges`. The SRS is mounted read-only. The
  systemd unit runs as a system user with `ProtectSystem=strict`, an empty
  capability set and only `AF_UNIX` sockets.

## 7. Lock leases

When `lock_path` is set, the device is exclusive under an exclusive `flock` on
that file. The service never takes the lock itself. The caller passes its
locked descriptor with the request (`SCM_RIGHTS`). The service accepts it as a
lease only when all three checks pass:

1. The descriptor names the configured lock file (same device and inode).
2. A fresh open of the lock file cannot take the lock.
3. The passed descriptor can take the lock without blocking, so the caller's
   own open file description holds it.

A lock held by an unrelated process gives no lease. The service keeps its copy
of the descriptor until the request is wiped, so the lock stays held when the
client disconnects early. A device user that ignores the lock is not seen and
not protected against. Under WSL2 a request without a lease runs no device
phase [GPU-057, GPU-061].

## 8. Threat model

In scope:

- another process on the host that allocates device memory after a request,
- another local user,
- a local client that floods or stalls the daemon,
- a device or kernel fault,
- a wrong or substituted key,
- witness data that leaves through the host side,
- a crash loop,
- a shared device under WSL2.

The controls for each are in section 12 of [design.md](../../gpu-spec/design.md).

Scope of the zero-knowledge rule (a named assumption):

- The rule covers every buffer that the GPU prover code owns: request
  envelopes, staging buffers, device buffers, read-backs and the wipe owners
  in the vendored crates. It also covers every log line, reply, statistic and
  file that the GPU prover code writes.
- Host memory that only the stock prover path owns (synthesis and commitment
  in `midnight-proofs`, `MockProver` internals) and serde internals is trusted
  process memory. This holds because the prover runs on the user's own
  machine.
- A copy of such bytes into a buffer that the GPU prover code owns, or into a
  log line, reply or file, is in scope again.
- Error text never formats a path or a value that the caller supplied.
- Proving on a machine that the user does not own is outside this assumption
  and needs a separate analysis.

The Metal backend and the record. `midnight-metal` declines a sparse MSM (one
with few non-zero scalars) to the stock CPU MSM, so how many MSMs the device
serves depends on the witness. The record does not show that split:

- It reports one MSM total, `msm.count` and `msm.seconds`, over every MSM hook
  invocation, served or declined. There is no MSM entry in `device_calls`,
  `declines` or `fallbacks`.
- The `gpu` or `cpu` label is decided from facts that do not depend on the
  witness: the admitted phases, the served `fft`, `ifft` and `quotient` calls,
  and the MSM calls the device takes by length and table before reading any
  scalar.
- With the default thresholds the device takes an MSM only when a registered
  table serves its bases. Any other MSM declines `unregistered-bases` before
  reading a scalar, because the one-shot path's per-call G1 membership check
  costs more than the CPU MSM. Only `MIDNIGHT_METAL_MIN_K` opens that path.
  The decline depends on public facts only.
- The split by path stays inside the process (`midnight_metal::stats` and
  `declines`). Proof time still depends on sparsity, as with the CPU MSM:
  timing is out of scope (below).

Out of scope:

- an attacker with root on the host or with control of the NVIDIA driver,
- physical access to the device,
- timing and power side channels (the MSM time depends on the scalar
  distribution, as the CPU MSM time does),
- confidential-computing modes [GPU-055].

## 9. Residual risks

These items are open in [RESULTS.md](../../gpu-spec/RESULTS.md):

1. **Crash before the wipe.** Device memory of a crashed daemon is freed
   without zeroing. No code inside the daemon can close this. A host that
   shares the device between users needs a policy, for example a supervisor
   that zeroes a reserved region before a restart, or acceptance of the risk.
2. **Zero-check read-back.** The check reads zeroed regions back to the host
   (section 5). A check on the device would keep a failed region off the host.
3. **Planned restarts.** A restart after an over-bound request counts toward
   the restart limit. Repeated over-bound requests can therefore stop the
   daemon.
4. **Wipe after a lost WSL2 lock.** The wipe is not a device phase, so it can
   run after the lock is released. If zeroing on a shared device must also
   hold the lock, the requirements need a separate statement.
5. **Scope of the models.** The oracle and the Quint model state the request
   state machine and the hook contract. Build behavior, real kernels, sockets,
   file modes, records and the container are checked by Rust tests, harness
   runs and review. Quint ran bounded random simulation, not exhaustive model
   checking.

### Known upstream issue: zkir logs private inputs

At the pinned versions, zkir logs private inputs on malformed-witness paths.
midnight-zkir 3.2.0 (`zkir/src/ir_vm.rs`, "Transcripts not fully consumed"
and "Communications commitment mismatch") logs the private transcript and the
commitment inputs at error level whenever a tracing subscriber is installed.
The library's log target is `midnight_zkir`. The stock proof server 9.0.1
turns off the target `zkir`, which matches only the zkir command-line tool,
so the stock filter does not stop these lines.

- The proof-server wrapper (`gpu-prover/bench/compact/proof-server`) turns off
  both `zkir` and `midnight_zkir` in a filter that does not read `RUST_LOG`.
  Its test `malformed_witness_logs_nothing_from_zkir` sends a malformed witness
  through zkir and checks that the log holds no zkir line.
- The daemon and the Compact bench install no tracing subscriber, so these
  events go nowhere.
- An operator who adds a subscriber to any of them, or runs the stock proof
  server with logging on, must turn off the targets `zkir` and
  `midnight_zkir`, for example `RUST_LOG=info,zkir=off,midnight_zkir=off`.

### Known upstream issue: the proof server binds all interfaces

Proof server 9.0.1 has no option for the listen address. It binds `0.0.0.0`
on its port, so a request that carries witness data can reach it from any
network that reaches the machine. The proof-server wrapper keeps this
behavior. Run it on loopback only: start it in a network namespace that has
only a loopback interface (`unshare -rn`) and bridge a mode-600 unix socket
to its port, or put it behind a firewall rule that drops the port on every
non-loopback interface. Then reach it through a tunnel. A systemd IP filter
on a unit does not cover a process that runs in a separate transient scope.
[PROOF-SERVER.md](../../gpu-prover/bench/compact/PROOF-SERVER.md) gives the
namespace method and the probe that refuses a session whose port answers on
a network address.

## 10. Test builds never ship

- The feature `gpu-test` of `midnight-proofs` adds the test switches and the
  seeded quotient blinding. Release builds do not enable it.
- The feature `test-seed` of `midnight-gpu-prover` adds `prove_seeded` for
  byte-identity tests. The daemon never takes a seed.
- The release image builds with `CARGO_FEATURES=cuda`. The `gpu-test` image
  target is a separate image and is never published.
- A `test-seed` build writes a marker string at start. The script
  `gpu-prover/container/check-no-test-seed.sh` refuses an image that holds the
  marker or a file named `*seeded*`.

## 11. Batch request boundary

A wave is the group of proof jobs admitted together by the batch scheduler.
Every job in a wave belongs to the same prover and request. The caller
supplies public memory estimates and a budget. At most `in_flight` jobs
(zero means one) run in a wave, with total estimated bytes within that
budget unless a single oversized job runs alone on the CPU.
While one job waits in a nested Rayon scope, the worker can start another
job of the wave on the same stack. Size each worker stack for the jobs that
can nest on it, up to the number of jobs in the wave.

Each batch transform and quotient releases its entire shared scratch allocation
and the host bounce and private read-back buffers before another batch call
can run. A job waiting for the shared device can observe time spent serving another job.
Each batch MSM evicts its registered contexts under the same lock.
A one-shot MSM checks for an unconfirmed drain before releasing its context.
An actor operation panic records the decline reason `operation-panic`.
An unconfirmed release of a live MSM context fails the boundary even if
the erasure counters are clean. An operation panic or a failed boundary
latches failure before the next batch entry.

Device exclusivity requires a live `BatchSession`. Passing a plain hook table
to the scheduler does not acquire the device. Outside operations that need
the actor decline during a session. Displaced registrations hand their live
contexts and buffers to the final session boundary for counted release.
Pass the scheduler's `BATCH_THREAD` key to `BatchSession::begin` before
scheduling proofs. A busy session or a failed
erasure check at the preceding request boundary returns an error. Associate
the hook table with `session.set_worker` through `BatchHooks::new` and join
all work started by each job. Only workers admitted by that session may use
its entries. Return `session.end_wave()` from the wave callback for a second
erasure check after the jobs join. Check both the outcome's `erasure_failed`
field and `session.finish()` before accepting the request. Dropping an
unfinished session attempts cleanup and latches any failure.

Each nonempty batch takes the embedding's current panic hook and installs
a hook that returns without I/O or locking on a scoped worker or on the
device owner during a batch request. A panicked job returns its typed error.
On other threads the hook passes the original panic information to the
embedding's hook. An OS thread that a job spawns and joins is unmarked.

The standard library has no atomic hook swap. A panic on another thread
reaches the default handler between `take_hook` and `set_hook` both at the
start of the batch, while installing the batch hook, and at the end, while
restoring the embedding's hook. Leave the batch hook in place for worker
redaction. If the embedding installs another hook during the batch, the
batch replaces it with the earlier hook on return or unwind. Outside the
batch the embedding has its own hook again and supplies its own redaction,
including during initial device session setup.

Taking and setting the hook wait for every thread that is inside a panic
hook at that moment: the standard library holds its hook lock while a hook
runs. A thread outside the batch that is blocked inside the embedding's
hook therefore blocks the start or the end of a batch. The embedding's hook
must not block on anything that the caller of a batch holds across the
batch, such as the stderr lock.

Panic payloads are dropped unread. After eight consecutive destructor panics
the last payload is leaked unread. It can hold a resource such as a budget
permit for the life of the process. The batch triggers its failure signal
at the leak, while the wave is still running. On a batch worker, use
`Shutdown::from(failure_signal().unwrap())` for budget and channel waits.
A bound session exposes the same signal through `session.failure_signal()`.
Waits using it return a decline, so the batch can report failure.
Code inside a proof must not panic with a payload that owns a resource
another job waits for without that signal.

A job must not hold a shared resource such as a budget permit across a
nested parallel call. A second job of the wave can start on the same worker
and wait for that resource while its owner is suspended. No failure has
occurred to trigger the signal. An embedding that cannot enforce this
resource rule runs waves of one job.

Panic payloads are never formatted, logged or returned to a caller.
Code inside a proof must not put witness values in a panic payload.
Concurrent scheduler entry returns a busy error even for an empty input
or a recursive call from a job or its wave cleanup.
