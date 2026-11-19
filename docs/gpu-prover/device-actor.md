<!-- This file is part of MIDNIGHT-ZK. -->
<!-- Copyright (C) Midnight Foundation -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Device-owner actor

Design for replacing the process-wide device lock of `midnight-gpu`
with one device-owner actor per GPU. Status: stage 1 is in place.
The device lock is gone: one dedicated thread in `gpu/src/ffi.rs`
(started on first use) makes the CUDA context current and is the
only thread that calls into the CUDA core for device work. Every
device call of the crate (NTT, MSM, quotient, copies, allocation,
registration and eviction, erasure, fault injection, the request
boundaries in `lib.rs`, teardown) is a typed `DeviceRequest` to
that thread and a blocking wait for its reply, over the channel
layer of `gpu/src/actor/chan.rs` (standard blocking channels).
Detection that makes no context (device properties, versions,
context-active query) and the host-memory-only counters stay
callable from any thread. In stage 1 every operation class is
exclusive (one operation in flight at a time), so the device sees
exactly the sequence it saw under the lock; overlap is stage 2.

Admission in stage 1: the public entry points are decline-or-run
hooks whose callers fall back to the CPU, so none of them may wait
for device memory. The existing "decline when it cannot fit"
checks therefore stay (now evaluated on the actor thread), and no
public call waits in the budget. The waiting FIFO budget
(`chan::Budget`, permits returned only at the wipe-confirmed free)
serves the device-free protocol actor's jobs, which is where
submit-and-wait semantics exist today.

Teardown is an actor operation: the shutdown signal stops
admission, the operation in flight finishes, queued operations
are dropped unrun (their callers decline with reason `teardown`,
and make no call on the dead context), the page-locked staging
buffer is zeroed before the reset (inside
`mgpu_teardown_context`, which the reset would unmap), and every
later request is answered the same way. A `DevBuf` belongs to the
operation that made it; its release is an actor request (wipe,
confirm, free), inline on the actor thread, and a release that
cannot run keeps the region in quarantine by its host record
instead of blocking.

Artefacts:

- Model: `gpu-spec/quint/device_actor.qnt`, directed tests in
  `gpu-spec/quint/device_actor_test.qnt`.
- Protocol core: `gpu/src/actor/` (`protocol.rs` is the pure state
  machine, `budget.rs` the admission budget, `chan.rs` the blocking
  channel layer, `mod.rs` the protocol actor thread and the
  `Backend` trait for effects).
- Device actor: `gpu/src/ffi.rs` (`call`, `call_live`,
  `call_teardown`, `DeviceRequest`).
- Tests: `gpu/tests/actor_protocol.rs`, `gpu/tests/actor_stress.rs`,
  `gpu/tests/actor_chan.rs`, `gpu/tests/actor_probe.rs` (device),
  `gpu/tests/actor_device_stress.rs` (device).

## Design

1. One actor thread per GPU owns the CUDA context. Nothing else
   calls CUDA, so no caller can run on a dead context and no lock is
   ever waited on across a device call.
2. Jobs talk to the actor only through typed messages on a bounded
   channel (`Request` in `gpu/src/actor/mod.rs`): submit with a byte
   reservation, run an operation (stage, MSM, NTT/coset, quotient,
   read-back), release, ask the pending-erasure count, teardown.
   Each job has its own stream(s) and its own buffers; an operation
   may name only its own job's buffer. Every request gets exactly one
   reply on its own channel.
3. Admission is a budget the actor holds: a capacity, the reserved
   bytes and a FIFO queue. A request whose reservation does not fit
   waits in the queue; it never fails for lack of memory.
4. Erasure: on release the actor drains the job's stream, wipes its
   buffers and confirms the wipe before the bytes return to the
   budget. No buffer is freed (or its memory reused) before its wipe
   is confirmed, except at a reset, where it is counted lost
   unerased. The pending-erasure report is exact at all times.
5. Teardown and reset are actor-only and in two steps. Begin: stop
   admission and new operations, zero the page-locked staging buffer
   (a reset unmaps it). Admitted jobs still drain, wipe and free.
   Finish (the reset): count every still-unerased buffer lost,
   return every byte, answer every queued job `teardown`, and answer
   every later submit `teardown` in the submit step itself.
6. An operation class may be marked exclusive (third-party kernels
   with global or static device state, pending a separate audit of
   which ones, and whether they get an instance per stream instead).
   The protocol then refuses to start an exclusive-class operation
   while another exclusive-class operation is in flight;
   non-exclusive operations may run beside anything.

## Refinements and their reasons

- Strict FIFO admission, no bypass. Only the queue head can be
  admitted, only when its whole reservation fits. A large head is
  therefore never overtaken forever by small requests (no
  starvation), at the cost of head-of-line blocking (free bytes can
  sit unused behind a large head). Accepted because a request must
  never fail for lack of memory and the admission order stays
  auditable.
- A reservation above the budget capacity is refused at submit
  (`ReplyKind::Refused`) instead of queueing forever; without this
  the queue would deadlock behind a request that can never fit.
- A completed operation, ok or failed, leaves its buffer holding a
  secret (witness values were staged into it). A failed job still
  drains, wipes and frees before its reply, which is then `Failed`.
- An unconfirmed drain marks the stream `drainBad`: draining may be
  retried, but a wipe on such a stream never confirms, so the buffer
  stays in the pending-erasure count until the reset counts it lost
  unerased. A failed wipe (drain confirmed) may be retried.
- A submit that arrives while teardown is draining is answered
  `teardown` at once, not queued until the reset, so no caller
  waits across a reset.
- Teardown is two steps (begin/finish) rather than one, so admitted
  jobs get the chance to wipe-confirm and free before the reset
  would count their buffers lost.
- One buffer per job is modelled in this round (buffer id = job id).
  The integration round generalises a job to several buffers behind
  the same per-job lifecycle; the invariants are stated per buffer
  with an owner, so the shape does not change.
- In the actor thread of this round a backend operation completes
  inside the loop (`StartOp`, launch, `CompleteOp` in one message),
  so the in-flight window exists in the protocol (and in the model,
  where two jobs' operations can be in flight at once) but is not
  yet used for real overlap. The integration round turns backend
  completion into its own actor-loop event, one stream per job,
  without changing the protocol.
- Drain and wipe are retried a bounded number of times (3) in the
  actor loop; after that the job stays pending until teardown, as
  the protocol states. The bound is an actor policy, not protocol.

## A full request queue

The request queue is bounded. A caller that finds it full retries the
send every 2 ms and reads the shutdown signal on every attempt; it has no
place in line, so a later caller can pass it and each retry can add up to
2 ms. There is no hang: the queue drains at the actor's rate. The device
lock that the actor replaced was not fair either.

## Model and code correspondence

The model and protocol core describe jobs, budget admission and buffer release.
At this stage the device actor in `ffi.rs` uses only the channel layer.
The key registry must be unlocked before a caller waits for the actor to
release a buffer. The registry regression test checks this code rule, which
is outside the model.

`gpu/src/actor/protocol.rs::step` mirrors the Quint actions one for
one (same names, same state fields, same `lastOp` encoding
`code + 100 * a + 10000 * b`). ITF traces of the model replay
against it (`protocol::replay_itf`); `gpu/tests/actor_protocol.rs`
replays every trace file placed in `gpu-spec/vectors/actor/`.
Invariants (named `val`s in the model, mirrored by tests):
`noDeadlock`, `budgetNeverExceeded`, `noReuseBeforeWipeConfirmed`,
`teardownAnswersEveryWaiter`, `noCrossJobRead`, `fifoAdmission`,
`pendingErasureExact`, plus `exclusiveNeverConcurrent`,
`exactlyOneReply` and `pinnedZeroedBeforeReset`; the concurrency
point is the `w_concurrent` witness (and `eventuallyConcurrent` in
temporal form).
