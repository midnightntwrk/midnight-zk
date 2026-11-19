// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Device-owner actor: one actor thread owns the CUDA context of one GPU.
// Jobs reach it only through typed messages; each job has its own stream
// and its own buffer. Written from the design note
// docs/gpu-prover/device-actor.md, not from code. The Rust protocol core
// (gpu/src/actor/protocol.rs) uses the same action names, the same state
// field names and the same op encoding, so ITF traces of this model can
// be replayed against it.
//
// Scale: 3 jobs (ids 0, 1, 2), one buffer per job (buffer id = job id),
// reservation sizes 1..CAPACITY in abstract units. Per-job facts are
// lists indexed by job id.
//
// Fairness rule (a refinement the design leaves open): strict FIFO
// admission with no bypass. Only the head of the queue can be admitted,
// and only when its whole reservation fits. A small later request never
// overtakes a large waiting head, so no request starves: the head is
// admitted as soon as enough bytes have been returned, and bytes are
// returned by every admitted job that finishes. The cost is head-of-line
// blocking (free bytes can sit unused behind a large head); that is
// accepted because a request must never fail for lack of memory and the
// queue order must be auditable. A reservation above CAPACITY can never
// fit; submit refuses it at once (reply kind REFUSED) instead of queueing
// it forever. Without that refusal the queue would deadlock.
//
// Other refinements, each marked REFINEMENT below: an unconfirmed drain
// or a failed wipe does not free the buffer; the job stays pending
// erasure and only the reset at teardown can close it, counted as lost
// unerased. A failed operation does not skip drain/wipe: the job still
// goes through release. Teardown is two steps (begin, finish) so that
// admitted jobs can drain and wipe between them; finish performs the
// reset, counts every still-unerased buffer as lost, answers every
// queued job with teardown, and every later submit is answered teardown
// in the submit step itself. The page-locked (host staging) buffer is
// one more buffer owned by no job: `pinnedZeroed` must hold before the
// reset in teardownFinish, because a reset unmaps it.
//
// The op a step takes is in `lastOp` as code + 100 * a + 10000 * b (the
// gpu_service encoding). `s` is the record a replay compares field by
// field; `prev` is a ghost copy of the state before the last step.
module device_actor {
  // ---- configuration (fixed per instance) ----
  const CAPACITY: int    // budget capacity in abstract units
  const CHAOS: bool      // injected failures occur

  pure val NJOBS = 3

  // Job phases.
  pure val ABSENT = 0
  pure val QUEUED = 1
  pure val ADMITTED = 2
  pure val RUNNING = 3
  pure val DRAINING = 4
  pure val WIPING = 5
  pure val WIPED = 6
  pure val RELEASED = 7
  pure val ANSWERED = 8   // terminal without admission (teardown / refused)

  // Buffer states (one buffer per job, buffer id = job id).
  pure val B_NONE = 0
  pure val B_ALLOCATED = 1
  pure val B_SECRET = 2        // holds-secret
  pure val B_WIPE_REQ = 3      // wipe-requested
  pure val B_WIPE_OK = 4       // wipe-confirmed
  pure val B_FREED = 5
  pure val B_LOST = 6          // counted lost unerased at a reset

  // Reply kinds (exactly one reply per submit).
  pure val R_NONE = 0
  pure val R_OK = 1
  pure val R_TEARDOWN = 2
  pure val R_FAILED = 3
  pure val R_REFUSED = 4       // reservation above capacity

  // Teardown phases.
  pure val T_NONE = 0
  pure val T_DRAINING = 1      // requested: admission stopped, jobs drain/wipe
  pure val T_DEAD = 2          // reset done; every later submit answered teardown

  // Op codes.
  pure val OP_SUBMIT = 1
  pure val OP_ADMIT = 2
  pure val OP_START_OP = 3
  pure val OP_COMPLETE_OP = 4
  pure val OP_REQUEST_RELEASE = 5
  pure val OP_DRAIN_CONFIRMED = 6
  pure val OP_DRAIN_UNCONFIRMED = 7
  pure val OP_WIPE_CONFIRMED = 8
  pure val OP_WIPE_FAILED = 9
  pure val OP_FREE_BUFFER = 10
  pure val OP_TEARDOWN_BEGIN = 11
  pure val OP_TEARDOWN_FINISH = 12

  type Actor = {
    capacity: int,
    reserved: int,             // bytes currently reserved (admitted, not yet returned)
    queue: List[int],          // FIFO admission queue of job ids, head first
    phase: List[int],          // per job
    size: List[int],           // per job: reservation size (0 while absent)
    submitSeq: List[int],      // per job: submission order (0 = never submitted)
    nextSeq: int,
    buf: List[int],            // per job: buffer state
    bufOwner: List[int],       // per buffer: owning job (-1 = none)
    inFlight: List[bool],      // per job: an operation is in flight on its stream
    opExclusive: List[bool],   // per job: the in-flight operation is of an exclusive class
    opBuf: List[int],          // per job: buffer the in-flight operation touches (-1 = none)
    opFailed: List[bool],      // per job: an operation of this job failed
    drainBad: List[bool],      // per job: a drain was unconfirmed (wipe can never confirm)
    replied: List[bool],       // per job: the single reply was sent
    replyKind: List[int],      // per job
    submits: int,              // submits taken (including teardown/refused answers)
    replies: int,              // replies sent; terminal states have replies == submits
    pendingErasure: int,       // reported count of unerased buffers
    lostUnerased: int,         // buffers counted lost unerased at resets
    pinnedZeroed: bool,        // the page-locked staging buffer was zeroed
    teardown: int,
  }

  var s: Actor
  var lastOp: int
  var prev: Actor

  pure def code(c: int, a: int, b: int): int = c + 100 * a + 10000 * b

  pure val zeros: List[int] = [0, 0, 0]
  pure val falses: List[bool] = [false, false, false]
  pure val negOnes: List[int] = [-1, -1, -1]

  pure val initial: Actor = {
    capacity: CAPACITY, reserved: 0, queue: [],
    phase: zeros, size: zeros, submitSeq: zeros, nextSeq: 1,
    buf: zeros, bufOwner: negOnes,
    inFlight: falses, opExclusive: falses, opBuf: negOnes,
    opFailed: falses, drainBad: falses,
    replied: falses, replyKind: zeros,
    submits: 0, replies: 0, pendingErasure: 0, lostUnerased: 0,
    pinnedZeroed: false, teardown: T_NONE,
  }

  action init = all { CAPACITY >= 1, s' = initial, lastOp' = 0, prev' = initial }
  action go(n: Actor, op: int): bool = all { s' = n, lastOp' = op, prev' = s }

  // Buffers that hold a secret and are not wipe-confirmed. A buffer holds
  // a secret from the first completed operation until its wipe confirms;
  // wipe-requested still counts. Freed and lost buffers do not count:
  // a lost buffer was reported in lostUnerased at the reset instead.
  pure def pendingOf(x: Actor): int =
    x.buf.foldl(0, (acc, b) => acc + (if (b == B_SECRET or b == B_WIPE_REQ) 1 else 0))

  pure def exclInFlight(x: Actor): bool =
    0.to(NJOBS - 1).exists(j => x.inFlight[j] and x.opExclusive[j])

  // ---- transitions (pure; the Rust step function mirrors these) ----

  // A submit after the reset, or above capacity, is answered in the step
  // itself and never queues. A submit while teardown drains queues no
  // longer either: admission has stopped, so it is answered teardown at
  // once (REFINEMENT: answering at once, rather than at teardownFinish,
  // keeps "no caller waits across a reset" true for late submits too).
  pure def doSubmit(x: Actor, j: int, sz: int): Actor = {
    val y = { ...x, submits: x.submits + 1,
              submitSeq: x.submitSeq.replaceAt(j, x.nextSeq), nextSeq: x.nextSeq + 1,
              size: x.size.replaceAt(j, sz) }
    if (x.teardown != T_NONE)
      { ...y, phase: y.phase.replaceAt(j, ANSWERED),
        replied: y.replied.replaceAt(j, true), replyKind: y.replyKind.replaceAt(j, R_TEARDOWN),
        replies: y.replies + 1 }
    else if (sz > x.capacity)
      { ...y, phase: y.phase.replaceAt(j, ANSWERED),
        replied: y.replied.replaceAt(j, true), replyKind: y.replyKind.replaceAt(j, R_REFUSED),
        replies: y.replies + 1 }
    else
      { ...y, phase: y.phase.replaceAt(j, QUEUED), queue: y.queue.append(j) }
  }

  // Strict FIFO: only the head, only when its whole reservation fits.
  // Admission allocates the job's buffer (owner = the job).
  pure def doAdmit(x: Actor): Actor = {
    val j = x.queue[0]
    { ...x, queue: x.queue.slice(1, x.queue.length()),
      reserved: x.reserved + x.size[j],
      phase: x.phase.replaceAt(j, ADMITTED),
      buf: x.buf.replaceAt(j, B_ALLOCATED), bufOwner: x.bufOwner.replaceAt(j, j) }
  }

  // bufId is an input so that the refusal is visible: an operation may
  // touch only its own job's buffer (bufId == j). An exclusive-class
  // operation starts only when no exclusive-class operation is in
  // flight; non-exclusive operations may run beside anything.
  pure def doStartOp(x: Actor, j: int, bufId: int, excl: bool): Actor = {
    ...x, phase: x.phase.replaceAt(j, RUNNING),
    inFlight: x.inFlight.replaceAt(j, true),
    opExclusive: x.opExclusive.replaceAt(j, excl),
    opBuf: x.opBuf.replaceAt(j, bufId) }

  // A completed operation (ok or failed) leaves the buffer holding a
  // secret: witness values were staged into it. REFINEMENT: a failed
  // operation marks the job failed but the job returns to ADMITTED; it
  // must still be released (drain, wipe, free) before its reply, and
  // its reply kind is then R_FAILED.
  pure def doCompleteOp(x: Actor, j: int, ok: bool): Actor = {
    val y = { ...x, phase: x.phase.replaceAt(j, ADMITTED),
              inFlight: x.inFlight.replaceAt(j, false),
              opExclusive: x.opExclusive.replaceAt(j, false),
              opBuf: x.opBuf.replaceAt(j, -1),
              buf: x.buf.replaceAt(j, B_SECRET),
              opFailed: x.opFailed.replaceAt(j, x.opFailed[j] or not(ok)) }
    { ...y, pendingErasure: pendingOf(y) }
  }

  pure def doRequestRelease(x: Actor, j: int): Actor =
    { ...x, phase: x.phase.replaceAt(j, DRAINING) }

  pure def doDrainConfirmed(x: Actor, j: int): Actor = {
    val y = { ...x, phase: x.phase.replaceAt(j, WIPING),
              buf: if (x.buf[j] == B_SECRET) x.buf.replaceAt(j, B_WIPE_REQ) else x.buf }
    { ...y, pendingErasure: pendingOf(y) }
  }

  // REFINEMENT: an unconfirmed drain leaves the job DRAINING with
  // drainBad set. Draining may be retried; a later drainConfirmed still
  // moves to WIPING, but wipeConfirmed is then refused (the wipe cannot
  // be trusted on a stream whose drain was once unconfirmed), so the
  // buffer stays pending until the reset counts it lost unerased.
  pure def doDrainUnconfirmed(x: Actor, j: int): Actor =
    { ...x, drainBad: x.drainBad.replaceAt(j, true) }

  pure def doWipeConfirmed(x: Actor, j: int): Actor = {
    val y = { ...x, phase: x.phase.replaceAt(j, WIPED),
              buf: x.buf.replaceAt(j, B_WIPE_OK) }
    { ...y, pendingErasure: pendingOf(y) }
  }

  // A failed wipe leaves the job WIPING; the wipe may be retried.
  pure def doWipeFailed(x: Actor, j: int): Actor = x

  // Free returns the bytes to the budget and sends the job's one reply.
  // Reachable only from WIPED, i.e. after a confirmed wipe (the reset
  // path frees inside teardownFinish and counts the buffer lost).
  pure def doFreeBuffer(x: Actor, j: int): Actor = {
    ...x, phase: x.phase.replaceAt(j, RELEASED),
    buf: x.buf.replaceAt(j, B_FREED), bufOwner: x.bufOwner.replaceAt(j, -1),
    reserved: x.reserved - x.size[j],
    replied: x.replied.replaceAt(j, true),
    replyKind: x.replyKind.replaceAt(j, if (x.opFailed[j]) R_FAILED else R_OK),
    replies: x.replies + 1 }

  // Begin: stop admission. The page-locked buffer is zeroed here
  // (before the reset unmaps it).
  pure def doTeardownBegin(x: Actor): Actor =
    { ...x, teardown: T_DRAINING, pinnedZeroed: true }

  // Finish (the reset): every admitted job must already be released or
  // still be mid-release with an unerased buffer; the reset discards
  // the context, so such a buffer is counted lost unerased, its bytes
  // return, and its job is answered (R_FAILED if it had failed, else
  // R_OK: its work finished, only the erasure was lost). Every queued
  // job is answered teardown. No operation may be in flight.
  pure def finishOne(x: Actor, j: int): Actor =
    if (x.phase[j] == QUEUED)
      { ...x, phase: x.phase.replaceAt(j, ANSWERED),
        replied: x.replied.replaceAt(j, true), replyKind: x.replyKind.replaceAt(j, R_TEARDOWN),
        replies: x.replies + 1 }
    else if (x.phase[j] == ADMITTED or x.phase[j] == DRAINING or x.phase[j] == WIPING or x.phase[j] == WIPED)
      { ...x, phase: x.phase.replaceAt(j, RELEASED),
        reserved: x.reserved - x.size[j],
        buf: x.buf.replaceAt(j, if (x.buf[j] == B_SECRET or x.buf[j] == B_WIPE_REQ) B_LOST else B_FREED),
        bufOwner: x.bufOwner.replaceAt(j, -1),
        lostUnerased: x.lostUnerased + (if (x.buf[j] == B_SECRET or x.buf[j] == B_WIPE_REQ) 1 else 0),
        replied: x.replied.replaceAt(j, true),
        replyKind: x.replyKind.replaceAt(j, if (x.opFailed[j]) R_FAILED else R_OK),
        replies: x.replies + 1 }
    else x

  pure def doTeardownFinish(x: Actor): Actor = {
    val y = finishOne(finishOne(finishOne(x, 0), 1), 2)
    { ...y, queue: [], teardown: T_DEAD, pendingErasure: pendingOf(y) }
  }

  // ---- guards (also used by noDeadlock) ----
  pure def canSubmit(x: Actor): bool = 0.to(NJOBS - 1).exists(j => x.phase[j] == ABSENT)
  pure def canAdmit(x: Actor): bool = and {
    x.teardown == T_NONE, x.queue.length() > 0,
    x.reserved + x.size[x.queue[0]] <= x.capacity }
  pure def canStartOp(x: Actor): bool = 0.to(NJOBS - 1).exists(j =>
    x.phase[j] == ADMITTED and x.teardown == T_NONE)
  pure def canCompleteOp(x: Actor): bool = 0.to(NJOBS - 1).exists(j => x.inFlight[j])
  pure def canRelease(x: Actor): bool = 0.to(NJOBS - 1).exists(j =>
    x.phase[j] == ADMITTED and not(x.inFlight[j]))
  pure def canDrain(x: Actor): bool = 0.to(NJOBS - 1).exists(j => x.phase[j] == DRAINING)
  pure def canWipe(x: Actor): bool = 0.to(NJOBS - 1).exists(j =>
    x.phase[j] == WIPING and not(x.drainBad[j]))
  pure def canWipeStep(x: Actor): bool = 0.to(NJOBS - 1).exists(j => x.phase[j] == WIPING)
  pure def canFree(x: Actor): bool = 0.to(NJOBS - 1).exists(j => x.phase[j] == WIPED)
  pure def canTeardownFinish(x: Actor): bool = and {
    x.teardown == T_DRAINING, x.pinnedZeroed,
    0.to(NJOBS - 1).forall(j => not(x.inFlight[j]) and x.phase[j] != RUNNING) }
  pure def someEnabled(x: Actor): bool = or {
    canSubmit(x), canAdmit(x), canStartOp(x), canCompleteOp(x), canRelease(x),
    canDrain(x), canWipeStep(x), canFree(x),
    x.teardown == T_NONE, canTeardownFinish(x) }

  // Terminal: every submitted job has its reply and nothing is queued.
  // (with teardown dead, or without any teardown once all jobs released)
  pure def terminal(x: Actor): bool = and {
    x.queue.length() == 0, x.replies == x.submits,
    0.to(NJOBS - 1).forall(j => x.phase[j] == ABSENT or x.phase[j] == RELEASED or x.phase[j] == ANSWERED) }

  pure def waiting(x: Actor): bool = or {
    x.queue.length() > 0,
    0.to(NJOBS - 1).exists(j => x.submitSeq[j] > 0 and not(x.replied[j])) }

  // ---- actions ----
  action submitJob(j: int, sz: int): bool = all {
    0 <= j, j < NJOBS, s.phase[j] == ABSENT, 1 <= sz, sz <= 99,
    go(doSubmit(s, j, sz), code(OP_SUBMIT, j, sz)) }
  action doSubmitStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    nondet sz = 1.to(6).oneOf()
    submitJob(j, sz)
  }
  action admitStep = all { canAdmit(s), go(doAdmit(s), code(OP_ADMIT, s.queue[0], 0)) }
  action startOpJob(j: int, bufId: int, excl: int): bool = all {
    0 <= j, j < NJOBS, s.phase[j] == ADMITTED, s.teardown == T_NONE,
    bufId == j, s.bufOwner[bufId] == j, 0 <= excl, excl <= 1,
    excl == 0 or not(exclInFlight(s)),
    go(doStartOp(s, j, bufId, excl == 1), code(OP_START_OP, j, excl)) }
  action doStartOpStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    nondet e = 0.to(1).oneOf()
    startOpJob(j, j, e)
  }
  action completeOpJob(j: int, ok: int): bool = all {
    0 <= j, j < NJOBS, s.inFlight[j], 0 <= ok, ok <= 1,
    go(doCompleteOp(s, j, ok == 1), code(OP_COMPLETE_OP, j, ok)) }
  action doCompleteOpStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    nondet ok = 0.to(1).oneOf()
    completeOpJob(j, ok)
  }
  action requestReleaseJob(j: int): bool = all {
    0 <= j, j < NJOBS, s.phase[j] == ADMITTED, not(s.inFlight[j]),
    go(doRequestRelease(s, j), code(OP_REQUEST_RELEASE, j, 0)) }
  action doRequestReleaseStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    requestReleaseJob(j)
  }
  action drainConfirmedJob(j: int): bool = all {
    0 <= j, j < NJOBS, s.phase[j] == DRAINING,
    go(doDrainConfirmed(s, j), code(OP_DRAIN_CONFIRMED, j, 0)) }
  action doDrainConfirmedStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    drainConfirmedJob(j)
  }
  action drainUnconfirmedJob(j: int): bool = all {
    0 <= j, j < NJOBS, s.phase[j] == DRAINING,
    go(doDrainUnconfirmed(s, j), code(OP_DRAIN_UNCONFIRMED, j, 0)) }
  action doDrainUnconfirmedStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    drainUnconfirmedJob(j)
  }
  action wipeConfirmedJob(j: int): bool = all {
    0 <= j, j < NJOBS, s.phase[j] == WIPING, not(s.drainBad[j]),
    go(doWipeConfirmed(s, j), code(OP_WIPE_CONFIRMED, j, 0)) }
  action doWipeConfirmedStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    wipeConfirmedJob(j)
  }
  action wipeFailedJob(j: int): bool = all {
    0 <= j, j < NJOBS, s.phase[j] == WIPING,
    go(doWipeFailed(s, j), code(OP_WIPE_FAILED, j, 0)) }
  action doWipeFailedStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    wipeFailedJob(j)
  }
  action freeBufferJob(j: int): bool = all {
    0 <= j, j < NJOBS, s.phase[j] == WIPED, s.buf[j] == B_WIPE_OK,
    go(doFreeBuffer(s, j), code(OP_FREE_BUFFER, j, 0)) }
  action doFreeBufferStep = {
    nondet j = 0.to(NJOBS - 1).oneOf()
    freeBufferJob(j)
  }
  action teardownBeginStep = all {
    s.teardown == T_NONE, go(doTeardownBegin(s), code(OP_TEARDOWN_BEGIN, 0, 0)) }
  action teardownFinishStep = all {
    canTeardownFinish(s), go(doTeardownFinish(s), code(OP_TEARDOWN_FINISH, 0, 0)) }

  action step = any {
    doSubmitStep, admitStep, doStartOpStep, doCompleteOpStep,
    doRequestReleaseStep, doDrainConfirmedStep, doWipeConfirmedStep,
    doFreeBufferStep, teardownBeginStep, teardownFinishStep,
    all { CHAOS, any { doDrainUnconfirmedStep, doWipeFailedStep } },
  }

  // ---- invariants ----
  val op = lastOp % 100

  // In every non-terminal state with a waiting job, some action is
  // enabled. (TeardownBegin is enabled in every T_NONE state and
  // TeardownFinish in every T_DRAINING state without in-flight work;
  // in-flight work can always complete. A queued head that does not
  // fit waits only while admitted jobs hold bytes, and those jobs can
  // always step towards free, or teardown can begin.)
  val noDeadlock = (waiting(s) and not(terminal(s))) implies someEnabled(s)

  val budgetNeverExceeded = s.reserved >= 0 and s.reserved <= s.capacity

  // A buffer becomes freed only from wipe-confirmed, or at the reset
  // where a secret-holding buffer becomes lost instead; bytes return
  // (reserved drops for a job) only in those two steps.
  val noReuseBeforeWipeConfirmed = and {
    0.to(NJOBS - 1).forall(j => (prev.buf[j] != B_FREED and s.buf[j] == B_FREED) implies
      (prev.buf[j] == B_WIPE_OK or op == OP_TEARDOWN_FINISH)),
    0.to(NJOBS - 1).forall(j => s.buf[j] == B_LOST implies
      (s.teardown == T_DEAD and s.lostUnerased >= 1)),
    (s.reserved < prev.reserved) implies (op == OP_FREE_BUFFER or op == OP_TEARDOWN_FINISH) }

  // After the reset: nothing queued, every submitted job replied, and
  // a queued-at-teardown job's reply is teardown (checked at the
  // finish step). Later submits are answered teardown by doSubmit.
  val teardownAnswersEveryWaiter = and {
    (s.teardown == T_DEAD) implies and {
      s.queue.length() == 0, s.replies == s.submits, s.reserved == 0,
      0.to(NJOBS - 1).forall(j => s.submitSeq[j] == 0 or s.replied[j]) },
    (op == OP_TEARDOWN_FINISH) implies
      0.to(NJOBS - 1).forall(j => prev.phase[j] != QUEUED or s.replyKind[j] == R_TEARDOWN),
    (op == OP_SUBMIT and prev.teardown != T_NONE) implies
      0.to(NJOBS - 1).forall(j => prev.phase[j] != ABSENT or s.phase[j] != ANSWERED
        or s.replyKind[j] == R_TEARDOWN) }

  // An in-flight operation touches only its own job's buffer, and a
  // buffer's owner is its job while allocated.
  val noCrossJobRead = and {
    0.to(NJOBS - 1).forall(j => s.inFlight[j] implies
      (s.opBuf[j] == j and s.bufOwner[j] == j)),
    0.to(NJOBS - 1).forall(j => (s.buf[j] != B_NONE and s.buf[j] != B_FREED and s.buf[j] != B_LOST)
      implies s.bufOwner[j] == j) }

  // Strict FIFO: the queue is sorted by submission order, and an admit
  // step admits exactly the earlier-submitted head.
  val fifoAdmission = and {
    s.queue.indices().forall(i => i == 0 or
      s.submitSeq[s.queue[i - 1]] < s.submitSeq[s.queue[i]]),
    (op == OP_ADMIT) implies and {
      prev.queue.length() > 0, s.queue.length() == prev.queue.length() - 1,
      0.to(NJOBS - 1).forall(j => s.phase[j] != ADMITTED or prev.phase[j] == ADMITTED
        or prev.phase[j] == RUNNING or j == prev.queue[0]) } }

  val pendingErasureExact = s.pendingErasure == pendingOf(s)

  // Two exclusive-class operations are never in flight together.
  val exclusiveNeverConcurrent =
    0.to(NJOBS - 1).forall(j => 0.to(NJOBS - 1).forall(k =>
      (j != k and s.inFlight[j] and s.opExclusive[j]) implies
        not(s.inFlight[k] and s.opExclusive[k])))

  // Exactly one reply per submit; a reply is never unsent.
  val exactlyOneReply = and {
    s.replies <= s.submits,
    0.to(NJOBS - 1).forall(j => prev.replied[j] implies s.replied[j]),
    0.to(NJOBS - 1).forall(j => s.replied[j] implies s.replyKind[j] != R_NONE),
    0.to(NJOBS - 1).forall(j => not(s.replied[j]) implies s.replyKind[j] == R_NONE) }

  // The reset happens only with the page-locked buffer zeroed.
  val pinnedZeroedBeforeReset = (op == OP_TEARDOWN_FINISH) implies prev.pinnedZeroed

  val inv = and {
    noDeadlock, budgetNeverExceeded, noReuseBeforeWipeConfirmed,
    teardownAnswersEveryWaiter, noCrossJobRead, fifoAdmission,
    pendingErasureExact, exclusiveNeverConcurrent, exactlyOneReply,
    pinnedZeroedBeforeReset }

  // ---- witnesses ----
  // The point of the design: two jobs with operations in flight at once.
  val w_concurrent = 0.to(NJOBS - 1).exists(j => 0.to(NJOBS - 1).exists(k =>
    j != k and s.inFlight[j] and s.inFlight[k]))
  val w_exclusive = exclInFlight(s)
  val w_concurrent_with_exclusive = w_concurrent and w_exclusive
  val w_queued_head_waits = s.queue.length() > 0 and not(canAdmit(s)) and s.teardown == T_NONE
  val w_released = 0.to(NJOBS - 1).exists(j => s.phase[j] == RELEASED and s.replyKind[j] == R_OK)
  val w_failed_released = 0.to(NJOBS - 1).exists(j => s.replyKind[j] == R_FAILED)
  val w_lost = s.lostUnerased > 0
  val w_dead = s.teardown == T_DEAD
  val w_teardown_replied = 0.to(NJOBS - 1).exists(j => s.replyKind[j] == R_TEARDOWN)
  val w_refused = 0.to(NJOBS - 1).exists(j => s.replyKind[j] == R_REFUSED)
  val w_pending = s.pendingErasure > 0

  // Temporal form of the concurrency point (for `quint verify` users;
  // the simulator gate uses the w_concurrent witness above).
  temporal eventuallyConcurrent = eventually(w_concurrent)
}

// Instances for the simulator.
module actor_default {
  import device_actor(CAPACITY = 4, CHAOS = true).*
}
module actor_tight {
  import device_actor(CAPACITY = 2, CHAOS = true).*
}
module actor_calm {
  import device_actor(CAPACITY = 4, CHAOS = false).*
}
module actor_roomy {
  import device_actor(CAPACITY = 12, CHAOS = true).*
}



