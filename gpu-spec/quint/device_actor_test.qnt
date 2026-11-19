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

// Directed tests of device_actor.qnt. Run with
//   quint test gpu-spec/quint/device_actor_test.qnt --main test_actor --match 'Test$'
//   quint test gpu-spec/quint/device_actor_test.qnt --main refuse_actor --match 'Test$'
// Refusal tests end in .fail(): the named step must be refused.

module test_actor {
  import device_actor(CAPACITY = 4, CHAOS = true).* from "./device_actor"

  // one whole job: submit, admit, run, complete, release, drain, wipe, free
  action wholeJob(j: int, sz: int): bool =
    submitJob(j, sz).then(admitStep).then(startOpJob(j, j, 0)).then(completeOpJob(j, 1))
      .then(requestReleaseJob(j)).then(drainConfirmedJob(j)).then(wipeConfirmedJob(j))
      .then(freeBufferJob(j))

  run wholeJobTest = init.then(wholeJob(0, 2))
    .expect(s.phase[0] == RELEASED and s.replyKind[0] == R_OK and s.reserved == 0
            and s.pendingErasure == 0 and s.buf[0] == B_FREED and s.replies == 1)

  // pending erasure is exact between completion and confirmed wipe
  run pendingExactTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(completeOpJob(0, 1))
    .expect(s.pendingErasure == 1 and s.buf[0] == B_SECRET)
    .then(requestReleaseJob(0)).then(drainConfirmedJob(0))
    .expect(s.pendingErasure == 1 and s.buf[0] == B_WIPE_REQ)
    .then(wipeConfirmedJob(0)).expect(s.pendingErasure == 0)

  // strict FIFO: capacity 4, job0 takes 3, job1 (size 3) waits at the
  // head, job2 (size 1) would fit in the free 1 unit but must not pass
  run fifoHeadWaitsTest = init.then(submitJob(0, 3)).then(admitStep)
    .then(submitJob(1, 3)).then(submitJob(2, 1))
    .expect(s.queue == [1, 2] and s.phase[2] == QUEUED and s.reserved == 3)
    .then(startOpJob(0, 0, 0)).then(completeOpJob(0, 1)).then(requestReleaseJob(0))
    .then(drainConfirmedJob(0)).then(wipeConfirmedJob(0)).then(freeBufferJob(0))
    .then(admitStep)
    .expect(s.phase[1] == ADMITTED and s.phase[2] == QUEUED and s.queue == [2])

  // two operations in flight at once (the point of the design)
  run concurrentOpsTest = init.then(submitJob(0, 2)).then(submitJob(1, 2))
    .then(admitStep).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(startOpJob(1, 1, 0))
    .expect(s.inFlight[0] and s.inFlight[1] and w_concurrent)

  // a non-exclusive operation may run beside an exclusive one
  run exclusiveBesidePlainTest = init.then(submitJob(0, 2)).then(submitJob(1, 2))
    .then(admitStep).then(admitStep)
    .then(startOpJob(0, 0, 1)).then(startOpJob(1, 1, 0))
    .expect(w_concurrent_with_exclusive and exclusiveNeverConcurrent)

  // a failed operation still drains, wipes and frees; reply is failed
  run failedOpStillWipedTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(completeOpJob(0, 0))
    .expect(s.opFailed[0] and s.pendingErasure == 1)
    .then(requestReleaseJob(0)).then(drainConfirmedJob(0)).then(wipeConfirmedJob(0))
    .then(freeBufferJob(0))
    .expect(s.replyKind[0] == R_FAILED and s.reserved == 0 and s.pendingErasure == 0)

  // a failed wipe can be retried
  run wipeRetryTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(completeOpJob(0, 1)).then(requestReleaseJob(0))
    .then(drainConfirmedJob(0)).then(wipeFailedJob(0))
    .expect(s.phase[0] == WIPING and s.pendingErasure == 1)
    .then(wipeConfirmedJob(0)).then(freeBufferJob(0))
    .expect(s.replyKind[0] == R_OK)

  // an unconfirmed drain: wipe can never confirm; the reset counts the
  // buffer lost unerased and returns its bytes
  run unconfirmedDrainLostTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(completeOpJob(0, 1)).then(requestReleaseJob(0))
    .then(drainUnconfirmedJob(0)).then(drainConfirmedJob(0))
    .expect(s.phase[0] == WIPING and s.drainBad[0] and s.pendingErasure == 1)
    .then(teardownBeginStep).then(teardownFinishStep)
    .expect(s.teardown == T_DEAD and s.buf[0] == B_LOST and s.lostUnerased == 1
            and s.reserved == 0 and s.pendingErasure == 0 and s.replied[0])

  // teardown answers every queued job, and every later submit
  run teardownAnswersAllTest = init.then(submitJob(0, 3)).then(admitStep)
    .then(submitJob(1, 3)).then(teardownBeginStep).then(teardownFinishStep)
    .expect(s.replyKind[1] == R_TEARDOWN and s.replies == 2 and s.queue.length() == 0)
    .then(submitJob(2, 1))
    .expect(s.replyKind[2] == R_TEARDOWN and s.phase[2] == ANSWERED and s.replies == 3)

  // teardown between begin and finish still lets an admitted job wipe
  run teardownDrainsFirstTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(completeOpJob(0, 1)).then(teardownBeginStep)
    .then(requestReleaseJob(0)).then(drainConfirmedJob(0)).then(wipeConfirmedJob(0))
    .then(freeBufferJob(0)).then(teardownFinishStep)
    .expect(s.replyKind[0] == R_OK and s.lostUnerased == 0 and s.teardown == T_DEAD)

  // a reservation above capacity is refused at once, never queued
  run overCapacityRefusedTest = init.then(submitJob(0, 5))
    .expect(s.replyKind[0] == R_REFUSED and s.queue.length() == 0 and s.replies == 1)
}

module refuse_actor {
  import device_actor(CAPACITY = 4, CHAOS = true).* from "./device_actor"

  // admission over capacity is refused (head does not fit)
  run admitOverCapacityTest = init.then(submitJob(0, 3)).then(admitStep)
    .then(submitJob(1, 3)).then(admitStep).fail()

  // an operation on another job's buffer is refused
  run crossJobBufferTest = init.then(submitJob(0, 2)).then(submitJob(1, 2))
    .then(admitStep).then(admitStep).then(startOpJob(0, 1, 0)).fail()

  // a second exclusive-class operation is refused while one runs
  run secondExclusiveTest = init.then(submitJob(0, 2)).then(submitJob(1, 2))
    .then(admitStep).then(admitStep).then(startOpJob(0, 0, 1))
    .then(startOpJob(1, 1, 1)).fail()

  // free before a confirmed wipe is refused
  run freeBeforeWipeTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(completeOpJob(0, 1)).then(requestReleaseJob(0))
    .then(freeBufferJob(0)).fail()

  // a wipe on a stream whose drain was unconfirmed never confirms
  run wipeAfterBadDrainTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(completeOpJob(0, 1)).then(requestReleaseJob(0))
    .then(drainUnconfirmedJob(0)).then(drainConfirmedJob(0))
    .then(wipeConfirmedJob(0)).fail()

  // no new operation starts once teardown has begun
  run opAfterTeardownBeginTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(teardownBeginStep).then(startOpJob(0, 0, 0)).fail()

  // the reset is refused while an operation is in flight
  run finishWhileRunningTest = init.then(submitJob(0, 2)).then(admitStep)
    .then(startOpJob(0, 0, 0)).then(teardownBeginStep).then(teardownFinishStep).fail()
}
