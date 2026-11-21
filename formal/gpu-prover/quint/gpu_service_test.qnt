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

// Directed tests of the event-driven requirements of gpu_service.qnt. Each
// test names the requirement it checks. Run with
//   quint test gpu_service_test.qnt --main <module> --match 'Test$'
// (match the test names; the imported actions are not tests). The gate replays
// the traces of these tests through the oracle, so every test takes at least
// one step and no test takes a step that the specification refuses.

module test_default {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  action request(a: int, b: int): bool =
    doArrive.then(admitWith(a, b)).then(finishWith(1)).then(wipeWith(1)).then(doReply)

  // three arrivals at a daemon that is down: three daemon failures at clock 0
  action downThree: bool = doCrash.then(doArrive).then(doArrive).then(doArrive)

  // GPU-029: free memory covers the cold need (6 + 8)
  run ladderGpuTest = init.then(doArrive).then(admitWith(14, 0))
    .expect(s.step == GPU and s.admNeed == 14 and s.onDev and s.dirty and s.tables and s.ctx)
  // GPU-026: covered only after the wait
  run ladderWaitTest = init.then(doArrive).then(admitWith(13, 14))
    .expect(s.step == WAIT and s.admFree == 14 and not(s.degraded))
  // GPU-026: the second reading is not bounded by the generator's range: a
  // reading of 100 after the wait covers the need of 14 (wire value b = 100)
  run ladderWaitLargeReadingTest = init.then(doArrive).then(admitWith(0, 100))
    .expect(s.step == WAIT and s.admNeed == 14 and s.admFree == 100 and not(s.degraded))
  // GPU-027, GPU-023: not covered after the wait; the reduced need fits
  run ladderEvictTest = init.then(doArrive).then(admitWith(3, 2))
    .expect(s.step == EVICT and not(s.onDev) and s.admNeed == 2 and s.degraded and s.devWork)
  // GPU-028, GPU-023: not even the reduced need fits
  run ladderCpuTest = init.then(doArrive).then(admitWith(1, 1))
    .expect(s.step == CPU and not(s.devWork) and not(s.tables) and s.degraded and s.phase == PROVING)
  // GPU-023: production mode serves a proof of step evict, marked degraded
  run evictServedDegradedTest = init.then(request(3, 2))
    .expect(s.served == 1 and s.degradedServed == 1 and s.degradedRefused == 0 and s.errors == 0)
  // GPU-030, GPU-034, GPU-082: the evict policy leaves nothing on the device after the reply
  run evictPolicyTest = init.then(request(20, 20))
    .expect(s.phase == IDLE and not(s.onDev) and not(s.tables) and not(s.dirty) and s.served == 1
            and s.degradedServed == 0 and s.verifyAccepts == 1 and not(s.cold))
  // GPU-045, GPU-046, GPU-077: one served, one waits, the third gets busy, falls
  // back and records no failure
  run queueTest = init.then(doArrive).then(doArrive).then(doArrive)
    .expect(s.waiting == 1 and s.busyReplies == 1 and s.clientCpu == 1 and s.brFails == []
            and s.brOpenUntil == 0)
    .then(admitWith(20, 20)).then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.phase == ACCEPTED and s.waiting == 0 and s.served == 1)
  // GPU-077: busy answers alone never open the breaker
  run busyNoFailureTest = init.then(doArrive).then(doArrive).then(doArrive).then(doArrive)
    .then(doArrive).then(doArrive)
    .expect(s.busyReplies == 4 and s.clientCpu == 4 and s.brFails == [] and s.brOpenUntil == 0
            and s.breakerSkips == 0)
  // GPU-040, GPU-021, GPU-077: a refused proof is an error, the client proves on
  // the CPU and records one failure; the daemon stays up
  run verifyRefusedTest = init.then(doArrive).then(admitWith(20, 20)).then(finishWith(0))
    .then(wipeWith(1)).then(doReply)
    .expect(s.errors == 1 and s.served == 0 and s.clientCpu == 1 and s.up and s.brFails == [0]
            and s.verifyAccepts == 0 and s.unverifiedReturned == 0)
  // GPU-035, GPU-077: an unconfirmed wipe ends the daemon after an error reply;
  // the caller and the waiting caller prove on their CPU and each records a failure
  run wipeUnconfirmedTest = init.then(doArrive).then(doArrive).then(admitWith(20, 20))
    .then(finishWith(1)).then(wipeWith(0)).expect(s.dirty and not(s.wipeOk)).then(doReply)
    .expect(not(s.up) and s.errors == 1 and s.clientCpu == 2 and s.served == 0
            and s.brFails == [0, 0] and s.brOpenUntil == 0 and s.verifyAccepts == 0)
  // GPU-035: the same without a waiting caller records one failure
  run wipeUnconfirmedAloneTest = init.then(doArrive).then(admitWith(20, 20))
    .then(finishWith(1)).then(wipeWith(0)).then(doReply)
    .expect(not(s.up) and s.errors == 1 and s.clientCpu == 1 and s.brFails == [0])
  // GPU-012, GPU-073, GPU-023: a decline with the reason fault is one fallback,
  // counts its reason and the total, and production mode serves the proof marked
  // degraded
  run declineTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(5))
    .expect(s.fallbacks == 1 and s.degraded and s.declines == [0, 0, 0, 0, 0, 1, 0] and s.declined == 1)
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.degradedServed == 1 and s.served == 1 and s.errors == 0 and s.degradedRefused == 0
            and s.declined == 1)
  // GPU-073: each of the seven reasons has its own count
  run declineReasonsTest = init.then(doArrive).then(admitWith(20, 20))
    .then(declineWith(0)).then(declineWith(1)).then(declineWith(2)).then(declineWith(3))
    .then(declineWith(4)).then(declineWith(5)).then(declineWith(6)).then(declineWith(6))
    .expect(s.declines == [1, 1, 1, 1, 1, 1, 2] and s.declined == 8 and s.fallbacks == 6
            and s.degraded)
  // GPU-085, GPU-023: declines with the reasons no-device and below-min-k are
  // counted, are no fallback and leave the proof unmarked: served, not degraded
  run expectedDeclineTest = init.then(doArrive).then(admitWith(20, 20))
    .then(declineWith(0)).then(declineWith(1)).then(declineWith(1))
    .expect(s.fallbacks == 0 and not(s.degraded) and s.declines == [1, 2, 0, 0, 0, 0, 0]
            and s.declined == 3 and s.devWork)
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 1 and s.degradedServed == 0 and s.errors == 0 and s.declined == 3)
  // GPU-012: each of the reasons 2..6 alone is one fallback and marks the proof
  run declineShapeTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(2))
    .expect(s.fallbacks == 1 and s.degraded)
  run declineUnreducedTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(3))
    .expect(s.fallbacks == 1 and s.degraded)
  run declineMemoryTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(4))
    .expect(s.fallbacks == 1 and s.degraded)
  run declineDeviceErrorTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(6))
    .expect(s.fallbacks == 1 and s.degraded)
  // GPU-085: each expected reason alone is no fallback
  run declineNoDeviceTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(0))
    .expect(s.fallbacks == 0 and not(s.degraded) and s.declined == 1)
  run declineBelowMinKTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(1))
    .expect(s.fallbacks == 0 and not(s.degraded) and s.declined == 1)
  // GPU-085, GPU-023: an expected decline does not remove the mark of step evict
  run expectedDeclineEvictTest = init.then(doArrive).then(admitWith(3, 2)).then(declineWith(1))
    .expect(s.degraded and s.fallbacks == 0)
    .then(finishWith(1)).then(wipeWith(1)).then(doReply).expect(s.degradedServed == 1)
  // GPU-038: a permitted read-back is counted; the transition counts a kind
  // above 3 as a bad read-back (such an op is refused and is not a step)
  run readbackTest = init.then(doArrive).then(admitWith(20, 20)).then(readbackOf(0))
    .then(readbackOf(1)).then(readbackOf(2)).then(readbackOf(3))
    .expect(s.readbacks == 4 and s.badReadbacks == 0 and readback(s, 4).badReadbacks == 1
            and readback(s, 5).badReadbacks == 1 and readback(s, 4).readbacks == 5)
  // GPU-036, GPU-038: the counters (kind 2) can be read while the request is
  // proved; nothing else changes
  run readbackProvedTest = init.then(doArrive).then(admitWith(20, 20)).then(readbackOf(2))
    .then(finishWith(1)).expect(s.phase == PROVED and not(s.devWork) and s.readbacks == 1)
    .then(readbackOf(2)).then(readbackOf(2))
    .expect(s.phase == PROVED and s.readbacks == 3 and s.badReadbacks == 0 and s.dirty)
    .then(wipeWith(1)).then(doReply).expect(s.served == 1 and s.readbacks == 3)
  // GPU-039: the accept is counted at the served reply, not at the end of the proof
  run acceptCountedAtReplyTest = init.then(doArrive).then(admitWith(20, 20)).then(finishWith(1))
    .expect(s.verifyOk and s.verifyAccepts == 0).then(wipeWith(1)).expect(s.verifyAccepts == 0)
    .then(doReply).expect(s.verifyAccepts == 1 and s.served == 1)
  // GPU-039, GPU-021: an accept is not counted when the daemon dies before the reply
  run acceptLostInCrashTest = init.then(doArrive).then(admitWith(20, 20)).then(finishWith(1))
    .then(doCrash).expect(s.verifyAccepts == 0 and s.served == 0 and s.clientCpu == 1)
  // GPU-048, GPU-049, GPU-022, GPU-077: three restarts in the window, then the
  // supervisor stops; an arrival then goes to the client's CPU and is a failure
  run restartLimitTest = init
    .then(doCrash).then(doRestart).then(doCrash).then(doRestart).then(doCrash).then(doRestart)
    .expect(s.up and s.restartTimes.length() == 3 and s.cold)
    .then(doCrash).then(doRestart).expect(s.stopped and not(s.up))
    .then(doArrive).expect(s.clientCpu == 1 and s.brFails == [0] and s.phase == IDLE)
  // GPU-048: restarts older than the window no longer count
  run restartWindowTest = init
    .then(doCrash).then(doRestart).then(doCrash).then(doRestart).then(doCrash).then(doRestart)
    .then(tickBy(400)).then(tickBy(200)).then(doCrash).then(doRestart)
    .expect(s.up and s.restartTimes == [600])
  // GPU-048: one second earlier the three restarts still count
  run restartWindowInsideTest = init
    .then(doCrash).then(doRestart).then(doCrash).then(doRestart).then(doCrash).then(doRestart)
    .then(tickBy(400)).then(tickBy(199)).then(doCrash).then(doRestart)
    .expect(s.stopped and not(s.up))
  // GPU-050: a breached bound restarts the daemon after the request, labelled cold
  run overBoundTest = init.then(doArrive).then(admitWith(20, 20)).then(doOverBound)
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(not(s.up) and s.served == 1 and s.brFails == [])
    .then(doRestart).expect(s.up and s.cold)
  // GPU-050, GPU-076, GPU-077: at the planned restart the waiting caller proves on
  // its CPU and records a failure, after the served proof cleared the record
  run overBoundWaitingTest = init.then(doArrive).then(admitWith(20, 20)).then(finishWith(0))
    .then(wipeWith(1)).then(doReply).expect(s.brFails == [0])
    .then(tickBy(7)).then(doArrive).then(doArrive).then(admitWith(20, 20)).then(doOverBound)
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(not(s.up) and s.served == 1 and s.clientCpu == 2 and s.brFails == [7])
  // GPU-037: a lost connection ends the device phases of the request
  run leaseLossTest = init.then(doArrive).then(admitWith(20, 20)).then(doLeaseLoss)
    .expect(not(s.devWork) and s.fallbacks == 1 and s.degraded and s.leaseLost and s.declined == 0)
  // GPU-021, GPU-077: a crash sends the caller in flight and the waiting caller to
  // their CPU and records a failure for each
  run crashFailuresTest = init.then(doArrive).then(doArrive).then(doCrash)
    .expect(not(s.up) and s.clientCpu == 2 and s.brFails == [0, 0] and s.phase == IDLE
            and s.waiting == 0)
  // GPU-077: a crash of an idle daemon is no failure until a request finds it absent
  run crashIdleTest = init.then(doCrash).expect(s.brFails == [] and s.clientCpu == 0)
    .then(doArrive).expect(s.brFails == [0] and s.clientCpu == 1)
  // GPU-075: the breaker opens at the third failure within the window
  run breakerOpensTest = init.then(doCrash).then(doArrive).then(doArrive)
    .expect(s.brFails == [0, 0] and s.brOpenUntil == 0 and not(brOpen(s)))
    .then(doArrive)
    .expect(s.brFails == [] and s.brOpenUntil == 600 and brOpen(s) and s.clientCpu == 3
            and s.breakerSkips == 0)
  // GPU-075: while it is open the client proves on its CPU without contacting
  // the daemon, even when the daemon is up again
  run breakerSkipTest = init.then(downThree).then(doRestart).then(doArrive)
    .expect(s.breakerSkips == 1 and s.clientCpu == 4 and s.phase == IDLE and s.up
            and s.brFails == [] and s.brOpenUntil == 600 and s.requests == 4)
  // GPU-075: the breaker does not open when the first failure is BR_WINDOW old
  run breakerWindowTest = init.then(doCrash).then(doArrive).then(tickBy(400)).then(tickBy(200))
    .then(doArrive).then(doArrive)
    .expect(s.brFails == [600, 600] and s.brOpenUntil == 0 and not(brOpen(s)))
  // GPU-075: one second earlier the first failure still counts
  run breakerWindowInsideTest = init.then(doCrash).then(doArrive).then(tickBy(400)).then(tickBy(199))
    .then(doArrive).then(doArrive)
    .expect(s.brFails == [] and s.brOpenUntil == 1199 and brOpen(s))
  // GPU-075: the breaker closes at exactly brOpenUntil
  run breakerClosesTest = init.then(downThree).then(doRestart).then(tickBy(400)).then(tickBy(199))
    .then(doArrive).expect(s.breakerSkips == 1 and s.phase == IDLE and s.clock == 599)
    .then(tickBy(1)).expect(s.clock == s.brOpenUntil and not(brOpen(s)))
    .then(doArrive).expect(s.breakerSkips == 1 and s.phase == ACCEPTED and s.clientCpu == 4)
  // GPU-076: a served proof clears the failure record
  run servedClearsTest = init.then(doCrash).then(doArrive).then(doArrive).then(doRestart)
    .then(doArrive).then(admitWith(20, 20)).then(finishWith(1)).then(wipeWith(1))
    .expect(s.brFails == [0, 0])
    .then(doReply).expect(s.brFails == [] and s.served == 1 and s.brOpenUntil == 0)
    .then(doCrash).then(doArrive).then(doArrive)
    .expect(s.brFails == [0, 0] and s.brOpenUntil == 0)
  // GPU-076: a served proof does not shorten an open cooldown
  run servedKeepsCooldownTest = init.then(doArrive).then(doArrive)
    .then(admitWith(20, 20)).then(finishWith(0)).then(wipeWith(1)).then(doReply).then(doArrive)
    .then(admitWith(20, 20)).then(finishWith(0)).then(wipeWith(1)).then(doReply).then(doArrive)
    .then(admitWith(20, 20)).then(finishWith(0)).then(wipeWith(1)).then(doReply)
    .expect(s.brOpenUntil == 600 and s.brFails == [] and s.phase == ACCEPTED and s.errors == 3)
    .then(admitWith(20, 20)).then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 1 and s.brOpenUntil == 600 and brOpen(s))
}

module test_keep {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = true,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = true,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  action request(a: int, b: int): bool =
    doArrive.then(admitWith(a, b)).then(finishWith(1)).then(wipeWith(1)).then(doReply)

  // GPU-025: with the copies resident the need is the per-proof part only
  run keepNeedTest = init.then(request(20, 20)).expect(s.onDev)
    .then(doArrive).then(admitWith(6, 6)).expect(s.step == GPU and s.admNeed == 6)
  // GPU-082, GPU-030: the keep policy frees the MSM tables at the end of the
  // request but keeps the key copies
  run keepTablesTest = init.then(doArrive).then(admitWith(20, 20)).expect(s.tables and s.onDev)
    .then(finishWith(1)).then(wipeWith(1)).expect(not(s.tables) and s.onDev and not(s.dirty))
    .then(doReply).expect(s.phase == IDLE and not(s.tables) and s.onDev and s.served == 1)
  // GPU-027: an evict step from a keep state with the key copies on the device:
  // the copies are gone and the need is the reduced need
  run keepEvictStepTest = init.then(request(20, 20)).expect(s.onDev)
    .then(doArrive).then(admitWith(3, 3))
    .expect(s.step == EVICT and not(s.onDev) and s.admNeed == 2 and s.admFree == 11
            and s.degraded and s.devWork)
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(not(s.onDev) and s.degradedServed == 1 and s.runFailed)
  // GPU-027: with no free memory at all the freed copies (8) cover the reduced need
  run keepEvictFromZeroTest = init.then(request(20, 20)).then(doArrive).then(admitWith(0, 0))
    .expect(s.step == EVICT and s.admFree == 8 and s.admNeed == 2 and not(s.onDev))
  // GPU-030: an explicit evict frees the key copies
  run explicitEvictTest = init.then(request(20, 20)).expect(s.onDev).then(doEvict)
    .expect(not(s.onDev) and not(s.tables))
  // GPU-024: a degraded proof in bench mode fails the run
  run benchTest = init.then(request(20, 20)).expect(not(s.runFailed))
    .then(request(1, 1)).expect(s.runFailed and s.degradedServed == 1 and s.served == 2)
  // GPU-085, GPU-024: an expected decline does not fail a bench run
  run benchExpectedDeclineTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(1))
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(not(s.runFailed) and s.served == 1 and s.degradedServed == 0)
    .then(doArrive).then(admitWith(20, 20)).then(declineWith(5))
    .then(finishWith(1)).then(wipeWith(1)).then(doReply).expect(s.runFailed)
}

module test_wsl {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 16, KEEP = false,
    WSL = true, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-057: no lock, no device phase
  run noLockTest = init.then(doArrive).then(admitWith(20, 20))
    .expect(s.step == CPU and not(s.devWork) and s.degraded)
  // GPU-058: the budget decides, not the free-memory reading
  run budgetTest = init.then(lockTo(1)).then(doArrive).then(admitWith(0, 0))
    .expect(s.step == GPU and s.admFree == 16)
  // GPU-061: a lost lock ends the device phases
  run lockLossTest = init.then(lockTo(1)).then(doArrive).then(admitWith(0, 0)).then(doLeaseLoss)
    .expect(not(s.devWork) and not(s.lockHeld) and s.fallbacks == 1)
  // GPU-060: nothing stays on the device after the request
  run wslIdleTest = init.then(lockTo(1)).then(doArrive).then(admitWith(0, 0)).expect(s.onDev)
    .then(finishWith(1)).then(wipeWith(1)).expect(not(s.onDev) and not(s.tables))
    .then(doReply).expect(s.served == 1 and not(s.onDev))
}

module test_nodevice {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = false, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-020: no device, every phase on the CPU, no context; the proof is not degraded
  run noDeviceTest = init.then(doArrive).then(admitWith(20, 20))
    .expect(s.step == NONE and not(s.devWork) and not(s.ctx) and not(s.degraded))
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 1 and s.degradedServed == 0)
}

module test_accept {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  action request(a: int, b: int): bool =
    doArrive.then(admitWith(a, b)).then(finishWith(1)).then(wipeWith(1)).then(doReply)

  // GPU-078: acceptance mode, step evict: degraded, no device work, a confirmed
  // empty wipe; the reply is a degraded error, nothing is served, no failure
  run acceptEvictTest = init.then(doArrive).then(admitWith(3, 2))
    .expect(s.phase == WIPED and s.step == EVICT and s.degraded and s.wipeOk and not(s.devWork)
            and not(s.dirty) and not(s.ctx) and not(s.devUsed) and not(s.tables) and not(s.onDev))
    .then(doReply)
    .expect(s.served == 0 and s.degradedRefused == 1 and s.errors == 1 and s.clientCpu == 1
            and s.brFails == [] and s.brOpenUntil == 0 and s.up and s.phase == IDLE
            and s.degradedServed == 0 and s.verifyAccepts == 0)
  // GPU-078: the same at step cpu
  run acceptCpuTest = init.then(doArrive).then(admitWith(1, 1))
    .expect(s.phase == WIPED and s.step == CPU and s.degraded and not(s.devWork) and not(s.dirty))
    .then(doReply).expect(s.served == 0 and s.degradedRefused == 1 and s.brFails == [])
  // GPU-085, GPU-078: an acceptance-mode proof with only expected declines is served
  run acceptExpectedDeclineTest = init.then(doArrive).then(admitWith(20, 20))
    .then(declineWith(1)).then(declineWith(0))
    .expect(s.fallbacks == 0 and not(s.degraded))
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 1 and s.degradedRefused == 0 and s.errors == 0 and s.degradedServed == 0
            and s.declines == [1, 1, 0, 0, 0, 0, 0])
  // GPU-012, GPU-078: one decline with a reason 2..6 among expected ones refuses it
  run acceptMixedDeclineTest = init.then(doArrive).then(admitWith(20, 20))
    .then(declineWith(1)).then(declineWith(3)).then(declineWith(0))
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 0 and s.degradedRefused == 1 and s.errors == 1 and s.declined == 3)
  // GPU-078: a decline with the reason memory in acceptance mode: a degraded error
  // although the verifier accepts; no proof, no failure
  run acceptDeclineTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(4))
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 0 and s.degradedRefused == 1 and s.errors == 1 and s.clientCpu == 1
            and s.verifyAccepts == 0 and s.brFails == [] and s.declines == [0, 0, 0, 0, 1, 0, 0])
  // GPU-078, GPU-040: the degraded check comes before the verifier's answer: a
  // degraded request that the verifier refused is a degraded error, not a failure
  run acceptDeclineRefusedTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(2))
    .then(finishWith(0)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 0 and s.degradedRefused == 1 and s.errors == 1 and s.brFails == [])
  // GPU-035, GPU-078: the unconfirmed wipe comes before the degraded check
  run acceptDeclineWipeTest = init.then(doArrive).then(admitWith(20, 20)).then(declineWith(2))
    .then(finishWith(1)).then(wipeWith(0)).then(doReply)
    .expect(not(s.up) and s.degradedRefused == 0 and s.errors == 1 and s.brFails == [0])
  // GPU-078: a lost lease is a fallback, so the request gets a degraded error
  run acceptLeaseLossTest = init.then(doArrive).then(admitWith(20, 20)).then(doLeaseLoss)
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 0 and s.degradedRefused == 1)
  // GPU-078: a request that is not degraded is served in acceptance mode
  run acceptCleanTest = init.then(request(20, 20))
    .expect(s.served == 1 and s.degradedServed == 0 and s.degradedRefused == 0 and s.errors == 0)
  // GPU-078, GPU-045: after a degraded error the waiting request is accepted
  run acceptWaitingTest = init.then(doArrive).then(doArrive).then(admitWith(1, 1)).then(doReply)
    .expect(s.phase == ACCEPTED and s.waiting == 0 and s.degradedRefused == 1 and s.clientCpu == 1)
  // GPU-078, GPU-050: an over-bound request with a degraded error still ends the
  // daemon; only the waiting caller records a failure
  run acceptOverBoundTest = init.then(doArrive).then(doArrive).then(admitWith(20, 20))
    .then(declineWith(6)).then(doOverBound).then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(not(s.up) and s.degradedRefused == 1 and s.clientCpu == 2 and s.brFails == [0])
}

module test_accept_keep {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = true,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  action request(a: int, b: int): bool =
    doArrive.then(admitWith(a, b)).then(finishWith(1)).then(wipeWith(1)).then(doReply)

  // GPU-078, GPU-027: acceptance mode, evict step from a keep state: the frees of
  // the step are applied (the key copies are gone), nothing runs, nothing is served
  run acceptKeepEvictTest = init.then(request(20, 20)).expect(s.onDev and s.served == 1)
    .then(doArrive).then(admitWith(3, 3))
    .expect(s.phase == WIPED and s.step == EVICT and not(s.onDev) and s.admNeed == 2
            and s.admFree == 11 and not(s.devWork) and not(s.dirty) and not(s.tables))
    .then(doReply).expect(s.served == 1 and s.degradedRefused == 1 and not(s.onDev))
}

module test_accept_nodevice {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = false, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-020, GPU-078: without a device the step is none, which is not degraded:
  // acceptance mode runs the request on the CPU and serves the proof
  run acceptNoDeviceTest = init.then(doArrive).then(admitWith(0, 0))
    .expect(s.step == NONE and s.phase == PROVING and not(s.degraded) and not(s.devWork))
    .then(finishWith(1)).then(wipeWith(1)).then(doReply)
    .expect(s.served == 1 and s.degradedRefused == 0 and s.errors == 0)
}

module test_accept_wsl {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 16, KEEP = false,
    WSL = true, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-057, GPU-078: on WSL2 without the lock the step is cpu, so acceptance
  // mode gives a degraded error and runs nothing
  run acceptNoLockTest = init.then(doArrive).then(admitWith(20, 20))
    .expect(s.step == CPU and s.phase == WIPED and s.degraded and s.wipeOk and s.admNeed == 0)
    .then(doReply).expect(s.served == 0 and s.degradedRefused == 1 and s.brFails == [])
  // GPU-058, GPU-078: with the lock and a budget that covers the need it is served
  run acceptLockTest = init.then(lockTo(1)).then(doArrive).then(admitWith(0, 0))
    .expect(s.step == GPU and s.phase == PROVING)
    .then(finishWith(1)).then(wipeWith(1)).then(doReply).expect(s.served == 1)
}

module test_breaker_short {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 5, BR_COOLDOWN = 7,
    CHAOS = true, TICKS = true, TICK_MAX = 3).* from "./gpu_service"

  // GPU-075: window 5, cooldown 7: a failure exactly 5 s old is dropped; the
  // breaker opens at three failures inside 5 s, skips until clock 13, and
  // contacts the daemon again at 13
  run shortWindowTest = init.then(doCrash).then(doArrive).then(tickBy(2)).then(doArrive)
    .expect(s.brFails == [0, 2])
    .then(tickBy(3)).then(doArrive).expect(s.brFails == [2, 5] and s.brOpenUntil == 0)
    .then(tickBy(1)).then(doArrive).expect(s.brFails == [] and s.brOpenUntil == 13)
    .then(tickBy(6)).then(doArrive).expect(s.breakerSkips == 1 and s.brFails == [])
    .then(tickBy(1)).then(doArrive).expect(s.breakerSkips == 1 and s.brFails == [13])
  // GPU-075: the breaker opens again after a cooldown
  run reopenTest = init.then(doCrash).then(doArrive).then(doArrive).then(doArrive)
    .expect(s.brOpenUntil == 7).then(tickBy(7)).then(doArrive).then(doArrive).then(doArrive)
    .expect(s.brOpenUntil == 14 and s.breakerSkips == 0 and s.clientCpu == 6)
}

module test_breaker1 {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 1, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-075: limit 1: the first failure opens the breaker
  run limitOneTest = init.then(doCrash).then(doArrive)
    .expect(s.brFails == [] and s.brOpenUntil == 600 and s.breakerSkips == 0)
    .then(doArrive).expect(s.breakerSkips == 1)
  // GPU-077: two failures of one event are recorded one after the other; at
  // limit 1 each of them opens the breaker, so the record stays empty
  run limitOneTwoFailuresTest = init.then(doArrive).then(doArrive).then(doCrash)
    .expect(s.brFails == [] and s.brOpenUntil == 600 and s.clientCpu == 2)
}

module test_breaker2 {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 2, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-077: two failures of one event are recorded one after the other at the
  // same clock value: at limit 2 the crash of a daemon with a caller in flight
  // and a waiting caller opens the breaker
  run twoFailuresOpenTest = init.then(doArrive).then(doArrive).then(tickBy(9)).then(doCrash)
    .expect(s.brFails == [] and s.brOpenUntil == 609 and s.clientCpu == 2)
  // GPU-077: with one failure on record, the first of the two opens the breaker
  // and the second is recorded after it
  run thirdFailureAfterOpenTest = init.then(doCrash).then(doArrive).then(doRestart)
    .then(doArrive).then(doArrive).then(tickBy(9)).then(doCrash)
    .expect(s.brFails == [9] and s.brOpenUntil == 609 and s.clientCpu == 3)
}

module test_breaker0 {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 0, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-075: a limit of 0 counts as 1; the configured value stays in the state
  run limitZeroTest = init.then(doCrash).then(doArrive)
    .expect(s.brFails == [] and s.brOpenUntil == 600 and s.brLimit == 0)
    .then(doArrive).expect(s.breakerSkips == 1)
}

module test_container {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 0, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-083: window 0 = no window: a container caps the restarts for its
  // lifetime, old restarts still count
  run containerCapTest = init
    .then(doCrash).then(doRestart).then(doCrash).then(doRestart).then(doCrash).then(doRestart)
    .expect(s.up and s.window == 0 and s.restartTimes == [0, 0, 0])
    .then(tickBy(400)).then(tickBy(400)).then(tickBy(400)).then(doCrash).then(doRestart)
    .expect(s.stopped and not(s.up) and s.restartTimes == [0, 0, 0])
  // GPU-083: restarts at different times all count
  run containerSpreadTest = init
    .then(doCrash).then(doRestart).then(tickBy(9999)).then(doCrash).then(doRestart)
    .then(tickBy(9999)).then(doCrash).then(doRestart)
    .expect(s.up and s.restartTimes == [0, 9999, 19998])
    .then(tickBy(9999)).then(doCrash).then(doRestart).expect(s.stopped and not(s.up))
}

module test_container1 {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 1, WINDOW = 0, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-083: limit 1, no window: after one restart a later exit stays stopped
  // however far the clock advances
  run containerLimitOneTest = init.then(doCrash).then(doRestart).expect(s.up and s.cold)
    .then(tickBy(9999)).then(tickBy(9999)).then(tickBy(9999)).then(doCrash).then(doRestart)
    .expect(s.stopped and not(s.up) and s.restartTimes == [0] and s.clock == 29997)
    .then(tickBy(9999)).then(doArrive).expect(s.clientCpu == 1 and s.phase == IDLE)
}

// ---- refusals ----
// A terminal `.fail()` checks that the action is blocked in the state before
// it. Quint 0.32.0 exports an empty last frame for such a run, which the replay
// script does not accept, so these modules are run with `quint test` only and
// are not in the replayed TESTS list of scripts/quint_check.sh. The guards they
// check are the model's reading: the specification states no precondition of
// any event.
module refuse_default {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-045: admission needs an accepted request
  run admitNeedsRequestTest = init.then(doArrive).then(admitWith(20, 20))
    .then(admitWith(20, 20).fail())
  // GPU-039, GPU-034: no reply before the end of the proof and the wipe
  run replyNeedsWipeTest = init.then(doArrive).then(admitWith(20, 20)).then(doReply.fail())
  // GPU-034: no wipe before the end of the proof
  run wipeNeedsProofTest = init.then(doArrive).then(admitWith(20, 20)).then(wipeWith(1).fail())
  // GPU-048: the supervisor acts only on a daemon that is down
  run restartNeedsDownTest = init.then(doArrive).then(doRestart.fail())
  // GPU-049: a stopped daemon is not restarted
  run stoppedStaysTest = init
    .then(doCrash).then(doRestart).then(doCrash).then(doRestart).then(doCrash).then(doRestart)
    .then(doCrash).then(doRestart).then(doRestart.fail())
  // GPU-028: at step cpu no device operation runs, so none declines
  run cpuStepNoDeclineTest = init.then(doArrive).then(admitWith(1, 1)).then(declineWith(4).fail())
  // GPU-037: after a lost lease no device operation runs
  run leaseLostNoReadbackTest = init.then(doArrive).then(admitWith(20, 20)).then(doLeaseLoss)
    .then(readbackOf(0).fail())
  run leaseLostNoCounterReadbackTest = init.then(doArrive).then(admitWith(20, 20)).then(doLeaseLoss)
    .then(readbackOf(2).fail())
  // GPU-038: a read-back of an extended-domain vector (kind 4) is refused
  run readbackKind4RefusedTest = init.then(doArrive).then(admitWith(20, 20))
    .then(readbackOf(4).fail())
  // GPU-036: a read-back of the contents of a zeroed region (kind 5) is refused
  run readbackKind5RefusedTest = init.then(doArrive).then(admitWith(20, 20))
    .then(readbackOf(5).fail())
  run readbackKind6RefusedTest = init.then(doArrive).then(admitWith(20, 20))
    .then(readbackOf(6).fail())
  run readbackNegativeRefusedTest = init.then(doArrive).then(admitWith(20, 20))
    .then(readbackOf(-1).fail())
  // GPU-038: while the request is proved only the counters can be read
  run provedNoQuotientReadbackTest = init.then(doArrive).then(admitWith(20, 20))
    .then(finishWith(1)).then(readbackOf(0).fail())
  run provedNoMsmReadbackTest = init.then(doArrive).then(admitWith(20, 20))
    .then(finishWith(1)).then(readbackOf(1).fail())
  run provedNoTransformReadbackTest = init.then(doArrive).then(admitWith(20, 20))
    .then(finishWith(1)).then(readbackOf(3).fail())
  run provedKind4RefusedTest = init.then(doArrive).then(admitWith(20, 20))
    .then(finishWith(1)).then(readbackOf(4).fail())
  // GPU-038: no read-back after the wipe or before admission
  run wipedNoReadbackTest = init.then(doArrive).then(admitWith(20, 20))
    .then(finishWith(1)).then(wipeWith(1)).then(readbackOf(2).fail())
  run acceptedNoReadbackTest = init.then(doArrive).then(readbackOf(2).fail())
  // GPU-073: there are seven decline reasons
  run declineReason7RefusedTest = init.then(doArrive).then(admitWith(20, 20))
    .then(declineWith(7).fail())
  run declineNegativeRefusedTest = init.then(doArrive).then(admitWith(20, 20))
    .then(declineWith(-1).fail())
  // the arguments of the other events: 0 or 1 only, a time step of at least 1,
  // readings that the op code can carry
  run finishArgRefusedTest = init.then(doArrive).then(admitWith(20, 20)).then(finishWith(2).fail())
  run finishNegativeRefusedTest = init.then(doArrive).then(admitWith(20, 20))
    .then(finishWith(-1).fail())
  run wipeArgRefusedTest = init.then(doArrive).then(admitWith(20, 20)).then(finishWith(1))
    .then(wipeWith(2).fail())
  run lockArgRefusedTest = init.then(doArrive).then(lockTo(2).fail())
  run tickZeroRefusedTest = init.then(doArrive).then(tickBy(0).fail())
  run admitReadingRefusedTest = init.then(doArrive).then(admitWith(100, 0).fail())
  run admitNegativeRefusedTest = init.then(doArrive).then(admitWith(-1, 0).fail())
}

module refuse_nodevice {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = false, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-020: without a device no hooked operation runs on it, so none declines
  run noDeviceNoDeclineTest = init.then(doArrive).then(admitWith(20, 20))
    .then(declineWith(0).fail())
}

module refuse_accept {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).* from "./gpu_service"

  // GPU-078: the acceptance short-cut has no proving phase
  run acceptNoProofTest = init.then(doArrive).then(admitWith(3, 2)).then(finishWith(1).fail())
  // GPU-078: nor a second wipe
  run acceptNoWipeTest = init.then(doArrive).then(admitWith(3, 2)).then(wipeWith(1).fail())
}
