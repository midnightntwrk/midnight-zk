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

// GPU prover service: the request life cycle of the resident prover daemon, its
// supervisor and its client (with the client circuit breaker). Written from
// gpu-spec/requirements.json, gpu-spec/design.md and gpu-spec/vectors/README.md
// only, without reading the Lean oracle. Each invariant and each action names
// the requirement IDs it states.
//
// Memory is in abstract units (one unit = one GiB in the examples). The op
// that a step takes is in `lastOp` as code + 100 * a + 10000 * b; the replay
// script sends it to the oracle's --step mode (see gpu-spec/vectors/README.md).
// `s` is the record that the replay compares field by field. `prev` is a ghost
// copy of the state before the last step; it is not part of the wire contract
// and exists so that event-driven requirements can be stated as invariants and
// witnesses over one transition.
//
// Not modelled (stated elsewhere): the operation class of a decline (GPU-073
// counts a class and a reason; the wire contract has the seven reasons only),
// the length of the admission wait (GPU-026: the model takes the reading after
// the wait as input `b`), the refusals at the input boundary (GPU-042, GPU-044,
// GPU-047) and the refused read-back kinds (see `readback`).
module gpu_service {
  // ---- configuration (fixed per instance) ----
  const PER_PROOF: int     // device need of the per-proof buffers with the numerator
  const RESIDENT: int      // size of the resident proving-key copies
  const REDUCED: int       // need of MSM, NTT and coset only (no numerator, no copies)
  const BUDGET: int        // WSL2: card total minus the reserve (GPU-058)
  const KEEP: bool         // resident policy keep (else evict, the default, GPU-081)
  const WSL: bool
  const DEVICE: bool       // a CUDA device is present and enabled at start (GPU-020)
  const LIMIT: int         // restart limit (GPU-048, GPU-083), default 3
  const WINDOW: int        // restart window in seconds (GPU-048), default 600
  const BENCH: bool        // bench run mode (GPU-024)
  const ACCEPTANCE: bool   // run mode acceptance (GPU-078); else production (GPU-023)
  const BR_LIMIT: int      // client breaker: failures that open it (GPU-075), default 3; 0 counts as 1
  const BR_WINDOW: int     // client breaker: window in seconds (GPU-075), default 600
  const BR_COOLDOWN: int   // client breaker: cooldown in seconds (GPU-075), default 600
  // model-only constants (not in the state record)
  const CHAOS: bool        // crashes, bound breaches and evict requests occur
  const TICKS: bool        // time passes
  const TICK_MAX: int      // largest time step of the random walk, in seconds

  // Admission steps.
  pure val NONE = 0
  pure val GPU = 1
  pure val WAIT = 2
  pure val EVICT = 3
  pure val CPU = 4

  // Request phases of the daemon.
  pure val IDLE = 0
  pure val ACCEPTED = 1
  pure val PROVING = 2
  pure val PROVED = 3
  pure val WIPED = 4

  // The largest permitted read-back kind (GPU-038).
  pure val MAX_KIND = 3

  // Op codes.
  pure val OP_ARRIVE = 1
  pure val OP_ADMIT = 2
  pure val OP_DECLINE = 3
  pure val OP_READBACK = 4
  pure val OP_LEASE_LOSS = 5
  pure val OP_FINISH = 6
  pure val OP_WIPE = 7
  pure val OP_REPLY = 8
  pure val OP_CRASH = 9
  pure val OP_RESTART = 10
  pure val OP_TICK = 11
  pure val OP_LOCK = 12
  pure val OP_EVICT = 13
  pure val OP_OVERBOUND = 14

  type Svc = {
    // configuration copied into the state so that the oracle sees it
    perProof: int, resident: int, reduced: int, budget: int, keep: bool, wsl: bool,
    device: bool, limit: int, window: int, bench: bool, acceptance: bool,
    brLimit: int, brWindow: int, brCooldown: int,
    // daemon
    up: bool, stopped: bool, phase: int, waiting: int,
    onDev: bool,        // resident proving-key copies on the device
    tables: bool,       // MSM tables (the MSM device contexts) on the device
    dirty: bool,        // witness-dependent buffers not yet zeroed and freed
    ctx: bool,          // CUDA context exists
    devUsed: bool,      // a device operation ran since this process started
    devWork: bool,      // the current request may run a device phase
    step: int, admNeed: int, admFree: int,
    fallbacks: int, degraded: bool, leaseLost: bool, overBound: bool,
    verifyOk: bool, wipeOk: bool,
    lockHeld: bool,     // the caller holds the device lock (environment)
    cold: bool,         // the next served request is labelled cold
    clock: int, restartTimes: List[int],
    // client breaker (GPU-075 to GPU-077)
    brFails: List[int], // times of the recorded daemon failures, oldest first
    brOpenUntil: int,   // the breaker is open while clock < brOpenUntil
    // counters
    requests: int, served: int, clientCpu: int, errors: int, busyReplies: int,
    degradedServed: int, readbacks: int, badReadbacks: int, unverifiedReturned: int,
    verifyAccepts: int,
    declines: List[int], // one count per decline reason, in the order of op 3
    declined: int, breakerSkips: int, degradedRefused: int,
    runFailed: bool,
  }

  var s: Svc
  var lastOp: int
  var prev: Svc          // ghost: the state before the last step

  pure def code(c: int, a: int, b: int): int = c + 100 * a + 10000 * b

  pure val initial: Svc = {
    perProof: PER_PROOF, resident: RESIDENT, reduced: REDUCED, budget: BUDGET, keep: KEEP,
    wsl: WSL, device: DEVICE, limit: LIMIT, window: WINDOW, bench: BENCH,
    acceptance: ACCEPTANCE, brLimit: BR_LIMIT, brWindow: BR_WINDOW, brCooldown: BR_COOLDOWN,
    up: true, stopped: false, phase: IDLE, waiting: 0,
    onDev: false, tables: false, dirty: false, ctx: false, devUsed: false, devWork: false,
    step: NONE, admNeed: 0, admFree: 0, fallbacks: 0, degraded: false, leaseLost: false,
    overBound: false, verifyOk: false, wipeOk: false, lockHeld: false, cold: true,
    clock: 0, restartTimes: [],
    brFails: [], brOpenUntil: 0,
    requests: 0, served: 0, clientCpu: 0, errors: 0, busyReplies: 0, degradedServed: 0,
    readbacks: 0, badReadbacks: 0, unverifiedReturned: 0, verifyAccepts: 0,
    declines: [0, 0, 0, 0, 0, 0, 0], declined: 0, breakerSkips: 0, degradedRefused: 0,
    runFailed: false,
  }

  // GPU-059: a WSL2 daemon refuses to start with the keep policy, so no such
  // instance starts. design.md section 5: the configuration refuses
  // reduced > perProof.
  pure val startable: bool = not(WSL and KEEP) and REDUCED <= PER_PROOF

  action init = all { startable, s' = initial, lastOp' = 0, prev' = initial }

  // every step: the new state, the op for the replayer, the ghost copy
  action go(n: Svc, op: int): bool = all { s' = n, lastOp' = op, prev' = s }

  // ---- client breaker: GPU-075, GPU-077 ----
  // a brLimit of 0 counts as 1 (design.md); the state field keeps the configured value
  pure def brEffLimit(x: Svc): int = if (x.brLimit < 1) 1 else x.brLimit
  // GPU-075: the breaker is open while clock < brOpenUntil
  pure def brOpen(x: Svc): bool = x.clock < x.brOpenUntil
  // One daemon failure at the time x.clock: drop every record t with
  // now - t >= brWindow, append now; at brLimit records clear the record and
  // open the breaker until now + brCooldown (GPU-075).
  pure def recordFailure(x: Svc): Svc = {
    val kept = x.brFails.select(t => x.clock - t < x.brWindow).append(x.clock)
    if (kept.length() >= brEffLimit(x))                                      // GPU-075: the limit is reached, open
      { ...x, brFails: [], brOpenUntil: x.clock + x.brCooldown }
    else { ...x, brFails: kept }                                             // GPU-077: one more failure on record
  }
  // n failures of one event, one after the other at the same clock value (n <= 2)
  pure def recordFailures(x: Svc, n: int): Svc =
    if (n <= 0) x else if (n == 1) recordFailure(x) else recordFailure(recordFailure(x))

  // ---- arrival: GPU-021, GPU-022, GPU-045, GPU-046, GPU-075, GPU-077 ----
  pure def arrive(x: Svc): Svc = {
    val y = { ...x, requests: x.requests + 1 }
    if (brOpen(x))                                                           // GPU-075: no contact
      { ...y, clientCpu: y.clientCpu + 1, breakerSkips: y.breakerSkips + 1 }
    else if (x.stopped or not(x.up))                                         // GPU-021, GPU-022, GPU-077
      recordFailure({ ...y, clientCpu: y.clientCpu + 1 })
    else if (x.phase == IDLE) { ...y, phase: ACCEPTED }                      // GPU-045
    else if (x.waiting == 0) { ...y, waiting: 1 }                            // GPU-045
    else {                                                                   // GPU-046, GPU-077: busy, no failure
      ...y, busyReplies: y.busyReplies + 1, clientCpu: y.clientCpu + 1 }
  }

  // ---- admission: GPU-020, GPU-025 to GPU-029, GPU-057, GPU-058, GPU-078 ----
  // full need: per-proof buffers, plus the resident copies when they are not
  // on the device yet (counted once, GPU-025)
  pure def fullNeed(x: Svc): int = x.perProof + (if (x.onDev) 0 else x.resident)

  pure def admitDevice(x: Svc, st: int, need: int, free: int): Svc = {
    ...x, phase: PROVING, step: st, admNeed: need, admFree: free,
    devWork: true, devUsed: true, ctx: true, dirty: true, tables: true,      // GPU-031: context at first device work
    onDev: st == GPU or st == WAIT,                                          // GPU-027: evict holds no copies
    degraded: st == EVICT,                                                   // GPU-023
  }

  pure def admitCpu(x: Svc, st: int, free: int): Svc = {
    ...x, phase: PROVING, step: st, admNeed: 0, admFree: free, devWork: false,
    onDev: false, tables: false,                                             // GPU-028
    degraded: st == CPU,                                                     // GPU-023
  }

  // The ladder of design.md section 5 (production reading).
  // a = free memory at the decision, b = free memory after the wait
  pure def ladder(x: Svc, a: int, b: int): Svc =
    if (not(x.device)) admitCpu(x, NONE, 0)                                  // GPU-020
    else if (x.wsl and not(x.lockHeld)) admitCpu(x, CPU, 0)                  // GPU-057
    else {
      val f0 = if (x.wsl) x.budget else a                                    // GPU-058
      val f1 = if (x.wsl) x.budget else b                                    // GPU-058: no wait on WSL2
      val need = fullNeed(x)
      val freed = f1 + (if (x.onDev) x.resident else 0)
      if (f0 >= need) admitDevice(x, GPU, need, f0)                          // GPU-029
      else if (not(x.wsl) and f1 >= need) admitDevice(x, WAIT, need, f1)     // GPU-026
      else if (freed >= x.reduced)
        admitDevice({ ...x, onDev: false }, EVICT, x.reduced, freed)         // GPU-027
      else admitCpu(x, CPU, freed)                                           // GPU-028
    }

  pure def admit(x: Svc, a: int, b: int): Svc = {
    val y = ladder(x, a, b)
    if (x.acceptance and (y.step == EVICT or y.step == CPU)) {
      // GPU-078: acceptance mode, step evict or cpu: the frees of the step
      // (evict: the key copies; cpu: also the MSM tables), degraded, no phase
      // starts (no device work, nothing dirty, no context made), and the
      // request is `wiped` with a confirmed (empty) wipe.
      ...x, phase: WIPED, step: y.step, admNeed: y.admNeed, admFree: y.admFree,
      onDev: false, tables: if (y.step == CPU) false else x.tables,
      devWork: false, degraded: true, wipeOk: true }
    else y                                                                   // GPU-023 (production), or not degraded
  }

  // ---- proving ----
  // GPU-073: every decline adds one to the count of its reason and to the total.
  // Reasons 0 (no-device) and 1 (below-min-k) are by design.
  pure def expectedDecline(r: int): bool = r <= 1
  pure def decline(x: Svc, r: int): Svc = {
    val y = { ...x, declines: x.declines.replaceAt(r, x.declines[r] + 1),
              declined: x.declined + 1 }
    if (expectedDecline(r)) y                                                // GPU-085: no fallback, unmarked
    else { ...y, fallbacks: x.fallbacks + 1, degraded: true }                // GPU-012: one fallback, degraded
  }

  // GPU-038, GPU-036: kinds 0 (quotient coefficients), 1 (MSM result points and
  // the partial bucket sums of the vendored MSM), 2 (counters), 3 (base-domain
  // transform output) are counted. Kinds 4 (a vector on the extended domain),
  // 5 (the contents of a zeroed region) and above are refused: a refused op is
  // not a model step, so `doReadback` picks kinds 0..3 only. The transition
  // adds one to badReadbacks for a kind above 3, so a model that lacks the
  // refusal breaks inv_readback.
  pure def readback(x: Svc, k: int): Svc =
    // every copy is a read-back; one of a kind above 3 is also a bad one
    // (design.md section 7 after the ruling on ambiguity A17)
    if (k > 3) { ...x, readbacks: x.readbacks + 1, badReadbacks: x.badReadbacks + 1 }
    else { ...x, readbacks: x.readbacks + 1 }

  // GPU-037, GPU-061: no device work after the lease is lost; one fallback
  pure def leaseLoss(x: Svc): Svc = {
    ...x, devWork: false, leaseLost: true, lockHeld: false,
    fallbacks: x.fallbacks + 1, degraded: true }

  // GPU-039: the answer the verifier would give is stored (a = 1 accepts); it is
  // not counted here but at the reply, on the path that reaches the verifier.
  // The device phases end with the proof.
  pure def finish(x: Svc, ok: bool): Svc = { ...x, phase: PROVED, verifyOk: ok, devWork: false }

  // GPU-034, GPU-082, GPU-030, GPU-060: zero and free before the reply; a = 1
  // confirms. A confirmed wipe leaves nothing dirty and no MSM context under
  // either policy; the key copies stay only under keep off WSL2.
  pure def wipe(x: Svc, ok: bool): Svc =
    if (ok) {
      ...x, phase: WIPED, wipeOk: true, dirty: false, devWork: false,
      onDev: x.onDev and x.keep and not(x.wsl),
      tables: false }
    else { ...x, phase: WIPED, wipeOk: false, devWork: false }               // GPU-035 at the reply

  // the daemon process ends: the driver releases its device memory
  pure def processGone(x: Svc): Svc = {
    ...x, up: false, phase: IDLE, waiting: 0, onDev: false, tables: false, dirty: false,
    ctx: false, devUsed: false, devWork: false, step: NONE, admNeed: 0, admFree: 0,
    fallbacks: 0, degraded: false, leaseLost: false, overBound: false,
    verifyOk: false, wipeOk: false }

  pure def clearRequest(x: Svc): Svc = {
    ...x, step: NONE, admNeed: 0, admFree: 0, fallbacks: 0, degraded: false,
    leaseLost: false, overBound: false, verifyOk: false, wipeOk: false, devWork: false }

  // After a reply without exit (y = the state after the reply, request cleared).
  pure def afterReply(over: bool, y: Svc): Svc =
    if (over)                                                                // GPU-050, GPU-077: planned restart;
      recordFailures({ ...processGone(y), clientCpu: y.clientCpu + y.waiting }, y.waiting)  // a waiting caller fails over
    else if (y.waiting == 1) { ...y, waiting: 0, phase: ACCEPTED }           // GPU-045
    else { ...y, phase: IDLE }                                               // GPU-045: nothing waits

  pure def reply(x: Svc): Svc = {
    val deg = x.degraded or x.fallbacks > 0
    if (not(x.wipeOk)) {                                                     // GPU-035, GPU-077: error, exit;
      val y = processGone(x)                                                 // caller and waiting caller fail over
      recordFailures({ ...y, errors: x.errors + 1, clientCpu: x.clientCpu + 1 + x.waiting },
                     1 + x.waiting)
    } else if (x.acceptance and deg) {                                       // GPU-078, GPU-021, GPU-077: degraded
      afterReply(x.overBound,                                                // error, no proof, no failure
        { ...clearRequest(x), errors: x.errors + 1, clientCpu: x.clientCpu + 1,
          degradedRefused: x.degradedRefused + 1 })
    } else if (not(x.verifyOk)) {                                            // GPU-040, GPU-021, GPU-077: error,
      afterReply(x.overBound,                                                // no proof, one failure
        recordFailure({ ...clearRequest(x), errors: x.errors + 1, clientCpu: x.clientCpu + 1 }))
    } else {                                                                 // GPU-039, GPU-023, GPU-076: served
      afterReply(x.overBound,
        { ...clearRequest(x), served: x.served + 1, cold: false,
          verifyAccepts: x.verifyAccepts + (if (x.verifyOk) 1 else 0),       // GPU-039: the accept is counted here
          unverifiedReturned: x.unverifiedReturned + (if (x.verifyOk) 0 else 1),  // GPU-039
          degradedServed: x.degradedServed + (if (deg) 1 else 0),            // GPU-023
          runFailed: x.runFailed or (x.bench and deg),                       // GPU-024
          brFails: [] })                                                     // GPU-076
    }
  }

  // GPU-021, GPU-077: the caller in flight and the waiting caller prove on
  // their CPU and each records a daemon failure
  pure def crash(x: Svc): Svc = {
    val n = (if (x.phase != IDLE) 1 else 0) + x.waiting
    recordFailures({ ...processGone(x), clientCpu: x.clientCpu + n }, n)
  }

  // GPU-048, GPU-049, GPU-083: restarts in the window are below the limit, else stop
  pure def recent(x: Svc): List[int] =
    if (x.window == 0) x.restartTimes                                        // GPU-083: no window, all count
    else x.restartTimes.select(t => t > x.clock - x.window)                  // GPU-048: sliding window
  pure def restart(x: Svc): Svc = {
    val r = recent(x)
    if (r.length() < x.limit)                                                // GPU-048, GPU-050: restart, cold
      { ...x, up: true, restartTimes: r.append(x.clock), cold: true }
    else { ...x, stopped: true, restartTimes: r }                            // GPU-049: left stopped
  }

  // time passes; it moves the restart window (GPU-048) and the breaker window
  // and cooldown (GPU-075)
  pure def tick(x: Svc, dt: int): Svc = { ...x, clock: x.clock + dt }

  // ---- actions ----
  // GPU-021, GPU-022, GPU-045, GPU-046, GPU-075, GPU-077
  action doArrive = go(arrive(s), code(OP_ARRIVE, 0, 0))

  // GPU-020, GPU-025 to GPU-029, GPU-057, GPU-058, GPU-078
  action admitWith(a: int, b: int): bool =
    all { s.up, s.phase == ACCEPTED, 0 <= a, a <= 99, 0 <= b,              // a readable op code
          go(admit(s, a, b), code(OP_ADMIT, a, b)) }
  action doAdmit = {
    nondet a = 0.to(20).oneOf()
    nondet b = 0.to(20).oneOf()
    admitWith(a, b)
  }

  // GPU-012, GPU-085, GPU-073: reason 0 no-device, 1 below-min-k (counted
  // only), 2 shape, 3 unreduced, 4 memory, 5 fault, 6 device-error (counted,
  // one fallback, degraded)
  action declineWith(r: int): bool =
    all { s.up, s.phase == PROVING, s.devWork, 0 <= r, r <= 6,
          go(decline(s, r), code(OP_DECLINE, r, 0)) }
  action doDecline = {
    nondet r = 0.to(6).oneOf()
    declineWith(r)
  }

  // GPU-038, GPU-036: only the permitted kinds 0..MAX_KIND are steps; a kind
  // above it is refused. Kinds 0, 1 and 3 need a proving request with device
  // work; counters (kind 2) can also be read while the request is proved (the
  // zero-check count, GPU-036).
  pure def readbackEnabled(x: Svc, k: int): bool = and {
    x.up, 0 <= k, k <= MAX_KIND,
    or { x.phase == PROVING and x.devWork, k == 2 and x.phase == PROVED } }
  action readbackOf(k: int): bool =
    all { readbackEnabled(s, k), go(readback(s, k), code(OP_READBACK, k, 0)) }
  action doReadback = {
    nondet k = 0.to(MAX_KIND).oneOf()
    readbackOf(k)
  }

  // GPU-037, GPU-061
  action doLeaseLoss = all {
    s.up, s.phase == PROVING, s.devWork, go(leaseLoss(s), code(OP_LEASE_LOSS, 0, 0)) }

  // GPU-039
  action finishWith(ok: int): bool =
    all { s.up, s.phase == PROVING, 0 <= ok, ok <= 1,
          go(finish(s, ok == 1), code(OP_FINISH, ok, 0)) }
  action doFinish = {
    nondet ok = 0.to(1).oneOf()
    finishWith(ok)
  }

  // GPU-034, GPU-082, GPU-030, GPU-060
  action wipeWith(ok: int): bool =
    all { s.up, s.phase == PROVED, 0 <= ok, ok <= 1,
          go(wipe(s, ok == 1), code(OP_WIPE, ok, 0)) }
  action doWipe = {
    nondet ok = 0.to(1).oneOf()
    wipeWith(ok)
  }

  // GPU-035, GPU-078, GPU-040, GPU-023, GPU-024, GPU-076, GPU-050, GPU-077
  action doReply = all {
    s.up, s.phase == WIPED, go(reply(s), code(OP_REPLY, 0, 0)) }

  // GPU-021, GPU-077
  action doCrash = all { s.up, go(crash(s), code(OP_CRASH, 0, 0)) }

  // GPU-048, GPU-049, GPU-083
  action doRestart = all {
    not(s.up), not(s.stopped), go(restart(s), code(OP_RESTART, 0, 0)) }

  // GPU-048, GPU-075: time passes: dt = a + 100 * b seconds, at least 1 (code + 100 * dt is the same number)
  action tickBy(dt: int): bool = all { dt >= 1, go(tick(s, dt), code(OP_TICK, dt, 0)) }
  action doTick = {
    nondet dt = 1.to(TICK_MAX).oneOf()
    tickBy(dt)
  }

  // GPU-057, GPU-061: the caller takes or gives back the device lock outside the proving phase
  action lockTo(h: int): bool =
    all { s.phase != PROVING, 0 <= h, h <= 1,
          go({ ...s, lockHeld: h == 1 }, code(OP_LOCK, h, 0)) }
  action doLock = {
    nondet h = 0.to(1).oneOf()
    lockTo(h)
  }

  // explicit evict request on an idle daemon: frees the key copies and the MSM
  // contexts (GPU-030, GPU-082)
  action doEvict = all {
    s.up, s.phase == IDLE, go({ ...s, onDev: false, tables: false }, code(OP_EVICT, 0, 0)) }

  // GPU-050: a bound is exceeded during the request
  action doOverBound = all {
    s.up, s.phase == PROVING or s.phase == PROVED, go({ ...s, overBound: true },
    code(OP_OVERBOUND, 0, 0)) }

  // Without CHAOS the walk spends its steps on whole requests (the reply path).
  action step = any {
    doArrive, doAdmit, doDecline, doReadback, doLeaseLoss, doFinish, doWipe, doReply,
    doRestart, doLock,
    all { TICKS, doTick },
    all { CHAOS, any { doCrash, doEvict, doOverBound } },
  }

  // ---- invariants ----
  pure def sum(l: List[int]): int = l.foldl(0, (acc, v) => acc + v)
  val op = lastOp % 100
  val brSame = s.brFails == prev.brFails and s.brOpenUntil == prev.brOpenUntil
  val servedNow = s.served > prev.served
  // the reply took the over-bound exit with a waiting caller (one failure recorded)
  val waitingFailedOver = prev.overBound and prev.waiting == 1

  // GPU-045: one request served, at most one waiting
  val inv_queue = s.waiting >= 0 and s.waiting <= 1 and (s.waiting == 1 implies s.phase != IDLE)
  // GPU-046: a busy answer only when one request is served and one waits; the
  // daemon reads nothing (its state is unchanged)
  val inv_busy = s.busyReplies > prev.busyReplies implies and {
    op == OP_ARRIVE, prev.up, prev.phase != IDLE, prev.waiting == 1,
    s == { ...prev, requests: prev.requests + 1, clientCpu: prev.clientCpu + 1,
           busyReplies: prev.busyReplies + 1 } }
  // GPU-034: a request is taken only after the previous one was zeroed and freed
  val inv_wipe = (s.up and (s.phase == IDLE or s.phase == ACCEPTED)) implies not(s.dirty)
  // GPU-029: a device step never needs more than was free at the decision
  val inv_admit = (s.step == GPU or s.step == WAIT or s.step == EVICT) implies s.admNeed <= s.admFree
  // GPU-025: the need counts the resident copies at most once
  val inv_need = s.admNeed <= s.perProof + s.resident
  // GPU-027: the evict step keeps no resident copies and runs the numerator on the CPU
  val inv_evict_step = s.step == EVICT implies (not(s.onDev) and s.admNeed == s.reduced)
  // GPU-028: the cpu step holds no MSM tables and runs no device phase
  val inv_cpu_step = s.step == CPU implies (not(s.tables) and not(s.devWork) and not(s.onDev))
  // GPU-030, GPU-081: evict policy holds no copies and no tables between requests
  val inv_evict_policy = (not(s.keep) and s.phase == IDLE) implies (not(s.onDev) and not(s.tables))
  // GPU-082: no MSM device context outlives its request, under either policy
  val inv_tables = (s.phase == IDLE or s.phase == ACCEPTED or (s.phase == WIPED and s.wipeOk))
    implies not(s.tables)
  // GPU-057, GPU-061, GPU-037: on WSL2 device work needs the lock; after a lost lease none
  val inv_lease = (s.wsl and s.devWork implies s.lockHeld) and (s.leaseLost implies not(s.devWork))
  // GPU-060: on WSL2 nothing stays on the device between requests
  val inv_wsl_idle = (s.wsl and s.phase == IDLE) implies (not(s.onDev) and not(s.tables))
  // GPU-059 (a check of the configuration: no action writes these fields)
  val inv_wsl_keep = not(s.wsl and s.keep)
  // GPU-020, GPU-031: no device, no context; a context only after a device operation
  val inv_ctx = (not(s.device) implies (not(s.ctx) and not(s.devWork) and not(s.devUsed)))
    and (s.ctx implies s.devUsed)
  // GPU-048, GPU-049, GPU-083: restarts in the window within the limit; stopped means down
  val inv_restart = recent(s).length() <= s.limit and (s.stopped implies not(s.up))
    and s.restartTimes.indices().forall(i => s.restartTimes[i] <= s.clock)
    // GPU-083: with no window every restart since the start stays on record and counts
    and (s.window == 0 implies s.restartTimes.length() <= s.limit)
    and ((s.window == 0 and op == OP_RESTART and s.up) implies
          (prev.restartTimes.length() < s.limit
           and s.restartTimes.length() == prev.restartTimes.length() + 1))
  // GPU-021, GPU-022: every request is served, falls back to the CPU, or is in flight
  val inv_accounted =
    s.requests == s.served + s.clientCpu + (if (s.phase != IDLE) 1 else 0) + s.waiting
  // GPU-022: while the supervisor has stopped restarting, an arrival goes to the client's CPU
  val inv_stopped = (op == OP_ARRIVE and prev.stopped) implies
    (s.clientCpu == prev.clientCpu + 1 and s.phase == IDLE and s.served == prev.served)
  // GPU-021: every error reply, busy answer and breaker skip is one request on the client's CPU
  val inv_errors = s.errors + s.busyReplies + s.breakerSkips <= s.clientCpu
    and s.degradedRefused <= s.errors
    and (s.errors > prev.errors implies
          (op == OP_REPLY and s.errors == prev.errors + 1 and s.clientCpu > prev.clientCpu
           and not(servedNow)))
  // GPU-039: no proof is served that the verifier did not accept
  // and every accept is counted exactly where it is consumed, at a served reply
  val inv_verified = s.unverifiedReturned == 0 and s.served == s.verifyAccepts
    and (servedNow implies (op == OP_REPLY and prev.verifyOk and s.served == prev.served + 1))
    and (s.verifyAccepts != prev.verifyAccepts implies
          (servedNow and s.verifyAccepts == prev.verifyAccepts + 1))
  // GPU-040: a refused proof is an error and no proof is written
  val inv_refused = (op == OP_REPLY and not(prev.verifyOk)) implies
    (not(servedNow) and s.errors == prev.errors + 1)
  // GPU-035: an unconfirmed wipe ends the daemon with an error reply and serves nothing
  val inv_wipe_error = (op == OP_REPLY and not(prev.wipeOk)) implies
    (not(s.up) and not(servedNow) and s.errors == prev.errors + 1)
  // GPU-038, GPU-036: only permitted read-backs
  val inv_readback = s.badReadbacks == 0
    and (op == OP_READBACK implies and {
      opArg <= 3, s.readbacks == prev.readbacks + 1,
      s == { ...prev, readbacks: prev.readbacks + 1 },
      or { prev.phase == PROVING and prev.devWork, opArg == 2 and prev.phase == PROVED } })
  // GPU-023: only served proofs are marked degraded
  val inv_degraded = s.degradedServed <= s.served and s.degradedServed >= prev.degradedServed
    and ((servedNow and (prev.degraded or prev.fallbacks > 0 or prev.step == EVICT or prev.step == CPU))
          implies s.degradedServed == prev.degradedServed + 1)
  // GPU-024: a bench run fails exactly when a degraded proof was served in it
  val inv_bench = s.runFailed == (s.bench and s.degradedServed > 0)
  // GPU-035: a daemon that is down holds no request state
  val inv_down = not(s.up) implies (s.phase == IDLE and s.waiting == 0 and not(s.dirty)
    and not(s.onDev) and not(s.tables) and not(s.ctx))
  // GPU-050: an over-bound request ends the daemon at its reply
  val inv_overbound = (op == OP_REPLY and prev.overBound) implies not(s.up)
  // GPU-075: the failure record never reaches the limit; no recorded time is in
  // the future; the record is oldest first; a cooldown is never shortened and
  // never longer than brCooldown from now
  val inv_breaker = and {
    s.brFails.length() < brEffLimit(s),
    s.brFails.indices().forall(i => s.brFails[i] <= s.clock),
    s.brFails.indices().forall(i => i == 0 or s.brFails[i - 1] <= s.brFails[i]),
    s.brOpenUntil >= prev.brOpenUntil,
    s.brOpenUntil <= s.clock + s.brCooldown,
    // (the second failure of one event may be recorded after the first one opened the breaker)
    s.brOpenUntil != prev.brOpenUntil implies (s.brOpenUntil == s.clock + s.brCooldown and s.brFails.length() <= 1),
  }
  // GPU-075: an arrival is a breaker skip exactly when the breaker is open, and
  // a skip does not contact the daemon (only the three client counts change)
  val inv_skips = and {
    s.breakerSkips <= s.clientCpu,
    s.breakerSkips >= prev.breakerSkips,
    s.breakerSkips > prev.breakerSkips implies (op == OP_ARRIVE and brOpen(prev)),
    (op == OP_ARRIVE and brOpen(prev)) implies
      s == { ...prev, requests: prev.requests + 1, clientCpu: prev.clientCpu + 1,
             breakerSkips: prev.breakerSkips + 1 },
  }
  // GPU-076: a served proof clears the failure record (a waiting caller that
  // fails over at an over-bound exit records its failure after the clearing)
  val inv_reset = servedNow implies
    (if (waitingFailedOver) s.brFails.length() <= 1 else s.brFails == [])
  // GPU-077: only an absent daemon (arrival at a down or stopped daemon), a
  // lost connection (crash, exit), a prove error, a verify error and a retired
  // reply are failures; a busy answer and a degraded error are not
  val inv_failures = and {
    not(brSame) implies (op == OP_ARRIVE or op == OP_REPLY or op == OP_CRASH),
    (op == OP_ARRIVE and not(brSame)) implies (not(brOpen(prev)) and (prev.stopped or not(prev.up))),
    (op == OP_ARRIVE and not(brOpen(prev)) and (prev.stopped or not(prev.up))) implies
      (s.brFails.length() > 0 and s.brFails[s.brFails.length() - 1] == s.clock) or
      (s.brFails == [] and s.brOpenUntil == s.clock + s.brCooldown),
    (s.degradedRefused > prev.degradedRefused and not(waitingFailedOver)) implies brSame,
    (op == OP_CRASH and prev.phase == IDLE) implies brSame,
  }
  // GPU-073: seven decline counts, none negative, whose sum is the total
  val inv_declines = and {
    s.declines.length() == 7,
    s.declines.indices().forall(i => s.declines[i] >= 0),
    sum(s.declines) == s.declined,
    s.declined - prev.declined == (if (op == OP_DECLINE) 1 else 0),
  }
  // GPU-012, GPU-061: a decline with a reason 2..6 or a lost lease is one fallback
  // and marks the request degraded; a request with a fallback is degraded
  val opArg = (lastOp / 100) % 100
  val inv_fallback = and {
    (op == OP_LEASE_LOSS or (op == OP_DECLINE and not(expectedDecline(opArg)))) implies
      (s.fallbacks == prev.fallbacks + 1 and s.degraded),
    s.fallbacks > 0 implies s.degraded,
    s.fallbacks >= 0,
  }
  // GPU-085: a decline with the reason no-device or below-min-k is counted, is no
  // fallback and leaves the request as it was (only the two decline counts change)
  val inv_expected_decline = (op == OP_DECLINE and expectedDecline(opArg)) implies
    (s.fallbacks == prev.fallbacks and s.degraded == prev.degraded
     and s == { ...prev, declines: s.declines, declined: prev.declined + 1 }
     and s.declines[opArg] == prev.declines[opArg] + 1)
  // GPU-078: in acceptance mode no degraded proof is served, a request at step
  // evict or cpu runs no phase, and a degraded error is given only there
  val inv_acceptance = and {
    s.acceptance implies s.degradedServed == 0,
    (s.acceptance and servedNow) implies not(prev.degraded or prev.fallbacks > 0),
    (s.acceptance and (s.step == EVICT or s.step == CPU)) implies
      (s.phase == WIPED and s.wipeOk and s.degraded and not(s.devWork) and not(s.dirty)),
    s.degradedRefused > 0 implies s.acceptance,
    s.degradedRefused > prev.degradedRefused implies
      (op == OP_REPLY and not(servedNow) and (prev.degraded or prev.fallbacks > 0)),
  }

  val inv = and {
    inv_queue, inv_busy, inv_wipe, inv_admit, inv_need, inv_evict_step, inv_cpu_step,
    inv_evict_policy, inv_tables, inv_lease, inv_wsl_idle, inv_wsl_keep, inv_ctx, inv_restart,
    inv_accounted, inv_stopped, inv_errors, inv_verified, inv_refused, inv_wipe_error,
    inv_readback, inv_degraded, inv_bench, inv_down, inv_overbound, inv_breaker, inv_skips,
    inv_reset, inv_failures, inv_declines, inv_fallback, inv_expected_decline, inv_acceptance,
  }

  // ---- witnesses (written positively; --witnesses counts traces that reach them) ----
  val w_wait = s.step == WAIT
  val w_evict = s.step == EVICT
  val w_cpu = s.step == CPU
  val w_queued = s.waiting == 1
  val w_busy = s.busyReplies > 0
  val w_stopped = s.stopped
  val w_degraded = s.degradedServed > 0
  val w_served = s.served > 0
  val w_lease = s.leaseLost
  val w_error = s.errors > 0
  // the breaker (GPU-075 to GPU-077)
  val w_breaker_open = brOpen(s)
  val w_breaker_skip = s.breakerSkips > 0
  val w_breaker_closed = s.brOpenUntil > 0 and not(brOpen(s))          // a cooldown has passed
  val w_breaker_after = s.brOpenUntil > 0 and not(brOpen(s)) and s.phase == ACCEPTED
    and op == OP_ARRIVE                                                 // the daemon is contacted again
  val w_breaker_reopen = prev.brOpenUntil > 0 and s.brOpenUntil > prev.brOpenUntil
  val w_breaker_reset = servedNow and prev.brFails.length() > 0 and s.brFails == []
  val w_breaker_aged = op == OP_ARRIVE and prev.brFails.length() > 0 and s.brFails.length() > 0
    and s.brFails[0] != prev.brFails[0]                                 // an old failure left the window
  val w_served_open = servedNow and brOpen(prev)                        // a request in flight is served while the breaker is open
  val w_fail_open = not(brSame) and brOpen(prev)                        // a failure is recorded while the breaker is open
  val w_fail_reply = op == OP_REPLY and not(brSame) and not(servedNow)
  val w_fail_crash = op == OP_CRASH and not(brSame)
  val w_fail_two = (op == OP_CRASH or op == OP_REPLY) and
    (s.brFails.length() == prev.brFails.length() + 2)                   // caller and waiting caller
  // acceptance mode (GPU-078)
  val w_accept_refused = s.degradedRefused > 0
  val w_accept_shortcut = s.acceptance and s.phase == WIPED and (s.step == EVICT or s.step == CPU)
  val w_accept_evict = s.acceptance and s.phase == WIPED and s.step == EVICT and prev.onDev
  val w_accept_fallback = s.degradedRefused > prev.degradedRefused and prev.fallbacks > 0
  val w_accept_served = s.acceptance and s.served > 0
  // GPU-085: the first request of the run had only expected declines (no other
  // request has ended, so every decline so far is its own) and is served unmarked
  val firstServedAfterExpected = servedNow and s.served == 1 and s.clientCpu == 0
    and s.declined > 0 and s.declined == s.declines[0] + s.declines[1] and s.degradedServed == 0
  val w_expected_served = not(s.acceptance) and firstServedAfterExpected  // production: served unmarked
  val w_accept_expected_served = s.acceptance and firstServedAfterExpected // acceptance: served, not refused
  val w_expected_then_fault = op == OP_DECLINE and not(expectedDecline(opArg))
    and prev.fallbacks == 0 and not(prev.degraded) and prev.declined > 0 and prev.served == 0
    and prev.clientCpu == 0                                              // an unmarked request becomes degraded
  // declines (GPU-073), one witness per reason
  val w_decline0 = s.declines[0] > 0
  val w_decline1 = s.declines[1] > 0
  val w_decline2 = s.declines[2] > 0
  val w_decline3 = s.declines[3] > 0
  val w_decline4 = s.declines[4] > 0
  val w_decline5 = s.declines[5] > 0
  val w_decline6 = s.declines[6] > 0
  // resident policy keep: the tables are freed, the key copies stay (GPU-082, GPU-030)
  val w_keep_tables = op == OP_WIPE and prev.tables and not(s.tables) and s.onDev
  val w_keep_evict = s.step == EVICT and prev.onDev                     // evict step from resident copies
  // antecedents of the implications above
  val w_readback = s.readbacks > 0
  val w_readback_proved = op == OP_READBACK and prev.phase == PROVED    // the zero-check count, read in the wipe
  val w_accept_unserved = op == OP_REPLY and prev.verifyOk and not(servedNow)  // an accept that is never consumed
  val w_refused = op == OP_REPLY and prev.wipeOk and not(prev.verifyOk) and s.errors > prev.errors
  val w_wipe_error = op == OP_REPLY and not(prev.wipeOk)
  val w_overbound = op == OP_REPLY and prev.overBound
  val w_none = s.step == NONE and s.phase == PROVING
  val w_wsl_work = s.wsl and s.devWork
  val w_run_failed = s.runFailed
  val w_restart_aged = op == OP_RESTART and s.up and s.restartTimes.length() <= prev.restartTimes.length()
    and prev.restartTimes.length() > 0
}

// ---- instances (one per interesting configuration) ----
module svc_default {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_keep {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = true,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_bench {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = true,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = true,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_nodevice {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = false, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_wsl {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 16, KEEP = false,
    WSL = true, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_wsl_tight {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 4, KEEP = false,
    WSL = true, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_limit1 {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 1, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_flow {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = false, TICKS = true, TICK_MAX = 400).*
}
module svc_flow_keep {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = true,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = true,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = false, TICKS = true, TICK_MAX = 400).*
}
module svc_flow_wsl {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 16, KEEP = false,
    WSL = true, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = false, TICKS = true, TICK_MAX = 400).*
}
module svc_accept {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_accept_keep {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = true,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_accept_flow {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = true,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = false, TICKS = true, TICK_MAX = 400).*
}
module svc_accept_wsl {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 16, KEEP = false,
    WSL = true, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = true, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_breaker1 {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 1, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_breaker0 {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 0, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_breaker_short {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 5, BR_COOLDOWN = 7,
    CHAOS = true, TICKS = true, TICK_MAX = 3).*
}
module svc_breaker_nocool {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 600, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 2, BR_WINDOW = 600, BR_COOLDOWN = 0,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
// GPU-083: window 0 = no window, restarts count for the lifetime of the container
module svc_container {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 3, WINDOW = 0, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
module svc_container1 {
  import gpu_service(PER_PROOF = 6, RESIDENT = 8, REDUCED = 2, BUDGET = 0, KEEP = false,
    WSL = false, DEVICE = true, LIMIT = 1, WINDOW = 0, BENCH = false,
    ACCEPTANCE = false, BR_LIMIT = 3, BR_WINDOW = 600, BR_COOLDOWN = 600,
    CHAOS = true, TICKS = true, TICK_MAX = 400).*
}
