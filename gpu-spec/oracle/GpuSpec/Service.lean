-- This file is part of MIDNIGHT-ZK.
-- Copyright (C) Midnight Foundation
-- SPDX-License-Identifier: Apache-2.0
-- Licensed under the Apache License, Version 2.0 (the "License");
-- You may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.


/-!
# Request state machine of the GPU prover service

The daemon, its supervisor and its client, as one state and one transition
per operation. Each branch names the requirement IDs it implements. Memory is
in abstract units. Field names match the Quint model's record `s` and the
`--step` wire format (gpu-spec/vectors/README.md).

Operations are numbered `code + 100 * a + 10000 * b`:

| code | operation | a | b |
|---|---|---|---|
| 1 | a request arrives at the client | | |
| 2 | the daemon admits the accepted request | free memory at the decision | free memory after the wait |
| 3 | a hooked operation declines or fails | reason: 0 no-device, 1 below-min-k (counted, no fallback), 2 shape, 3 unreduced, 4 memory, 5 fault, 6 device-error (counted, one fallback, degraded) | |
| 4 | a device-to-host copy | kind: 0 quotient coefficients, 1 MSM result points and the partial bucket sums of the vendored MSM, 2 counters, 3 base-domain transform output; 4 and above are refused | |
| 5 | the lease (connection or device lock) is lost | | |
| 6 | the proof ends; the verifier's answer is stored | 1 accepts | |
| 7 | the request buffers are zeroed and freed | 1 confirmed | |
| 8 | the daemon writes the reply | | |
| 9 | the daemon process dies | | |
| 10 | the supervisor acts on a stopped daemon | | |
| 11 | time passes | seconds `a + 100 * b` (at least 1) | |
| 12 | the caller sets the device lock | 1 held | |
| 13 | an explicit evict request | | |
| 14 | a memory bound is exceeded | | |
-/

namespace GpuSpec.Service

/-- Admission steps. -/
def stepNone : Nat := 0
def stepGpu : Nat := 1
def stepWait : Nat := 2
def stepEvict : Nat := 3
def stepCpu : Nat := 4

/-- Request phases. -/
def idle : Nat := 0
def accepted : Nat := 1
def proving : Nat := 2
def proved : Nat := 3
def wiped : Nat := 4

/-- The number of decline reasons (GPU-073): no-device, below-min-k, shape,
unreduced, memory, fault, device-error. -/
def reasons : Nat := 7

structure St where
  -- configuration
  perProof : Nat
  resident : Nat
  reduced : Nat
  budget : Nat
  keep : Bool
  wsl : Bool
  device : Bool
  limit : Nat
  window : Nat
  bench : Bool
  acceptance : Bool
  brLimit : Nat
  brWindow : Nat
  brCooldown : Nat
  -- daemon
  up : Bool
  stopped : Bool
  phase : Nat
  waiting : Nat
  onDev : Bool
  tables : Bool
  dirty : Bool
  ctx : Bool
  devUsed : Bool
  devWork : Bool
  step : Nat
  admNeed : Nat
  admFree : Nat
  fallbacks : Nat
  degraded : Bool
  leaseLost : Bool
  overBound : Bool
  verifyOk : Bool
  wipeOk : Bool
  lockHeld : Bool
  cold : Bool
  clock : Nat
  restartTimes : List Nat
  -- client breaker
  brFails : List Nat
  brOpenUntil : Nat
  -- counters
  requests : Nat
  served : Nat
  clientCpu : Nat
  errors : Nat
  busyReplies : Nat
  degradedServed : Nat
  readbacks : Nat
  badReadbacks : Nat
  unverifiedReturned : Nat
  verifyAccepts : Nat
  declines : List Nat
  declined : Nat
  breakerSkips : Nat
  degradedRefused : Nat
  runFailed : Bool
  deriving Repr, DecidableEq

structure Config where
  perProof : Nat
  resident : Nat
  reduced : Nat
  budget : Nat
  keep : Bool
  wsl : Bool
  device : Bool
  limit : Nat
  window : Nat
  bench : Bool
  acceptance : Bool
  brLimit : Nat
  brWindow : Nat
  brCooldown : Nat
  deriving Repr, DecidableEq

/-- The configuration when nothing is named. GPU-081: the resident policy is
evict (`keep = false`). GPU-048: 3 restarts in 600 s. GPU-075: 3 failures in
600 s open the breaker for 600 s. Run mode production. The memory sizes are
abstract units (those of the golden traces). -/
def defaultConfig : Config :=
  { perProof := 6, resident := 8, reduced := 2, budget := 0, keep := false, wsl := false,
    device := true, limit := 3, window := 600, bench := false, acceptance := false,
    brLimit := 3, brWindow := 600, brCooldown := 600 }

/-- The start state of a daemon with configuration `c` (GPU-031: no context;
GPU-059 is a refusal of the configuration, see `configRefusals`). The breaker
is closed and every decline count is zero (GPU-073). -/
def init (c : Config) : St :=
  { perProof := c.perProof, resident := c.resident, reduced := c.reduced, budget := c.budget,
    keep := c.keep, wsl := c.wsl, device := c.device, limit := c.limit, window := c.window,
    bench := c.bench, acceptance := c.acceptance, brLimit := c.brLimit, brWindow := c.brWindow,
    brCooldown := c.brCooldown,
    up := true, stopped := false, phase := idle, waiting := 0, onDev := false, tables := false,
    dirty := false, ctx := false, devUsed := false, devWork := false, step := stepNone,
    admNeed := 0, admFree := 0, fallbacks := 0, degraded := false, leaseLost := false,
    overBound := false, verifyOk := false, wipeOk := false, lockHeld := false, cold := true,
    clock := 0, restartTimes := [],
    brFails := [], brOpenUntil := 0,
    requests := 0, served := 0, clientCpu := 0, errors := 0, busyReplies := 0,
    degradedServed := 0, readbacks := 0, badReadbacks := 0, unverifiedReturned := 0,
    verifyAccepts := 0,
    declines := [0, 0, 0, 0, 0, 0, 0], declined := 0, breakerSkips := 0, degradedRefused := 0,
    runFailed := false }

/-! ## Refusals -/

inductive Refusal where
  | wslKeep            -- GPU-059: the daemon refuses to start
  | badConfig          -- the reduced need exceeds the full per-proof need
  | notAnOperation     -- an op code outside the table
  | badArgument        -- an argument outside its range
  | readbackNotPermitted -- GPU-038
  | notEnabled         -- the operation cannot happen in this state
  | outsideStateDomain -- the state fails `stateOk`
  deriving Repr, DecidableEq

def Refusal.code : Refusal → String
  | .wslKeep => "wsl-keep-refused"
  | .badConfig => "bad-config"
  | .notAnOperation => "not-an-operation"
  | .badArgument => "bad-argument"
  | .readbackNotPermitted => "readback-not-permitted"
  | .notEnabled => "not-enabled"
  | .outsideStateDomain => "outside-state-domain"

/-- The reduced mask (MSM, NTT, coset) is part of the full mask, so its need is
at most the per-proof need. -/
def configRefusals (c : Config) : List Refusal :=
  (if c.reduced > c.perProof then [.badConfig] else []) ++
  (if c.wsl && c.keep then [.wslKeep] else [])

/-! ## Transitions -/

def opCode (op : Nat) : Nat := op % 100
def argA (op : Nat) : Nat := (op / 100) % 100
def argB (op : Nat) : Nat := op / 10000

/-! ### The client breaker -/

/-- GPU-075, GPU-077: record one daemon failure at the time `now = clock`.
First drop every record `t` with `now - t ≥ brWindow`, then append `now`. When
the record then holds `brLimit` failures (a `brLimit` of 0 counts as 1), clear
it and open the breaker until `now + brCooldown`. -/
def recordFailure (s : St) : St :=
  let kept := (s.brFails.filter fun t => !decide (s.brWindow ≤ s.clock - t)) ++ [s.clock]
  if max s.brLimit 1 ≤ kept.length then
    { s with brFails := [], brOpenUntil := s.clock + s.brCooldown }
  else { s with brFails := kept }

/-- `k` failures of one event, one after the other at the same clock value. -/
def recordFailures : Nat → St → St
  | 0, s => s
  | k + 1, s => recordFailures k (recordFailure s)

/-- GPU-075: the breaker is open while `clock < brOpenUntil`. -/
def breakerOpen (s : St) : Bool := decide (s.clock < s.brOpenUntil)

/-- A request reaches the client. -/
def arrive (s : St) : St :=
  let s := { s with requests := s.requests + 1 }
  if breakerOpen s then
    -- GPU-075: breaker open: the client proves on its CPU, no daemon contact
    { s with clientCpu := s.clientCpu + 1, breakerSkips := s.breakerSkips + 1 }
  else if s.stopped || !s.up then
    -- GPU-021, GPU-022: daemon absent: CPU; GPU-077: one daemon failure
    recordFailure { s with clientCpu := s.clientCpu + 1 }
  else if s.phase ≠ idle then
    if s.waiting = 0 then { s with waiting := 1 }                      -- GPU-045
    -- GPU-046: busy; the caller proves on its CPU (GPU-021); GPU-077: no failure
    else { s with busyReplies := s.busyReplies + 1, clientCpu := s.clientCpu + 1 }
  else { s with phase := accepted }                                    -- GPU-045

/-- GPU-025: the need of the full mask counts the resident copies once: only
when they are not on the device yet. -/
def fullNeed (s : St) : Nat := s.perProof + if s.onDev then 0 else s.resident

def onDevice (s : St) (st need free : Nat) : St :=
  { s with phase := proving, step := st, admNeed := need, admFree := free,
           devWork := true, devUsed := true, ctx := true, dirty := true, tables := true,
           onDev := (st == stepGpu || st == stepWait),
           degraded := st == stepEvict }

def onCpu (s : St) (st free : Nat) : St :=
  { s with phase := proving, step := st, admNeed := 0, admFree := free, devWork := false,
           onDev := false, tables := false, degraded := st == stepCpu }

/-- GPU-078: in acceptance mode a result of step evict or cpu starts no phase.
The frees of the step apply (the key copies; at step cpu the MSM tables too),
the request is degraded and goes straight to `wiped` with a confirmed (empty)
wipe. The decision (`step`, `admNeed`, `admFree`) is recorded as the ladder
made it. -/
def noPhase (s : St) (st need free : Nat) (tables : Bool) : St :=
  { s with phase := wiped, wipeOk := true, step := st, admNeed := need, admFree := free,
           devWork := false, onDev := false, tables := tables, degraded := true }

/-- Step cpu: every phase on the CPU in production (GPU-028, GPU-057), no phase
in acceptance mode (GPU-078). -/
def cpuStep (s : St) (free : Nat) : St :=
  if s.acceptance then noPhase s stepCpu 0 free false else onCpu s stepCpu free

/-- GPU-020, GPU-025 to GPU-029, GPU-057, GPU-058, GPU-078: the admission ladder. -/
def admit (s : St) (a b : Nat) : St :=
  if !s.device then onCpu s stepNone 0                       -- GPU-020
  else if s.wsl && !s.lockHeld then cpuStep s 0              -- GPU-057 (GPU-078)
  else
    -- GPU-058: on WSL2 the budget replaces both readings and there is no wait
    let free0 := if s.wsl then s.budget else a
    let free1 := if s.wsl then s.budget else b
    let need := fullNeed s
    if need ≤ free0 then onDevice s stepGpu need free0         -- GPU-029
    else if !s.wsl && need ≤ free1 then onDevice s stepWait need free1  -- GPU-026
    else
      -- GPU-027: freeing the resident copies returns their memory
      let freed := free1 + if s.onDev then s.resident else 0
      if s.reduced ≤ freed then
        if s.acceptance then noPhase s stepEvict s.reduced freed s.tables       -- GPU-078
        -- GPU-027: `onDevice` at step evict leaves no key copy on the device
        else onDevice s stepEvict s.reduced freed
      else cpuStep s freed                                     -- GPU-028 (GPU-078)

/-- Add one to entry `r` of the decline counts. -/
def countAt : List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, r + 1 => x :: countAt xs r

/-- GPU-073: a hooked operation declines or fails with reason `r`: the count of
the reason and the total decline count rise by one. GPU-012: with a reason from
2 (shape, unreduced, memory, fault, device-error) the device was asked and the
CPU code ran in its place: one fallback, and the request is degraded (GPU-023).
GPU-085: with reason 0 (no-device) or 1 (below-min-k) the decline is by design:
no fallback, and the request stays unmarked. -/
def fault (s : St) (r : Nat) : St :=
  if 2 ≤ r then
    { s with fallbacks := s.fallbacks + 1, degraded := true,                 -- GPU-012
             declines := countAt s.declines r, declined := s.declined + 1 }  -- GPU-073
  else
    { s with declines := countAt s.declines r, declined := s.declined + 1 }  -- GPU-085, GPU-073

/-- GPU-038, GPU-036: a device-to-host copy of kind `k`. Kinds 0 quotient
coefficients, 1 MSM result points (and the partial bucket sums of the vendored
MSM), 2 counters and 3 base-domain transform output are permitted. The
transition counts a kind above 3 in `badReadbacks`; `opRefusals` refuses such
an op, so the count stays 0 (`invReadback`) only because of the refusal. -/
def readback (s : St) (k : Nat) : St :=
  { s with readbacks := s.readbacks + 1,
           badReadbacks := s.badReadbacks + (if k > 3 then 1 else 0) }

/-- GPU-037, GPU-061: the lease is lost; no device phase runs after it. -/
def leaseLoss (s : St) : St :=
  { s with devWork := false, leaseLost := true, lockHeld := false,
           fallbacks := s.fallbacks + 1, degraded := true }

/-- GPU-039: the proof ends and the device phases end; the wipe is not a device
phase. The answer the verifier would give is stored and not counted: the daemon
runs the wipe before the verifier, and does not run the verifier at all after
an unconfirmed wipe or an acceptance refusal. The answer is consumed, and an
accept counted, at the reply, on the path that reaches the verifier (`serve`). -/
def finish (s : St) (ok : Bool) : St :=
  { s with phase := proved, verifyOk := ok, devWork := false }

/-- GPU-034, GPU-082, GPU-030, GPU-060: zero and free before the reply. The MSM
tables (device contexts) go at the end of every request under either policy
(they hold the bucket sums of the last MSM). With the evict policy, and always
on WSL2, the key copies go too. -/
def wipe (s : St) (ok : Bool) : St :=
  if ok then
    let hold := s.keep && !s.wsl
    { s with phase := wiped, wipeOk := true, dirty := false, devWork := false,
             onDev := s.onDev && hold, tables := false }
  else { s with phase := wiped, wipeOk := false, devWork := false }

/-- The process ends; the driver releases its device memory. -/
def gone (s : St) : St :=
  { s with up := false, phase := idle, waiting := 0, onDev := false, tables := false,
           dirty := false, ctx := false, devUsed := false, devWork := false, step := stepNone,
           admNeed := 0, admFree := 0, fallbacks := 0, degraded := false, leaseLost := false,
           overBound := false, verifyOk := false, wipeOk := false }

def endRequest (s : St) : St :=
  { s with step := stepNone, admNeed := 0, admFree := 0, fallbacks := 0, degraded := false,
           leaseLost := false, overBound := false, verifyOk := false, wipeOk := false,
           devWork := false }

/-- After a reply without exit. `callerFails` is the number of daemon failures
that the reply itself gave its caller (0 or 1); they are recorded first.
An over-bound request: the daemon exits for a planned restart, a waiting
caller proves on its CPU and records a failure (GPU-050, GPU-077). Otherwise
the waiting connection is accepted (GPU-045), or the daemon is idle. -/
def afterReply (s : St) (overBound : Bool) (callerFails : Nat) : St :=
  if overBound then
    recordFailures (callerFails + s.waiting) { (gone s) with clientCpu := s.clientCpu + s.waiting }
  else if s.waiting = 1 then recordFailures callerFails { s with waiting := 0, phase := accepted }
  else recordFailures callerFails { s with phase := idle }

/-- The served branch of the reply, before `afterReply`: the verifier's accept
is consumed and counted here (GPU-039), the request ends, one proof is served
and counted (GPU-023, GPU-024), and the failure record is cleared (GPU-076). -/
def serve (s : St) : St :=
  let deg := s.degraded || decide (0 < s.fallbacks)                   -- GPU-023
  { (endRequest s) with
    served := s.served + 1, cold := false,
    degradedServed := s.degradedServed + (if deg then 1 else 0),
    runFailed := s.runFailed || (s.bench && deg),                     -- GPU-024
    -- GPU-039: a proof served without a verifier accept is counted; `reply`
    -- serves only after an accept, which keeps this at 0 (`invVerified`)
    unverifiedReturned := s.unverifiedReturned + (if s.verifyOk then 0 else 1),
    -- GPU-039: the accept is counted where it is consumed: with the served proof
    verifyAccepts := s.verifyAccepts + (if s.verifyOk then 1 else 0),
    brFails := [] }                                                   -- GPU-076

/-- The reply, in the order of the design. -/
def reply (s : St) : St :=
  if !s.wipeOk then
    -- GPU-035: error reply, then exit before another request; the caller and a
    -- waiting caller prove on their CPU (GPU-021) and each records a failure (GPU-077)
    recordFailures (1 + s.waiting)
      { (gone s) with errors := s.errors + 1, clientCpu := s.clientCpu + 1 + s.waiting }
  else if s.acceptance && (s.degraded || decide (0 < s.fallbacks)) then
    -- GPU-078: degraded error, no proof; the caller proves on its CPU (GPU-021);
    -- GPU-077: not a daemon failure. The verifier's answer is not used.
    afterReply { (endRequest s) with errors := s.errors + 1, clientCpu := s.clientCpu + 1,
                                     degradedRefused := s.degradedRefused + 1 } s.overBound 0
  else if !s.verifyOk then
    -- GPU-040: error, no proof; the caller proves on its CPU (GPU-021) and
    -- records a failure (GPU-077)
    afterReply { (endRequest s) with errors := s.errors + 1, clientCpu := s.clientCpu + 1 }
      s.overBound 1
  else afterReply (serve s) s.overBound 0

/-- The process dies. GPU-021, GPU-077: the caller in flight and the waiting
caller prove on their CPU, and each records a daemon failure. -/
def crash (s : St) : St :=
  let callers := (if s.phase = idle then 0 else 1) + s.waiting
  recordFailures callers { (gone s) with clientCpu := s.clientCpu + callers }

/-- The restart times that count against the limit now: those inside the window
that ends now. GPU-083: a `window` of 0 means "no window": every restart since
the start counts, whatever the clock says (the lifetime cap of a container). -/
def recent (s : St) : List Nat :=
  if s.window = 0 then s.restartTimes
  else s.restartTimes.filter fun t => s.clock < t + s.window

/-- GPU-048, GPU-049: restart below the limit, else stay stopped. GPU-083: a
container cap is this rule with `window = 0` (no window, see `recent`). -/
def restart (s : St) : St :=
  let r := recent s
  if r.length < s.limit then { s with up := true, restartTimes := r ++ [s.clock], cold := true }
  else { s with stopped := true, restartTimes := r }

/-- Whether the operation can happen in the state. -/
def enabled (s : St) (op : Nat) : Bool :=
  match opCode op with
  | 1 => true
  | 2 => s.up && s.phase == accepted
  | 3 | 5 => s.up && s.phase == proving && s.devWork
  -- a read-back needs device work; the counters (kind 2) are also read while the
  -- request is proved: the zero-check count of the wipe (GPU-036)
  | 4 => s.up && ((s.phase == proving && s.devWork) || (argA op == 2 && s.phase == proved))
  | 6 => s.up && s.phase == proving
  | 7 => s.up && s.phase == proved
  | 8 => s.up && s.phase == wiped
  | 9 => s.up
  | 10 => !s.up && !s.stopped
  | 11 => true
  | 12 => s.phase != proving
  | 13 => s.up && s.phase == idle
  | 14 => s.up && (s.phase == proving || s.phase == proved)
  | _ => false

def flag (x : Nat) : Bool := x == 1

def apply (s : St) (op : Nat) : St :=
  match opCode op with
  | 1 => arrive s
  | 2 => admit s (argA op) (argB op)
  | 3 => fault s (argA op)                                           -- GPU-012, GPU-085, GPU-073
  | 4 => readback s (argA op)                                        -- GPU-038
  | 5 => leaseLoss s
  | 6 => finish s (flag (argA op))
  | 7 => wipe s (flag (argA op))
  | 8 => reply s
  | 9 => crash s
  | 10 => restart s
  | 11 => { s with clock := s.clock + (argA op + 100 * argB op) }
  | 12 => { s with lockHeld := flag (argA op) }
  | 13 => { s with onDev := false, tables := false }                 -- GPU-030, GPU-082
  | 14 => { s with overBound := true }                               -- GPU-050
  | _ => s

/-! ## Invariants (one Bool per requirement group) -/

def invQueue (s : St) : Bool := s.waiting ≤ 1 && (s.waiting == 1 → s.phase != idle)
def invWipe (s : St) : Bool := (s.up && (s.phase == idle || s.phase == accepted)) → !s.dirty
def invAdmit (s : St) : Bool :=
  (s.step == stepGpu || s.step == stepWait || s.step == stepEvict) → s.admNeed ≤ s.admFree
def invNeed (s : St) : Bool := s.admNeed ≤ s.perProof + s.resident
def invEvictStep (s : St) : Bool := (s.step == stepEvict && s.phase == proving) → !s.onDev
def invEvictPolicy (s : St) : Bool :=
  (!s.keep && (s.phase == idle || s.phase == accepted)) → (!s.onDev && !s.tables)
def invLease (s : St) : Bool := ((s.wsl && s.devWork) → s.lockHeld) && (s.leaseLost → !s.devWork)
def invWslIdle (s : St) : Bool :=
  (s.wsl && (s.phase == idle || s.phase == accepted)) → (!s.onDev && !s.tables)
def invWslKeep (s : St) : Bool := !(s.wsl && s.keep) && s.reduced ≤ s.perProof
def invCtx (s : St) : Bool := (!s.device → (!s.ctx && !s.devWork)) && (s.ctx → s.devUsed)
def invRestart (s : St) : Bool := s.restartTimes.length ≤ s.limit && (s.stopped → !s.up)
def invAccounted (s : St) : Bool :=
  s.requests == s.served + s.clientCpu + (if s.phase == idle then 0 else 1) + s.waiting
/-- GPU-039: no proof is returned unverified, and every served proof was
accepted by the verifier: the served count never passes the count of accepts. -/
def invVerified (s : St) : Bool := s.unverifiedReturned == 0 && s.served ≤ s.verifyAccepts
/-- GPU-038: no copy of a kind outside the permitted set. -/
def invReadback (s : St) : Bool := s.badReadbacks == 0
/-- GPU-039, the other direction: an accept is counted only where it is consumed,
with a served proof. A stored answer that is not yet replied (or never reaches
the verifier: an unconfirmed wipe, an acceptance refusal) is not counted. With
`invVerified` the two counts are equal. -/
def invVerifyPending (s : St) : Bool := s.verifyAccepts ≤ s.served
/-- GPU-021: every error reply is followed by a CPU proof of the client. -/
def invErrors (s : St) : Bool := s.errors ≤ s.clientCpu
def invBench (s : St) : Bool := (s.bench && decide (0 < s.degradedServed)) → s.runFailed
def invDown (s : St) : Bool := !s.up → (s.phase == idle && s.waiting == 0 && !s.dirty)
def invPhase (s : St) : Bool := s.phase ≤ wiped && (s.devWork → s.phase == proving)
  && ((s.phase == wiped && s.wipeOk) → !s.dirty)
  && ((s.phase == wiped && s.wipeOk && (!s.keep || s.wsl)) → (!s.onDev && !s.tables))
  && (s.dirty → s.up) && (s.devWork → s.device)

/-- Between requests no request state is left over (GPU-034: each request starts clean). -/
def invFresh (s : St) : Bool :=
  (s.phase == idle || s.phase == accepted) →
    (!s.leaseLost && !s.degraded && s.fallbacks == 0 && !s.overBound && s.step == stepNone &&
     !s.devWork)

/-- GPU-082: between requests, and after a confirmed wipe, no MSM table is on
the device, under either resident policy. -/
def invTables (s : St) : Bool :=
  (s.phase == idle || s.phase == accepted || (s.phase == wiped && s.wipeOk)) → !s.tables
/-- GPU-075: every skipped request was proved on the client's CPU. -/
def invSkips (s : St) : Bool := s.breakerSkips ≤ s.clientCpu
/-- GPU-073: seven reasons; every decline is counted under exactly one. -/
def invDeclines (s : St) : Bool := s.declines.length == reasons && s.declines.sum == s.declined
/-- GPU-078: acceptance mode serves no degraded proof. -/
def invAcceptance (s : St) : Bool := s.acceptance → s.degradedServed == 0
/-- GPU-075: the record stays below the limit (it is cleared when it reaches
it), and no recorded time is in the future. -/
def invBreaker (s : St) : Bool :=
  decide (s.brFails.length < max s.brLimit 1) && s.brFails.all fun t => decide (t ≤ s.clock)

/-- Group A: the daemon and the request accounting. -/
def InvA (s : St) : Bool :=
  invQueue s && invWipe s && invAdmit s && invNeed s && invEvictStep s && invEvictPolicy s &&
  invLease s && invWslIdle s && invWslKeep s && invCtx s && invRestart s && invAccounted s &&
  invBench s && invDown s && invPhase s && invFresh s && invTables s

/-- Group B: the counters. -/
def InvB (s : St) : Bool :=
  invVerified s && invVerifyPending s && invReadback s && invErrors s && invSkips s &&
  invDeclines s && invAcceptance s

/-- The invariants that do not read the failure record. -/
def InvCore (s : St) : Bool := InvA s && InvB s

def Inv (s : St) : Bool := InvCore s && invBreaker s

/-- The state domain of `--step`: the invariant. A state outside it is refused. -/
def stateOk (s : St) : Bool := Inv s

def opRefusals (s : St) (op : Nat) : List Refusal :=
  let c := opCode op
  if c = 0 || c > 14 || argB op > 0 && c ≠ 2 && c ≠ 11 then [.notAnOperation]
  else if c = 4 && argA op > 3 then [.readbackNotPermitted]            -- GPU-038, GPU-036
  else if c = 3 && argA op ≥ reasons || (c = 6 || c = 7 || c = 12) && argA op > 1
      || c = 11 && op / 100 = 0 then [.badArgument]
  else if !enabled s op then [.notEnabled]
  else []

def stepRefusals (s : St) (op : Nat) : List Refusal :=
  if !stateOk s then [.outsideStateDomain] else opRefusals s op

/-- One `--step` transition: the next state, or the state unchanged when refused. -/
def stepOp (s : St) (op : Nat) : St := if stepRefusals s op = [] then apply s op else s

/-- A whole run from the start state (the default mode). Refused operations
are skipped and reported by `runRefusals`. -/
def run (c : Config) (ops : List Nat) : St := ops.foldl stepOp (init c)

end GpuSpec.Service
