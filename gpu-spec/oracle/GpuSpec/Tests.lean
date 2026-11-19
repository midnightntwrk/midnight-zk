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

import GpuSpec.Vectors
import GpuSpec.Hooks

/-!
# Pins and device-model checks

Each pin is written from a requirement sentence. Small-field pins are checked
twice: `decide +kernel` (the kernel, against the definitions) and `#guard`
(the compiled evaluator). The BLS12-381 checks use `#guard` only: they compare
the device models (radix-2 FFT, bucket MSM, compiled quotient program) with the
reference definitions on every golden vector case.
-/

namespace GpuSpec

/-! ## GPU-007: device FFT equals the reference transforms -/

-- every input of length 4 over F_5 (ω = 2 has order 4)
theorem fft_eq_ntt_F5_all : ∀ a b c d : Fin 5,
    fft 5 2 [a.val, b.val, c.val, d.val] = ntt 5 2 [a.val, b.val, c.val, d.val] := by
  decide +kernel

theorem pin_ntt_F17 : ntt 17 (rootOfUnity 17 3 4) [1, 2, 3, 4] = [10, 6, 15, 7] := by decide +kernel
#guard ntt 17 (rootOfUnity 17 3 4) [1, 2, 3, 4] == [10, 6, 15, 7]

theorem pin_fft_F17_8 :
    fft 17 (rootOfUnity 17 3 8) [3, 1, 4, 1, 5, 9, 2, 6] = ntt 17 (rootOfUnity 17 3 8) [3, 1, 4, 1, 5, 9, 2, 6] := by
  decide +kernel
#guard fft 17 (rootOfUnity 17 3 8) [3, 1, 4, 1, 5, 9, 2, 6] == ntt 17 (rootOfUnity 17 3 8) [3, 1, 4, 1, 5, 9, 2, 6]

theorem pin_intt_F17 : intt 17 (rootOfUnity 17 3 8) (ntt 17 (rootOfUnity 17 3 8) [3, 1, 4, 1, 5, 9, 2, 6]) =
    [3, 1, 4, 1, 5, 9, 2, 6] := by decide +kernel
#guard intt 17 (rootOfUnity 17 3 8) (ntt 17 (rootOfUnity 17 3 8) [3, 1, 4, 1, 5, 9, 2, 6]) == [3, 1, 4, 1, 5, 9, 2, 6]

theorem pin_coset_F17 : fftCosetExt 17 3 (rootOfUnity 17 3 8) 2 [1, 2, 3, 4] =
    cosetExt 17 3 (rootOfUnity 17 3 8) 2 [1, 2, 3, 4] := by decide +kernel
#guard fftCosetExt 17 3 (rootOfUnity 17 3 8) 2 [1, 2, 3, 4] == [6, 3, 8, 15, 16, 4, 8, 16]
theorem pin_coset_back_F17 : cosetToCoeff 17 3 (rootOfUnity 17 3 8) 4
    (cosetExt 17 3 (rootOfUnity 17 3 8) 2 [1, 2, 3, 4]) = [1, 2, 3, 4] := by decide +kernel
#guard cosetToCoeff 17 3 (rootOfUnity 17 3 8) 4 (cosetExt 17 3 (rootOfUnity 17 3 8) 2 [1, 2, 3, 4]) == [1, 2, 3, 4]

-- GPU-010: sizes the kernels take, and sizes they decline
#guard deviceSize 23 8 && deviceSize 23 (2 ^ 23) && !deviceSize 23 (2 ^ 24) && !deviceSize 23 6 &&
  !deviceSize 23 1 && !deviceSize 23 0
theorem pin_deviceSize : deviceSize 4 16 = true ∧ deviceSize 4 12 = false ∧ deviceSize 4 32 = false := by
  decide +kernel

/-! ## BLS12-381 Fr: the device models on every golden vector case -/

#guard Vectors.nttCases.all fun c => fft blsR c.omega c.input == ntt blsR c.omega c.input
#guard Vectors.nttCases.all fun c => ifft blsR c.omega c.input == intt blsR c.omega c.input
#guard Vectors.nttCases.all fun c => intt blsR c.omega (ntt blsR c.omega c.input) == c.input
#guard Vectors.cosetCases.all fun c =>
  fftCosetExt blsR c.zeta c.omegaExt c.ext c.input == cosetExt blsR c.zeta c.omegaExt c.ext c.input
#guard Vectors.cosetCases.all fun c =>
  fftCosetToCoeff blsR c.zeta c.omegaExt c.input.length (cosetExt blsR c.zeta c.omegaExt c.ext c.input)
    == c.input
-- the roots: ω has order exactly n (ω^n = 1, ω^(n/2) = p - 1)
#guard Vectors.nttCases.all fun c =>
  powM blsR c.omega (2 ^ c.logN) == 1 && powM blsR c.omega (2 ^ c.logN / 2) == blsR - 1
#guard powM blsR Vectors.zeta3 3 == 1 && Vectors.zeta3 != 1

/-! ## GPU-007, GPU-013: MSM -/

#guard Vectors.msmCases.all fun c => msmBucket blsR 8 256 c.scalars c.bases == msm blsR c.scalars c.bases
#guard Vectors.msmCases.all fun c => msmBucket blsR 13 256 c.scalars c.bases == msm blsR c.scalars c.bases
#guard Vectors.msmCases.all fun c => msmMasked blsR c.mask c.scalars c.bases == msm blsR c.scalars c.bases
theorem pin_msm_bucket_F97 :
    msmBucket 97 2 7 [5, 0, 96, 33] [3, 4, 5, 6] = msm 97 [5, 0, 96, 33] [3, 4, 5, 6] := by decide +kernel
theorem pin_msm_mask_F97 :
    msmMasked 97 [90, 1, 50, 7] [5, 0, 96, 33] [3, 4, 5, 6] = msm 97 [5, 0, 96, 33] [3, 4, 5, 6] := by
  decide +kernel

/-! ## GPU-007: quotient numerator -/

#guard Vectors.quotientCases.all fun c =>
  deviceNumerator blsR c.y c.cols c.gates == numerator blsR c.y c.cols c.gates
-- the first case reaches every node type
def nodeTypes : Expr → List Nat
  | .const _ => [0] | .fixed _ _ => [1] | .advice _ _ => [2] | .inst _ _ => [3]
  | .challenge _ => [4] | .neg e => 5 :: nodeTypes e | .sum a b => 6 :: nodeTypes a ++ nodeTypes b
  | .prod a b => 7 :: nodeTypes a ++ nodeTypes b | .scaled e _ => 8 :: nodeTypes e
#guard match Vectors.quotientCases with
  | c :: _ => (List.range 9).all fun k => c.gates.any fun g => (nodeTypes g).contains k
  | [] => false

/-! ## GPU-009: a decline must leave the buffer unchanged -/

theorem dirtyDecline_breaks :
    runInPlace (List.map (· * 2)) dirtyDecline [1] ≠ [1].map (· * 2) := by decide +kernel

end GpuSpec

/-! ## Service pins (written from the requirement sentences) -/

namespace GpuSpec.Service

def cfg : Config := Vectors.cfgDefault
def runOps (c : Config) (ops : List Nat) : St := ops.foldl stepOp (init c)

-- GPU-029: free 20 covers the cold need 6 + 8: step gpu
theorem pin_gpu : (runOps cfg [1, 2 + 100 * 20 + 10000 * 20]).step = stepGpu := by decide +kernel
#guard (runOps cfg [1, 2 + 100 * 20 + 10000 * 20]).step == stepGpu
-- GPU-026: 13 free, 14 after the wait: step wait
theorem pin_wait : (runOps cfg [1, 2 + 100 * 13 + 10000 * 14]).step = stepWait := by decide +kernel
#guard (runOps cfg [1, 2 + 100 * 13 + 10000 * 14]).step == stepWait
-- GPU-027: 3 and 3: the reduced need 2 fits: step evict, need 2, no copies
theorem pin_evict : (runOps cfg [1, 2 + 300 + 30000]).step = stepEvict ∧
    (runOps cfg [1, 2 + 300 + 30000]).admNeed = 2 ∧ (runOps cfg [1, 2 + 300 + 30000]).onDev = false := by
  decide +kernel
#guard (runOps cfg [1, 2 + 300 + 30000]).step == stepEvict
-- GPU-028: 1 and 1: step cpu, no device work
theorem pin_cpu : (runOps cfg [1, 2 + 100 + 10000]).step = stepCpu ∧
    (runOps cfg [1, 2 + 100 + 10000]).devWork = false := by decide +kernel
#guard (runOps cfg [1, 2 + 100 + 10000]).step == stepCpu
-- GPU-025: with the copies resident (keep), the need is the per-proof part only
theorem pin_keep_need :
    (runOps { cfg with keep := true } ([1, 2 + 2000 + 200000, 106, 107, 8] ++ [1, 2 + 600 + 60000])).admNeed = 6 := by
  decide +kernel
-- GPU-030, GPU-034: after a default-policy reply nothing stays on the device
theorem pin_evict_policy : let s := runOps cfg [1, 2 + 2000 + 200000, 106, 107, 8]
    s.onDev = false ∧ s.tables = false ∧ s.dirty = false ∧ s.served = 1 := by decide +kernel
-- GPU-045, GPU-046: the third concurrent request gets busy and falls back
theorem pin_busy : let s := runOps cfg [1, 1, 1]
    s.waiting = 1 ∧ s.busyReplies = 1 ∧ s.clientCpu = 1 := by decide +kernel
-- GPU-040: a refused proof is an error; the client proves on the CPU
theorem pin_verify : let s := runOps cfg [1, 2 + 2000 + 200000, 6, 107, 8]
    s.errors = 1 ∧ s.served = 0 ∧ s.clientCpu = 1 := by decide +kernel
-- GPU-035: an unconfirmed wipe ends the daemon after the error reply
theorem pin_wipe_fail : (runOps cfg [1, 2 + 2000 + 200000, 106, 7, 8]).up = false := by decide +kernel
-- GPU-048, GPU-049: three restarts in the window, the fourth stop is final
theorem pin_restart_limit : let s := runOps cfg [9, 10, 9, 10, 9, 10, 9, 10]
    s.stopped = true ∧ s.up = false := by decide +kernel
-- GPU-048: a restart 600 s later counts alone (window boundary)
theorem pin_restart_window : let s := runOps { cfg with limit := 1 } [9, 10, 11 + 100 * 0 + 10000 * 6, 9, 10]
    s.up = true ∧ s.restartTimes = [600] := by decide +kernel
theorem pin_restart_window_inside : let s := runOps { cfg with limit := 1 } [9, 10, 11 + 59900, 9, 10]
    s.stopped = true := by decide +kernel
-- GPU-057: WSL2 without the lock: no device phase
theorem pin_wsl_nolock : (runOps { cfg with wsl := true, budget := 16 } [1, 2]).step = stepCpu := by
  decide +kernel
-- GPU-058: WSL2 with the lock: the budget decides
theorem pin_wsl_budget : (runOps { cfg with wsl := true, budget := 16 } [112, 1, 2]).admFree = 16 := by
  decide +kernel
-- GPU-059: keep on WSL2 is refused
theorem pin_wsl_keep : configRefusals { cfg with wsl := true, keep := true } = [.wslKeep] := by decide +kernel
-- GPU-038, GPU-036: kind 3 (base-domain transform output) is accepted and counted;
-- kind 4 (extended-domain vector) and kind 5 (a zeroed region) are refused
theorem pin_readback_kinds : let s := runOps cfg [1, 2 + 2000 + 200000]
    opRefusals s 304 = [] ∧ (stepOp s 304).readbacks = 1 ∧
    opRefusals s 404 = [.readbackNotPermitted] ∧ opRefusals s 504 = [.readbackNotPermitted] ∧
    stepOp s 404 = s ∧ stepOp s 504 = s := by decide +kernel
#guard opRefusals (runOps cfg [1, 2 + 2000 + 200000]) 504 == [.readbackNotPermitted]
-- GPU-036: the counters (kind 2) are also read while the request is proved (the zero-check
-- count of the wipe): 204 after the end of the proof is applied and counted. Kinds 0, 1
-- and 3 need a proving request with device work and are not enabled there; kind 4 is
-- refused as not permitted in either phase. After the wipe no read-back is enabled.
theorem pin_readback_proved : let s := runOps cfg [1, 2 + 2000 + 200000, 106]
    s.phase = proved ∧ s.devWork = false ∧
    opRefusals s 204 = [] ∧ (stepOp s 204).readbacks = 1 ∧ (stepOp s 204).badReadbacks = 0 ∧
    stepOp s 204 = { s with readbacks := 1 } ∧
    opRefusals s 4 = [.notEnabled] ∧ opRefusals s 104 = [.notEnabled] ∧
    opRefusals s 304 = [.notEnabled] ∧ opRefusals s 404 = [.readbackNotPermitted] ∧
    stepOp s 4 = s ∧ stepOp s 104 = s ∧ stepOp s 304 = s ∧
    opRefusals (stepOp s 107) 204 = [.notEnabled] ∧
    -- while proving, with device work, every permitted kind is enabled
    (let t := runOps cfg [1, 2 + 2000 + 200000]
     opRefusals t 4 = [] ∧ opRefusals t 104 = [] ∧ opRefusals t 204 = [] ∧ opRefusals t 304 = []) ∧
    -- after a lease loss (proving, no device work) not even the counters
    opRefusals (runOps cfg [1, 2 + 2000 + 200000, 5]) 204 = [.notEnabled] := by decide +kernel
#guard (runOps cfg [1, 2 + 2000 + 200000, 106, 204, 107, 8]).readbacks == 1
#guard (runOps cfg [1, 2 + 2000 + 200000, 106, 204, 107, 8]).served == 1
#guard (runOps cfg [1, 2 + 2000 + 200000, 106, 4, 104, 304, 107, 8]).readbacks == 0
-- GPU-038: the transition itself counts a kind above 3 (the refusal keeps it at 0)
theorem pin_bad_readback_counted : let s := runOps cfg [1, 2 + 2000 + 200000]
    (apply s 404).badReadbacks = 1 ∧ (apply s 304).badReadbacks = 0 ∧
    Inv (apply s 404) = false := by decide +kernel
-- mutant control: a no-op read-back would leave the count at 0
theorem pin_readback_counts : (runOps cfg [1, 2 + 2000 + 200000, 4, 104, 204, 304]).readbacks = 4 := by
  decide +kernel
#guard (runOps cfg [1, 2 + 2000 + 200000, 4, 104, 204, 304]).readbacks == 4
-- mutant control: a no-op admission would leave the request accepted
theorem pin_admit_moves : (runOps cfg [1, 2 + 2000 + 200000]).phase = proving := by decide +kernel
-- mutant control: a no-op reply would leave the request wiped and unserved
theorem pin_reply_moves : let s := runOps cfg [1, 2 + 2000 + 200000, 106, 107, 8]
    s.phase = idle ∧ s.served = 1 ∧ s.verifyAccepts = 1 ∧ s.degradedServed = 0 := by
  decide +kernel
#guard (runOps cfg [1, 2 + 2000 + 200000, 106, 107, 8]).phase == idle

/-! ### GPU-027, GPU-023: the evict step -/

-- mutant control: an evict step that is not marked degraded
theorem pin_evict_degraded : let s := runOps cfg [1, 2 + 300 + 30000]
    s.degraded = true ∧ s.devWork = true ∧ s.phase = proving := by decide +kernel
#guard (runOps cfg [1, 2 + 300 + 30000]).degraded
-- from a keep state with the key copies on the device: the copies are freed
-- (their 8 units return: 3 + 8 = 11 free), the need is the reduced need 2
theorem pin_keep_evict_step :
    let before := runOps { cfg with keep := true } [1, 2 + 2000 + 200000, 106, 107, 8, 1]
    let s := stepOp before (2 + 300 + 30000)
    before.onDev = true ∧ s.step = stepEvict ∧ s.onDev = false ∧ s.admNeed = 2 ∧
    s.admFree = 11 ∧ s.degraded = true := by decide +kernel
#guard (runOps { cfg with keep := true } [1, 2 + 2000 + 200000, 106, 107, 8, 1, 2 + 300 + 30000]).onDev
  == false

/-! ### GPU-012, GPU-085, GPU-073: declines -/

-- each of the seven reasons is counted in its own slot, once (GPU-073). GPU-085: reasons 0
-- (no-device) and 1 (below-min-k): no fallback, not degraded. GPU-012: reasons 2 to 6: one
-- fallback, degraded.
theorem pin_decline_reasons : ∀ r : Fin 7,
    let s := runOps cfg [1, 2 + 2000 + 200000, 3 + 100 * r.val]
    s.declines = (List.range 7).map (fun i => if i = r.val then 1 else 0) ∧ s.declined = 1 ∧
    s.fallbacks = (if r.val = 0 ∨ r.val = 1 then 0 else 1) ∧
    s.degraded = (if r.val = 0 ∨ r.val = 1 then false else true) := by decide +kernel
-- the same, reason by reason, written out: fallbacks and the degraded mark
#guard (List.range 7).map (fun r =>
    let s := runOps cfg [1, 2 + 2000 + 200000, 3 + 100 * r]
    (s.fallbacks, s.degraded)) ==
  [(0, false), (0, false), (1, true), (1, true), (1, true), (1, true), (1, true)]
#guard (List.range 7).all fun r =>
  (runOps cfg [1, 2 + 2000 + 200000, 3 + 100 * r]).declines ==
    (List.range 7).map (fun i => if i = r then 1 else 0)
-- `3` alone is reason 0 (no-device); two declines of one reason count twice. Of the three
-- declines only the device-error (603) is a fallback
theorem pin_decline_twice : let s := runOps cfg [1, 2 + 2000 + 200000, 3, 603, 3]
    s.declines = [2, 0, 0, 0, 0, 0, 1] ∧ s.declined = 3 ∧ s.fallbacks = 1 := by decide +kernel
-- one decline of each reason: 7 declines, 5 fallbacks
theorem pin_decline_all_reasons :
    let s := runOps cfg [1, 2 + 2000 + 200000, 3, 103, 203, 303, 403, 503, 603]
    s.declines = [1, 1, 1, 1, 1, 1, 1] ∧ s.declined = 7 ∧ s.fallbacks = 5 := by decide +kernel
-- the reason set is closed: argument 7 is refused and nothing is counted
theorem pin_decline_reason7 : let s := runOps cfg [1, 2 + 2000 + 200000]
    opRefusals s 703 = [.badArgument] ∧ stepOp s 703 = s := by decide +kernel
#guard opRefusals (runOps cfg [1, 2 + 2000 + 200000]) 703 == [.badArgument]
-- GPU-023, GPU-012: production mode serves a proof with a `fault` decline (503), marked
-- degraded
theorem pin_production_decline : let s := runOps cfg [1, 2 + 2000 + 200000, 503, 106, 107, 8]
    s.served = 1 ∧ s.degradedServed = 1 ∧ s.errors = 0 ∧ s.degradedRefused = 0 := by
  decide +kernel
#guard (runOps cfg [1, 2 + 2000 + 200000, 503, 106, 107, 8]).degradedServed == 1
-- GPU-085: production mode serves a proof with one below-min-k decline (103: a small MSM)
-- NOT degraded; the decline is counted. The same with no-device (3)
theorem pin_production_expected_decline :
    let s := runOps cfg [1, 2 + 2000 + 200000, 103, 106, 107, 8]
    let t := runOps cfg [1, 2 + 2000 + 200000, 3, 106, 107, 8]
    s.served = 1 ∧ s.degradedServed = 0 ∧ s.errors = 0 ∧ s.declined = 1 ∧
    s.declines = [0, 1, 0, 0, 0, 0, 0] ∧
    t.served = 1 ∧ t.degradedServed = 0 ∧ t.declines = [1, 0, 0, 0, 0, 0, 0] := by decide +kernel
#guard (runOps cfg [1, 2 + 2000 + 200000, 103, 106, 107, 8]).degradedServed == 0
-- GPU-024: under bench a below-min-k decline does not fail the run; a fault decline does
theorem pin_bench_expected_decline :
    (runOps { cfg with bench := true } [1, 2 + 2000 + 200000, 103, 106, 107, 8]).runFailed = false ∧
    (runOps { cfg with bench := true } [1, 2 + 2000 + 200000, 503, 106, 107, 8]).runFailed = true := by
  decide +kernel

/-! ### GPU-078: acceptance mode -/

def acc : Config := { cfg with acceptance := true }

-- step evict: no phase starts and there is no device work; the reply is a
-- degraded error, nothing is served, the caller proves on its CPU, no failure
theorem pin_acceptance_evict : let a := runOps acc [1, 2 + 300 + 30000]
    let s := stepOp a 8
    a.step = stepEvict ∧ a.phase = wiped ∧ a.degraded = true ∧ a.devWork = false ∧
    a.devUsed = false ∧ a.ctx = false ∧ a.dirty = false ∧
    s.served = 0 ∧ s.errors = 1 ∧ s.degradedRefused = 1 ∧ s.clientCpu = 1 ∧ s.brFails = [] ∧
    s.phase = idle := by decide +kernel
#guard (runOps acc [1, 2 + 300 + 30000, 8]).served == 0
#guard (runOps acc [1, 2 + 300 + 30000, 8]).degradedRefused == 1
-- step cpu, the same
theorem pin_acceptance_cpu : let s := runOps acc [1, 2 + 100 + 10000, 8]
    s.served = 0 ∧ s.degradedRefused = 1 ∧ s.clientCpu = 1 ∧ s.brFails = [] := by decide +kernel
-- a `fault` decline (503): the proof completes and the verifier accepts, still a degraded
-- error (GPU-012: one fallback)
theorem pin_acceptance_decline : let s := runOps acc [1, 2 + 2000 + 200000, 503, 106, 107, 8]
    s.served = 0 ∧ s.degradedRefused = 1 ∧ s.errors = 1 ∧ s.clientCpu = 1 ∧
    s.verifyAccepts = 0 ∧ s.brFails = [] := by decide +kernel
#guard (runOps acc [1, 2 + 2000 + 200000, 503, 106, 107, 8]).degradedRefused == 1
-- GPU-085: one below-min-k MSM decline (103) in acceptance mode: the proof is SERVED, with
-- no degraded error. This is why the split exists: without it every proof with one small
-- MSM would be refused. The same with no-device (3) and with both
theorem pin_acceptance_expected_decline :
    let s := runOps acc [1, 2 + 2000 + 200000, 103, 106, 107, 8]
    let t := runOps acc [1, 2 + 2000 + 200000, 3, 103, 106, 107, 8]
    s.served = 1 ∧ s.degradedRefused = 0 ∧ s.errors = 0 ∧ s.clientCpu = 0 ∧
    s.degradedServed = 0 ∧ s.declined = 1 ∧
    t.served = 1 ∧ t.degradedRefused = 0 ∧ t.errors = 0 ∧ t.declined = 2 := by decide +kernel
#guard (runOps acc [1, 2 + 2000 + 200000, 103, 106, 107, 8]).served == 1
#guard (runOps acc [1, 2 + 2000 + 200000, 103, 106, 107, 8]).degradedRefused == 0
-- mutant control: one fallback reason next to the expected ones is refused
#guard (runOps acc [1, 2 + 2000 + 200000, 103, 203, 106, 107, 8]).served == 0
-- step evict from a keep state with the key copies on the device: the frees of
-- the step apply (the copies go, 3 + 8 = 11 free), no phase starts
theorem pin_acceptance_evict_frees :
    let s := runOps { acc with keep := true } [1, 2 + 2000 + 200000, 106, 107, 8, 1, 2 + 300 + 30000]
    s.onDev = false ∧ s.phase = wiped ∧ s.step = stepEvict ∧ s.admNeed = 2 ∧ s.admFree = 11 ∧
    s.devWork = false := by decide +kernel
-- GPU-057 with GPU-078: WSL2 without the lock is step cpu, so no phase starts
theorem pin_acceptance_wsl_nolock : let s := runOps { acc with wsl := true, budget := 16 } [1, 2]
    s.phase = wiped ∧ s.step = stepCpu ∧ s.degraded = true ∧ s.wipeOk = true := by decide +kernel
-- GPU-020 with GPU-078: without a device the step is none, which is not degraded
theorem pin_acceptance_no_device : let s := runOps { acc with device := false } [1, 2]
    s.phase = proving ∧ s.step = stepNone ∧ s.degraded = false := by decide +kernel
-- a clean proof is served in acceptance mode
theorem pin_acceptance_clean : let s := runOps acc [1, 2 + 2000 + 200000, 106, 107, 8]
    s.served = 1 ∧ s.degradedRefused = 0 := by decide +kernel

/-! ### GPU-075, GPU-076, GPU-077: the client breaker -/

-- the daemon is down: two failures do not open the breaker, the third at the
-- same time does, until 0 + 600
theorem pin_breaker_opens :
    (runOps cfg [9, 1, 1]).brFails = [0, 0] ∧ (runOps cfg [9, 1, 1]).brOpenUntil = 0 ∧
    (runOps cfg [9, 1, 1, 1]).brFails = [] ∧ (runOps cfg [9, 1, 1, 1]).brOpenUntil = 600 := by
  decide +kernel
#guard (runOps cfg [9, 1, 1, 1]).brOpenUntil == 600
-- the third failure 599 s after the first two is inside the window: open until 599 + 600
theorem pin_breaker_window_inside : (runOps cfg [9, 1, 1, 11 + 9900 + 50000, 1]).brOpenUntil = 1199 := by
  decide +kernel
-- the third failure 600 s after the first two: they are dropped, the breaker stays closed
theorem pin_breaker_window_expiry : let s := runOps cfg [9, 1, 1, 11 + 60000, 1]
    s.brFails = [600] ∧ s.brOpenUntil = 0 := by decide +kernel
#guard (runOps cfg [9, 1, 1, 11 + 60000, 1]).brFails == [600]
-- open: the restarted daemon is not contacted at 599 s (a skip, nothing accepted)
theorem pin_breaker_open_skips : let s := runOps cfg [9, 1, 1, 1, 10, 11 + 9900 + 50000, 1]
    s.up = true ∧ s.breakerSkips = 1 ∧ s.phase = idle ∧ s.clientCpu = 4 ∧ s.brFails = [] := by
  decide +kernel
-- the breaker closes at exactly `brOpenUntil` = 600: the request reaches the daemon
theorem pin_breaker_closes : let s := runOps cfg [9, 1, 1, 1, 10, 11 + 9900 + 50000, 11 + 100, 1]
    s.clock = 600 ∧ s.breakerSkips = 0 ∧ s.phase = accepted ∧ s.clientCpu = 3 := by decide +kernel
#guard (runOps cfg [9, 1, 1, 1, 10, 11 + 9900 + 50000, 11 + 100, 1]).phase == accepted
-- GPU-076: a served proof clears two recorded failures
theorem pin_served_clears :
    (runOps cfg [9, 1, 1, 10, 1, 2 + 2000 + 200000, 106, 107]).brFails = [0, 0] ∧
    (runOps cfg [9, 1, 1, 10, 1, 2 + 2000 + 200000, 106, 107, 8]).brFails = [] ∧
    (runOps cfg [9, 1, 1, 10, 1, 2 + 2000 + 200000, 106, 107, 8]).served = 1 := by decide +kernel
#guard (runOps cfg [9, 1, 1, 10, 1, 2 + 2000 + 200000, 106, 107, 8]).brFails == []
-- GPU-076: a served proof does not shorten an open cooldown. With a limit of 1
-- the verify error of the first request opens the breaker until 600; the
-- waiting request was already accepted, and its served proof keeps 600.
theorem pin_served_keeps_cooldown :
    let t := runOps { cfg with brLimit := 1 }
      [1, 1, 2 + 2000 + 200000, 6, 107, 8, 2 + 2000 + 200000, 106, 107]
    t.brOpenUntil = 600 ∧ (stepOp t 8).served = 1 ∧ (stepOp t 8).brOpenUntil = 600 := by
  decide +kernel
-- GPU-077: a busy reply is not a failure
theorem pin_busy_no_failure : let s := runOps cfg [1, 1, 1]
    s.busyReplies = 1 ∧ s.brFails = [] ∧ s.brOpenUntil = 0 := by decide +kernel
-- GPU-077: a verify error is one failure
theorem pin_verify_failure : (runOps cfg [1, 2 + 2000 + 200000, 6, 107, 8]).brFails = [0] := by
  decide +kernel
-- GPU-035, GPU-077: a retired reply: the caller and the waiting caller each record one
theorem pin_wipe_fail_failures : let s := runOps cfg [1, 1, 2 + 2000 + 200000, 106, 7, 8]
    s.up = false ∧ s.errors = 1 ∧ s.served = 0 ∧ s.clientCpu = 2 ∧ s.brFails = [0, 0] := by
  decide +kernel
-- GPU-035, GPU-039: after an unconfirmed wipe the verifier does not run: the two end
-- states for a = 0 and a = 1 are equal, the count of verifier accepts included (0)
theorem pin_wipe_fail_no_verify :
    let s0 := runOps cfg [1, 2 + 2000 + 200000, 6, 7, 8]
    let s1 := runOps cfg [1, 2 + 2000 + 200000, 106, 7, 8]
    s0 = s1 ∧ s0.verifyAccepts = 0 ∧ s1.verifyAccepts = 0 ∧ s1.served = 0 ∧ s1.errors = 1 := by
  decide +kernel
#guard runOps cfg [1, 2 + 2000 + 200000, 106, 7, 8] == runOps cfg [1, 2 + 2000 + 200000, 6, 7, 8]
-- GPU-078, GPU-039: an acceptance refusal does not reach the verifier: the count of
-- verifier accepts is unchanged whatever a was, and the two end states are equal
theorem pin_acceptance_refusal_no_verify :
    let s0 := runOps { cfg with acceptance := true } [1, 2 + 2000 + 200000, 503, 6, 107, 8]
    let s1 := runOps { cfg with acceptance := true } [1, 2 + 2000 + 200000, 503, 106, 107, 8]
    s0 = s1 ∧ s0.verifyAccepts = 0 ∧ s1.verifyAccepts = 0 ∧ s1.degradedRefused = 1 ∧
    s1.served = 0 ∧ s1.brFails = [] := by decide +kernel
#guard (runOps { cfg with acceptance := true } [1, 2 + 2000 + 200000, 503, 106, 107, 8]).verifyAccepts
  == 0
-- GPU-039: the accept is counted where it is consumed. After op 106 the answer is stored and
-- the count is still 0; the served reply raises it to 1; a refused proof (a = 0) leaves 0
theorem pin_verify_counted_at_reply :
    (runOps cfg [1, 2 + 2000 + 200000, 106]).verifyAccepts = 0 ∧
    (runOps cfg [1, 2 + 2000 + 200000, 106]).verifyOk = true ∧
    (runOps cfg [1, 2 + 2000 + 200000, 106, 107]).verifyAccepts = 0 ∧
    (runOps cfg [1, 2 + 2000 + 200000, 106, 107, 8]).verifyAccepts = 1 ∧
    (runOps cfg [1, 2 + 2000 + 200000, 106, 107, 8]).served = 1 ∧
    (runOps cfg [1, 2 + 2000 + 200000, 6, 107, 8]).verifyAccepts = 0 ∧
    (runOps cfg [1, 2 + 2000 + 200000, 6, 107, 8]).served = 0 ∧
    -- a crash between the end of the proof and the reply: the accept was never counted
    (runOps cfg [1, 2 + 2000 + 200000, 106, 9]).verifyAccepts = 0 ∧
    -- two served proofs: two accepts
    (runOps cfg [1, 2 + 2000 + 200000, 106, 107, 8, 1, 2 + 2000 + 200000, 106, 107, 8]).verifyAccepts
      = 2 := by decide +kernel
#guard (runOps cfg [1, 2 + 2000 + 200000, 106]).verifyAccepts == 0
#guard (runOps cfg [1, 2 + 2000 + 200000, 106, 107, 8]).verifyAccepts == 1
-- GPU-021, GPU-077: a crash with one request in flight and one waiting: two CPU
-- proofs and two failures at the same clock value
theorem pin_crash_waiting : let s := runOps cfg [1, 1, 2 + 2000 + 200000, 9]
    s.clientCpu = 2 ∧ s.brFails = [0, 0] ∧ s.up = false := by decide +kernel
-- a crash of an idle daemon has no caller: no failure
theorem pin_crash_idle : (runOps cfg [9]).brFails = [] := by decide +kernel
-- GPU-050, GPU-077: a planned restart with a waiting caller: one failure
theorem pin_overbound_waiting : let s := runOps cfg [1, 1, 2 + 2000 + 200000, 6, 14, 107, 8]
    s.up = false ∧ s.clientCpu = 2 ∧ s.brFails = [0, 0] := by decide +kernel
-- GPU-076 then GPU-050: the served reply clears the record, then the waiting
-- caller of the planned restart records its failure (the record is not empty)
theorem pin_served_then_overbound : let s := runOps cfg [1, 1, 2 + 2000 + 200000, 14, 106, 107, 8]
    s.served = 1 ∧ s.brFails = [0] ∧ s.clientCpu = 1 := by decide +kernel
-- a `brLimit` of 0 counts as 1: the first failure opens the breaker
theorem pin_breaker_limit0 : (runOps { cfg with brLimit := 0 } [9, 1]).brOpenUntil = 600 := by
  decide +kernel

/-! ### GPU-081, GPU-082, GPU-030: resident policy -/

-- GPU-081: no policy named: evict
theorem pin_default_policy : defaultConfig.keep = false ∧ defaultConfig.acceptance = false ∧
    defaultConfig.limit = 3 ∧ defaultConfig.window = 600 ∧ defaultConfig.brLimit = 3 ∧
    defaultConfig.brWindow = 600 ∧ defaultConfig.brCooldown = 600 ∧
    Vectors.cfgDefault = defaultConfig := by decide +kernel
#guard defaultConfig.keep == false
-- GPU-082, GPU-030: under keep the MSM tables are on the device during the proof
-- and gone after the wipe; the key copies stay
theorem pin_keep_tables :
    (runOps { cfg with keep := true } [1, 2 + 2000 + 200000, 106]).tables = true ∧
    (runOps { cfg with keep := true } [1, 2 + 2000 + 200000, 106, 107]).tables = false ∧
    (runOps { cfg with keep := true } [1, 2 + 2000 + 200000, 106, 107]).onDev = true ∧
    (runOps { cfg with keep := true } [1, 2 + 2000 + 200000, 106, 107, 8]).onDev = true := by
  decide +kernel
#guard (runOps { cfg with keep := true } [1, 2 + 2000 + 200000, 106, 107]).tables == false

/-! ### GPU-083: the container cap -/

-- no window (`window := 0`): the fourth exit, two days (172800 s) after the
-- third restart, stays stopped; under the systemd window of 600 s it restarts
theorem pin_restart_lifetime :
    let ops := [9, 10, 9, 10, 9, 10, 11 + 10000 * 1728, 9, 10]
    (runOps { cfg with window := 0 } ops).stopped = true ∧
    (runOps { cfg with window := 0 } ops).up = false ∧
    (runOps { cfg with window := 0 } ops).restartTimes.length = 3 ∧
    (runOps cfg ops).up = true := by decide +kernel
#guard (runOps { cfg with window := 0 } [9, 10, 9, 10, 9, 10, 11 + 10000 * 1728, 9, 10]).stopped
-- limit 1 and no window: one restart, then the second exit stays stopped after ANY tick.
-- Ticks of 1 s, 599 s, 600 s, 601 s, 9999 s and two days, and several ticks in a row; a
-- further supervisor action after more time changes nothing. With any finite window the
-- second exit restarts once the clock has passed the window (here 600 s and 10^9 s: the
-- largest tick of the wire format is 999999 s, so 1001 of them pass 10^9).
theorem pin_restart_lifetime_any_tick :
    let one : Config := { cfg with limit := 1, window := 0 }
    (([1, 599, 600, 601, 9999, 172800].all fun d =>
      let s := runOps one [9, 10, Vectors.tick d, 9, 10]
      s.stopped && !s.up && s.restartTimes == [0]) = true) ∧
    (let s := runOps one [9, 10, Vectors.tick 600, Vectors.tick 600, Vectors.tick 9999, 9, 10,
        Vectors.tick 9999, 10]
     s.stopped = true ∧ s.up = false ∧ s.restartTimes = [0]) ∧
    (runOps { cfg with limit := 1 } [9, 10, Vectors.tick 600, 9, 10]).up = true ∧
    (runOps { cfg with limit := 1 } [9, 10, Vectors.tick 599, 9, 10]).stopped = true := by
  decide +kernel
#guard (runOps { cfg with limit := 1, window := 0 } [9, 10, Vectors.tick 172800, 9, 10]).stopped
-- no directed trace and no default uses `window = 0` with the old meaning ("nothing is
-- recent"): the one configuration with 0 is the container cap
#guard (Vectors.traces.filter fun t => t.config.window == 0).map (·.name) ==
  ["container-restart-cap"]
#guard defaultConfig.window == 600

/-! ### The directed traces are present (`.all` over an empty list is vacuous) -/

#guard Vectors.traces.length == 29
#guard (Vectors.traces.map (·.name)).eraseDups.length == 29
#guard Vectors.traces.all fun t => configRefusals t.config == [] && !t.ops.isEmpty
#guard ["breaker-open-cooldown", "breaker-window-expiry", "breaker-reset-on-served",
  "acceptance-evict", "acceptance-decline", "decline-reasons", "readback-kinds",
  "keep-tables-freed", "container-restart-cap", "crash-with-waiting", "default-policy",
  "keep-evict-step", "expected-decline-accepted", "zero-check-count"].all fun n => Vectors.traces.any (·.name == n)

end GpuSpec.Service
