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


import GpuSpec.Service

/-!
# Invariant proofs of the request state machine

`Inv` (the conjunction of the invariants, each named with its requirement IDs
in `Service.lean`) holds in the start state of every accepted configuration
and is kept by every transition. So it holds in every reachable state.

`Inv` has three groups, proved apart so that each proof stays small. `InvA`
(the daemon and the request accounting) and `InvB` (the counters) do not read
the failure record of the client breaker, so recording a failure keeps them
(`a_recordFailures`, `b_recordFailures`). `invBreaker` reads only the record,
the limit and the clock.
-/

namespace GpuSpec.Service

-- The side conditions share one simp set; some entries are unused in some cases.
set_option linter.unusedSimpArgs false

/-! ## The failure record -/

theorem a_recordFailure (s : St) : InvA (recordFailure s) = InvA s := by
  simp only [recordFailure]; split <;> rfl

theorem a_recordFailures (k : Nat) : ∀ s, InvA (recordFailures k s) = InvA s := by
  induction k with
  | zero => intro s; rfl
  | succ k ih => intro s; simp only [recordFailures, ih, a_recordFailure]

theorem b_recordFailure (s : St) : InvB (recordFailure s) = InvB s := by
  simp only [recordFailure]; split <;> rfl

theorem b_recordFailures (k : Nat) : ∀ s, InvB (recordFailures k s) = InvB s := by
  induction k with
  | zero => intro s; rfl
  | succ k ih => intro s; simp only [recordFailures, ih, b_recordFailure]

theorem breaker_recordFailure (s : St) (h : invBreaker s = true) :
    invBreaker (recordFailure s) = true := by
  simp only [invBreaker, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  simp only [recordFailure]
  split
  · simp only [invBreaker, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.length_nil]
    exact ⟨by omega, by simp⟩
  · rename_i hlt
    simp only [invBreaker, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨by omega, ?_⟩
    intro t ht
    simp only [List.mem_append, List.mem_filter, List.mem_singleton] at ht
    rcases ht with ht | ht
    · exact h.2 t ht.1
    · omega

theorem breaker_recordFailures (k : Nat) :
    ∀ s, invBreaker s = true → invBreaker (recordFailures k s) = true := by
  induction k with
  | zero => intro s h; exact h
  | succ k ih => intro s h; exact ih _ (breaker_recordFailure s h)

/-- `invBreaker` reads only the record, the limit and the clock. -/
theorem breaker_congr (s t : St) (h : invBreaker s = true) (hf : t.brFails = s.brFails)
    (hl : t.brLimit = s.brLimit) (hc : s.clock ≤ t.clock) : invBreaker t = true := by
  simp only [invBreaker, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  rw [hf, hl]
  exact ⟨h.1, fun x hx => Nat.le_trans (h.2 x hx) hc⟩

theorem breaker_cleared (t : St) (hf : t.brFails = []) : invBreaker t = true := by
  simp only [invBreaker, hf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.length_nil]
  exact ⟨by omega, by simp⟩

/-- The fields that recording failures does not change (those the theorems below read). -/
theorem recordFailure_other (s : St) :
    (recordFailure s).up = s.up ∧ (recordFailure s).stopped = s.stopped ∧
    (recordFailure s).errors = s.errors ∧ (recordFailure s).served = s.served ∧
    (recordFailure s).clock = s.clock ∧ (recordFailure s).brLimit = s.brLimit := by
  simp only [recordFailure]; split <;> simp

theorem recordFailures_other (k : Nat) : ∀ s : St,
    (recordFailures k s).up = s.up ∧ (recordFailures k s).stopped = s.stopped ∧
    (recordFailures k s).errors = s.errors ∧ (recordFailures k s).served = s.served ∧
    (recordFailures k s).clock = s.clock ∧ (recordFailures k s).brLimit = s.brLimit := by
  induction k with
  | zero => intro s; simp [recordFailures]
  | succ k ih =>
    intro s
    have h1 := ih (recordFailure s)
    have h2 := recordFailure_other s
    simp only [recordFailures]
    grind

/-! ## The decline counts -/

theorem countAt_length : ∀ (l : List Nat) (r : Nat), (countAt l r).length = l.length
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, r + 1 => by simp [countAt, countAt_length xs r]

theorem countAt_sum : ∀ (l : List Nat) (r : Nat), r < l.length → (countAt l r).sum = l.sum + 1
  | [], _, h => by simp at h
  | x :: xs, 0, _ => by simp [countAt]; omega
  | x :: xs, r + 1, h => by
    have := countAt_sum xs r (by simpa using h)
    simp [countAt, this]; omega

theorem countAt_getD : ∀ (l : List Nat) (r i : Nat), r < l.length →
    (countAt l r).getD i 0 = l.getD i 0 + (if i = r then 1 else 0)
  | [], _, _, h => by simp at h
  | x :: xs, 0, i, _ => by cases i <;> simp [countAt]
  | x :: xs, r + 1, i, h => by
    cases i with
    | zero => simp [countAt]
    | succ i => simpa [countAt] using countAt_getD xs r i (by simpa using h)

/-! ## `InvCore` in the start state and under each event -/

macro "inv_unfold" : tactic => `(tactic| simp only [Inv, InvCore, InvA, InvB, invQueue, invWipe, invAdmit,
    invNeed, invEvictStep, invEvictPolicy, invLease, invWslIdle, invWslKeep, invCtx, invRestart,
    invAccounted, invVerified, invVerifyPending, invReadback, invErrors, invBench, invDown, invPhase, invFresh,
    invTables, invSkips, invDeclines, invAcceptance, reasons,
    idle, accepted, proving,
    proved, wiped, stepNone, stepGpu, stepWait, stepEvict, stepCpu, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true', Bool.or_eq_true]
    at *)

macro "inv_close" : tactic => `(tactic|
  ((inv_unfold; and_intros) <;> grind (splits := 40)))

/-- Split the branches of the event, drop the recorded failures (`InvA` and
`InvB` do not read the record), then close each conjunct. -/
macro "inv_close_split" : tactic => `(tactic|
  ((repeat' split) <;>
   (try simp only [a_recordFailure, a_recordFailures, b_recordFailure, b_recordFailures]) <;>
   (inv_unfold; and_intros) <;> grind (splits := 40)))

theorem inv_init (c : Config) (h : configRefusals c = []) : Inv (init c) = true := by
  unfold configRefusals at h
  have hr : c.reduced ≤ c.perProof := by
    by_cases hc : c.reduced > c.perProof <;> simp_all
  have hb : invBreaker (init c) = true := breaker_cleared (init c) rfl
  simp only [Inv, hb, Bool.and_true]
  cases hw : c.wsl <;> cases hk : c.keep <;> simp_all [InvCore, InvA, InvB, init, invQueue, invWipe,
    invAdmit, invNeed, invEvictStep, invEvictPolicy, invLease, invWslIdle, invWslKeep, invCtx,
    invRestart, invAccounted, invVerified, invVerifyPending, invReadback, invErrors, invBench,
    invDown, invPhase, invFresh, invTables, invSkips, invDeclines, invAcceptance, reasons, idle,
    stepNone, wiped]

/-! ### Group A: the daemon and the request accounting -/

theorem a_arrive (s : St) (h : InvA s = true) : InvA (arrive s) = true := by
  simp only [arrive, breakerOpen, decide_eq_true_eq]; inv_close_split

set_option maxHeartbeats 4000000 in
theorem a_admit (s : St) (a b : Nat) (h : InvA s = true) (hu : s.up = true)
    (hp : s.phase = accepted) : InvA (admit s a b) = true := by
  unfold admit cpuStep noPhase onCpu onDevice fullNeed; inv_close_split

theorem a_fault (s : St) (r : Nat) (h : InvA s = true) (hp : s.phase = proving)
    (hd : s.devWork = true) : InvA (fault s r) = true := by
  unfold fault; split <;> inv_close

theorem a_readback (s : St) (k : Nat) (h : InvA s = true) : InvA (readback s k) = true := by
  unfold readback; inv_close

theorem a_leaseLoss (s : St) (h : InvA s = true) (hp : s.phase = proving) :
    InvA (leaseLoss s) = true := by
  unfold leaseLoss; inv_close

theorem a_finish (s : St) (ok : Bool) (h : InvA s = true) (hu : s.up = true)
    (hp : s.phase = proving) : InvA (finish s ok) = true := by
  unfold finish; inv_close

theorem a_wipe (s : St) (ok : Bool) (h : InvA s = true) (hu : s.up = true)
    (hp : s.phase = proved) : InvA (wipe s ok) = true := by
  unfold wipe; inv_close_split

set_option maxHeartbeats 4000000 in
theorem a_reply (s : St) (h : InvA s = true) (hu : s.up = true) (hp : s.phase = wiped) :
    InvA (reply s) = true := by
  unfold reply serve afterReply endRequest gone
  cases hw : s.wipeOk <;> cases ho : s.overBound <;> by_cases h1 : s.waiting = 1 <;>
    simp only [hw, ho, h1, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
    inv_close_split

theorem a_crash (s : St) (h : InvA s = true) : InvA (crash s) = true := by
  unfold crash gone; inv_close_split

theorem recent_length_le (s : St) : (recent s).length ≤ s.restartTimes.length := by
  unfold recent
  split
  · exact Nat.le_refl _
  · exact List.length_filter_le _ _

/-- GPU-083: with no window every restart on record counts. -/
theorem recent_no_window (s : St) (h : s.window = 0) : recent s = s.restartTimes := by
  simp [recent, h]

theorem a_restart (s : St) (h : InvA s = true) (hu : s.up = false) (hs : s.stopped = false) :
    InvA (restart s) = true := by
  unfold restart
  have := recent_length_le s
  by_cases hl : (recent s).length < s.limit
  · simp only [hl, ↓reduceIte]
    have : (recent s ++ [s.clock]).length ≤ s.limit := by
      simp only [List.length_append, List.length_singleton]; omega
    inv_close
  · simp only [hl, ↓reduceIte]
    have : (recent s).length ≤ s.limit := by inv_unfold; omega
    inv_close

theorem a_tick (s : St) (d : Nat) (h : InvA s = true) :
    InvA { s with clock := s.clock + d } = true := by inv_close

theorem a_lock (s : St) (x : Bool) (h : InvA s = true) (hp : s.phase ≠ proving) :
    InvA { s with lockHeld := x } = true := by inv_close

theorem a_evict (s : St) (h : InvA s = true) :
    InvA { s with onDev := false, tables := false } = true := by inv_close

theorem a_overBound (s : St) (h : InvA s = true) (hp : s.phase = proving ∨ s.phase = proved) :
    InvA { s with overBound := true } = true := by inv_close

/-! ### Group B: the counters of the verifier, the read-backs, the declines,
the breaker skips and acceptance mode. Each proof reads only `InvB` and the
guard of the event, so a missing guard shows here. -/

theorem b_arrive (s : St) (h : InvB s = true) : InvB (arrive s) = true := by
  simp only [arrive, breakerOpen, decide_eq_true_eq]; inv_close_split

theorem b_admit (s : St) (a b : Nat) (h : InvB s = true) :
    InvB (admit s a b) = true := by
  unfold admit cpuStep noPhase onCpu onDevice fullNeed; inv_close_split

/-- GPU-073: needs the refusal of a reason above 6 (`hr` comes from `stepRefusals_nil`). -/
theorem b_fault (s : St) (r : Nat) (h : InvB s = true)
    (hr : r < reasons) : InvB (fault s r) = true := by
  have hl : s.declines.length = reasons := by inv_unfold; grind
  have h1 := countAt_length s.declines r
  have h2 := countAt_sum s.declines r (by omega)
  unfold fault; split <;> inv_close

/-- GPU-038: needs the refusal of a kind above 3 (`hk` comes from `stepRefusals_nil`). -/
theorem b_readback (s : St) (k : Nat) (h : InvB s = true) (hk : k ≤ 3) :
    InvB (readback s k) = true := by
  unfold readback; inv_close

theorem b_leaseLoss (s : St) (h : InvB s = true) :
    InvB (leaseLoss s) = true := by
  unfold leaseLoss; inv_close

theorem b_finish (s : St) (ok : Bool) (h : InvB s = true) :
    InvB (finish s ok) = true := by
  unfold finish; cases ok <;> inv_close

theorem b_wipe (s : St) (ok : Bool) (h : InvB s = true) :
    InvB (wipe s ok) = true := by
  unfold wipe; inv_close_split

/-- GPU-039, GPU-078: needs the verifier branch and the acceptance branch of `reply`. -/
theorem b_reply (s : St) (h : InvB s = true) : InvB (reply s) = true := by
  unfold reply serve afterReply endRequest gone
  cases hv : s.verifyOk <;> cases ha : s.acceptance <;> cases hd : s.degraded <;>
    by_cases hf : 0 < s.fallbacks <;>
    simp only [hv, ha, hd, hf, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_or, Bool.false_or, Bool.or_false, Bool.and_true, Bool.true_and, Bool.false_and,
      Bool.and_false, decide_true, decide_false, Bool.or_true, ↓reduceIte] <;> inv_close_split

theorem b_crash (s : St) (h : InvB s = true) : InvB (crash s) = true := by
  unfold crash gone; inv_close_split

theorem b_restart (s : St) (h : InvB s = true) :
    InvB (restart s) = true := by
  unfold restart; inv_close_split

theorem b_tick (s : St) (d : Nat) (h : InvB s = true) :
    InvB { s with clock := s.clock + d } = true := by inv_close

theorem b_lock (s : St) (x : Bool) (h : InvB s = true) :
    InvB { s with lockHeld := x } = true := by inv_close

theorem b_evict (s : St) (h : InvB s = true) :
    InvB { s with onDev := false, tables := false } = true := by inv_close

theorem b_overBound (s : St) (h : InvB s = true) :
    InvB { s with overBound := true } = true := by inv_close

/-! ## `invBreaker` under each event -/

/-- Close `invBreaker` of a state that keeps or clears the record, or records failures on one. -/
macro "br_close" h:ident : tactic => `(tactic|
  first
    | exact breaker_congr _ _ $h rfl rfl (Nat.le_refl _)
    | exact breaker_cleared _ rfl
    | exact breaker_recordFailure _ (breaker_congr _ _ $h rfl rfl (Nat.le_refl _))
    | exact breaker_recordFailures _ _ (breaker_congr _ _ $h rfl rfl (Nat.le_refl _))
    | exact breaker_recordFailures _ _ (breaker_cleared _ rfl))

theorem breaker_arrive (s : St) (h : invBreaker s = true) : invBreaker (arrive s) = true := by
  simp only [arrive]; (repeat' split) <;> br_close h

theorem breaker_admit (s : St) (a b : Nat) (h : invBreaker s = true) :
    invBreaker (admit s a b) = true := by
  simp only [admit, cpuStep, noPhase, onCpu, onDevice]; (repeat' split) <;> br_close h

theorem breaker_afterReply (s : St) (ob : Bool) (k : Nat) (h : invBreaker s = true) :
    invBreaker (afterReply s ob k) = true := by
  unfold afterReply
  cases ob <;> by_cases hw : s.waiting = 1 <;>
    simp only [hw, ↓reduceIte, Bool.false_eq_true] <;> br_close h

theorem breaker_reply (s : St) (h : invBreaker s = true) : invBreaker (reply s) = true := by
  simp only [reply, serve]
  (repeat' split) <;> first
    | br_close h
    | exact breaker_afterReply _ _ _ (breaker_congr _ _ h rfl rfl (Nat.le_refl _))
    | exact breaker_afterReply _ _ _ (breaker_cleared _ rfl)

theorem breaker_crash (s : St) (h : invBreaker s = true) : invBreaker (crash s) = true := by
  unfold crash gone; br_close h

theorem breaker_apply (s : St) (op : Nat) (h : invBreaker s = true) :
    invBreaker (apply s op) = true := by
  unfold apply
  split
  · exact breaker_arrive s h
  · exact breaker_admit s _ _ h
  · unfold fault; split <;> br_close h
  · unfold readback; br_close h
  · unfold leaseLoss; br_close h
  · unfold finish; br_close h
  · unfold wipe; split <;> br_close h
  · exact breaker_reply s h
  · exact breaker_crash s h
  · simp only [restart]; split <;> br_close h
  · exact breaker_congr _ _ h rfl rfl (Nat.le_add_right _ _)
  · br_close h
  · br_close h
  · br_close h
  · exact h

/-! ## Every event keeps `Inv` -/

theorem stepRefusals_nil (s : St) (op : Nat) (h : stepRefusals s op = []) :
    stateOk s = true ∧ enabled s op = true ∧ (opCode op = 3 → argA op < reasons) ∧
      (opCode op = 4 → argA op ≤ 3) := by
  unfold stepRefusals at h
  split at h
  · simp at h
  · rename_i hs
    refine ⟨by simpa using hs, ?_⟩
    unfold opRefusals at h
    simp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hk
        split at h
        · simp at h
        · rename_i hb
          split at h
          · simp at h
          · rename_i he
            refine ⟨by simpa using he, fun h3 => ?_, fun h4 => ?_⟩
            · simp only [h3, true_and, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
                not_or] at hb
              omega
            · simp [h4] at hk
              omega

set_option maxHeartbeats 2000000 in
/-- Every transition keeps the invariant (all requirement IDs of `Inv`). -/
theorem inv_step (s : St) (op : Nat) (h : Inv s = true) : Inv (stepOp s op) = true := by
  unfold stepOp
  split
  · rename_i hr
    have hen := (stepRefusals_nil s op hr).2.1
    have harg := (stepRefusals_nil s op hr).2.2.1
    have hkind := (stepRefusals_nil s op hr).2.2.2
    simp only [Inv, InvCore, Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb'⟩, hb⟩ := h
    simp only [Inv, InvCore, Bool.and_eq_true]
    refine ⟨?_, breaker_apply s op hb⟩
    unfold apply
    unfold enabled at hen
    split <;> rename_i heq <;> simp only [heq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      bne_iff_ne, ne_eq, Bool.or_eq_true, proving, proved, accepted, wiped, idle] at hen
    next => exact ⟨a_arrive s ha, b_arrive s hb'⟩
    next => exact ⟨a_admit s _ _ ha hen.1 hen.2, b_admit s _ _ hb'⟩
    next => exact ⟨a_fault s _ ha (by simp_all [proving]) (by simp_all),
      b_fault s _ hb' (harg heq)⟩
    next => exact ⟨a_readback s _ ha, b_readback s _ hb' (hkind heq)⟩
    next => exact ⟨a_leaseLoss s ha (by simp_all [proving]), b_leaseLoss s hb'⟩
    next => exact ⟨a_finish s _ ha (by simp_all) (by simp_all [proving]),
      b_finish s _ hb'⟩
    next => exact ⟨a_wipe s _ ha (by simp_all) (by simp_all [proved]), b_wipe s _ hb'⟩
    next => exact ⟨a_reply s ha (by simp_all) (by simp_all [wiped]), b_reply s hb'⟩
    next => exact ⟨a_crash s ha, b_crash s hb'⟩
    next => exact ⟨a_restart s ha (by simp_all) (by simp_all), b_restart s hb'⟩
    next => exact ⟨a_tick s _ ha, b_tick s _ hb'⟩
    next => exact ⟨a_lock s _ ha (by simp_all [proving]), b_lock s _ hb'⟩
    next => exact ⟨a_evict s ha, b_evict s hb'⟩
    next => exact ⟨a_overBound s ha (by simp_all [proving, proved]), b_overBound s hb'⟩
    next => simp at hen
  · exact h

theorem inv_foldl (ops : List Nat) : ∀ s, Inv s = true → Inv (ops.foldl stepOp s) = true := by
  induction ops with
  | nil => intro s h; exact h
  | cons o os ih => intro s h; exact ih _ (inv_step s o h)

/-- Every state reachable from an accepted configuration satisfies `Inv`. -/
theorem inv_run (c : Config) (h : configRefusals c = []) (ops : List Nat) :
    Inv (run c ops) = true :=
  inv_foldl ops _ (inv_init c h)

/-! ## Theorems beyond `Inv` (each at the level of its requirement) -/

theorem recordFailures_up (k : Nat) (s : St) : (recordFailures k s).up = s.up :=
  (recordFailures_other k s).1
theorem recordFailures_errors (k : Nat) (s : St) : (recordFailures k s).errors = s.errors :=
  (recordFailures_other k s).2.2.1
theorem recordFailures_served (k : Nat) (s : St) : (recordFailures k s).served = s.served :=
  (recordFailures_other k s).2.2.2.1

theorem stepOp_of_ok (s : St) (op : Nat) (h : stepRefusals s op = []) : stepOp s op = apply s op := by
  simp [stepOp, h]

theorem stepOp_cases (s : St) (op : Nat) :
    (stepRefusals s op = [] ∧ stepOp s op = apply s op) ∨ stepOp s op = s := by
  unfold stepOp; split
  · exact .inl ⟨by assumption, rfl⟩
  · exact .inr rfl

/-- GPU-075: while the breaker is open an arrival changes only the request
count, the client's CPU count and the skip count: the daemon is not contacted. -/
theorem breaker_open_skips (s : St) (h : Inv s = true) (ho : s.clock < s.brOpenUntil) :
    stepOp s 1 = { s with requests := s.requests + 1, clientCpu := s.clientCpu + 1,
                          breakerSkips := s.breakerSkips + 1 } := by
  have hr : stepRefusals s 1 = [] := by
    simp [stepRefusals, stateOk, h, opRefusals, opCode, argA, argB, enabled]
  simp [stepOp, hr, apply, opCode, arrive, breakerOpen, ho]

theorem recordFailure_served (s : St) : (recordFailure s).served = s.served :=
  (recordFailure_other s).2.2.2.1

theorem afterReply_served (s : St) (ob : Bool) (k : Nat) : (afterReply s ob k).served = s.served := by
  unfold afterReply
  split
  · simp [recordFailures_served, gone]
  · split <;> simp [recordFailures_served]

theorem afterReply_brFails (s : St) (ob : Bool) (h : ob = false ∨ s.waiting = 0) :
    (afterReply s ob 0).brFails = s.brFails := by
  unfold afterReply
  split
  · rcases h with h | h
    · simp_all
    · simp [h, recordFailures, gone]
  · split <;> simp [recordFailures]

/-- The reply serves a proof only in its last branch. -/
theorem reply_served (s : St) (h : s.served < (reply s).served) :
    reply s = afterReply { (endRequest s) with
      served := s.served + 1, cold := false,
      degradedServed := s.degradedServed +
        (if (s.degraded || decide (0 < s.fallbacks)) then 1 else 0),
      runFailed := s.runFailed || (s.bench && (s.degraded || decide (0 < s.fallbacks))),
      unverifiedReturned := s.unverifiedReturned + (if s.verifyOk then 0 else 1),
      verifyAccepts := s.verifyAccepts + (if s.verifyOk then 1 else 0),
      brFails := [] } s.overBound 0 := by
  unfold reply serve at h ⊢
  by_cases c1 : (!s.wipeOk) = true
  · simp only [c1, ↓reduceIte, recordFailures_served, gone] at h; omega
  · by_cases c2 : (s.acceptance && (s.degraded || decide (0 < s.fallbacks))) = true
    · simp only [c1, c2, ↓reduceIte, Bool.false_eq_true, afterReply_served, endRequest] at h; omega
    · by_cases c3 : (!s.verifyOk) = true
      · simp only [c1, c2, c3, ↓reduceIte, Bool.false_eq_true, afterReply_served, endRequest] at h
        omega
      · simp only [c1, c2, c3, ↓reduceIte, Bool.false_eq_true]

theorem recordFailure_verifyAccepts (s : St) :
    (recordFailure s).verifyAccepts = s.verifyAccepts := by
  simp only [recordFailure]; split <;> rfl

theorem recordFailures_verifyAccepts (k : Nat) : ∀ s : St,
    (recordFailures k s).verifyAccepts = s.verifyAccepts := by
  induction k with
  | zero => intro s; rfl
  | succ k ih => intro s; simp only [recordFailures]; rw [ih, recordFailure_verifyAccepts]

theorem afterReply_verifyAccepts (s : St) (ob : Bool) (k : Nat) :
    (afterReply s ob k).verifyAccepts = s.verifyAccepts := by
  unfold afterReply
  split
  · simp [recordFailures_verifyAccepts, gone]
  · split <;> simp [recordFailures_verifyAccepts]

/-- GPU-039: the reply counts a verifier accept exactly when it serves a proof. -/
theorem reply_verify (s : St) :
    (reply s).verifyAccepts = s.verifyAccepts + (if s.served < (reply s).served then 1 else 0) := by
  unfold reply serve
  by_cases c1 : (!s.wipeOk) = true
  · simp [c1, recordFailures_served, recordFailures_verifyAccepts, gone]
  · by_cases c2 : (s.acceptance && (s.degraded || decide (0 < s.fallbacks))) = true
    · simp [c1, c2, afterReply_served, afterReply_verifyAccepts, endRequest]
    · by_cases c3 : (!s.verifyOk) = true
      · simp [c1, c2, c3, afterReply_served, afterReply_verifyAccepts, endRequest]
      · have hv : s.verifyOk = true := by simpa using c3
        simp [c1, c2, hv, afterReply_served, afterReply_verifyAccepts, endRequest]

/-- GPU-039: for every state, the count of verifier accepts rises at a reply
exactly when the reply serves a proof, and then by one. An accept is counted
where it is consumed: not at the end of the proof, not after an unconfirmed wipe
(the verifier does not run), not at an acceptance refusal, not at a refused
proof. A refused op 8 changes nothing. -/
theorem verify_counted_only_when_served (s : St) :
    (stepOp s 8).verifyAccepts =
      s.verifyAccepts + (if (stepOp s 8).served > s.served then 1 else 0) := by
  rcases stepOp_cases s 8 with ⟨_, he⟩ | he
  · have ha : apply s 8 = reply s := by simp [apply, opCode]
    rw [he, ha]
    exact reply_verify s
  · rw [he]; simp

/-- No other operation changes the count of verifier accepts. -/
theorem verify_count_other_ops (s : St) (op : Nat) (h : opCode op ≠ 8) :
    (stepOp s op).verifyAccepts = s.verifyAccepts := by
  rcases stepOp_cases s op with ⟨_, he⟩ | he
  · rw [he]
    unfold apply
    split
    all_goals first
      | (exfalso; exact h (by assumption))
      | rfl
      | (simp only [arrive, admit, cpuStep, noPhase, onCpu, onDevice, fault, readback, leaseLoss,
           finish, wipe, crash, restart, gone]
         repeat' split
         all_goals simp [recordFailure_verifyAccepts, recordFailures_verifyAccepts])
  · rw [he]

/-- GPU-076: a reply that serves a proof clears the failure record. The side
condition is needed: when the served request was over its bound and a caller
waits, the planned restart (GPU-050) records that caller's failure after the
clear (`served_then_restart`, pin `pin_served_then_overbound`). -/
theorem served_clears_failures (s : St) (h : s.served < (stepOp s 8).served)
    (hw : s.overBound = false ∨ s.waiting = 0) : (stepOp s 8).brFails = [] := by
  rcases stepOp_cases s 8 with ⟨_, he⟩ | he
  · have ha : apply s 8 = reply s := by simp [apply, opCode]
    rw [he, ha] at h ⊢
    rw [reply_served s h, afterReply_brFails _ _ (by simpa [endRequest] using hw)]
  · rw [he] at h; omega

/-- GPU-076, GPU-050: in the remaining case the record holds at most the one
failure of the waiting caller, at the current time: no older failure survives. -/
theorem served_then_restart (s : St) (h : s.served < (stepOp s 8).served) :
    (stepOp s 8).brFails = [] ∨ (stepOp s 8).brFails = [s.clock] := by
  rcases stepOp_cases s 8 with ⟨hr, he⟩ | he
  · by_cases hw : s.overBound = false ∨ s.waiting = 0
    · exact .inl (served_clears_failures s h hw)
    · have hinv : InvA s = true := by
        have := (stepRefusals_nil s 8 hr).1
        simp only [stateOk, Inv, InvCore, Bool.and_eq_true] at this; exact this.1.1
      have hw1 : s.waiting = 1 := by inv_unfold; grind
      have hob : s.overBound = true := by grind
      have ha : apply s 8 = reply s := by simp [apply, opCode]
      rw [he, ha] at h ⊢
      rw [reply_served s h]
      simp only [afterReply, endRequest, gone, hob, hw1, ↓reduceIte, recordFailures, recordFailure]
      split <;> simp
  · rw [he] at h; omega

/-- GPU-077: a busy reply is not a daemon failure: the record and the cooldown
are unchanged. -/
theorem busy_no_failure (s : St) (h : (stepOp s 1).busyReplies ≠ s.busyReplies) :
    (stepOp s 1).brFails = s.brFails ∧ (stepOp s 1).brOpenUntil = s.brOpenUntil := by
  rcases stepOp_cases s 1 with ⟨_, he⟩ | he
  · rw [he] at h ⊢
    have ha : apply s 1 = arrive s := by simp [apply, opCode]
    rw [ha] at h ⊢
    unfold arrive at h ⊢
    simp only at h ⊢
    repeat' split at h
    all_goals first
      | (exfalso; apply h; simp only [recordFailure]; split <;> rfl)
      | (exfalso; exact h rfl)
      | skip
    simp_all
  · rw [he]; exact ⟨rfl, rfl⟩

/-- GPU-078: in acceptance mode a reply to a degraded request (marked degraded
or with a fallback) serves no proof. -/
theorem acceptance_no_degraded_proof (s : St) (ha : s.acceptance = true)
    (hd : s.degraded = true ∨ 0 < s.fallbacks) : (stepOp s 8).served = s.served := by
  rcases stepOp_cases s 8 with ⟨_, he⟩ | he
  · rw [he]
    have hr : apply s 8 = reply s := by simp [apply, opCode]
    rw [hr]
    have hdeg : (s.degraded || decide (0 < s.fallbacks)) = true := by
      rcases hd with hd | hd <;> simp [hd]
    unfold reply afterReply
    cases h1 : s.wipeOk <;> cases h4 : s.overBound <;>
      simp [h1, h4, ha, hdeg, recordFailures_served, endRequest, gone] <;>
      (split <;> simp [recordFailures_served])
  · rw [he]

/-- The failures of the record that are still inside the window at the clock
(`now - t < brWindow`), before the new one is appended. -/
def keptFails (s : St) : List Nat := s.brFails.filter fun t => !decide (s.brWindow ≤ s.clock - t)

/-- GPU-075, GPU-077: the exact behaviour of recording one failure, for every
state. When the kept record already holds `max brLimit 1 - 1` failures (or
more), the new failure reaches the limit: the breaker opens until
`clock + brCooldown` and the record is emptied. Otherwise `brOpenUntil` keeps
its value and the clock is appended to the kept record. No other field changes
in either case. -/
theorem breaker_opens_at_limit (s : St) :
    (max s.brLimit 1 - 1 ≤ (keptFails s).length →
      recordFailure s = { s with brFails := [], brOpenUntil := s.clock + s.brCooldown }) ∧
    ((keptFails s).length < max s.brLimit 1 - 1 →
      recordFailure s = { s with brFails := keptFails s ++ [s.clock] }) := by
  constructor
  · intro h
    simp only [keptFails] at h ⊢
    simp [recordFailure]
    omega
  · intro h
    simp only [keptFails] at h ⊢
    simp [recordFailure]
    omega

/-- Recording a failure reads the record, the clock and the breaker settings only. -/
theorem recordFailure_breaker_congr (s t : St) (hf : t.brFails = s.brFails)
    (hc : t.clock = s.clock) (hw : t.brWindow = s.brWindow) (hl : t.brLimit = s.brLimit)
    (hd : t.brCooldown = s.brCooldown) (ho : t.brOpenUntil = s.brOpenUntil) :
    (recordFailure t).brFails = (recordFailure s).brFails ∧
    (recordFailure t).brOpenUntil = (recordFailure s).brOpenUntil := by
  simp only [recordFailure, hf, hc, hw, hl, hd]
  split <;> simp [ho]

/-- GPU-077, GPU-075, GPU-046: the failure classes of an arrival, for every
state, as an exact case split. An applied arrival with the breaker closed and
the daemon absent (`stopped ∨ ¬ up`) records one daemon failure: the breaker
record and the cooldown become those of `recordFailure s`. In every other case
(the arrival is refused, the breaker is open and the request is skipped, the
request is accepted, queued, or answered busy) `brFails` and `brOpenUntil`
keep their values.

This is not stated as "the record changes iff ...": with `brWindow = 0`,
`brFails = [clock]` and `brLimit ≥ 3`, recording a failure drops the old entry
and appends the clock, which gives the same list. -/
theorem arrive_failure_classes (s : St) :
    (stepRefusals s 1 = [] ∧ breakerOpen s = false ∧ (s.stopped = true ∨ s.up = false) →
      (stepOp s 1).brFails = (recordFailure s).brFails ∧
      (stepOp s 1).brOpenUntil = (recordFailure s).brOpenUntil) ∧
    (¬ (stepRefusals s 1 = [] ∧ breakerOpen s = false ∧ (s.stopped = true ∨ s.up = false)) →
      (stepOp s 1).brFails = s.brFails ∧ (stepOp s 1).brOpenUntil = s.brOpenUntil) := by
  have ha : apply s 1 = arrive s := by simp [apply, opCode]
  constructor
  · rintro ⟨hr, hb, habs⟩
    rw [stepOp_of_ok s 1 hr, ha]
    have habs' : (s.stopped || !s.up) = true := by rcases habs with h | h <;> simp [h]
    simp only [breakerOpen, decide_eq_false_iff_not] at hb
    simp only [arrive, breakerOpen, hb, decide_false, Bool.false_eq_true, ↓reduceIte, habs']
    exact recordFailure_breaker_congr s _ rfl rfl rfl rfl rfl rfl
  · intro hn
    rcases stepOp_cases s 1 with ⟨hr, he⟩ | he
    · rw [he, ha]
      by_cases hb : breakerOpen s = true
      · simp only [breakerOpen] at hb
        simp [arrive, breakerOpen, hb]
      · have hb' : breakerOpen s = false := by simpa using hb
        have hpres : ¬ (s.stopped = true ∨ s.up = false) := fun h => hn ⟨hr, hb', h⟩
        have h1 : s.stopped = false := by cases h : s.stopped <;> simp_all
        have h2 : s.up = true := by cases h : s.up <;> simp_all
        simp only [breakerOpen, decide_eq_false_iff_not] at hb'
        simp only [arrive, breakerOpen, hb', decide_false, Bool.false_eq_true, ↓reduceIte, h1, h2,
          Bool.not_true, Bool.or_self]
        split
        · split <;> exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
    · rw [he]; exact ⟨rfl, rfl⟩

theorem recordFailure_counters (s : St) :
    (recordFailure s).clientCpu = s.clientCpu ∧
    (recordFailure s).degradedRefused = s.degradedRefused := by
  simp only [recordFailure]; split <;> exact ⟨rfl, rfl⟩

theorem recordFailures_counters (k : Nat) : ∀ s : St,
    (recordFailures k s).clientCpu = s.clientCpu ∧
    (recordFailures k s).degradedRefused = s.degradedRefused := by
  induction k with
  | zero => intro s; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro s
    simp only [recordFailures]
    rw [(ih _).1, (ih _).2]
    exact recordFailure_counters s

/-- GPU-078, GPU-021, GPU-077, GPU-039: an applied reply in acceptance mode to a
degraded request (marked degraded or with a fallback count above zero) after a
confirmed wipe, for every state: no proof is served, one error and one degraded
refusal are counted, the caller proves on its CPU, and the count of verifier
accepts keeps its value (the verifier's answer is not used). The breaker record
and the cooldown keep their values: a degraded error is not a daemon failure.

Two of the clauses carry the planned restart of GPU-050, which follows the reply
when the request was over its bound: a waiting caller then proves on its CPU and
records a failure. So `clientCpu` rises by `1 + (if overBound then waiting else
0)`, and the breaker is unchanged when `overBound = false ∨ waiting = 0`. Without
that condition the breaker clause is false: with `overBound`, `waiting = 1` the
restart records the waiting caller's failure. -/
theorem acceptance_degraded_refused (s : St) (hr : stepRefusals s 8 = [])
    (hw : s.wipeOk = true) (ha : s.acceptance = true)
    (hd : s.degraded = true ∨ 0 < s.fallbacks) :
    (stepOp s 8).served = s.served ∧ (stepOp s 8).errors = s.errors + 1 ∧
    (stepOp s 8).degradedRefused = s.degradedRefused + 1 ∧
    (stepOp s 8).verifyAccepts = s.verifyAccepts ∧
    (stepOp s 8).clientCpu = s.clientCpu + 1 + (if s.overBound then s.waiting else 0) ∧
    (s.overBound = false ∨ s.waiting = 0 →
      (stepOp s 8).brFails = s.brFails ∧ (stepOp s 8).brOpenUntil = s.brOpenUntil) := by
  have hap : apply s 8 = reply s := by simp [apply, opCode]
  have hdeg : (s.degraded || decide (0 < s.fallbacks)) = true := by
    rcases hd with hd | hd <;> simp [hd]
  rw [stepOp_of_ok s 8 hr, hap]
  unfold reply afterReply
  simp only [hw, ha, hdeg, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_self]
  cases ho : s.overBound
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : s.waiting = 1
    · simp [h1, recordFailures, endRequest]
    · simp [h1, recordFailures, endRequest]
  · simp only [↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [recordFailures_served, gone, endRequest]
    · simp [recordFailures_errors, gone, endRequest]
    · simp [(recordFailures_counters _ _).2, gone, endRequest]
    · simp [recordFailures_verifyAccepts, gone, endRequest]
    · simp [(recordFailures_counters _ _).1, gone, endRequest]
    · intro h
      have hz : s.waiting = 0 := by simpa using h
      simp [hz, recordFailures, gone, endRequest]

/-- The side condition of `acceptance_degraded_refused` is needed: over the bound
with a caller waiting, the planned restart after the degraded error records the
waiting caller's failure (GPU-050, GPU-077). -/
theorem acceptance_degraded_refused_needs_side :
    let s := (List.foldl stepOp (init { defaultConfig with acceptance := true })
      [1, 1, 2 + 2000 + 200000, 503, 14, 106, 107])
    stepRefusals s 8 = [] ∧ s.wipeOk = true ∧ s.overBound = true ∧ s.waiting = 1 ∧
    s.brFails = [] ∧ (stepOp s 8).brFails = [0] ∧ (stepOp s 8).clientCpu = s.clientCpu + 2 := by
  decide +kernel

/-- GPU-073, GPU-012, GPU-085: an applied decline with reason `r` adds one to
the total and one to exactly entry `r` of the counts. It adds one fallback and
marks the request degraded exactly when `r` is a fallback reason (2 to 6); with
reason 0 or 1 the fallback count and the mark keep their values. -/
theorem decline_counted (s : St) (op : Nat) (hc : opCode op = 3)
    (hr : stepRefusals s op = []) :
    argA op < reasons ∧
    (stepOp s op).declined = s.declined + 1 ∧
    (stepOp s op).fallbacks = s.fallbacks + (if 2 ≤ argA op then 1 else 0) ∧
    (stepOp s op).degraded = (s.degraded || decide (2 ≤ argA op)) ∧
    ∀ i, (stepOp s op).declines.getD i 0 = s.declines.getD i 0 + (if i = argA op then 1 else 0) := by
  have hn := stepRefusals_nil s op hr
  have hlt := hn.2.2.1 hc
  have hl : s.declines.length = reasons := by
    have := hn.1
    simp only [stateOk] at this
    inv_unfold; grind
  have ha : apply s op = fault s (argA op) := by simp [apply, hc]
  rw [stepOp_of_ok s op hr, ha]
  refine ⟨hlt, ?_, ?_, ?_, fun i => ?_⟩
  · unfold fault; split <;> rfl
  · unfold fault; split <;> simp [*]
  · unfold fault; split <;> simp [*]
  · have := countAt_getD s.declines (argA op) i (by omega)
    unfold fault; split <;> exact this

/-- GPU-085: a decline by design (reason 0 no-device or 1 below-min-k) changes
the two decline counts and nothing else: no fallback, no degraded mark, every
other field as it was. -/
theorem expected_decline_no_fallback (s : St) (r : Nat) (h : r < 2) :
    fault s r = { s with declines := countAt s.declines r, declined := s.declined + 1 } := by
  have : ¬ 2 ≤ r := by omega
  simp [fault, this]

/-- The same through `stepOp`: an applied decline with reason 0 or 1. -/
theorem expected_decline_step (s : St) (op : Nat) (hc : opCode op = 3) (ha : argA op < 2)
    (hr : stepRefusals s op = []) :
    stepOp s op = { s with declines := countAt s.declines (argA op), declined := s.declined + 1 } := by
  have hap : apply s op = fault s (argA op) := by simp [apply, hc]
  rw [stepOp_of_ok s op hr, hap, expected_decline_no_fallback s _ ha]

/-- GPU-012: a decline with a fallback reason (2 to 6) is one fallback and marks
the request degraded. -/
theorem fallback_decline (s : St) (r : Nat) (h : 2 ≤ r) :
    fault s r = { s with fallbacks := s.fallbacks + 1, degraded := true,
                         declines := countAt s.declines r, declined := s.declined + 1 } := by
  simp [fault, h]

/-- GPU-083: with no window (`window = 0`) and the limit reached, the supervisor
leaves the daemon stopped after any amount of time: the clock is not read. -/
theorem lifetime_cap (s : St) (d : Nat) (hw : s.window = 0)
    (hl : s.limit ≤ s.restartTimes.length) :
    (restart { s with clock := s.clock + d }).stopped = true ∧
    (restart { s with clock := s.clock + d }).up = s.up ∧
    (restart { s with clock := s.clock + d }).restartTimes = s.restartTimes := by
  have hn : ¬ s.restartTimes.length < s.limit := by omega
  simp [restart, recent, hw, hn]

/-- GPU-082: a confirmed wipe frees the MSM tables under either resident policy. -/
theorem wipe_frees_tables (s : St) : (wipe s true).tables = false := by
  simp [wipe]

theorem wipe_frees_tables_step (s : St) (op : Nat) (hc : opCode op = 7) (ha : argA op = 1)
    (hr : stepRefusals s op = []) : (stepOp s op).tables = false := by
  rw [stepOp_of_ok s op hr]
  simp [apply, hc, ha, flag, wipe]

/-- GPU-035: the reply after an unconfirmed wipe is an error, serves nothing
and leaves the daemon down. -/
theorem wipe_fail_retires (s : St) (hw : s.wipeOk = false) (hr : stepRefusals s 8 = []) :
    (stepOp s 8).up = false ∧ (stepOp s 8).errors = s.errors + 1 ∧
    (stepOp s 8).served = s.served := by
  rw [stepOp_of_ok s 8 hr]
  simp [apply, opCode, reply, hw, recordFailures_up, recordFailures_errors, recordFailures_served,
    gone]

/-- GPU-048, GPU-049, GPU-083: after the supervisor acts, at most `limit`
restarts are on record, and when `limit` restarts are recent (inside the
window; with `window = 0` every restart on record is recent, `recent_no_window`)
the daemon stays stopped. -/
theorem restart_cap (s : St) (h : Inv s = true) :
    (stepOp s 10).restartTimes.length ≤ s.limit ∧
    (s.up = false → s.limit ≤ (recent s).length →
      (stepOp s 10).stopped = true ∧ (stepOp s 10).up = false) := by
  have hi := inv_step s 10 h
  refine ⟨?_, fun hu hl => ?_⟩
  · have hlim : (stepOp s 10).limit = s.limit := by
      rcases stepOp_cases s 10 with ⟨_, he⟩ | he
      · rw [he]; simp only [apply, opCode, restart]; split <;> rfl
      · rw [he]
    have : (stepOp s 10).restartTimes.length ≤ (stepOp s 10).limit := by
      simp only [Inv, InvCore, InvA, invRestart, Bool.and_eq_true, decide_eq_true_eq] at hi
      grind
    omega
  · rcases stepOp_cases s 10 with ⟨_, he⟩ | he
    · rw [he]
      have : ¬ (recent s).length < s.limit := by omega
      simp [apply, opCode, restart, this, hu]
    · rw [he]
      refine ⟨?_, hu⟩
      -- refused: the state is in `Inv` and the daemon is down, so it was already stopped
      cases hs : s.stopped
      · exfalso
        have : stepRefusals s 10 = [] := by
          simp [stepRefusals, stateOk, h, opRefusals, opCode, argA, argB, enabled, hu, hs]
        simp [stepOp, this, apply, opCode, restart] at he
        have hne : ¬ (recent s).length < s.limit := by omega
        simp [hne] at he
        have := congrArg St.stopped he
        simp [hs] at this
      · rfl

end GpuSpec.Service
