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

import GpuSpec.Hooks
import GpuSpec.Ntt

/-!
# Decline reasons, decline counts and the entry gate (GPU-073, GPU-074, GPU-010, GPU-012)

A device operation that declines gives one reason out of seven. The crate
counts each decline once, under the class of the operation and under that
reason (GPU-073). The daemon counts one fallback per decline with a fallback
reason (shape, unreduced, memory, fault, device-error: GPU-012) and none for a
decline by design (no-device, below-min-k: GPU-085). The proof does not depend
on the reasons.

The entry gate is the part of a hook that runs before any buffer is touched. It
is a function of the input shape, so its declines leave the caller buffer
unchanged (GPU-010, GPU-074). The reasons `memory`, `fault` and `device-error`
come after the gate and are not decided here.
-/

namespace GpuSpec

/-- The decline reasons. The order is a wire contract (`Reason.index`). -/
inductive Reason where
  | noDevice | belowMinK | shape | unreduced | memory | fault | deviceError
  deriving Repr, DecidableEq

def Reason.code : Reason → String
  | .noDevice => "no-device"
  | .belowMinK => "below-min-k"
  | .shape => "shape"
  | .unreduced => "unreduced"
  | .memory => "memory"
  | .fault => "fault"
  | .deviceError => "device-error"

def Reason.index : Reason → Nat
  | .noDevice => 0
  | .belowMinK => 1
  | .shape => 2
  | .unreduced => 3
  | .memory => 4
  | .fault => 5
  | .deviceError => 6

def Reason.all : List Reason :=
  [.noDevice, .belowMinK, .shape, .unreduced, .memory, .fault, .deviceError]

def Kind.all : List Kind := [.msm, .ntt, .intt, .quotient]

theorem Reason.all_complete (r : Reason) : r ∈ Reason.all := by cases r <;> decide
theorem Reason.all_nodup : Reason.all.Nodup := by decide
theorem Kind.all_complete (k : Kind) : k ∈ Kind.all := by cases k <;> decide
theorem Kind.all_nodup : Kind.all.Nodup := by decide

/-- The wire index is the position in `Reason.all`, and the codes differ. -/
theorem Reason.index_order : Reason.all.map Reason.index = [0, 1, 2, 3, 4, 5, 6] := by decide
theorem Reason.code_injective (a b : Reason) (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (revert h; decide)

/-- A device answer with its decline reason. -/
inductive Answer where
  | value (v : List Nat)
  | decline (r : Reason)
  deriving Repr, DecidableEq

/-- A device that says why it declines. Like `Device`, the answer may depend on
the position of the event: the same call can be answered once and declined at a
later occurrence. -/
abbrev RDevice := Nat → Call → Answer

/-- Forget the reason. -/
def RDevice.toDevice (dev : RDevice) : Device := fun i c =>
  match dev i c with
  | .value v => some v
  | .decline _ => none

/-- GPU-007 for a device with reasons, at every occurrence of every call. -/
def RHonest (ref : Call → List Nat) (dev : RDevice) : Prop :=
  ∀ i c v, dev i c = .value v → v = ref c

theorem RHonest.toDevice {ref : Call → List Nat} {dev : RDevice} (h : RHonest ref dev) :
    Honest ref dev.toDevice := by
  intro i c v hv
  unfold RDevice.toDevice at hv
  cases hd : dev i c with
  | value w => rw [hd] at hv; cases hv; exact h i c v hd
  | decline r => rw [hd] at hv; cases hv

/-- GPU-012, GPU-085: the reasons that are a fallback. `shape`, `unreduced`,
`memory`, `fault` and `device-error` mean the device was asked and the CPU code
ran in its place. `no-device` and `below-min-k` are declines by design: counted
(GPU-073), no fallback, and the proof stays unmarked. -/
def Reason.isFallback : Reason → Bool
  | .noDevice | .belowMinK => false
  | .shape | .unreduced | .memory | .fault | .deviceError => true

/-- On the wire the fallback reasons are the indices from 2 (the test of
`Service.fault`). -/
theorem Reason.isFallback_index (r : Reason) : r.isFallback = decide (2 ≤ r.index) := by
  cases r <;> decide

/-- The fallback reasons, in wire order. -/
def Reason.fallbacks : List Reason := [.shape, .unreduced, .memory, .fault, .deviceError]

/-- They are exactly the reasons with `isFallback`. -/
theorem Reason.fallbacks_eq : Reason.all.filter Reason.isFallback = Reason.fallbacks := by decide

/-- Decline counts: one cell for each operation class and reason. -/
abbrev Counts := Kind → Reason → Nat

def Counts.zero : Counts := fun _ _ => 0

/-- Add one to the cell `(k, r)`. -/
def Counts.bump (cs : Counts) (k : Kind) (r : Reason) : Counts :=
  fun k' r' => cs k' r' + if k' = k ∧ r' = r then 1 else 0

/-- The sum of all cells. -/
def Counts.total (cs : Counts) : Nat := (Kind.all.map fun k => (Reason.all.map (cs k)).sum).sum

/-- The sum of the cells of the fallback reasons. -/
def Counts.fallbackTotal (cs : Counts) : Nat :=
  (Kind.all.map fun k => (Reason.fallbacks.map (cs k)).sum).sum

/-- One event with its position in the event list (`List.zipIdx`). -/
def countStep (dev : RDevice) (cs : Counts) : Event × Nat → Counts
  | (.op c, i) =>
    match dev i c with
    | .decline r => cs.bump c.kind r
    | .value _ => cs
  | _ => cs

/-- GPU-073: the decline counts after a list of events. -/
def countDeclines (dev : RDevice) (evs : List Event) : Counts :=
  evs.zipIdx.foldl (countStep dev) Counts.zero

/-- Is the event an operation of class `k` that the device declines with reason `r`? -/
def declinedAs (dev : RDevice) (k : Kind) (r : Reason) : Event × Nat → Bool
  | (.op c, i) => c.kind = k && dev i c = .decline r
  | _ => false

/-- The reason of the decline, when the event is an operation that the device declines. -/
def declineReason (dev : RDevice) : Event × Nat → Option Reason
  | (.op c, i) =>
    match dev i c with
    | .decline r => some r
    | .value _ => none
  | _ => none

/-- Is the event an operation that the device declines? -/
def isDeclined (dev : RDevice) (ie : Event × Nat) : Bool := (declineReason dev ie).isSome

/-- Is the event an operation that the device declines with a fallback reason? -/
def isFallbackDecline (dev : RDevice) (ie : Event × Nat) : Bool :=
  (declineReason dev ie).any Reason.isFallback

/-- Is the event an operation that the device declines by design (no-device, below-min-k)? -/
def isExpectedDecline (dev : RDevice) (ie : Event × Nat) : Bool :=
  (declineReason dev ie).any fun r => !r.isFallback

/-- The number of operation events that the device declines. -/
def declinedOps (dev : RDevice) (evs : List Event) : Nat :=
  (evs.zipIdx.filter (isDeclined dev)).length

/-- GPU-012: the number of operation events that the device declines with a
fallback reason: the daemon's fallback count. -/
def fallbackOps (dev : RDevice) (evs : List Event) : Nat :=
  (evs.zipIdx.filter (isFallbackDecline dev)).length

/-- GPU-085: the number of declines by design. -/
def expectedOps (dev : RDevice) (evs : List Event) : Nat :=
  (evs.zipIdx.filter (isExpectedDecline dev)).length

theorem Counts.total_bump (cs : Counts) (k : Kind) (r : Reason) :
    (cs.bump k r).total = cs.total + 1 := by
  cases k <;> cases r <;> simp [Counts.total, Counts.bump, Kind.all, Reason.all] <;> omega

theorem Counts.fallbackTotal_bump (cs : Counts) (k : Kind) (r : Reason) :
    (cs.bump k r).fallbackTotal = cs.fallbackTotal + (if r.isFallback then 1 else 0) := by
  cases k <;> cases r <;>
    simp [Counts.fallbackTotal, Counts.bump, Kind.all, Reason.fallbacks, Reason.isFallback] <;>
    omega

/-- GPU-073: one declined call raises exactly one cell, the cell of its class
and its reason, by one; every other cell keeps its value. -/
theorem count_one_reason (dev : RDevice) (cs : Counts) (c : Call) (i : Nat) (r : Reason)
    (h : dev i c = .decline r) (k' : Kind) (r' : Reason) :
    countStep dev cs (.op c, i) k' r' = cs k' r' + (if k' = c.kind ∧ r' = r then 1 else 0) := by
  simp [countStep, h, Counts.bump]

/-- An answered call, a blinding draw and a squeeze change no cell. -/
theorem count_no_decline (dev : RDevice) (cs : Counts) (ie : Event × Nat)
    (h : isDeclined dev ie = false) : countStep dev cs ie = cs := by
  obtain ⟨e, i⟩ := ie
  cases e with
  | op c =>
    cases hd : dev i c with
    | value v => simp [countStep, hd]
    | decline r => simp [isDeclined, declineReason, hd] at h
  | blind _ => rfl
  | squeeze => rfl

theorem countStep_total (dev : RDevice) (cs : Counts) (ie : Event × Nat) :
    (countStep dev cs ie).total = cs.total + (if isDeclined dev ie then 1 else 0) := by
  obtain ⟨e, i⟩ := ie
  cases e with
  | op c =>
    cases hd : dev i c with
    | value v => simp [countStep, isDeclined, declineReason, hd]
    | decline r => simp [countStep, isDeclined, declineReason, hd, Counts.total_bump]
  | blind _ => simp [countStep, isDeclined, declineReason]
  | squeeze => simp [countStep, isDeclined, declineReason]

theorem countStep_fallbackTotal (dev : RDevice) (cs : Counts) (ie : Event × Nat) :
    (countStep dev cs ie).fallbackTotal =
      cs.fallbackTotal + (if isFallbackDecline dev ie then 1 else 0) := by
  obtain ⟨e, i⟩ := ie
  cases e with
  | op c =>
    cases hd : dev i c with
    | value v => simp [countStep, isFallbackDecline, declineReason, hd]
    | decline r =>
      simp [countStep, isFallbackDecline, declineReason, hd, Counts.fallbackTotal_bump]
  | blind _ => simp [countStep, isFallbackDecline, declineReason]
  | squeeze => simp [countStep, isFallbackDecline, declineReason]

theorem count_foldl_total (dev : RDevice) : ∀ (ies : List (Event × Nat)) (cs : Counts),
    (ies.foldl (countStep dev) cs).total = cs.total + (ies.filter (isDeclined dev)).length
  | [], cs => by simp
  | ie :: ies, cs => by
    rw [List.foldl_cons, count_foldl_total dev ies, countStep_total]
    cases h : isDeclined dev ie <;> simp [h] <;> omega

theorem count_foldl_fallbackTotal (dev : RDevice) : ∀ (ies : List (Event × Nat)) (cs : Counts),
    (ies.foldl (countStep dev) cs).fallbackTotal =
      cs.fallbackTotal + (ies.filter (isFallbackDecline dev)).length
  | [], cs => by simp
  | ie :: ies, cs => by
    rw [List.foldl_cons, count_foldl_fallbackTotal dev ies, countStep_fallbackTotal]
    cases h : isFallbackDecline dev ie <;> simp [h] <;> omega

theorem count_foldl_cell (dev : RDevice) (k : Kind) (r : Reason) :
    ∀ (ies : List (Event × Nat)) (cs : Counts),
      (ies.foldl (countStep dev) cs) k r = cs k r + (ies.filter (declinedAs dev k r)).length
  | [], cs => by simp
  | ie :: ies, cs => by
    rw [List.foldl_cons, count_foldl_cell dev k r ies]
    obtain ⟨e, i⟩ := ie
    cases e with
    | op c =>
      cases hd : dev i c with
      | value v => simp [countStep, declinedAs, hd]
      | decline r0 =>
        by_cases hk : c.kind = k <;> by_cases hr : r0 = r
        · subst hr; simp [countStep, declinedAs, hd, Counts.bump, hk]; omega
        · have hr' : ¬ r = r0 := fun h => hr h.symm
          simp [countStep, declinedAs, hd, Counts.bump, hk, hr, hr']
        · have hk' : ¬ k = c.kind := fun h => hk h.symm
          simp [countStep, declinedAs, hd, Counts.bump, hk, hk']
        · have hk' : ¬ k = c.kind := fun h => hk h.symm
          simp [countStep, declinedAs, hd, Counts.bump, hk, hk']
    | blind _ => simp [countStep, declinedAs]
    | squeeze => simp [countStep, declinedAs]

/-- GPU-073, per cell: the count of class `k` and reason `r` is the number of
operation events of class `k` that the device declined with reason `r`. -/
theorem countDeclines_cell (dev : RDevice) (evs : List Event) (k : Kind) (r : Reason) :
    countDeclines dev evs k r = (evs.zipIdx.filter (declinedAs dev k r)).length := by
  simp [countDeclines, count_foldl_cell, Counts.zero]

/-- A decline is a fallback or a decline by design, never both. -/
theorem decline_split (dev : RDevice) : ∀ ies : List (Event × Nat),
    (ies.filter (isDeclined dev)).length =
      (ies.filter (isFallbackDecline dev)).length + (ies.filter (isExpectedDecline dev)).length
  | [] => rfl
  | ie :: ies => by
    have ih := decline_split dev ies
    simp only [List.filter_cons]
    cases hr : declineReason dev ie with
    | none => simpa [isDeclined, isFallbackDecline, isExpectedDecline, hr] using ih
    | some r =>
      cases hf : r.isFallback <;>
        simp [isDeclined, isFallbackDecline, isExpectedDecline, hr, hf] <;> omega

/-- GPU-012, GPU-085: the daemon's fallback count (`fallbackOps`: the declines
with a fallback reason) is the sum of the decline counts over the fallback
reasons (shape, unreduced, memory, fault, device-error) and every class. It is
at most the number of declined operations, and equal to it exactly when no
decline is by design (no-device, below-min-k). No hypothesis on the device. -/
theorem fallbacks_by_reason (dev : RDevice) (evs : List Event) :
    (countDeclines dev evs).fallbackTotal = fallbackOps dev evs ∧
    declinedOps dev evs = fallbackOps dev evs + expectedOps dev evs ∧
    fallbackOps dev evs ≤ declinedOps dev evs ∧
    (fallbackOps dev evs = declinedOps dev evs ↔ expectedOps dev evs = 0) := by
  have h1 : (countDeclines dev evs).fallbackTotal = fallbackOps dev evs := by
    have h := count_foldl_fallbackTotal dev evs.zipIdx Counts.zero
    have z : Counts.zero.fallbackTotal = 0 := by decide
    unfold countDeclines fallbackOps
    omega
  have h2 : declinedOps dev evs = fallbackOps dev evs + expectedOps dev evs :=
    decline_split dev evs.zipIdx
  exact ⟨h1, h2, by omega, by omega⟩

/-- One prover step raises the CPU-resolution count by one exactly on a declined call. -/
theorem proveStep_fallbacks (ref : Call → List Nat) (dev : RDevice) (r : Run) (e : Event) :
    (proveStep ref dev.toDevice r e).fallbacks =
      r.fallbacks + (if isDeclined dev (e, r.pos) then 1 else 0) := by
  cases e with
  | op c =>
    cases hd : dev r.pos c <;>
      simp [proveStep, RDevice.toDevice, isDeclined, declineReason, hd]
  | blind src =>
    cases src
    · cases hr : r.rng <;> simp [proveStep, hr, isDeclined, declineReason]
    · cases hr : r.osRng <;> simp [proveStep, hr, isDeclined, declineReason]
  | squeeze => simp [proveStep, isDeclined, declineReason]

theorem fallbacks_foldl (ref : Call → List Nat) (dev : RDevice) : ∀ (evs : List Event) (r : Run),
    (evs.foldl (proveStep ref dev.toDevice) r).fallbacks =
      r.fallbacks + ((evs.zipIdx r.pos).filter (isDeclined dev)).length
  | [], r => by simp
  | e :: evs, r => by
    rw [List.foldl_cons, fallbacks_foldl ref dev evs, proveStep_fallbacks, proveStep_pos,
      List.zipIdx_cons, List.filter_cons]
    cases h : isDeclined dev (e, r.pos) <;> simp <;> omega

/-- GPU-073: for every device and every event list, the sum of all decline
counts (over the classes and the reasons) is the number of operation events the
device declined, and that is the `fallbacks` field of the prover run of
`Hooks.lean` on the same device with the reasons forgotten. That field counts
the CPU resolutions, expected ones included: every declined call is resolved by
the stock CPU function, whatever the reason. The daemon's fallback count of
GPU-012 is smaller: it is `fallbackOps`, the declines with a fallback reason
(`fallbacks_by_reason`; the service transition `Service.fault` adds exactly
that, `service_fallbacks_eq_fallbackOps` in `PinsExt.lean`). No hypothesis on
the device. -/
theorem declines_all_counted (ref : Call → List Nat) (dev : RDevice) (evs : List Event)
    (rng osRng : List Nat) :
    (countDeclines dev evs).total = declinedOps dev evs ∧
    (prove ref dev.toDevice evs rng osRng).fallbacks = declinedOps dev evs := by
  have h1 : (countDeclines dev evs).total = declinedOps dev evs := by
    have h := count_foldl_total dev evs.zipIdx Counts.zero
    have z : Counts.zero.total = 0 := by decide
    unfold countDeclines declinedOps
    omega
  refine ⟨h1, ?_⟩
  rw [prove, fallbacks_foldl]
  simp [Run.start, declinedOps]

/-- `prove_any_schedule` for a device with reasons: the transcript, the draw
count of each source and both remaining random streams are those of the
CPU-only prover. -/
theorem prove_any_reasons (ref : Call → List Nat) (dev : RDevice) (h : RHonest ref dev)
    (evs : List Event) (rng osRng : List Nat) :
    (prove ref dev.toDevice evs rng osRng).proof.transcript =
      (prove ref cpuOnly evs rng osRng).proof.transcript ∧
    (prove ref dev.toDevice evs rng osRng).proof.drawn =
      (prove ref cpuOnly evs rng osRng).proof.drawn ∧
    (prove ref dev.toDevice evs rng osRng).proof.drawnOs =
      (prove ref cpuOnly evs rng osRng).proof.drawnOs ∧
    (prove ref dev.toDevice evs rng osRng).rng = (prove ref cpuOnly evs rng osRng).rng ∧
    (prove ref dev.toDevice evs rng osRng).osRng = (prove ref cpuOnly evs rng osRng).osRng :=
  prove_any_schedule ref dev.toDevice h.toDevice evs rng osRng

/-- The proof does not depend on the reasons, nor on which calls decline: two
honest devices give the same proof whatever reasons each gives. -/
theorem prove_reason_independent (ref : Call → List Nat) (d1 d2 : RDevice)
    (h1 : RHonest ref d1) (h2 : RHonest ref d2) (evs : List Event) (rng osRng : List Nat) :
    (prove ref d1.toDevice evs rng osRng).proof = (prove ref d2.toDevice evs rng osRng).proof :=
  prove_two_devices ref d1.toDevice d2.toDevice h1.toDevice h2.toDevice evs rng osRng

/-! ## The entry gate (GPU-074, GPU-010) -/

/-- `n` is a power of two (`n = 2 ^ ⌊log2 n⌋`; false at 0). -/
def isPow2 (n : Nat) : Bool := n == 2 ^ n.log2

theorem isPow2_iff (n : Nat) : isPow2 n = true ↔ ∃ k, n = 2 ^ k := by
  unfold isPow2
  constructor
  · intro h; exact ⟨n.log2, by simpa using h⟩
  · rintro ⟨k, rfl⟩; simp [Nat.log2_two_pow]

/-- The transform gate: the decline reason, or `none` when the kernel runs. The
tests run in this order: shape (fewer than two elements, not a power of two,
above `2^maxLog`), below-min-k, no-device, unreduced. Ruling ORACLE-27: a
transform of one element is a `shape` decline, like the empty input; the kernel
takes sizes from 2 (`deviceSize`). -/
def gate (minK maxLog : Nat) (devicePresent reduced : Bool) (len : Nat) : Option Reason :=
  if len < 2 ∨ isPow2 len = false ∨ 2 ^ maxLog < len then some .shape
  else if len < 2 ^ minK then some .belowMinK
  else if devicePresent = false then some .noDevice
  else if reduced = false then some .unreduced
  else none

/-- The MSM gate: the same without the power-of-two test, and from one element
(an MSM of one point is valid; only the empty input is a `shape` decline). -/
def gateMsm (minK maxLog : Nat) (devicePresent reduced : Bool) (len : Nat) : Option Reason :=
  if len = 0 ∨ 2 ^ maxLog < len then some .shape
  else if len < 2 ^ minK then some .belowMinK
  else if devicePresent = false then some .noDevice
  else if reduced = false then some .unreduced
  else none

/-- GPU-010: the MSM gate on both lengths. The hook's first test is
`n == 0 || n != bases.len()`: a scalar count that differs from the base count
(longer or shorter) is a `shape` decline. With equal lengths the decision is
`gateMsm` on that length. -/
def gateMsm2 (minK maxLog : Nat) (devicePresent reduced : Bool) (scalars bases : Nat) :
    Option Reason :=
  if scalars ≠ bases then some .shape else gateMsm minK maxLog devicePresent reduced scalars

/-- GPU-010: the coset shift the kernel takes is a primitive cube root of unity
(`zeta^3 = 1` and `zeta ≠ 1` in the field; the periodic factors are
`1, zeta, zeta^2`). Any other shift is a `shape` decline. -/
def gateShift (p zeta : Nat) : Option Reason :=
  if powM p zeta 3 = 1 % p ∧ zeta % p ≠ 1 % p then none else some .shape

/-- GPU-010, ORACLE-27: an input of fewer than two elements (empty or one
element), a length that is not a power of two, or a length above `2^maxLog` is a
`shape` decline, and nothing else is. -/
theorem gate_shape (minK maxLog : Nat) (dp red : Bool) (len : Nat) :
    gate minK maxLog dp red len = some .shape ↔
      len < 2 ∨ (¬ ∃ k, len = 2 ^ k) ∨ 2 ^ maxLog < len := by
  have hc : (len < 2 ∨ isPow2 len = false ∨ 2 ^ maxLog < len) ↔
      (len < 2 ∨ (¬ ∃ k, len = 2 ^ k) ∨ 2 ^ maxLog < len) := by
    rw [← isPow2_iff]; simp
  rw [← hc]
  unfold gate
  constructor
  · intro h
    split at h
    · assumption
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> cases h
  · intro h
    simp [h]

/-- GPU-074 (transform): a power-of-two length from 2 that is below `2^minK`
declines with `below-min-k`. `minK ≤ maxLog` is needed: with `minK = 5`,
`maxLog = 3` the length 16 is above the kernel's range and declines with
`shape` (`gate_below_min_k_needs_config`). `2 ≤ len` is needed: the length 1 is
a power of two below `2^1` and declines with `shape`
(`gate_below_min_k_needs_two`). -/
theorem gate_below_min_k (minK maxLog : Nat) (dp red : Bool) (len : Nat) (hcfg : minK ≤ maxLog)
    (h2 : 2 ≤ len) (hpow : ∃ k, len = 2 ^ k) (hlt : len < 2 ^ minK) :
    gate minK maxLog dp red len = some .belowMinK := by
  have hp := (isPow2_iff len).mpr hpow
  have hle : 2 ^ minK ≤ 2 ^ maxLog := Nat.pow_le_pow_right (by decide) hcfg
  have h0 : ¬ len < 2 := by omega
  have h3 : ¬ 2 ^ maxLog < len := by omega
  simp [gate, hp, h0, h3, hlt]

theorem gate_below_min_k_needs_config : gate 5 3 true true 16 = some .shape := by decide +kernel

/-- The counterexample to `gate_below_min_k` without `2 ≤ len`: length 1 is
`2^0`, at least one element and below `2^1`, and the gate answers `shape`. -/
theorem gate_below_min_k_needs_two :
    gate 1 28 true true 1 = some .shape ∧ (∃ k, 1 = 2 ^ k) ∧ 1 < 2 ^ 1 := by
  refine ⟨by decide +kernel, ⟨0, rfl⟩, by decide⟩

/-- GPU-074 (MSM), as the sentence reads: any length from 1 below `2^minK`. -/
theorem gateMsm_below_min_k (minK maxLog : Nat) (dp red : Bool) (len : Nat) (hcfg : minK ≤ maxLog)
    (h1 : 1 ≤ len) (hlt : len < 2 ^ minK) : gateMsm minK maxLog dp red len = some .belowMinK := by
  have hle : 2 ^ minK ≤ 2 ^ maxLog := Nat.pow_le_pow_right (by decide) hcfg
  have h0 : len ≠ 0 := by omega
  have h2 : ¬ 2 ^ maxLog < len := by omega
  simp [gateMsm, h0, h2, hlt]

/-- The kernel runs exactly when every condition holds: the length is `2^k` with
`1 ≤ k` (ORACLE-27: at least two elements), `minK ≤ k ≤ maxLog`, a device is
present and the input is reduced. -/
theorem gate_none_iff (minK maxLog : Nat) (dp red : Bool) (len : Nat) :
    gate minK maxLog dp red len = none ↔
      (∃ k, 1 ≤ k ∧ minK ≤ k ∧ k ≤ maxLog ∧ len = 2 ^ k) ∧ dp = true ∧ red = true := by
  have hp := isPow2_iff len
  constructor
  · intro h
    unfold gate at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i hs hm hd hr
    have hpow : isPow2 len = true := by cases hq : isPow2 len <;> simp [hq] at hs ⊢
    obtain ⟨k, hk⟩ := hp.mp hpow
    subst hk
    refine ⟨⟨k, ?_, ?_, ?_, rfl⟩, by simpa using hd, by simpa using hr⟩
    · cases k with
      | zero => exact absurd (.inl (by decide)) hs
      | succ k => omega
    · exact (Nat.pow_le_pow_iff_right (by decide)).mp (Nat.le_of_not_lt hm)
    · exact (Nat.pow_le_pow_iff_right (by decide)).mp (Nat.le_of_not_lt (fun hh => hs (.inr (.inr hh))))
  · rintro ⟨⟨k, h1k, hmk, hkm, rfl⟩, rfl, rfl⟩
    have a : 2 ^ minK ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hmk
    have b : 2 ^ k ≤ 2 ^ maxLog := Nat.pow_le_pow_right (by decide) hkm
    have c : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h1k
    have d : isPow2 (2 ^ k) = true := hp.mpr ⟨k, rfl⟩
    have e : ¬ 2 ^ maxLog < 2 ^ k := by omega
    have f : ¬ 2 ^ k < 2 ^ minK := by omega
    have g : ¬ 2 ^ k < 2 := by omega
    simp [gate, d, e, f, g]

theorem gateMsm_none_iff (minK maxLog : Nat) (dp red : Bool) (len : Nat) :
    gateMsm minK maxLog dp red len = none ↔
      (1 ≤ len ∧ 2 ^ minK ≤ len ∧ len ≤ 2 ^ maxLog) ∧ dp = true ∧ red = true := by
  unfold gateMsm
  constructor
  · intro h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i hs hm hd hr
    refine ⟨⟨?_, ?_, ?_⟩, by simpa using hd, by simpa using hr⟩ <;> omega
  · rintro ⟨⟨h1, h2, h3⟩, rfl, rfl⟩
    have a : len ≠ 0 := by omega
    have b : ¬ 2 ^ maxLog < len := by omega
    have c : ¬ len < 2 ^ minK := by omega
    simp [a, b, c]

/-- GPU-010: unequal lengths are a `shape` decline, whatever the rest of the input. -/
theorem gateMsm2_mismatch (minK maxLog : Nat) (dp red : Bool) (scalars bases : Nat)
    (h : scalars ≠ bases) : gateMsm2 minK maxLog dp red scalars bases = some .shape := by
  simp [gateMsm2, h]

/-- With equal lengths the two-length gate is the one-length gate. -/
theorem gateMsm2_eq (minK maxLog : Nat) (dp red : Bool) (len : Nat) :
    gateMsm2 minK maxLog dp red len len = gateMsm minK maxLog dp red len := by
  simp [gateMsm2]

/-- The MSM kernel runs exactly when the lengths are equal and every condition
of `gateMsm` holds. -/
theorem gateMsm2_none_iff (minK maxLog : Nat) (dp red : Bool) (scalars bases : Nat) :
    gateMsm2 minK maxLog dp red scalars bases = none ↔
      scalars = bases ∧ (1 ≤ scalars ∧ 2 ^ minK ≤ scalars ∧ scalars ≤ 2 ^ maxLog) ∧
        dp = true ∧ red = true := by
  by_cases h : scalars = bases
  · subst h; rw [gateMsm2_eq, gateMsm_none_iff]; simp
  · simp [gateMsm2, h]

/-- The sizes the kernels take (`deviceSize`) are the powers of two `2^k` with
`1 ≤ k ≤ maxLog`. -/
theorem deviceSize_iff (maxLog len : Nat) :
    deviceSize maxLog len = true ↔ ∃ k, 1 ≤ k ∧ k ≤ maxLog ∧ len = 2 ^ k := by
  constructor
  · intro h
    simp only [deviceSize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨h2, hle⟩, hand⟩ := h
    have hpow : isPow2 len = true := by
      have := Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (n := len) (by omega)
      obtain ⟨k, hk⟩ := this.mp hand
      exact (isPow2_iff len).mpr ⟨k, hk⟩
    obtain ⟨k, rfl⟩ := (isPow2_iff len).mp hpow
    refine ⟨k, ?_, (Nat.pow_le_pow_iff_right (by decide)).mp hle, rfl⟩
    cases k with
    | zero => simp at h2
    | succ k => omega
  · rintro ⟨k, h1, hk, rfl⟩
    have a : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h1
    have b : 2 ^ k ≤ 2 ^ maxLog := Nat.pow_le_pow_right (by decide) hk
    have c : 2 ^ k &&& (2 ^ k - 1) = 0 := by
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
    have a' : 2 ≤ 2 ^ k := a
    simp [deviceSize, a', b, c]

/-- ORACLE-27: for every `minK`, a length the gate lets through is a size the
kernels take (`deviceSize`). -/
theorem gate_none_deviceSize (minK maxLog : Nat) (dp red : Bool) (len : Nat)
    (h : gate minK maxLog dp red len = none) : deviceSize maxLog len = true := by
  obtain ⟨⟨k, h1, -, hkm, rfl⟩, -, -⟩ := (gate_none_iff minK maxLog dp red len).mp h
  exact (deviceSize_iff maxLog _).mpr ⟨k, h1, hkm, rfl⟩

/-- With a device and a reduced input, the gate lets a length through exactly
when the kernels take the size and the length is not below the threshold. -/
theorem gate_none_iff_deviceSize (minK maxLog : Nat) (len : Nat) :
    gate minK maxLog true true len = none ↔ deviceSize maxLog len = true ∧ 2 ^ minK ≤ len := by
  rw [gate_none_iff, deviceSize_iff]
  constructor
  · rintro ⟨⟨k, h1, hmk, hkm, rfl⟩, -, -⟩
    exact ⟨⟨k, h1, hkm, rfl⟩, Nat.pow_le_pow_right (by decide) hmk⟩
  · rintro ⟨⟨k, h1, hkm, rfl⟩, hle⟩
    exact ⟨⟨k, h1, (Nat.pow_le_pow_iff_right (by decide)).mp hle, hkm, rfl⟩, rfl, rfl⟩

/-- ORACLE-27: at length 1 the gate and `deviceSize` agree, also at `minK = 0`:
one element is a `shape` decline and not a size the kernels take. -/
theorem gate_len_one_agrees :
    gate 0 28 true true 1 = some .shape ∧ deviceSize 28 1 = false := by decide +kernel

/-! ### The gate as an in-place hook -/

/-- A hook built from the gate: a gated decline returns the buffer as it came,
otherwise the kernel's output. `red` is the reduced test on the buffer. -/
def gatedHook (minK maxLog : Nat) (dp : Bool) (red : List Nat → Bool)
    (kernel : List Nat → List Nat) : InPlace := fun b =>
  match gate minK maxLog dp (red b) b.length with
  | some _ => (false, b)
  | none => (true, kernel b)

/-- GPU-010, GPU-074, GPU-008: a gated decline leaves the buffer unchanged and
the fallback gives the reference value. This holds for any kernel, correct or
not: the decline path does not run it. -/
theorem gate_declines_before_write (minK maxLog : Nat) (dp : Bool) (red : List Nat → Bool)
    (kernel ref : List Nat → List Nat) (b : List Nat) (r : Reason)
    (h : gate minK maxLog dp (red b) b.length = some r) :
    gatedHook minK maxLog dp red kernel b = (false, b) ∧
    runInPlace ref (gatedHook minK maxLog dp red kernel) b = ref b := by
  have h1 : gatedHook minK maxLog dp red kernel b = (false, b) := by simp [gatedHook, h]
  exact ⟨h1, by simp [runInPlace, h1]⟩

/-- A consequence of the hook contract, not a proof of it. Kernel correctness on
the inputs the gate lets through is the hypothesis `hk`: it is assumed here, and
the oracle does not prove it for any device kernel. Under that hypothesis the
gated hook meets the in-place contract (`HonestInPlace`). What holds with no
hypothesis on the kernel is the decline path: `gate_declines_before_write`. -/
theorem gatedHook_honest (minK maxLog : Nat) (dp : Bool) (red : List Nat → Bool)
    (kernel ref : List Nat → List Nat)
    (hk : ∀ b, gate minK maxLog dp (red b) b.length = none → kernel b = ref b) :
    HonestInPlace ref (gatedHook minK maxLog dp red kernel) := by
  intro b
  unfold gatedHook
  cases hg : gate minK maxLog dp (red b) b.length with
  | none => simp [hk b hg]
  | some r => simp

/-- A consequence of the hook contract as well: under the same hypothesis `hk`
(kernel correctness on gated inputs, assumed and not proved), the result is the
reference value on every buffer (`runInPlace_eq`). -/
theorem gatedHook_run (minK maxLog : Nat) (dp : Bool) (red : List Nat → Bool)
    (kernel ref : List Nat → List Nat)
    (hk : ∀ b, gate minK maxLog dp (red b) b.length = none → kernel b = ref b) (b : List Nat) :
    runInPlace ref (gatedHook minK maxLog dp red kernel) b = ref b :=
  runInPlace_eq ref _ (gatedHook_honest minK maxLog dp red kernel ref hk) b

end GpuSpec
