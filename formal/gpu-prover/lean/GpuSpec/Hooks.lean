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
# Hook contract and the prover with any decline pattern

The midnight-proofs hooks return the stock value or decline (GPU-007,
GPU-008). This module states that contract and proves its consequence: a
proof is a function of the reference values and the two random streams only, so
every schedule of accepts and declines gives the same proof bytes, the same
random draws from each source and the same transcript (GPU-014, GPU-015, GPU-016).

The prover is abstract: a list of events, each an operation call (MSM,
forward NTT, inverse NTT, or the quotient: numerator, division by the vanishing
polynomial and transform back, all on the extended coset), a blinding draw on
the CPU at the point where the stock prover draws it, from one of two random
sources (`Source.caller`: the caller's RNG, advice and lookup blinding;
`Source.os`: the OS source, the quotient limb blinding after the quotient call),
or a transcript squeeze. Operation values are absorbed into the transcript.
Blinding values come from the two random streams on the CPU; no hook can draw or
skip one (GPU-016, `draws_independent_of_device`).
-/

namespace GpuSpec

inductive Kind where
  | msm | ntt | intt | quotient
  deriving Repr, DecidableEq

structure Call where
  kind : Kind
  input : List Nat
  deriving Repr, DecidableEq

/-- A device: for each occurrence of a call, a value or a decline (`none`). The
first argument is the position of the event in the prover's event list, so the
answer may differ between two occurrences of the same call (a device that
accepts a call and declines an identical later one, for example after it ran
out of memory). A device that ignores the position is the special case. -/
abbrev Device := Nat → Call → Option (List Nat)

/-- The CPU-only device: declines everything (feature off, no device, or the
stub build of GPU-003). -/
def cpuOnly : Device := fun _ _ => none

/-- GPU-007: an honest device returns the reference value or declines, at every
occurrence of every call. -/
def Honest (ref : Call → List Nat) (dev : Device) : Prop :=
  ∀ i c v, dev i c = some v → v = ref c

/-- GPU-008: a decline falls back to the stock CPU function on the same input. -/
def resolve (ref : Call → List Nat) (dev : Device) (i : Nat) (c : Call) : List Nat :=
  match dev i c with
  | some v => v
  | none => ref c

theorem resolve_eq (ref : Call → List Nat) (dev : Device) (h : Honest ref dev) (i : Nat)
    (c : Call) : resolve ref dev i c = ref c := by
  unfold resolve
  cases hd : dev i c with
  | none => rfl
  | some v => exact h i c v hd

/-- The two random sources of the stock prover (GPU-014, GPU-016): the caller's
RNG (advice and lookup blinding) and the OS source (the quotient limb blinding,
drawn after the quotient hook). -/
inductive Source where
  | caller | os
  deriving Repr, DecidableEq

/-- The tag of a source in a transcript entry. -/
def Source.tag : Source → Nat
  | .caller => 0
  | .os => 1

inductive Event where
  | op (c : Call)
  | blind (src : Source)
  | squeeze
  deriving Repr, DecidableEq

/-- The proof-relevant output: the transcript entries and the number of random
values drawn from each source (`drawn`: the caller's RNG, `drawnOs`: the OS
source). Fallback counts are a report, not part of the proof. -/
structure Proof where
  transcript : List (List Nat)
  drawn : Nat
  drawnOs : Nat
  deriving Repr, DecidableEq

/-- `rng` is the rest of the caller's stream, `osRng` the rest of the OS stream,
`pos` the number of events done (the position of the next event). `fallbacks`
counts the CPU resolutions: every call the device declined, the expected
declines (no-device, below-min-k) included. The daemon's fallback count of
GPU-012 leaves the expected ones out (`fallbackOps` in `Declines.lean`). -/
structure Run where
  proof : Proof
  rng : List Nat
  osRng : List Nat
  pos : Nat
  fallbacks : Nat
  deriving Repr

/-- A toy transcript hash (any function of the transcript works for the theorem). -/
def tHash (t : List (List Nat)) : Nat := t.foldl (fun acc e => e.foldl (fun a x => a * 31 + x + 1) acc) 7

/-- One event. The device is asked with the position of the event. A blinding
draw takes the next value of the named source on the CPU and records the entry
`[source tag, value]`; the device is not consulted (GPU-016). An empty source
draws nothing. Every event advances the position by one. -/
def proveStep (ref : Call → List Nat) (dev : Device) (r : Run) : Event → Run
  | .op c =>
    { r with proof := { r.proof with transcript := r.proof.transcript ++ [resolve ref dev r.pos c] },
             pos := r.pos + 1,
             fallbacks := r.fallbacks + (if (dev r.pos c).isSome then 0 else 1) }
  | .blind .caller =>
    match r.rng with
    | x :: rest =>
      { r with proof := { r.proof with transcript := r.proof.transcript ++ [[Source.caller.tag, x]],
                                       drawn := r.proof.drawn + 1 },
               rng := rest, pos := r.pos + 1 }
    | [] => { r with pos := r.pos + 1 }
  | .blind .os =>
    match r.osRng with
    | x :: rest =>
      { r with proof := { r.proof with transcript := r.proof.transcript ++ [[Source.os.tag, x]],
                                       drawnOs := r.proof.drawnOs + 1 },
               osRng := rest, pos := r.pos + 1 }
    | [] => { r with pos := r.pos + 1 }
  | .squeeze =>
    { r with proof := { r.proof with transcript := r.proof.transcript ++ [[tHash r.proof.transcript]] },
             pos := r.pos + 1 }

/-- The start of a run. -/
def Run.start (rng osRng : List Nat) : Run :=
  { proof := { transcript := [], drawn := 0, drawnOs := 0 }, rng, osRng, pos := 0, fallbacks := 0 }

def prove (ref : Call → List Nat) (dev : Device) (evs : List Event) (rng osRng : List Nat) : Run :=
  evs.foldl (proveStep ref dev) (Run.start rng osRng)

/-- Every event advances the position by one, whatever the device answers. -/
theorem proveStep_pos (ref : Call → List Nat) (dev : Device) (r : Run) (e : Event) :
    (proveStep ref dev r e).pos = r.pos + 1 := by
  cases e with
  | op c => rfl
  | squeeze => rfl
  | blind src => cases src <;> simp only [proveStep] <;> split <;> rfl

/-- One step with an honest device gives the CPU step's proof and both random streams. -/
theorem proveStep_honest (ref : Call → List Nat) (dev : Device) (h : Honest ref dev)
    (r : Run) (e : Event) :
    (proveStep ref dev r e).proof = (proveStep ref cpuOnly r e).proof ∧
    (proveStep ref dev r e).rng = (proveStep ref cpuOnly r e).rng ∧
    (proveStep ref dev r e).osRng = (proveStep ref cpuOnly r e).osRng := by
  cases e with
  | op c =>
    simp [proveStep, resolve_eq ref dev h r.pos c,
      resolve_eq ref cpuOnly (by intro _ _ _ h; cases h) r.pos c]
  | blind src => cases src <;> simp [proveStep]
  | squeeze => simp [proveStep]

/-- The proof and both random streams after a step depend only on the proof, the
two random streams and the position before it. -/
theorem proveStep_congr (ref : Call → List Nat) (d : Device) (e : Event) (r1 r2 : Run)
    (hp : r1.proof = r2.proof) (hr : r1.rng = r2.rng) (ho : r1.osRng = r2.osRng)
    (hi : r1.pos = r2.pos) :
    (proveStep ref d r1 e).proof = (proveStep ref d r2 e).proof ∧
    (proveStep ref d r1 e).rng = (proveStep ref d r2 e).rng ∧
    (proveStep ref d r1 e).osRng = (proveStep ref d r2 e).osRng := by
  cases r1 with
  | mk p1 g1 o1 i1 f1 =>
    cases r2 with
    | mk p2 g2 o2 i2 f2 =>
      simp only at hp hr ho hi
      subst hp; subst hr; subst ho; subst hi
      cases e with
      | op c => simp [proveStep]
      | squeeze => simp [proveStep]
      | blind src =>
        cases src
        · cases g1 <;> simp [proveStep]
        · cases o1 <;> simp [proveStep]

theorem prove_foldl (ref : Call → List Nat) (dev : Device) (h : Honest ref dev) :
    ∀ (evs : List Event) (r1 r2 : Run), r1.proof = r2.proof → r1.rng = r2.rng →
      r1.osRng = r2.osRng → r1.pos = r2.pos →
      (evs.foldl (proveStep ref dev) r1).proof = (evs.foldl (proveStep ref cpuOnly) r2).proof ∧
      (evs.foldl (proveStep ref dev) r1).rng = (evs.foldl (proveStep ref cpuOnly) r2).rng ∧
      (evs.foldl (proveStep ref dev) r1).osRng = (evs.foldl (proveStep ref cpuOnly) r2).osRng
  | [], _, _, hp, hr, ho, _ => ⟨hp, hr, ho⟩
  | e :: evs, r1, r2, hp, hr, ho, hi => by
    simp only [List.foldl_cons]
    have hh := proveStep_honest ref dev h r1 e
    have hc := proveStep_congr ref cpuOnly e r1 r2 hp hr ho hi
    exact prove_foldl ref dev h evs _ _ (hh.1.trans hc.1) (hh.2.1.trans hc.2.1)
      (hh.2.2.trans hc.2.2) (by rw [proveStep_pos, proveStep_pos, hi])

/-- GPU-007, GPU-008, GPU-014, GPU-015, GPU-016: with any honest device (any
pattern of accepts and declines, which may differ between two occurrences of
the same call), the proof (the transcript and the draw count of each source)
and both remaining random streams equal those of the CPU-only prover. -/
theorem prove_any_schedule (ref : Call → List Nat) (dev : Device) (h : Honest ref dev)
    (evs : List Event) (rng osRng : List Nat) :
    (prove ref dev evs rng osRng).proof.transcript =
      (prove ref cpuOnly evs rng osRng).proof.transcript ∧
    (prove ref dev evs rng osRng).proof.drawn = (prove ref cpuOnly evs rng osRng).proof.drawn ∧
    (prove ref dev evs rng osRng).proof.drawnOs = (prove ref cpuOnly evs rng osRng).proof.drawnOs ∧
    (prove ref dev evs rng osRng).rng = (prove ref cpuOnly evs rng osRng).rng ∧
    (prove ref dev evs rng osRng).osRng = (prove ref cpuOnly evs rng osRng).osRng := by
  have h := prove_foldl ref dev h evs (Run.start rng osRng) _ rfl rfl rfl rfl
  unfold prove
  exact ⟨by rw [h.1], by rw [h.1], by rw [h.1], h.2.1, h.2.2⟩

/-- Two honest devices give the same proof. -/
theorem prove_two_devices (ref : Call → List Nat) (d1 d2 : Device)
    (h1 : Honest ref d1) (h2 : Honest ref d2) (evs : List Event) (rng osRng : List Nat) :
    (prove ref d1 evs rng osRng).proof = (prove ref d2 evs rng osRng).proof := by
  have a := (prove_foldl ref d1 h1 evs (Run.start rng osRng) _ rfl rfl rfl rfl).1
  have b := (prove_foldl ref d2 h2 evs (Run.start rng osRng) _ rfl rfl rfl rfl).1
  unfold prove
  rw [a, b]

/-- The draw state of a run: both remaining streams and both draw counts. -/
def Run.draws (r : Run) : List Nat × List Nat × Nat × Nat :=
  (r.rng, r.osRng, r.proof.drawn, r.proof.drawnOs)

/-- A step's draw state is a function of the draw state before it and the
event. The device, the position and the reference function are not read. -/
theorem proveStep_draws (ref1 ref2 : Call → List Nat) (d1 d2 : Device) (e : Event) (r1 r2 : Run)
    (h : r1.draws = r2.draws) : (proveStep ref1 d1 r1 e).draws = (proveStep ref2 d2 r2 e).draws := by
  simp only [Run.draws, Prod.mk.injEq] at h
  obtain ⟨hr, ho, hd, hdo⟩ := h
  cases e with
  | op c => simp [proveStep, Run.draws, hr, ho, hd, hdo]
  | squeeze => simp [proveStep, Run.draws, hr, ho, hd, hdo]
  | blind src =>
    cases src
    · simp only [proveStep, ← hr]; split <;> simp [Run.draws, *]
    · simp only [proveStep, ← ho]; split <;> simp [Run.draws, *]

theorem draws_foldl (ref1 ref2 : Call → List Nat) (d1 d2 : Device) :
    ∀ (evs : List Event) (r1 r2 : Run), r1.draws = r2.draws →
      (evs.foldl (proveStep ref1 d1) r1).draws = (evs.foldl (proveStep ref2 d2) r2).draws
  | [], _, _, h => h
  | e :: evs, r1, r2, h => by
    simp only [List.foldl_cons]
    exact draws_foldl ref1 ref2 d1 d2 evs _ _ (proveStep_draws ref1 ref2 d1 d2 e r1 r2 h)

/-- GPU-014, GPU-016: for any two devices, honest or not (and any two reference
functions), both remaining random streams and both draw counts are equal. The
draws do not depend on the hook answers: no hook draws or skips a value. No
hypothesis on the devices. -/
theorem draws_independent_of_device (ref1 ref2 : Call → List Nat) (d1 d2 : Device)
    (evs : List Event) (rng osRng : List Nat) :
    (prove ref1 d1 evs rng osRng).rng = (prove ref2 d2 evs rng osRng).rng ∧
    (prove ref1 d1 evs rng osRng).osRng = (prove ref2 d2 evs rng osRng).osRng ∧
    (prove ref1 d1 evs rng osRng).proof.drawn = (prove ref2 d2 evs rng osRng).proof.drawn ∧
    (prove ref1 d1 evs rng osRng).proof.drawnOs = (prove ref2 d2 evs rng osRng).proof.drawnOs := by
  have h := draws_foldl ref1 ref2 d1 d2 evs (Run.start rng osRng) _ rfl
  simpa [Run.draws, prove] using h

/-! ## In-place hooks (GPU-009, GPU-010)

Some hooks transform the caller's buffer in place and return a flag. The
contract: on accept the buffer holds the reference value; on decline the
buffer is unchanged. The stock code then runs on that buffer. -/

abbrev InPlace := List Nat → Bool × List Nat

def HonestInPlace (ref : List Nat → List Nat) (h : InPlace) : Prop :=
  ∀ b, ((h b).1 = true → (h b).2 = ref b) ∧ ((h b).1 = false → (h b).2 = b)

def runInPlace (ref : List Nat → List Nat) (h : InPlace) (b : List Nat) : List Nat :=
  if (h b).1 then (h b).2 else ref (h b).2

theorem runInPlace_eq (ref : List Nat → List Nat) (h : InPlace) (hh : HonestInPlace ref h)
    (b : List Nat) : runInPlace ref h b = ref b := by
  unfold runInPlace
  cases hb : (h b).1
  · simp [(hh b).2 hb]
  · simp [(hh b).1 hb]

/-- A hook that declines after it changed the buffer breaks the fallback: the
stock code then runs on the wrong input. This is why GPU-009 requires the
buffer to be unchanged on a decline. -/
def dirtyDecline : InPlace := fun b => (false, b.map (· + 1))

/-! ## Installation (GPU-011) -/

def install {α : Type} (slot : Option α) (h : α) : Bool × Option α :=
  match slot with
  | none => (true, some h)
  | some x => (false, some x)

theorem install_twice {α : Type} (a b : α) :
    install (install none a).2 b = (false, some a) := rfl

end GpuSpec
