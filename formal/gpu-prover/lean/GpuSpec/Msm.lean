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

import GpuSpec.Field

/-!
# MSM over a toy group

The group is the additive group `Z_p`: a "point" is a field element, the group
law is `addM`, and the scalar multiple `s · g` is `mulM p s g`. This group has
the properties the MSM contract uses (associative, commutative, an inverse), and
it is cheap to compute, so the oracle can check bucket and window logic and
the mask identity of GPU-013 exactly.

* `msm p s g` is the reference: `Σ s_i · g_i`.
* `msmBucket p c bits s g` is the device algorithm (Pippenger): windows of `c`
  bits from the top, one bucket per digit, a running sum per window.
* `msmMasked p r s g` is the skewed MSM the device runs: `MSM(s + r) - MSM(r)`
  for a fixed public vector `r`.
-/

namespace GpuSpec

/-- The reference MSM: `Σ s_i · g_i` in `Z_p`, as one sum then one reduction. -/
def msmRaw (s g : List Nat) : Nat := (s.zip g).foldr (fun (a, b) acc => a * b + acc) 0

def msm (p : Nat) (s g : List Nat) : Nat := msmRaw s g % p

/-- The masked scalars: `(s_i + r_i) mod p`. -/
def maskScalars (p : Nat) (s r : List Nat) : List Nat := (s.zip r).map fun (a, b) => (a + b) % p

/-- GPU-013: the skewed MSM, `MSM(s + r) - MSM(r)`. -/
def msmMasked (p : Nat) (r s g : List Nat) : Nat :=
  subM p (msm p (maskScalars p s r) g) (msm p r g)

/-! ## Pippenger bucket method (the device algorithm) -/

/-- Digit `w` (window of `c` bits) of scalar `x`. -/
def digit (c w x : Nat) : Nat := (x / 2 ^ (c * w)) % 2 ^ c

/-- The window sum `Σ_d d · bucket[d]`, computed with a running sum from the top
bucket down, as the device does. -/
def windowSum (p c w : Nat) (s g : List Nat) : Nat :=
  let buckets := (List.range (2 ^ c)).map fun d =>
    sumM p ((s.zip g).filterMap fun (x, b) => if digit c w x = d then some b else none)
  let step := fun (acc : Nat × Nat) (b : Nat) =>
    let run := addM p acc.1 b
    (run, addM p acc.2 run)
  -- iterate buckets from the highest digit down to digit 1
  ((buckets.drop 1).reverse.foldl step (0, 0)).2

/-- Double-and-add `c` times: `acc · 2^c` in the toy group. -/
def shiftWindow (p c acc : Nat) : Nat := (List.replicate c ()).foldl (fun a _ => addM p a a) acc

/-- The bucket MSM over `bits`-bit scalars with `c`-bit windows. -/
def msmBucket (p c bits : Nat) (s g : List Nat) : Nat :=
  let nw := (bits + c - 1) / c
  (List.range nw).reverse.foldl (fun acc w => addM p (shiftWindow p c acc) (windowSum p c w s g)) 0
    % p

/-! ## Signed-digit (Booth) bucket method (the sppark kernel) -/

/-- The carry into window `w`: bit `c*w - 1` of `x`, and `0` below bit `0`. -/
def boothCarry (c w x : Nat) : Nat := 2 * x / 2 ^ (c * w) % 2

/-- The signed digit of window `w` of `x` in radix `2^c`, as the kernel computes it.
`wval` holds the bits of `x` from bit `c*w - 1` up (window 0 reads `x << 1`). The sign is bit
`c` of `wval`. `enc` is `((wval + 1) & wmask) >> 1` with `wmask = 2^(c+1) - 1`. A set sign
gives the two's complement `0 - enc`, whose low `c` bits are the magnitude. -/
def boothDigit (c w x : Nat) : Int :=
  let wval := 2 * x / 2 ^ (c * w)
  let enc := (wval + 1) % 2 ^ (c + 1) / 2
  if wval / 2 ^ c % 2 = 1 then -(((2 ^ c - enc) % 2 ^ c : Nat) : Int) else (enc : Int)

/-- The scalar after `abs` with fold test `flip`: `p - x` when the test fires. -/
def absVal (flip : Nat → Bool) (p x : Nat) : Nat := if flip x then p - x else x

/-- `abs` with fold test `flip`: when the test fires the scalar becomes `p - s` and its base
is negated. -/
def scalarAbsBy (flip : Nat → Bool) (p : Nat) (sg : Nat × Nat) : Nat × Nat :=
  if flip sg.1 then (p - sg.1, negM p sg.2) else sg

/-- The exact fold test: `s > (p-1)/2`. -/
def absExact (p x : Nat) : Bool := decide (x > (p - 1) / 2)

/-- The fold test of sppark's `mont_t::abs`: it computes `p - s` and compares only the top
limbs, `top(p - s) < top(s)`, where a limb boundary is at bit `L` (`L = 224` for 8 limbs of
32 bits). It agrees with `absExact` except when the two top limbs are equal. -/
def absTopLimb (L p x : Nat) : Bool := decide ((p - x) / 2 ^ L < x / 2 ^ L)

/-- `abs` with the exact test: a scalar above `(p-1)/2` becomes `p - s`, base negated. -/
def scalarAbs (p : Nat) (sg : Nat × Nat) : Nat × Nat := scalarAbsBy (absExact p) p sg

/-- The running-sum combination of one window: `Σ_m m · bucket[m]` for a row whose first
entry is the bucket of magnitude 1, computed from the top bucket down. -/
def runningSum (p : Nat) (row : List Nat) : Nat :=
  (row.reverse.foldl (fun (acc : Nat × Nat) (b : Nat) =>
    let run := addM p acc.1 b
    (run, addM p acc.2 run)) (0, 0)).2

/-- The bucket of magnitude `m` in window `w`: every base whose digit is `m` is added and
every base whose digit is `-m` is subtracted. A zero digit goes to no bucket (`m ≥ 1`). -/
def boothBucket (p c w m : Nat) (ps : List (Nat × Nat)) : Nat :=
  ps.foldl (fun acc (xb : Nat × Nat) =>
    let d := boothDigit c w xb.1
    if d.natAbs = m then (if d < 0 then subM p acc xb.2 else addM p acc xb.2) else acc) 0

/-- One window of the signed method: `2^(c-1)` buckets (magnitudes `1..2^(c-1)`), then the
running sum. -/
def boothWindowSum (p c w : Nat) (ps : List (Nat × Nat)) : Nat :=
  runningSum p ((List.range' 1 (2 ^ (c - 1))).map fun m => boothBucket p c w m ps)

/-- The signed-bucket MSM (sppark Pippenger) with fold test `flip`: `abs`, signed `c`-bit
digits, `2^(c-1)` buckets per window, a running sum per window, and windows combined
top-down with `c` doublings. The window count is the kernel's `nwins = (bits - 1) / c + 1`. -/
def msmBoothBy (flip : Nat → Bool) (p c bits : Nat) (s g : List Nat) : Nat :=
  let ps := (s.zip g).map (scalarAbsBy flip p)
  let nw := (bits - 1) / c + 1
  (List.range nw).reverse.foldl
    (fun acc w => addM p (shiftWindow p c acc) (boothWindowSum p c w ps)) 0 % p

/-- The signed-bucket MSM with the exact `abs` test `s > (p-1)/2`. -/
def msmBooth (p c bits : Nat) (s g : List Nat) : Nat := msmBoothBy (absExact p) p c bits s g

/-! ## Batched MSM: several scalar vectors over the same bases in one pass -/

/-- One step of the single pass: base `b` is added, times the head scalar of each vector, to
that vector's accumulator; every vector then moves to its next scalar. A vector that has run
out contributes `0`. -/
def msmBatchStep (p : Nat) (st : List Nat × List (List Nat)) (b : Nat) :
    List Nat × List (List Nat) :=
  (List.zipWith (fun acc s => addM p acc (mulM p (s.headD 0) b)) st.1 st.2, st.2.map List.tail)

/-- The batched MSM: one fold over the bases with one accumulator per scalar vector. -/
def msmBatch (p : Nat) (ss : List (List Nat)) (g : List Nat) : List Nat :=
  (g.foldl (msmBatchStep p) (ss.map fun _ => 0, ss)).1.map (· % p)

/-- One step of the single pass of the batched bucket method. A bucket table maps (window,
digit) to the bucket value; each scalar vector has its own table. Base `b` goes, in every
window, to the bucket of the digit of that vector's head scalar. A vector that has run out
reads scalar `0`: its base lands in bucket `0`, which the running sum never reads. -/
def bucketBatchStep (p c : Nat) (st : List (Nat → Nat → Nat) × List (List Nat)) (b : Nat) :
    List (Nat → Nat → Nat) × List (List Nat) :=
  (List.zipWith (fun tbl s => fun w d =>
      if digit c w (s.headD 0) = d then addM p (tbl w d) b else tbl w d) st.1 st.2,
    st.2.map List.tail)

/-- The batched bucket MSM: one fold over the bases fills one bucket table per scalar vector;
each table is then combined as in `msmBucket` (running sum per window, windows top-down). -/
def msmBucketBatch (p c bits : Nat) (ss : List (List Nat)) (g : List Nat) : List Nat :=
  let nw := (bits + c - 1) / c
  (g.foldl (bucketBatchStep p c) (ss.map fun _ => fun _ _ => 0, ss)).1.map fun tbl =>
    (List.range nw).reverse.foldl (fun acc w => addM p (shiftWindow p c acc)
      (runningSum p ((List.range' 1 (2 ^ c - 1)).map (tbl w)))) 0 % p

/-! ## GPU-013: the mask changes no group element -/

theorem msmRaw_mask_mod (p : Nat) :
    ∀ (s r g : List Nat), s.length = r.length →
      msmRaw (maskScalars p s r) g % p = (msmRaw s g + msmRaw r g) % p
  | [], [], g => by simp [msmRaw, maskScalars]
  | [], _ :: _, _ => by intro h; simp at h
  | _ :: _, [], _ => by intro h; simp at h
  | a :: s, b :: r, [] => by simp [msmRaw, maskScalars]
  | a :: s, b :: r, x :: g => by
    intro h
    have ih := msmRaw_mask_mod p s r g (by simpa using h)
    simp only [msmRaw, maskScalars, List.zip_cons_cons, List.map_cons, List.foldr_cons] at ih ⊢
    generalize List.foldr (fun x acc => x.fst * x.snd + acc) 0
      ((List.map (fun x => (x.fst + x.snd) % p) (s.zip r)).zip g) = M at ih ⊢
    generalize List.foldr (fun x acc => x.fst * x.snd + acc) 0 (s.zip g) = S at ih ⊢
    generalize List.foldr (fun x acc => x.fst * x.snd + acc) 0 (r.zip g) = R at ih ⊢
    calc ((a + b) % p * x + M) % p = ((a + b) % p * x % p + M % p) % p := Nat.add_mod _ _ _
      _ = ((a + b) * x % p + (S + R) % p) % p := by rw [ih, Nat.mod_mul_mod]
      _ = ((a + b) * x + (S + R)) % p := (Nat.add_mod _ _ _).symm
      _ = (a * x + S + (b * x + R)) % p := by rw [Nat.add_mul]; congr 1; omega

/-- Subtraction undoes addition in `Z_p`. -/
theorem sub_add_cancel_mod (p a y : Nat) (hp : 0 < p) :
    subM p ((a + y) % p) (y % p) = a % p := by
  unfold subM
  have ha := Nat.mod_lt a hp
  have hy := Nat.mod_lt y hp
  rw [Nat.mod_mod, Nat.add_mod a y]
  generalize a % p = a' at *
  generalize y % p = y' at *
  by_cases h : a' + y' < p
  · rw [Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt h, show a' + y' + p - y' = a' + p by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · have h2 : (a' + y') % p = a' + y' - p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h2, Nat.mod_eq_of_lt hy, show a' + y' - p + p - y' = a' by omega, Nat.mod_eq_of_lt ha]

/-- GPU-013: the masked MSM equals the reference MSM for every mask. -/
theorem msmMasked_eq (p : Nat) (hp : 0 < p) (r s g : List Nat) (h : s.length = r.length) :
    msmMasked p r s g = msm p s g := by
  unfold msmMasked msm
  rw [msmRaw_mask_mod p s r g h]
  exact sub_add_cancel_mod p _ _ hp

end GpuSpec
