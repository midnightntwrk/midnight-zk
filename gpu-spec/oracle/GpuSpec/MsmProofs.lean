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

import GpuSpec.Msm

/-!
# MSM: general correctness theorems

Every device model of `GpuSpec.Msm` equals the reference `msm` for every modulus, window
width and input length, not only on the pinned vectors of `GpuSpec.Tests`.

* `msmBucket_eq_msm_trunc`: the bucket method computes the MSM of the scalars reduced modulo
  `2^(c * nw)`; no hypothesis. `msmBucket_eq_msm_of_cover` and `msmBucket_eq_msm` follow.
* `msmBooth_eq_msm`: the signed-digit (sppark) method equals `msm` for `c ≥ 1`.
  `msmBoothBy_eq_msm` is the same for any `abs` fold test, and `msmBoothBy_blsR_topLimb` is
  the instance for the top-limb test of the vendored `mont_t::abs`.
* `msmBatch_eq`: the single-pass batched MSM equals the MSM of each scalar vector.
* `msm_append`, `msm_zero_scalar`, `msm_infinity_base` and their device forms.

The proofs work on the zipped list of (scalar, base) pairs, so lists of different lengths
need no separate case. Every step is a congruence `a % p = b % p`.
-/

namespace GpuSpec

/-! ## Sums over pair lists -/

/-- `Σ f x · b` over a list of (scalar, base) pairs. -/
def dotF (f : Nat → Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | xb :: ps => f xb.1 * xb.2 + dotF f ps

/-- `Σ_{w < n} f w`. -/
def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f n + f n

/-- The sum of the values of the items whose magnitude is `d`. -/
def cnt (d : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | mv :: it => (if mv.1 = d then mv.2 else 0) + cnt d it

/-- `Σ_i (k + i) · l[i]`. -/
def wsumFrom : Nat → List Nat → Nat
  | _, [] => 0
  | k, b :: l => k * b + wsumFrom (k + 1) l

theorem mod_add_congr {p a a' b b' : Nat} (h1 : a % p = a' % p) (h2 : b % p = b' % p) :
    (a + b) % p = (a' + b') % p := by
  rw [Nat.add_mod, h1, h2, ← Nat.add_mod]

theorem mod_mul_congr {p a a' b b' : Nat} (h1 : a % p = a' % p) (h2 : b % p = b' % p) :
    (a * b) % p = (a' * b') % p := by
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

theorem msmRaw_eq_dotF (s g : List Nat) : msmRaw s g = dotF id (s.zip g) := by
  unfold msmRaw
  induction s.zip g with
  | nil => rfl
  | cons xb ps ih => obtain ⟨a, b⟩ := xb; simp only [List.foldr_cons, dotF, id, ih]

theorem dotF_map_left (f : Nat → Nat) (ps : List (Nat × Nat)) :
    dotF id (ps.map (Prod.map f id)) = dotF f ps := by
  induction ps with
  | nil => rfl
  | cons xb ps ih => simp only [List.map_cons, dotF, Prod.map, id, ih]

theorem msmRaw_map (f : Nat → Nat) (s g : List Nat) :
    msmRaw (s.map f) g = dotF f (s.zip g) := by
  rw [msmRaw_eq_dotF, List.zip_map_left, dotF_map_left]

theorem dotF_append (f : Nat → Nat) (ps qs : List (Nat × Nat)) :
    dotF f (ps ++ qs) = dotF f ps + dotF f qs := by
  induction ps with
  | nil => simp [dotF]
  | cons xb ps ih => simp only [List.cons_append, dotF, ih]; omega

theorem dotF_congr {f h : Nat → Nat} (ps : List (Nat × Nat))
    (e : ∀ xb ∈ ps, f xb.1 = h xb.1) : dotF f ps = dotF h ps := by
  induction ps with
  | nil => rfl
  | cons xb ps ih =>
    simp only [dotF]
    rw [e xb (List.mem_cons_self), ih fun y hy => e y (List.mem_cons_of_mem _ hy)]

/-- `dotF` is linear in the scalar function. -/
theorem dotF_add_mul (f h : Nat → Nat) (k : Nat) (ps : List (Nat × Nat)) :
    dotF (fun x => f x + k * h x) ps = dotF f ps + k * dotF h ps := by
  induction ps with
  | nil => rfl
  | cons xb ps ih =>
    simp only [dotF, ih, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    omega

theorem sumRange_dotF (c : Nat) (f : Nat → Nat → Nat) (ps : List (Nat × Nat)) (n : Nat) :
    sumRange (fun w => 2 ^ (c * w) * dotF (f w) ps) n
      = dotF (fun x => sumRange (fun w => 2 ^ (c * w) * f w x) n) ps := by
  induction n with
  | zero =>
    simp only [sumRange]
    induction ps with
    | nil => rfl
    | cons xb ps ih => simp [dotF, ← ih]
  | succ n ih => simp only [sumRange, ih, dotF_add_mul]

theorem sumRange_congr_mod {p : Nat} {f h : Nat → Nat} (e : ∀ w, f w % p = h w % p) (n : Nat) :
    sumRange f n % p = sumRange h n % p := by
  induction n with
  | zero => rfl
  | succ n ih => exact mod_add_congr ih (e n)

/-! ## The running sum of one window -/

theorem wsumFrom_succ (k : Nat) (l : List Nat) :
    wsumFrom (k + 1) l = wsumFrom k l + l.sum := by
  induction l generalizing k with
  | nil => rfl
  | cons b l ih => simp only [wsumFrom, ih, List.sum_cons, Nat.add_mul]; omega

theorem runningSum_aux (p : Nat) (row : List Nat) :
    (row.foldr (fun (b : Nat) (acc : Nat × Nat) =>
        (addM p acc.1 b, addM p acc.2 (addM p acc.1 b))) (0, 0)).1 % p = row.sum % p ∧
    (row.foldr (fun (b : Nat) (acc : Nat × Nat) =>
        (addM p acc.1 b, addM p acc.2 (addM p acc.1 b))) (0, 0)).2 % p = wsumFrom 1 row % p := by
  induction row with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [List.foldr_cons, List.sum_cons, wsumFrom, Nat.reduceAdd]
    have e2 : wsumFrom 2 l = wsumFrom 1 l + l.sum := wsumFrom_succ 1 l
    generalize List.foldr (fun (b : Nat) (acc : Nat × Nat) =>
        (addM p acc.1 b, addM p acc.2 (addM p acc.1 b))) (0, 0) l = r at h1 h2 ⊢
    simp only [addM, Nat.mod_mod]
    have e1 := mod_add_congr h1 (rfl : b % p = b % p)
    refine ⟨by rw [e1, Nat.add_comm], ?_⟩
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, mod_add_congr h2 e1]
    congr 1
    omega

/-- The running sum from the top bucket down is `Σ_i (i + 1) · row[i]`. -/
theorem runningSum_mod (p : Nat) (row : List Nat) :
    runningSum p row % p = wsumFrom 1 row % p := by
  unfold runningSum
  rw [List.foldl_reverse]
  exact (runningSum_aux p row).2

theorem wsumFrom_congr_mod {p : Nat} {B C : Nat → Nat} (e : ∀ d, B d % p = C d % p)
    (k : Nat) (l : List Nat) : wsumFrom k (l.map B) % p = wsumFrom k (l.map C) % p := by
  induction l generalizing k with
  | nil => rfl
  | cons d l ih =>
    simp only [List.map_cons, wsumFrom]
    exact mod_add_congr (mod_mul_congr rfl (e d)) (ih _)

theorem wsumFrom_add (a b : Nat → Nat) (k : Nat) (l : List Nat) :
    wsumFrom k (l.map fun d => a d + b d) = wsumFrom k (l.map a) + wsumFrom k (l.map b) := by
  induction l generalizing k with
  | nil => rfl
  | cons d l ih => simp only [List.map_cons, wsumFrom, ih, Nat.mul_add]; omega

/-- One item lands in exactly one bucket. -/
theorem wsumFrom_single (m v k n : Nat) :
    wsumFrom k ((List.range' k n).map fun d => if m = d then v else 0)
      = if k ≤ m ∧ m < k + n then m * v else 0 := by
  induction n generalizing k with
  | zero => simp [wsumFrom]; omega
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, wsumFrom, ih]
    by_cases h : m = k
    · subst h; simp; intro h; omega
    · have e : (k + 1 ≤ m ∧ m < k + 1 + n) ↔ (k ≤ m ∧ m < k + (n + 1)) := by omega
      simp [h, e]

/-- Bucket counting: `Σ_{d = k}^{k+n-1} d · bucket[d]` is `Σ magnitude · value` when every
magnitude is below `k + n` (`k ≤ 1`, so only a zero magnitude can fall below the range). -/
theorem wsumFrom_cnt (k n : Nat) (hk : k ≤ 1) (it : List (Nat × Nat))
    (hm : ∀ mv ∈ it, mv.1 < k + n) :
    wsumFrom k ((List.range' k n).map fun d => cnt d it) = dotF id it := by
  induction it with
  | nil =>
    simp only [cnt, dotF]
    generalize List.range' k n = l
    clear hk hm
    induction l generalizing k with
    | nil => rfl
    | cons d l ih => simp only [List.map_cons, wsumFrom, ih (k + 1)]; omega
  | cons mv it ih =>
    simp only [cnt, dotF, id]
    rw [wsumFrom_add, wsumFrom_single, ih fun y hy => hm y (List.mem_cons_of_mem _ hy)]
    have := hm mv List.mem_cons_self
    by_cases h : k ≤ mv.1 ∧ mv.1 < k + n
    · simp [h]
    · have : mv.1 = 0 := by omega
      simp [this]

/-- The generic window lemma: for items (magnitude, value) with magnitudes at most `n`, any
bucket row that agrees with the item buckets modulo `p` has running sum
`Σ magnitude · value`. Zero magnitudes contribute nothing. -/
theorem runningSum_buckets (p n : Nat) (B : Nat → Nat) (it : List (Nat × Nat))
    (hB : ∀ d, B d % p = cnt d it % p) (hm : ∀ mv ∈ it, mv.1 ≤ n) :
    runningSum p ((List.range' 1 n).map B) % p = dotF id it % p := by
  rw [runningSum_mod, wsumFrom_congr_mod hB,
    wsumFrom_cnt 1 n (Nat.le_refl 1) it fun mv h => by have := hm mv h; omega]

/-! ## The window fold -/

theorem shiftWindow_mod (p c acc : Nat) : shiftWindow p c acc % p = acc * 2 ^ c % p := by
  unfold shiftWindow
  induction c generalizing acc with
  | zero => simp
  | succ c ih =>
    rw [List.replicate_succ, List.foldl_cons, ih, addM, Nat.pow_succ]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    congr 1
    rw [Nat.mul_comm (2 ^ c) 2, ← Nat.mul_assoc]
    congr 1
    omega

/-- Windows combined top-down with `c` doublings between windows give `Σ_w 2^(c·w) · D w`. -/
theorem windowFold_mod (p c : Nat) (WS D : Nat → Nat) (h : ∀ w, WS w % p = D w % p)
    (n init : Nat) :
    (List.range n).reverse.foldl (fun acc w => addM p (shiftWindow p c acc) (WS w)) init % p
      = (init * 2 ^ (c * n) + sumRange (fun w => 2 ^ (c * w) * D w) n) % p := by
  induction n generalizing init with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, ih, sumRange, addM]
    have e : (shiftWindow p c init + WS n) % p = (init * 2 ^ c + D n) % p :=
      mod_add_congr (shiftWindow_mod p c init) (h n)
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, e, ← Nat.mul_mod, ← Nat.add_mod]
    congr 1
    rw [Nat.mul_succ, Nat.pow_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ c),
      Nat.mul_comm (D n)]
    omega

/-! ## Theorem 1: the bucket method -/

theorem foldl_addM_mod (p a : Nat) (xs : List Nat) :
    xs.foldl (addM p) a % p = (a + xs.sum) % p := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, addM, List.sum_cons, Nat.mod_add_mod, Nat.add_assoc]

theorem bucket_sum (c w d : Nat) (ps : List (Nat × Nat)) :
    (ps.filterMap fun (x, b) => if digit c w x = d then some b else none).sum
      = cnt d (ps.map fun xb => (digit c w xb.1, xb.2)) := by
  induction ps with
  | nil => rfl
  | cons xb ps ih =>
    obtain ⟨x, b⟩ := xb
    simp only [List.filterMap_cons, List.map_cons, cnt]
    split <;> simp_all

theorem digit_lt (c w x : Nat) : digit c w x < 2 ^ c := Nat.mod_lt _ (Nat.pow_pos (by omega))

theorem dotF_digitItems (c w : Nat) (ps : List (Nat × Nat)) :
    dotF id (ps.map fun xb => (digit c w xb.1, xb.2)) = dotF (digit c w) ps := by
  induction ps with
  | nil => rfl
  | cons xb ps ih => simp only [List.map_cons, dotF, id, ih]

/-- One window of the bucket method is `Σ digit · base`. -/
theorem windowSum_mod (p c w : Nat) (s g : List Nat) :
    windowSum p c w s g % p = dotF (digit c w) (s.zip g) % p := by
  have e : windowSum p c w s g = runningSum p ((List.range' 1 (2 ^ c - 1)).map fun d =>
      sumM p ((s.zip g).filterMap fun (x, b) => if digit c w x = d then some b else none)) := by
    show runningSum p (List.drop 1 ((List.range (2 ^ c)).map _)) = _
    rw [← List.map_drop, List.range_eq_range', List.drop_range']
  rw [e, runningSum_buckets p (2 ^ c - 1) _ ((s.zip g).map fun xb => (digit c w xb.1, xb.2)),
    dotF_digitItems]
  · intro d
    rw [← bucket_sum, sumM, foldl_addM_mod, Nat.zero_add]
  · intro mv hmv
    obtain ⟨xb, -, rfl⟩ := List.mem_map.1 hmv
    have := digit_lt c w xb.1
    show digit c w xb.1 ≤ 2 ^ c - 1
    omega

/-- The digits of `x` recompose to `x mod 2^(c·n)`. -/
theorem digit_recompose (c x n : Nat) :
    sumRange (fun w => 2 ^ (c * w) * digit c w x) n = x % 2 ^ (c * n) := by
  induction n with
  | zero => simp [sumRange, Nat.mod_one]
  | succ n ih => rw [sumRange, ih, Nat.mul_succ, Nat.pow_add, Nat.mod_mul]; rfl

/-- The bucket method computes the MSM of the scalars reduced modulo `2^(c · nw)`, with
`nw = (bits + c - 1) / c` windows. No hypothesis: every modulus, width and length. -/
theorem msmBucket_eq_msm_trunc (p c bits : Nat) (s g : List Nat) :
    msmBucket p c bits s g = msm p (s.map (· % 2 ^ (c * ((bits + c - 1) / c)))) g := by
  rw [msmBucket, msm]
  refine Eq.trans (windowFold_mod p c (fun w => windowSum p c w s g) _
    (fun w => windowSum_mod p c w s g) _ 0) ?_
  rw [Nat.zero_mul, Nat.zero_add, sumRange_dotF, msmRaw_map]
  congr 1
  exact dotF_congr _ fun xb _ => digit_recompose c xb.1 _

theorem map_mod_self (K : Nat) (s : List Nat) (h : ∀ x ∈ s, x < K) : s.map (· % K) = s := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    rw [List.map_cons, Nat.mod_eq_of_lt (h x List.mem_cons_self),
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- The bucket method equals the reference when the windows cover every scalar. This is the
weakest pointwise bound: the method drops the bits from `c · nw` up. -/
theorem msmBucket_eq_msm_of_cover (p c bits : Nat) (s g : List Nat)
    (h : ∀ x ∈ s, x < 2 ^ (c * ((bits + c - 1) / c))) :
    msmBucket p c bits s g = msm p s g := by
  rw [msmBucket_eq_msm_trunc, map_mod_self _ s h]

/-- `nw = (bits + c - 1) / c` windows of `c ≥ 1` bits cover `bits` bits. -/
theorem bits_le_windows (c bits : Nat) (hc : 0 < c) : bits ≤ c * ((bits + c - 1) / c) := by
  have h1 := Nat.div_add_mod (bits + c - 1) c
  have h2 := Nat.mod_lt (bits + c - 1) hc
  omega

/-- Theorem 1: the bucket method equals the reference MSM for every modulus, every window
width `c ≥ 1`, every `bits` and all lists (any lengths), when each scalar is below
`2^bits`. -/
theorem msmBucket_eq_msm (p c bits : Nat) (s g : List Nat) (hc : 0 < c)
    (h : ∀ x ∈ s, x < 2 ^ bits) : msmBucket p c bits s g = msm p s g :=
  msmBucket_eq_msm_of_cover p c bits s g fun x hx =>
    Nat.lt_of_lt_of_le (h x hx) (Nat.pow_le_pow_right (by omega) (bits_le_windows c bits hc))

/-! ## Theorem 5: the point-chunk split -/

theorem msmRaw_append (s₁ s₂ g₁ g₂ : List Nat) (h : s₁.length = g₁.length) :
    msmRaw (s₁ ++ s₂) (g₁ ++ g₂) = msmRaw s₁ g₁ + msmRaw s₂ g₂ := by
  rw [msmRaw_eq_dotF, msmRaw_eq_dotF, msmRaw_eq_dotF, List.zip_append h, dotF_append]

theorem msm_append (p : Nat) (s₁ s₂ g₁ g₂ : List Nat) (h : s₁.length = g₁.length) :
    msm p (s₁ ++ s₂) (g₁ ++ g₂) = addM p (msm p s₁ g₁) (msm p s₂ g₂) := by
  rw [msm, msm, msm, addM, msmRaw_append _ _ _ _ h, Nat.add_mod]

/-! ## Theorem 4 (reference and bucket method): zero scalars and infinity bases -/

theorem msmRaw_cons (x b : Nat) (s g : List Nat) :
    msmRaw (x :: s) (b :: g) = x * b + msmRaw s g := rfl

theorem msmRaw_insert (x b : Nat) (s₁ s₂ g₁ g₂ : List Nat) (h : s₁.length = g₁.length) :
    msmRaw (s₁ ++ x :: s₂) (g₁ ++ b :: g₂) = msmRaw (s₁ ++ s₂) (g₁ ++ g₂) + x * b := by
  rw [msmRaw_append _ _ _ _ h, msmRaw_append _ _ _ _ h, msmRaw_cons]
  omega

/-- A pair with scalar `0`, at any position, does not change the MSM. -/
theorem msm_zero_scalar (p b : Nat) (s₁ s₂ g₁ g₂ : List Nat) (h : s₁.length = g₁.length) :
    msm p (s₁ ++ 0 :: s₂) (g₁ ++ b :: g₂) = msm p (s₁ ++ s₂) (g₁ ++ g₂) := by
  rw [msm, msm, msmRaw_insert _ _ _ _ _ _ h, Nat.zero_mul, Nat.add_zero]

/-- A pair whose base is the identity (`0` in the toy group), at any position, does not
change the MSM. -/
theorem msm_infinity_base (p x : Nat) (s₁ s₂ g₁ g₂ : List Nat) (h : s₁.length = g₁.length) :
    msm p (s₁ ++ x :: s₂) (g₁ ++ 0 :: g₂) = msm p (s₁ ++ s₂) (g₁ ++ g₂) := by
  rw [msm, msm, msmRaw_insert _ _ _ _ _ _ h, Nat.mul_zero, Nat.add_zero]

/-- The bucket method ignores a zero scalar at any position. No scalar bound is needed. -/
theorem msmBucket_zero_scalar (p c bits b : Nat) (s₁ s₂ g₁ g₂ : List Nat)
    (h : s₁.length = g₁.length) :
    msmBucket p c bits (s₁ ++ 0 :: s₂) (g₁ ++ b :: g₂)
      = msmBucket p c bits (s₁ ++ s₂) (g₁ ++ g₂) := by
  rw [msmBucket_eq_msm_trunc, msmBucket_eq_msm_trunc, List.map_append, List.map_cons,
    List.map_append, Nat.zero_mod]
  exact msm_zero_scalar p b _ _ _ _ (by rw [List.length_map, h])

/-- The bucket method ignores an identity base at any position. No scalar bound is needed. -/
theorem msmBucket_infinity_base (p c bits x : Nat) (s₁ s₂ g₁ g₂ : List Nat)
    (h : s₁.length = g₁.length) :
    msmBucket p c bits (s₁ ++ x :: s₂) (g₁ ++ 0 :: g₂)
      = msmBucket p c bits (s₁ ++ s₂) (g₁ ++ g₂) := by
  rw [msmBucket_eq_msm_trunc, msmBucket_eq_msm_trunc, List.map_append, List.map_cons,
    List.map_append]
  exact msm_infinity_base p _ _ _ _ _ (by rw [List.length_map, h])

/-! ## Theorem 3: the batched MSM -/

theorem zipWith_step {α β : Type} (F : α → List Nat → β) (f : α → List Nat → α) (accs : List α)
    (ss : List (List Nat)) :
    List.zipWith F (List.zipWith f accs ss) (ss.map List.tail)
      = List.zipWith (fun a s => F (f a s) s.tail) accs ss := by
  induction accs generalizing ss with
  | nil => simp
  | cons a accs ih => cases ss with
    | nil => simp
    | cons s ss => simp [ih]

theorem zipWith_const {α β : Type} (G : α → List Nat → β) (a : α) (ss : List (List Nat)) :
    List.zipWith G (ss.map fun _ => a) ss = ss.map (G a) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [ih]

theorem msmBatch_fold (p : Nat) (g : List Nat) (accs : List Nat) (ss : List (List Nat))
    (h : accs.length = ss.length) :
    (g.foldl (msmBatchStep p) (accs, ss)).1.map (· % p)
      = List.zipWith (fun acc s => (acc + msmRaw s g) % p) accs ss := by
  induction g generalizing accs ss with
  | nil =>
    simp only [List.foldl_nil]
    induction accs generalizing ss with
    | nil => simp
    | cons a accs ih => cases ss with
      | nil => simp at h
      | cons s ss => simp [msmRaw, ih ss (by simpa using h)]
  | cons b g ih =>
    rw [List.foldl_cons, msmBatchStep, ih _ _ (by simp [h]), zipWith_step]
    congr 1
    funext acc s
    cases s with
    | nil => simp [msmRaw, addM, mulM]
    | cons x s =>
      simp only [List.headD_cons, List.tail_cons, msmRaw_cons, addM, mulM, Nat.mod_add_mod,
        Nat.add_mod_mod, Nat.add_assoc]

/-- Theorem 3: the single-pass batched MSM equals the MSM of each scalar vector. Every batch
size (also empty) and every length: a scalar vector shorter or longer than the bases agrees
with the zip truncation of `msm`. -/
theorem msmBatch_eq (p : Nat) (ss : List (List Nat)) (g : List Nat) :
    msmBatch p ss g = ss.map fun s => msm p s g := by
  rw [msmBatch, msmBatch_fold p g _ ss (by simp), zipWith_const]
  exact List.map_congr_left fun s _ => by rw [Nat.zero_add, msm]

/-! ## Theorem 3, bucket variant: one bucket table per scalar vector, one pass -/

/-- The table of one scalar vector after the pass over the bases `g`. -/
def fillTable (p c : Nat) (tbl : Nat → Nat → Nat) : List Nat → List Nat → Nat → Nat → Nat
  | _, [] => tbl
  | s, b :: g => fillTable p c (fun w d =>
      if digit c w (s.headD 0) = d then addM p (tbl w d) b else tbl w d) s.tail g

/-- The pairs the pass reads: a vector that has run out reads scalar `0`. -/
def padZip : List Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | s, b :: g => (s.headD 0, b) :: padZip s.tail g

theorem bucketBatch_fold (p c : Nat) (g : List Nat) (tbls : List (Nat → Nat → Nat))
    (ss : List (List Nat)) (h : tbls.length = ss.length) :
    (g.foldl (bucketBatchStep p c) (tbls, ss)).1
      = List.zipWith (fun tbl s => fillTable p c tbl s g) tbls ss := by
  induction g generalizing tbls ss with
  | nil =>
    simp only [List.foldl_nil, fillTable]
    induction tbls generalizing ss with
    | nil => simp
    | cons a tbls ih => cases ss with
      | nil => simp at h
      | cons s ss => simp [← ih ss (by simpa using h)]
  | cons b g ih =>
    rw [List.foldl_cons, bucketBatchStep, ih _ _ (by simp [h]), zipWith_step]
    rfl

theorem fillTable_mod (p c w d : Nat) (g s : List Nat) (tbl : Nat → Nat → Nat) :
    fillTable p c tbl s g w d % p
      = (tbl w d + cnt d ((padZip s g).map fun xb => (digit c w xb.1, xb.2))) % p := by
  induction g generalizing s tbl with
  | nil => rfl
  | cons b g ih =>
    rw [fillTable, ih]
    simp only [padZip, List.map_cons, cnt]
    rw [← Nat.add_assoc]
    refine mod_add_congr ?_ rfl
    split
    · rw [addM, Nat.mod_mod]
    · rfl

theorem dotF_padZip (f : Nat → Nat) (hf : f 0 = 0) (g s : List Nat) :
    dotF f (padZip s g) = dotF f (s.zip g) := by
  induction g generalizing s with
  | nil => simp [padZip, dotF]
  | cons b g ih =>
    cases s with
    | nil => simp [padZip, dotF, hf, ih []]
    | cons x s => simp [padZip, dotF, ih s]

/-- One filled table, combined as in `msmBucket`, gives `msmBucket` of that vector. -/
theorem fillTable_result (p c bits : Nat) (s g : List Nat) :
    (List.range ((bits + c - 1) / c)).reverse.foldl (fun acc w => addM p (shiftWindow p c acc)
      (runningSum p ((List.range' 1 (2 ^ c - 1)).map
        (fillTable p c (fun _ _ => 0) s g w)))) 0 % p = msmBucket p c bits s g := by
  rw [msmBucket_eq_msm_trunc, msm, msmRaw_map]
  refine Eq.trans (windowFold_mod p c _ (fun w => dotF (digit c w) (padZip s g))
    (fun w => ?_) _ 0) ?_
  · rw [runningSum_buckets p (2 ^ c - 1) _ ((padZip s g).map fun xb => (digit c w xb.1, xb.2)),
      dotF_digitItems]
    · intro d
      rw [fillTable_mod, Nat.zero_add]
    · intro mv hmv
      obtain ⟨xb, -, rfl⟩ := List.mem_map.1 hmv
      have := digit_lt c w xb.1
      show digit c w xb.1 ≤ 2 ^ c - 1
      omega
  · rw [Nat.zero_mul, Nat.zero_add, sumRange_dotF, dotF_padZip _ _ g s]
    · congr 1
      exact dotF_congr _ fun xb _ => digit_recompose c xb.1 _
    · exact digit_recompose c 0 _ |>.trans (Nat.zero_mod _)

/-- Theorem 3, bucket variant: the single-pass batched bucket method equals `msmBucket` of
each scalar vector, for every modulus, width, batch size and length. -/
theorem msmBucketBatch_eq_msmBucket (p c bits : Nat) (ss : List (List Nat)) (g : List Nat) :
    msmBucketBatch p c bits ss g = ss.map fun s => msmBucket p c bits s g := by
  rw [msmBucketBatch, bucketBatch_fold p c g _ ss (by simp), zipWith_const, List.map_map]
  exact List.map_congr_left fun s _ => fillTable_result p c bits s g

/-- The batched bucket method equals the reference MSM of each scalar vector when every
scalar is below `2^bits`. -/
theorem msmBucketBatch_eq (p c bits : Nat) (ss : List (List Nat)) (g : List Nat) (hc : 0 < c)
    (h : ∀ s ∈ ss, ∀ x ∈ s, x < 2 ^ bits) :
    msmBucketBatch p c bits ss g = ss.map fun s => msm p s g := by
  rw [msmBucketBatch_eq_msmBucket]
  exact List.map_congr_left fun s hs => msmBucket_eq_msm p c bits s g hc (h s hs)

/-! ## Theorem 2: the signed-digit (Booth) method -/

/-- The kernel's encoding on a `(c+1)`-bit window value `v` (`T = 2^c`): the digit is
`⌈v/2⌉ - T · (top bit)`. -/
theorem booth_core (T v : Nat) (hv : v < 2 * T) :
    (if v / T % 2 = 1 then -(((T - (v + 1) % (2 * T) / 2) % T : Nat) : Int)
      else (((v + 1) % (2 * T) / 2 : Nat) : Int))
      = ((v / 2 : Nat) : Int) + ((v % 2 : Nat) : Int) - ((T * (v / T) : Nat) : Int) := by
  by_cases h : v < T
  · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt (show v + 1 < 2 * T by omega)]
    simp only [Nat.zero_mod, Nat.mul_zero]
    omega
  · have h1 : v / T = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [h1, Nat.mul_one]
    by_cases h2 : v + 1 < 2 * T
    · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (show T - (v + 1) / 2 < T by omega)]
      simp only [Nat.one_mod, ite_true]
      omega
    · have h3 : v + 1 = 2 * T := by omega
      rw [h3, Nat.mod_self]
      simp only [Nat.one_mod, ite_true, Nat.zero_div, Nat.sub_zero, Nat.mod_self]
      omega

/-- The window value `v`: bits `c·w - 1 .. c·w + c - 1` of `x` (with `0` below bit `0`). -/
def boothWval (c w x : Nat) : Nat := 2 * x / 2 ^ (c * w) % (2 * 2 ^ c)

theorem boothDigit_wval (c w x : Nat) :
    boothDigit c w x = ((boothWval c w x / 2 : Nat) : Int) + ((boothWval c w x % 2 : Nat) : Int)
      - ((2 ^ c * (boothWval c w x / 2 ^ c) : Nat) : Int) := by
  have hT : 0 < 2 ^ c := Nat.pow_pos (by omega)
  have hb := booth_core (2 ^ c) (boothWval c w x) (Nat.mod_lt _ (by omega))
  have hs : 2 * x / 2 ^ (c * w) / 2 ^ c % 2 = boothWval c w x / 2 ^ c % 2 := by
    rw [boothWval, Nat.mul_comm 2 (2 ^ c), Nat.mod_mul_right_div_self, Nat.mod_mod]
  have he : (2 * x / 2 ^ (c * w) + 1) % (2 * 2 ^ c) = (boothWval c w x + 1) % (2 * 2 ^ c) :=
    (Nat.mod_add_mod _ _ _).symm
  rw [← hb, ← hs, ← he]
  simp only [boothDigit, Nat.pow_succ, Nat.mul_comm (2 ^ c) 2]

theorem digit_eq_wval (c w x : Nat) : digit c w x = boothWval c w x / 2 := by
  rw [boothWval, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ (c * w)) 2,
    Nat.mul_div_mul_left _ _ (by omega)]
  rfl

theorem boothCarry_eq_wval (c w x : Nat) : boothCarry c w x = boothWval c w x % 2 := by
  rw [boothWval, Nat.mod_mul_right_mod]
  rfl

theorem boothCarry_succ_eq_wval (c w x : Nat) :
    boothCarry c (w + 1) x = boothWval c w x / 2 ^ c := by
  rw [boothWval, Nat.mul_comm 2 (2 ^ c), Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul,
    ← Nat.pow_add, ← Nat.mul_succ]
  rfl

/-- The arithmetic form of the signed digit: the unsigned digit, plus the carry in (the bit
below the window), minus `2^c` times the carry out (the top bit of the window). -/
theorem boothDigit_eq (c w x : Nat) :
    boothDigit c w x = (digit c w x : Int) + (boothCarry c w x : Int)
      - ((2 ^ c * boothCarry c (w + 1) x : Nat) : Int) := by
  rw [boothDigit_wval, digit_eq_wval, boothCarry_eq_wval, boothCarry_succ_eq_wval]

/-- Signed digits lie in `[-2^(c-1), 2^(c-1)]`: `2^(c-1)` buckets per window are enough. -/
theorem boothDigit_natAbs_le (c w x : Nat) (hc : 0 < c) :
    (boothDigit c w x).natAbs ≤ 2 ^ (c - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  have hv : boothWval (k + 1) w x < 2 * 2 ^ (k + 1) :=
    Nat.mod_lt _ (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
  rw [boothDigit_wval, Nat.add_sub_cancel]
  rw [Nat.pow_succ] at hv ⊢
  generalize boothWval (k + 1) w x = v at hv ⊢
  generalize 2 ^ k = H at hv ⊢
  by_cases h : v < H * 2
  · rw [Nat.div_eq_of_lt h]; omega
  · rw [show v / (H * 2) = 1 from Nat.div_eq_of_lt_le (by omega) (by omega)]; omega

/-- The positive and the negative part of the signed digit. -/
def posD (c w x : Nat) : Nat := (boothDigit c w x).toNat
def negD (c w x : Nat) : Nat := (-boothDigit c w x).toNat

theorem booth_window (c w x : Nat) :
    posD c w x + 2 ^ c * boothCarry c (w + 1) x = digit c w x + negD c w x + boothCarry c w x := by
  have h := boothDigit_eq c w x
  unfold posD negD
  omega

/-- Recomposition of the signed digits: `Σ_w 2^(c·w) · d_w = x mod 2^(c·n) - 2^(c·n) · carry_n`,
written without subtraction. -/
theorem booth_recompose (c x n : Nat) :
    sumRange (fun w => 2 ^ (c * w) * posD c w x) n + 2 ^ (c * n) * boothCarry c n x
      = x % 2 ^ (c * n) + sumRange (fun w => 2 ^ (c * w) * negD c w x) n := by
  induction n with
  | zero => simp [sumRange, boothCarry, Nat.mod_one]
  | succ n ih =>
    have hw := congrArg (2 ^ (c * n) * ·) (booth_window c n x)
    have hd : x % 2 ^ (c * (n + 1)) = x % 2 ^ (c * n) + 2 ^ (c * n) * digit c n x := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]; rfl
    simp only [Nat.mul_add, ← Nat.mul_assoc] at hw
    rw [sumRange, sumRange, hd, Nat.mul_succ, Nat.pow_add]
    omega

theorem add_mod_zero {p a k : Nat} (h : k % p = 0) : (a + k) % p = a % p := by
  rw [Nat.add_mod, h, Nat.add_zero, Nat.mod_mod]

theorem mul_mod_zero {p k : Nat} (b : Nat) (h : k % p = 0) : k * b % p = 0 := by
  rw [Nat.mul_mod, h, Nat.zero_mul, Nat.zero_mod]

theorem add_negM_mod (p b : Nat) (hp : 0 < p) : (b + negM p b) % p = 0 := by
  have hb := Nat.mod_lt b hp
  simp only [negM, subM, Nat.zero_mod, Nat.zero_add]
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod, show b % p + (p - b % p) = p by omega, Nat.mod_self]

theorem subM_mod (p a b : Nat) (hp : 0 < p) : subM p a b % p = (a + negM p b) % p := by
  have hb := Nat.mod_lt b hp
  simp only [subM, negM, Nat.zero_mod, Nat.zero_add, Nat.mod_mod, Nat.add_mod_mod]
  rw [show a % p + p - b % p = a % p + (p - b % p) by omega, Nat.mod_add_mod]

/-- The items of one signed window: (magnitude, base or negated base). -/
def boothItems (p c w : Nat) (ps : List (Nat × Nat)) : List (Nat × Nat) :=
  ps.map fun xb => ((boothDigit c w xb.1).natAbs,
    if boothDigit c w xb.1 < 0 then negM p xb.2 else xb.2)

/-- The pairs with every base negated. -/
def negBases (p : Nat) (ps : List (Nat × Nat)) : List (Nat × Nat) :=
  ps.map fun xb => (xb.1, negM p xb.2)

theorem boothBucket_fold (p c w m : Nat) (hp : 0 < p) (ps : List (Nat × Nat)) (a : Nat) :
    ps.foldl (fun acc (xb : Nat × Nat) =>
      let d := boothDigit c w xb.1
      if d.natAbs = m then (if d < 0 then subM p acc xb.2 else addM p acc xb.2) else acc) a % p
      = (a + cnt m (boothItems p c w ps)) % p := by
  induction ps generalizing a with
  | nil => rfl
  | cons xb ps ih =>
    rw [List.foldl_cons, ih]
    simp only [boothItems, List.map_cons, cnt]
    rw [← Nat.add_assoc]
    refine mod_add_congr ?_ rfl
    by_cases h1 : (boothDigit c w xb.1).natAbs = m
    · by_cases h2 : boothDigit c w xb.1 < 0
      · simp only [h1, h2, ite_true]; exact subM_mod p a xb.2 hp
      · simp only [h1, h2, ite_true, ite_false, addM, Nat.mod_mod]
    · simp only [h1, ite_false, Nat.add_zero]

theorem boothBucket_mod (p c w m : Nat) (ps : List (Nat × Nat)) (hp : ps ≠ [] → 0 < p) :
    boothBucket p c w m ps % p = cnt m (boothItems p c w ps) % p := by
  cases ps with
  | nil => rfl
  | cons xb ps =>
    rw [boothBucket, boothBucket_fold p c w m (hp (by simp)), Nat.zero_add]

theorem item_split (d : Int) (b nb : Nat) :
    d.natAbs * (if d < 0 then nb else b) = d.toNat * b + (-d).toNat * nb := by
  by_cases h : d < 0
  · rw [show d.toNat = 0 by omega, show d.natAbs = (-d).toNat by omega]; simp [h]
  · rw [show (-d).toNat = 0 by omega, show d.natAbs = d.toNat by omega]; simp [h]

theorem dotF_boothItems (p c w : Nat) (ps : List (Nat × Nat)) :
    dotF id (boothItems p c w ps) = dotF (posD c w) ps + dotF (negD c w) (negBases p ps) := by
  induction ps with
  | nil => rfl
  | cons xb ps ih =>
    simp only [boothItems, negBases, List.map_cons, dotF, id] at ih ⊢
    rw [ih, item_split, posD, negD]
    omega

/-- One signed window is `Σ (positive part) · base + Σ (negative part) · (−base)`. -/
theorem boothWindowSum_mod (p c w : Nat) (hc : 0 < c) (ps : List (Nat × Nat))
    (hp : ps ≠ [] → 0 < p) :
    boothWindowSum p c w ps % p
      = (dotF (posD c w) ps + dotF (negD c w) (negBases p ps)) % p := by
  rw [boothWindowSum, runningSum_buckets p (2 ^ (c - 1)) _ (boothItems p c w ps)
    (fun m => boothBucket_mod p c w m ps hp), dotF_boothItems]
  intro mv hmv
  obtain ⟨xb, -, rfl⟩ := List.mem_map.1 hmv
  exact boothDigit_natAbs_le c w xb.1 hc

theorem sumRange_mul_add (k a b : Nat → Nat) (n : Nat) :
    sumRange (fun w => k w * (a w + b w)) n
      = sumRange (fun w => k w * a w) n + sumRange (fun w => k w * b w) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show sumRange _ n + k n * (a n + b n) = (sumRange _ n + k n * a n) + (sumRange _ n + k n * b n)
    rw [ih, Nat.mul_add]
    omega

/-- A scalar whose signed digits recompose to it modulo `p`, times its base. -/
theorem booth_pair (p K P N cy x b : Nat) (hp : 0 < p) (hr : P + K * cy = x + N)
    (hz : K * cy % p = 0) : (P * b + N * negM p b) % p = x * b % p := by
  have e : P * b + N * negM p b + K * cy * b = x * b + N * (b + negM p b) := by
    have := congrArg (· * b) hr
    simp only [Nat.add_mul] at this
    rw [Nat.mul_add]
    omega
  rw [← add_mod_zero (mul_mod_zero b hz), e]
  exact add_mod_zero (by rw [Nat.mul_comm]; exact mul_mod_zero N (add_negM_mod p b hp))

/-- The signed windows of all pairs recompose to the plain MSM when the windows cover each
scalar and the top carry is `0` modulo `p`. -/
theorem booth_dot (p c n : Nat) (hp : 0 < p) (ps : List (Nat × Nat))
    (h : ∀ xb ∈ ps, xb.1 < 2 ^ (c * n) ∧ 2 ^ (c * n) * boothCarry c n xb.1 % p = 0) :
    (dotF (fun x => sumRange (fun w => 2 ^ (c * w) * posD c w x) n) ps
      + dotF (fun x => sumRange (fun w => 2 ^ (c * w) * negD c w x) n) (negBases p ps)) % p
      = dotF id ps % p := by
  induction ps with
  | nil => rfl
  | cons xb ps ih =>
    have ⟨h1, h2⟩ := h xb List.mem_cons_self
    have hr := booth_recompose c xb.1 n
    rw [Nat.mod_eq_of_lt h1] at hr
    simp only [negBases, List.map_cons, dotF, id] at ih ⊢
    have e := mod_add_congr (booth_pair p _ _ _ _ _ xb.2 hp hr h2)
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [← e]
    congr 1
    omega

theorem abs_pair (p x b : Nat) (hx : x < p) : (p - x) * negM p b % p = x * b % p := by
  have hp : 0 < p := by omega
  have e1 : ((p - x) * b + x * b) % p = 0 := by
    rw [← Nat.add_mul, show p - x + x = p by omega, Nat.mul_mod_right]
  have e2 : ((p - x) * negM p b + (p - x) * b) % p = 0 := by
    rw [← Nat.mul_add, Nat.add_comm, Nat.mul_comm]
    exact mul_mod_zero _ (add_negM_mod p b hp)
  rw [← add_mod_zero e1, ← Nat.add_assoc, Nat.add_mod, e2, Nat.zero_add, Nat.mod_mod]

/-- The `abs` fold changes no group element, whatever the fold test. -/
theorem dotF_scalarAbsBy (flip : Nat → Bool) (p : Nat) (ps : List (Nat × Nat))
    (h : ∀ xb ∈ ps, xb.1 < p) :
    dotF id (ps.map (scalarAbsBy flip p)) % p = dotF id ps % p := by
  induction ps with
  | nil => rfl
  | cons xb ps ih =>
    simp only [List.map_cons, dotF, id]
    refine mod_add_congr ?_ (ih fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold scalarAbsBy
    split
    · exact abs_pair p xb.1 xb.2 (h xb List.mem_cons_self)
    · rfl

theorem scalarAbsBy_fst (flip : Nat → Bool) (p : Nat) (xb : Nat × Nat) :
    (scalarAbsBy flip p xb).1 = absVal flip p xb.1 := by
  unfold scalarAbsBy absVal
  split <;> rfl

/-- After the exact `abs` every scalar is at most `p / 2`. -/
theorem absExact_le (p x : Nat) (h : x < p) : 2 * absVal (absExact p) p x ≤ p := by
  unfold absVal absExact
  split
  · rename_i hf
    have := of_decide_eq_true hf
    omega
  · rename_i hf
    have := of_decide_eq_false (Bool.eq_false_iff.2 hf)
    omega

/-- A folded scalar `x` is covered by the windows (`K = 2^(c·n)`), and its top carry vanishes
modulo `p`: the carry is `0`, or `2·x = p = K`. -/
theorem top_carry (p K x : Nat) (h : 2 * x < K ∨ (2 * x ≤ p ∧ p ≤ K)) (hp : 0 < p) :
    x < K ∧ K * (2 * x / K % 2) % p = 0 := by
  refine ⟨by omega, ?_⟩
  by_cases h1 : 2 * x < K
  · rw [Nat.div_eq_of_lt h1]; simp
  · have e : 2 * x = K := by omega
    rw [e, Nat.div_self (by omega), show K = p by omega]; simp

/-- The signed-digit method with any fold test equals the reference MSM when every folded
scalar `t` has `2·t < 2^(c · nwins)`, or `2·t ≤ p ≤ 2^(c · nwins)`. -/
theorem msmBoothBy_eq_msm_core (flip : Nat → Bool) (p c bits : Nat) (s g : List Nat)
    (hc : 0 < c) (hs : ∀ x ∈ s, x < p)
    (hf : ∀ x ∈ s, 2 * absVal flip p x < 2 ^ (c * ((bits - 1) / c + 1)) ∨
      (2 * absVal flip p x ≤ p ∧ p ≤ 2 ^ (c * ((bits - 1) / c + 1)))) :
    msmBoothBy flip p c bits s g = msm p s g := by
  have hps : ∀ xb ∈ s.zip g, xb.1 < p := fun xb h => hs _ (List.of_mem_zip h).1
  have hpos : (s.zip g).map (scalarAbsBy flip p) ≠ [] → 0 < p := by
    intro hne
    cases hz : s.zip g with
    | nil => rw [hz] at hne; simp at hne
    | cons xb ps => have := hps xb (by rw [hz]; exact List.mem_cons_self); omega
  rw [msmBoothBy, msm, msmRaw_eq_dotF, ← dotF_scalarAbsBy flip p _ hps]
  refine Eq.trans (windowFold_mod p c (fun w => boothWindowSum p c w _) _
    (fun w => boothWindowSum_mod p c w hc _ hpos) _ 0) ?_
  rw [Nat.zero_mul, Nat.zero_add, sumRange_mul_add, sumRange_dotF, sumRange_dotF]
  cases hz : (s.zip g).map (scalarAbsBy flip p) with
  | nil => rfl
  | cons yb qs =>
    have hp0 : 0 < p := hpos (by rw [hz]; simp)
    rw [← hz]
    refine booth_dot p c _ hp0 _ fun xb hxb => ?_
    obtain ⟨zb, hzb, rfl⟩ := List.mem_map.1 hxb
    rw [scalarAbsBy_fst]
    exact top_carry p _ _ (hf _ (List.of_mem_zip hzb).1) hp0

/-- The signed-digit method with ANY fold test (also one that folds too few or too many
scalars) equals the reference MSM when every folded scalar is below `2^(c · nwins - 1)`. -/
theorem msmBoothBy_eq_msm (flip : Nat → Bool) (p c bits : Nat) (s g : List Nat) (hc : 0 < c)
    (hs : ∀ x ∈ s, x < p)
    (hf : ∀ x ∈ s, 2 * absVal flip p x < 2 ^ (c * ((bits - 1) / c + 1))) :
    msmBoothBy flip p c bits s g = msm p s g :=
  msmBoothBy_eq_msm_core flip p c bits s g hc hs fun x hx => Or.inl (hf x hx)

/-- Theorem 2, weakest form: the signed-digit method equals the reference MSM when
`p ≤ 2^(c · nwins)`, with the kernel's `nwins = (bits - 1) / c + 1`. Every `c ≥ 1`, all
lengths, every scalar below `p`. -/
theorem msmBooth_eq_msm_of_cover (p c bits : Nat) (s g : List Nat) (hc : 0 < c)
    (hp : p ≤ 2 ^ (c * ((bits - 1) / c + 1))) (hs : ∀ x ∈ s, x < p) :
    msmBooth p c bits s g = msm p s g :=
  msmBoothBy_eq_msm_core (absExact p) p c bits s g hc hs fun x hx =>
    Or.inr ⟨absExact_le p x (hs x hx), hp⟩

/-- The kernel's `nwins = (bits - 1) / c + 1` windows of `c ≥ 1` bits cover `bits` bits. -/
theorem bits_le_nwins (c bits : Nat) (hc : 0 < c) : bits ≤ c * ((bits - 1) / c + 1) := by
  have h1 := Nat.div_add_mod (bits - 1) c
  have h2 := Nat.mod_lt (bits - 1) hc
  rw [Nat.mul_succ]
  omega

/-- Theorem 2: the signed-digit (sppark) method equals the reference MSM for every window
width `c ≥ 1`, all lists (any lengths), every scalar below `p`, and `bits` at least the bit
length of `p - 1` (`p ≤ 2^bits`). -/
theorem msmBooth_eq_msm (p c bits : Nat) (s g : List Nat) (hc : 0 < c) (hp : p ≤ 2 ^ bits)
    (hs : ∀ x ∈ s, x < p) : msmBooth p c bits s g = msm p s g :=
  msmBooth_eq_msm_of_cover p c bits s g hc
    (Nat.le_trans hp (Nat.pow_le_pow_right (by omega) (bits_le_nwins c bits hc))) hs

/-! ## Theorem 4 (signed-digit method) -/

theorem mem_insert_lt {p x : Nat} {s₁ s₂ : List Nat} (hx : x < p) (hs : ∀ y ∈ s₁ ++ s₂, y < p) :
    ∀ y ∈ s₁ ++ x :: s₂, y < p := by
  intro y hy
  rcases List.mem_append.1 hy with h | h
  · exact hs y (List.mem_append_left _ h)
  · rcases List.mem_cons.1 h with h | h
    · exact h ▸ hx
    · exact hs y (List.mem_append_right _ h)

/-- The signed-digit method ignores a zero scalar at any position. -/
theorem msmBooth_zero_scalar (p c bits b : Nat) (s₁ s₂ g₁ g₂ : List Nat) (hc : 0 < c)
    (hp : p ≤ 2 ^ bits) (h0 : 0 < p) (hs : ∀ x ∈ s₁ ++ s₂, x < p) (h : s₁.length = g₁.length) :
    msmBooth p c bits (s₁ ++ 0 :: s₂) (g₁ ++ b :: g₂)
      = msmBooth p c bits (s₁ ++ s₂) (g₁ ++ g₂) := by
  rw [msmBooth_eq_msm p c bits _ _ hc hp (mem_insert_lt h0 hs),
    msmBooth_eq_msm p c bits _ _ hc hp hs, msm_zero_scalar p b _ _ _ _ h]

/-- The signed-digit method ignores an identity base at any position. -/
theorem msmBooth_infinity_base (p c bits x : Nat) (s₁ s₂ g₁ g₂ : List Nat) (hc : 0 < c)
    (hp : p ≤ 2 ^ bits) (hx : x < p) (hs : ∀ y ∈ s₁ ++ s₂, y < p) (h : s₁.length = g₁.length) :
    msmBooth p c bits (s₁ ++ x :: s₂) (g₁ ++ 0 :: g₂)
      = msmBooth p c bits (s₁ ++ s₂) (g₁ ++ g₂) := by
  rw [msmBooth_eq_msm p c bits _ _ hc hp (mem_insert_lt hx hs),
    msmBooth_eq_msm p c bits _ _ hc hp hs, msm_infinity_base p x _ _ _ _ h]

/-! ## Theorem 6: the kernel's parameters (BLS12-381 scalar field, `10 ≤ c ≤ 18`)

The hypotheses `10 ≤ c` and `c ≤ 18` of the corollaries below describe the window
range of the vendored kernel. They are not a logical need: the proofs use only
`0 < c` (from `10 ≤ c`), `c ≤ 18` is not used at all, and the general theorems
(`msmBucket_eq_msm`, `msmBooth_eq_msm`, `msmBoothBy_eq_msm`) hold for every
window width `c ≥ 1`. -/

theorem blsR_le_pow255 : blsR ≤ 2 ^ 255 := by decide

/-- The signed-digit method at the kernel's parameters: `bits = bit_length = 255`.
`10 ≤ c ≤ 18` is the vendored kernel's window range, not a logical need: the
general theorem `msmBooth_eq_msm` holds for every `c ≥ 1`. -/
theorem msmBooth_blsR (c : Nat) (h10 : 10 ≤ c) (_h18 : c ≤ 18) (s g : List Nat)
    (hs : ∀ x ∈ s, x < blsR) : msmBooth blsR c 255 s g = msm blsR s g :=
  msmBooth_eq_msm blsR c 255 s g (by omega) blsR_le_pow255 hs

/-- sppark's top-limb `abs` test (8 limbs of 32 bits) leaves every scalar below `2^254`. -/
theorem absTopLimb_blsR (x : Nat) (h : x < blsR) :
    2 * absVal (absTopLimb 224 blsR) blsR x < 2 ^ 255 := by
  unfold absVal absTopLimb blsR at *
  split
  · rename_i hf
    have := of_decide_eq_true hf
    omega
  · rename_i hf
    have := of_decide_eq_false (Bool.eq_false_iff.2 hf)
    omega

/-- The signed-digit method with the fold test the vendored kernel really uses (top-limb
compare), at the kernel's parameters. `10 ≤ c ≤ 18` is the vendored kernel's window range,
not a logical need: `msmBoothBy_eq_msm` holds for every `c ≥ 1`. -/
theorem msmBoothBy_blsR_topLimb (c : Nat) (h10 : 10 ≤ c) (_h18 : c ≤ 18) (s g : List Nat)
    (hs : ∀ x ∈ s, x < blsR) :
    msmBoothBy (absTopLimb 224 blsR) blsR c 255 s g = msm blsR s g :=
  msmBoothBy_eq_msm _ blsR c 255 s g (by omega) hs fun x hx =>
    Nat.lt_of_lt_of_le (absTopLimb_blsR x (hs x hx))
      (Nat.pow_le_pow_right (by omega) (bits_le_nwins c 255 (by omega)))

/-- The bucket method at the kernel's window range, `bits = 255`. `10 ≤ c ≤ 18` is the
vendored kernel's range, not a logical need: `msmBucket_eq_msm` holds for every `c ≥ 1`. -/
theorem msmBucket_blsR_255 (c : Nat) (h10 : 10 ≤ c) (_h18 : c ≤ 18) (s g : List Nat)
    (hs : ∀ x ∈ s, x < blsR) : msmBucket blsR c 255 s g = msm blsR s g :=
  msmBucket_eq_msm blsR c 255 s g (by omega) fun x hx =>
    Nat.lt_of_lt_of_le (hs x hx) blsR_le_pow255

/-- The bucket method at the kernel's window range, `bits = 256` (the value `Tests` uses).
`10 ≤ c ≤ 18` is the vendored kernel's range, not a logical need: `msmBucket_eq_msm` holds
for every `c ≥ 1`. -/
theorem msmBucket_blsR_256 (c : Nat) (h10 : 10 ≤ c) (_h18 : c ≤ 18) (s g : List Nat)
    (hs : ∀ x ∈ s, x < blsR) : msmBucket blsR c 256 s g = msm blsR s g :=
  msmBucket_eq_msm blsR c 256 s g (by omega) fun x hx =>
    Nat.lt_of_lt_of_le (hs x hx) (Nat.le_trans blsR_le_pow255 (by decide))

/-- A small instance of Theorems 1 and 2, closed by the general theorems (no evaluation of
either device model). -/
theorem msm_F97_instance :
    msmBucket 97 2 7 [5, 0, 96, 33] [3, 4, 5, 6] = msm 97 [5, 0, 96, 33] [3, 4, 5, 6] ∧
    msmBooth 97 2 7 [5, 0, 96, 33] [3, 4, 5, 6] = msm 97 [5, 0, 96, 33] [3, 4, 5, 6] :=
  ⟨msmBucket_eq_msm 97 2 7 _ _ (by decide) (by decide),
   msmBooth_eq_msm 97 2 7 _ _ (by decide) (by decide) (by decide)⟩

/-! ## Counterexamples for the hypotheses of Theorems 1, 2 and 5, and probes -/

-- Theorem 1 needs `0 < c`: a zero-width window reads nothing.
#guard msmBucket 97 0 7 [5] [3] = 0 && msm 97 [5] [3] = 15
-- Theorem 1 needs the scalar bound: bits from `c · nw` up are dropped (`512 = 2^9`, `nw = 3`).
#guard msmBucket 97 3 9 [512] [1] = 0 && msm 97 [512] [1] = 27
-- `x < 2^bits` is not the weakest bound: 3 windows of 3 bits cover 9 bits, so 200 passes.
#guard msmBucket 97 3 7 [200] [3] = msm 97 [200] [3]
-- Theorem 2 needs `0 < c`.
#guard msmBooth 97 0 7 [5] [3] = 0 && msm 97 [5] [3] = 15
-- Theorem 2 holds at `c = 1` (digits in `{-1, 0, 1}`, one bucket per window).
#guard msmBooth 97 1 7 [5, 0, 96, 33, 48, 49] [3, 4, 5, 6, 7, 8]
  = msm 97 [5, 0, 96, 33, 48, 49] [3, 4, 5, 6, 7, 8]
-- Theorem 2 needs `p ≤ 2^(c · nwins)`: with `bits = 6`, `c = 2` the top carry of 40 is lost.
#guard msmBooth 97 2 6 [40] [1] = 73 && msm 97 [40] [1] = 40
-- Theorem 2 needs every scalar below `p`: `abs` computes `p - s`.
#guard msmBooth 97 3 7 [100] [1] = 0 && msm 97 [100] [1] = 3
-- The kernel's top-limb `abs` test is not the exact test: it leaves `(r+1)/2` unfolded.
#guard absExact blsR ((blsR + 1) / 2) && !absTopLimb 224 blsR ((blsR + 1) / 2)
-- `msm_append` and the insertion theorems need `s₁.length = g₁.length`.
#guard msm 97 ([1] ++ [2]) ([] ++ [3, 4]) = 11 && addM 97 (msm 97 [1] []) (msm 97 [2] [3, 4]) = 6
#guard msm 97 ([] ++ 0 :: [5]) ([1] ++ 9 :: [2]) = 45 && msm 97 ([] ++ [5]) ([1] ++ [2]) = 5
-- The batched models agree with zip truncation on vectors of different lengths.
#guard msmBatch 97 [[1, 2, 3], [4], [], [5, 6, 7, 8, 9]] [10, 20, 30] = [43, 40, 0, 89]
#guard msmBucketBatch 97 3 7 [[1, 2, 3], [4], [], [5, 6, 7, 8, 9]] [10, 20, 30] = [43, 40, 0, 89]

/-! ## Axiom pins -/

/-- info: 'GpuSpec.msmBucket_eq_msm_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucket_eq_msm_trunc
/-- info: 'GpuSpec.msmBucket_eq_msm_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucket_eq_msm_of_cover
/-- info: 'GpuSpec.msmBucket_eq_msm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucket_eq_msm
/-- info: 'GpuSpec.msmBooth_eq_msm_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBooth_eq_msm_of_cover
/-- info: 'GpuSpec.msmBoothBy_eq_msm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBoothBy_eq_msm
/-- info: 'GpuSpec.msmBoothBy_blsR_topLimb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBoothBy_blsR_topLimb
/-- info: 'GpuSpec.msmBooth_eq_msm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBooth_eq_msm
/-- info: 'GpuSpec.boothDigit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boothDigit_eq
/-- info: 'GpuSpec.msmBatch_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms msmBatch_eq
/-- info: 'GpuSpec.msmBucketBatch_eq_msmBucket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucketBatch_eq_msmBucket
/-- info: 'GpuSpec.msmBucketBatch_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucketBatch_eq
/-- info: 'GpuSpec.msm_zero_scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms msm_zero_scalar
/-- info: 'GpuSpec.msm_infinity_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms msm_infinity_base
/-- info: 'GpuSpec.msmBucket_zero_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucket_zero_scalar
/-- info: 'GpuSpec.msmBucket_infinity_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucket_infinity_base
/-- info: 'GpuSpec.msmBooth_zero_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBooth_zero_scalar
/-- info: 'GpuSpec.msmBooth_infinity_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBooth_infinity_base
/-- info: 'GpuSpec.msm_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms msm_append
/-- info: 'GpuSpec.msmBooth_blsR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBooth_blsR
/-- info: 'GpuSpec.msmBucket_blsR_255' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucket_blsR_255
/-- info: 'GpuSpec.msmBucket_blsR_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msmBucket_blsR_256
/-- info: 'GpuSpec.msm_F97_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msm_F97_instance

end GpuSpec
