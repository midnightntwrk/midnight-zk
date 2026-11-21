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

import GpuSpec.Ntt

/-!
# The bridge from the oracle's arithmetic to a commutative ring

The oracle computes on `Nat` with an explicit modulus `p` (`addM`, `mulM`,
`subM`, `powM`, `sumM`, `evalPoly`). For `0 < p` these are the ring operations
of `Fin p` under the map `toF p : Nat → Fin p`, `x ↦ x % p`. This file proves
that correspondence and the ring facts the transform proofs need:

* finite sums over an index range (`gsum`) and their algebra,
* Horner evaluation (`ev`) and its even/odd split (the radix-2 butterfly),
* the geometric sum of a power of a root with `u ^ (2 ^ (m - 1)) = -1` is zero
  (orthogonality). The proof uses only the commutative ring laws, so no
  primality or field hypothesis appears.

Ring identities are closed by `grind`, which decides commutative ring
equalities for any `Lean.Grind.CommRing` (and `Fin p` is one when `p ≠ 0`).
-/

namespace GpuSpec

open Lean.Grind

/-! ## Generic ring lemmas -/

section Ring

variable {R : Type} [CommRing R]

theorem pow_mul' (x : R) (a b : Nat) : x ^ (a * b) = (x ^ a) ^ b := by
  induction b with
  | zero => simp [Semiring.pow_zero]
  | succ b ih => rw [Nat.mul_succ, Semiring.pow_add, Semiring.pow_succ, ih]

theorem one_pow' (k : Nat) : (1 : R) ^ k = 1 := by
  induction k with
  | zero => exact Semiring.pow_zero _
  | succ k ih => rw [Semiring.pow_succ, ih]; grind

/-- `gsum n f = f 0 + f 1 + … + f (n - 1)`. -/
def gsum : Nat → (Nat → R) → R
  | 0, _ => 0
  | n + 1, f => gsum n f + f n

theorem gsum_congr {n : Nat} {f g : Nat → R} (h : ∀ k, k < n → f k = g k) :
    gsum n f = gsum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gsum]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem gsum_zero (n : Nat) : gsum n (fun _ => (0 : R)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gsum, ih]; grind

theorem gsum_add (n : Nat) (f g : Nat → R) :
    gsum n (fun k => f k + g k) = gsum n f + gsum n g := by
  induction n with
  | zero => simp only [gsum]; grind
  | succ n ih => simp only [gsum, ih]; grind

theorem gsum_mul_left (n : Nat) (c : R) (f : Nat → R) :
    gsum n (fun k => c * f k) = c * gsum n f := by
  induction n with
  | zero => simp only [gsum]; grind
  | succ n ih => simp only [gsum, ih]; grind

theorem gsum_mul_right (n : Nat) (c : R) (f : Nat → R) :
    gsum n (fun k => f k * c) = gsum n f * c := by
  induction n with
  | zero => simp only [gsum]; grind
  | succ n ih => simp only [gsum, ih]; grind

/-- Peel the first term instead of the last. -/
theorem gsum_succ' (n : Nat) (f : Nat → R) :
    gsum (n + 1) f = f 0 + gsum n (fun k => f (k + 1)) := by
  induction n with
  | zero => simp only [gsum]; grind
  | succ n ih => rw [gsum, ih]; simp only [gsum]; grind

/-- Exchange the order of a double sum. -/
theorem gsum_swap (n m : Nat) (f : Nat → Nat → R) :
    gsum n (fun k => gsum m (fun j => f k j)) = gsum m (fun j => gsum n (fun k => f k j)) := by
  induction n with
  | zero => simp only [gsum]; exact (gsum_zero m).symm
  | succ n ih => simp only [gsum, ih]; exact (gsum_add m _ _).symm

/-- A sum with one non-zero term. -/
theorem gsum_single {n : Nat} {f : Nat → R} (i : Nat) (hi : i < n)
    (h : ∀ j, j < n → j ≠ i → f j = 0) : gsum n f = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [gsum]
    by_cases hin : i = n
    · subst hin
      rw [gsum_congr (g := fun _ => 0) (fun k hk => h k (by omega) (by omega)), gsum_zero]
      grind
    · rw [ih (by omega) (fun j hj hji => h j (by omega) hji), h n (by omega) (by omega)]
      grind

/-- Pair consecutive terms. -/
theorem gsum_double (n : Nat) (f : Nat → R) :
    gsum (2 * n) f = gsum n (fun k => f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by omega]
    simp only [gsum, ih]; grind

/-- `1 + x + … + x^(2^(m+1) - 1) = (1 + x) (1 + x² + … + (x²)^(2^m - 1))`. -/
theorem geom_double (m : Nat) (x : R) :
    gsum (2 ^ (m + 1)) (fun k => x ^ k) = (1 + x) * gsum (2 ^ m) (fun k => (x * x) ^ k) := by
  rw [show 2 ^ (m + 1) = 2 * 2 ^ m from by omega, gsum_double, ← gsum_mul_left]
  apply gsum_congr
  intro k _
  rw [show 2 * k + 1 = k + k + 1 from by omega, show 2 * k = k + k from by omega,
    CommSemiring.mul_pow, Semiring.pow_succ, Semiring.pow_add]
  grind

/-- The square of a root for size `2^(m+1)` is a root for size `2^m`. -/
theorem root_sq {m : Nat} {u : R} (hu : u ^ (2 ^ m) = -1) :
    m = 0 ∨ (u * u) ^ (2 ^ (m - 1)) = -1 := by
  cases m with
  | zero => exact Or.inl rfl
  | succ m =>
    right
    rw [CommSemiring.mul_pow, ← Semiring.pow_add,
      show 2 ^ (m + 1 - 1) + 2 ^ (m + 1 - 1) = 2 ^ (m + 1) from by simp; omega]
    exact hu

/-- The inverse of a root is a root. -/
theorem root_inv {e : Nat} {u u' : R} (hu : u ^ e = -1) (huu : u * u' = 1) : u' ^ e = -1 := by
  have h : u ^ e * u' ^ e = 1 := by rw [← CommSemiring.mul_pow, huu, one_pow']
  rw [hu] at h; grind

/-- Orthogonality. If `u ^ (2 ^ (m - 1)) = -1` (or `m = 0`), the geometric sum of
`u ^ d` over `2 ^ m` terms is zero for every `0 < d < 2 ^ m`. -/
theorem geom_zero (m : Nat) : ∀ (u : R), (m = 0 ∨ u ^ (2 ^ (m - 1)) = -1) →
    ∀ d, 0 < d → d < 2 ^ m → gsum (2 ^ m) (fun k => (u ^ d) ^ k) = 0 := by
  induction m with
  | zero => intro u _ d h0 h1; simp at h1; omega
  | succ m ih =>
    intro u hu d h0 h1
    have hu : u ^ (2 ^ m) = -1 := by simpa using hu
    rw [geom_double]
    have hsq : u ^ d * u ^ d = (u * u) ^ d := (CommSemiring.mul_pow u u d).symm
    by_cases hd : d = 2 ^ m
    · rw [hd, hu]; grind
    · have hroot := root_sq hu
      have hpm : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by omega
      by_cases hlt : d < 2 ^ m
      · rw [hsq, ih (u * u) hroot d h0 hlt]; grind
      · have hd' : d = 2 ^ m + (d - 2 ^ m) := by omega
        have hone : (u * u) ^ (2 ^ m) = 1 := by rw [CommSemiring.mul_pow, hu]; grind
        have : (u * u) ^ d = (u * u) ^ (d - 2 ^ m) := by
          rw [hd', Semiring.pow_add, hone, ← hd']; grind
        rw [hsq, this, ih (u * u) hroot (d - 2 ^ m) (by omega) (by omega)]; grind

end Ring

/-! ## The map `Nat → Fin p` and the oracle's field operations -/

section Bridge

variable (p : Nat) [NeZero p]

/-- Reduction modulo `p` as a map into the ring `Fin p`. -/
def toF (x : Nat) : Fin p := Fin.ofNat p x

theorem toF_val (x : Nat) : (toF p x).val = x % p := rfl

theorem toF_of_val (x : Fin p) : toF p x.val = x :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt)

theorem toF_mod (x : Nat) : toF p (x % p) = toF p x :=
  Fin.ext (Nat.mod_mod _ _)

/-- The value of a ring element known to be the image of `n`. -/
theorem val_eq_mod {x : Fin p} {n : Nat} (h : x = toF p n) : x.val = n % p := by rw [h]; rfl

theorem toF_zero : toF p 0 = 0 := rfl

theorem toF_one : toF p 1 = 1 := rfl

theorem toF_succ (n : Nat) : toF p (n + 1) = toF p n + 1 := by
  apply Fin.ext
  show (n + 1) % p = (n % p + 1 % p) % p
  exact Nat.add_mod _ _ _

theorem addM_eq (a b : Nat) : addM p a b = (toF p a + toF p b).val := by
  simp [addM, toF, Fin.val_add]

theorem mulM_eq (a b : Nat) : mulM p a b = (toF p a * toF p b).val := by
  simp [mulM, toF, Fin.val_mul, Nat.mul_mod]

theorem subM_eq (a b : Nat) : subM p a b = (toF p a - toF p b).val := by
  have hb : b % p < p := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))
  show (a % p + p - b % p) % p = ((p - b % p) + a % p) % p
  congr 1; omega

theorem powM_eq (b : Nat) : ∀ e, powM p b e = (toF p b ^ e).val := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    unfold powM
    split
    · next h => subst h; rfl
    · next h =>
      have hpow : toF p b ^ e = toF p b ^ (e / 2) * toF p b ^ (e / 2) * toF p b ^ (e % 2) := by
        rw [← Semiring.pow_add, ← Semiring.pow_add]; congr 1; omega
      simp only [ih (e / 2) (by omega), mulM_eq, toF_of_val]
      split
      · next h1 => rw [hpow, h1]; congr 1; grind
      · next h1 =>
        rw [hpow, show e % 2 = 0 from by omega]; congr 1; grind

theorem toF_addM (a b : Nat) : toF p (addM p a b) = toF p a + toF p b := by
  rw [addM_eq, toF_of_val]

theorem toF_mulM (a b : Nat) : toF p (mulM p a b) = toF p a * toF p b := by
  rw [mulM_eq, toF_of_val]

theorem toF_powM (b e : Nat) : toF p (powM p b e) = toF p b ^ e := by
  rw [powM_eq, toF_of_val]

/-- `p - 1` is `-1` in `Fin p`. -/
theorem toF_pred : toF p ((p - 1) % p) = -1 := by
  have h : toF p ((p - 1) % p) + 1 = 0 := by
    rw [toF_mod, ← toF_succ]
    apply Fin.ext
    have := NeZero.ne p
    simp [toF, show p - 1 + 1 = p from by omega]
  grind

/-! ## Sums and Horner evaluation -/

/-- Horner evaluation of a coefficient list (lowest first) in `Fin p`. -/
def ev (a : List Nat) (x : Fin p) : Fin p :=
  a.foldr (fun c acc => toF p c + acc * x) 0

@[simp] theorem ev_nil (x : Fin p) : ev p [] x = 0 := rfl

@[simp] theorem ev_cons (c : Nat) (t : List Nat) (x : Fin p) :
    ev p (c :: t) x = toF p c + ev p t x * x := rfl

theorem evalPoly_eq (a : List Nat) (x : Nat) : evalPoly p a x = (ev p a (toF p x)).val := by
  induction a with
  | nil => rfl
  | cons c t ih =>
    show addM p c (mulM p (evalPoly p t x) x) = _
    rw [ih, addM_eq, mulM_eq, toF_of_val, toF_of_val]; rfl

/-- Reducing the coefficients does not change the value. -/
theorem ev_map_mod (a : List Nat) (x : Fin p) : ev p (a.map (· % p)) x = ev p a x := by
  induction a with
  | nil => rfl
  | cons c t ih => simp [ih, toF_mod]

/-- Trailing zero coefficients do not change the value. -/
theorem ev_append_zeros (a : List Nat) (z : Nat) (x : Fin p) :
    ev p (a ++ List.replicate z 0) x = ev p a x := by
  induction a with
  | nil =>
    induction z with
    | zero => rfl
    | succ z ih =>
      simp only [List.nil_append] at ih
      simp only [List.nil_append, List.replicate_succ, ev_cons, ih, toF_zero, ev_nil]; grind
  | cons c t ih => simp [ih]

/-- The even/odd split behind the radix-2 butterfly. -/
theorem ev_evens_odds : ∀ (a : List Nat) (x : Fin p),
    ev p a x = ev p (evens a) (x * x) + x * ev p (odds a) (x * x)
  | [], x => by simp only [evens, odds, ev_nil]; grind
  | [c], x => by simp only [evens, odds, ev_nil, ev_cons]; grind
  | c :: d :: t, x => by
    simp only [evens, odds, ev_cons, ev_evens_odds t x]; grind

/-- `sumM` as a fold in `Fin p`. -/
theorem foldl_addM (xs : List Nat) : ∀ acc,
    xs.foldl (addM p) acc % p = (toF p acc + xs.foldr (fun c s => toF p c + s) 0).val := by
  induction xs with
  | nil => intro acc; simp [toF_val]
  | cons c t ih =>
    intro acc
    simp only [List.foldl_cons, List.foldr_cons, ih, toF_addM]; congr 1; grind

theorem sumM_lt (xs : List Nat) : sumM p xs = sumM p xs % p := by
  have hp := Nat.pos_of_ne_zero (NeZero.ne p)
  have key : ∀ (xs : List Nat) (acc : Nat), acc < p → xs.foldl (addM p) acc < p := by
    intro xs
    induction xs with
    | nil => intro acc h; exact h
    | cons c t ih => intro acc _; exact ih _ (Nat.mod_lt _ hp)
  exact (Nat.mod_eq_of_lt (key xs 0 hp)).symm

/-- The sum of the terms `a[j] X^(s+j)` is `X^s` times the Horner value. -/
theorem fsum_terms (ω k : Nat) : ∀ (a : List Nat) (s : Nat),
    ((List.range' s a.length).zip a |>.map fun (j, aj) => mulM p aj (powM p ω (j * k))).foldr
      (fun c acc => toF p c + acc) 0 = (toF p ω ^ k) ^ s * ev p a (toF p ω ^ k)
  | [], s => by simp; grind
  | c :: t, s => by
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons,
      List.foldr_cons, fsum_terms ω k t (s + 1), toF_mulM, toF_powM, ev_cons, Semiring.pow_succ,
      Nat.mul_comm s k, pow_mul']
    grind

/-- One output of the reference transform is a Horner value. -/
theorem ntt_term (ω k : Nat) (a : List Nat) :
    sumM p ((List.range a.length).zip a |>.map fun (j, aj) => mulM p aj (powM p ω (j * k))) =
      (ev p a (toF p ω ^ k)).val := by
  rw [sumM_lt, sumM, foldl_addM, List.range_eq_range', fsum_terms, toF_zero, Semiring.pow_zero]
  congr 1; grind

/-- Horner evaluation as an indexed sum. -/
theorem ev_eq_gsum : ∀ (a : List Nat) (x : Fin p),
    ev p a x = gsum a.length (fun j => toF p (a.getD j 0) * x ^ j)
  | [], x => rfl
  | c :: t, x => by
    rw [ev_cons, List.length_cons, gsum_succ', ev_eq_gsum t x, ← gsum_mul_right]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Semiring.pow_zero, Semiring.pow_succ]
    rw [gsum_congr (g := fun k => toF p (t.getD k 0) * (x ^ k * x)) (fun k _ => by grind)]
    grind

/-- Horner evaluation of a tabulated list. -/
theorem ev_tabulate (n : Nat) (g : Nat → Nat) (x : Fin p) :
    ev p ((List.range n).map g) x = gsum n (fun k => toF p (g k) * x ^ k) := by
  rw [ev_eq_gsum, List.length_map, List.length_range]
  apply gsum_congr
  intro k hk
  simp [List.getD_eq_getElem?_getD, hk]

/-- The sum of `n` ones is the image of `n`. -/
theorem gsum_one (n : Nat) : gsum n (fun _ => (1 : Fin p)) = toF p n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum, ih, toF_succ]

end Bridge

end GpuSpec
