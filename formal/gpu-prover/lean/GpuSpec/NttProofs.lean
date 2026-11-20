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

import GpuSpec.Algebra
import GpuSpec.Vectors

/-!
# General correctness of the transforms

`Tests.lean` pins the device FFT against the reference formulas on instances.
This file proves the same facts for every modulus `0 < p`, every size `2^m` and
every input, from the single algebraic hypothesis `ω^(2^(m-1)) = -1` (plus
invertibility where an inverse transform appears). No primality hypothesis and
no canonical-input hypothesis is used.

Every theorem assumes `0 < p`, because the proofs work in the ring `Fin p`. For
the two device-equals-reference theorems with a butterfly (`fft_eq_ntt`,
`fftCosetExt_eq`) the hypothesis is necessary: at `p = 0` the oracle's `subM` is
truncated subtraction and the statements fail (`p0_counterexample`,
`p0_counterexample_coset`). For the others it is a property of the proof route
and is not claimed necessary (`cosetExt_eq_ntt_scaled` is a polynomial identity
that also holds over `Nat`).

The last two sections show that the hypotheses hold for the BLS12-381 roots the
golden vectors use (kernel-checked, sizes `2^1 … 2^32`) and give one concrete
instance of every hypothesis set.
-/

namespace GpuSpec

open Lean.Grind

/-! ## Hypothesis vocabulary -/

/-- `ω ^ (n / 2) = -1` for `n = 2 ^ m` (no condition for `n = 1`). For `m ≥ 1`
this makes `ω` a primitive `2^m`-th root of unity in the sense the transforms need. -/
def IsRoot2 (p ω m : Nat) : Prop := m = 0 ∨ powM p ω (2 ^ (m - 1)) = (p - 1) % p

/-- `b` is a multiplicative inverse of `a` modulo `p`. -/
def IsInv (p a b : Nat) : Prop := mulM p a b = 1 % p

instance (p ω m : Nat) : Decidable (IsRoot2 p ω m) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (p a b : Nat) : Decidable (IsInv p a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- Why `0 < p` is a hypothesis of `fft_eq_ntt`. -/
theorem p0_counterexample : IsRoot2 0 0 1 ∧ fft 0 0 [1, 1] ≠ ntt 0 0 [1, 1] := by decide +kernel

/-- Why `0 < p` is a hypothesis of `fftCosetExt_eq`. -/
theorem p0_counterexample_coset :
    IsRoot2 0 0 1 ∧ fftCosetExt 0 1 0 1 [1, 1] ≠ cosetExt 0 1 0 1 [1, 1] := by decide +kernel

section General

variable {p : Nat}

theorem IsRoot2.toF [NeZero p] {ω m : Nat} (h : IsRoot2 p ω m) :
    m = 0 ∨ toF p ω ^ (2 ^ (m - 1)) = -1 :=
  h.imp id fun h => by rw [← toF_powM, h, toF_pred]

theorem IsInv.toF [NeZero p] {a b : Nat} (h : IsInv p a b) : toF p a * toF p b = 1 := by
  rw [← toF_mulM, show mulM p a b = 1 % p from h, toF_mod, toF_one]

/-- The inverse of a root is a root (used for the inverse transforms). -/
theorem IsRoot2.inv (hp : 0 < p) {ω m : Nat} (h : IsRoot2 p ω m) (hi : IsInv p ω (invM p ω)) :
    IsRoot2 p (invM p ω) m := by
  have : NeZero p := ⟨by omega⟩
  refine h.toF.imp id fun h' => ?_
  rw [powM_eq, root_inv h' hi.toF, ← toF_pred, toF_val, Nat.mod_mod]

/-! ## Pointwise form of the reference transform -/

theorem ntt_spec [NeZero p] (ω : Nat) (a : List Nat) :
    ntt p ω a = (List.range a.length).map fun k => (ev p a (toF p ω ^ k)).val :=
  List.map_congr_left fun k _ => ntt_term p ω k a

theorem length_ntt (q ω : Nat) (a : List Nat) : (ntt q ω a).length = a.length := by
  simp [ntt]

/-! ## 1. The device FFT equals the reference transform -/

theorem length_evens_odds : ∀ (a : List Nat) (h : Nat), a.length = 2 * h →
    (evens a).length = h ∧ (odds a).length = h
  | [], h, hl => by simp at hl; simp [evens, odds]; omega
  | [_], h, hl => by simp at hl; omega
  | _ :: _ :: t, h, hl => by
    have := length_evens_odds t (h - 1) (by simp at hl; omega)
    simp at hl
    simp [evens, odds]; omega

theorem fftAux_spec [NeZero p] : ∀ (m ω : Nat) (a : List Nat), a.length = 2 ^ m →
    (m = 0 ∨ toF p ω ^ (2 ^ (m - 1)) = -1) →
    fftAux p m ω a = (List.range (2 ^ m)).map fun k => (ev p a (toF p ω ^ k)).val
  | 0, ω, a, hl, _ => by
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hl)
    show [x % p] = [(ev p [x] (toF p ω ^ 0)).val]
    rw [← toF_val, ev_cons, ev_nil]; congr 2; grind
  | m + 1, ω, a, hl, hr => by
    have hw : toF p ω ^ (2 ^ m) = -1 := by simpa using hr
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by omega
    have h2 : 0 < 2 ^ m := Nat.two_pow_pos m
    obtain ⟨he, ho⟩ := length_evens_odds a (2 ^ m) (by omega)
    have hroot : m = 0 ∨ toF p (mulM p ω ω) ^ (2 ^ (m - 1)) = -1 := by
      rw [toF_mulM]; exact root_sq hw
    have hhalf : a.length / 2 = 2 ^ m := by omega
    simp only [fftAux, show ¬a.length ≤ 1 from by omega, ↓reduceIte, fftAux_spec m _ _ he hroot,
      fftAux_spec m _ _ ho hroot, hhalf, toF_mulM]
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2'
      simp only [List.length_map, List.length_range] at h2'
      simp only [List.getElem_map, List.getElem_range]
      rw [ev_evens_odds p a (toF p ω ^ i)]
      by_cases hi : i < 2 ^ m
      · rw [List.getElem_append_left (by simpa using hi)]
        simp only [List.getElem_map, List.getElem_zip, List.getElem_range, addM_eq, mulM_eq,
          powM_eq, toF_of_val, CommSemiring.mul_pow]
      · rw [List.getElem_append_right (by simpa using hi)]
        have hX : toF p ω ^ i = -(toF p ω ^ (i - 2 ^ m)) := by
          rw [show i = 2 ^ m + (i - 2 ^ m) from by omega, Semiring.pow_add, hw,
            ← show i = 2 ^ m + (i - 2 ^ m) from by omega]
          grind
        have hXX : -(toF p ω ^ (i - 2 ^ m)) * -(toF p ω ^ (i - 2 ^ m)) =
            toF p ω ^ (i - 2 ^ m) * toF p ω ^ (i - 2 ^ m) := by grind
        simp only [List.length_map, List.length_zip, List.length_range, Nat.min_self,
          List.getElem_map, List.getElem_zip, List.getElem_range, addM_eq, mulM_eq, subM_eq,
          powM_eq, toF_of_val, CommSemiring.mul_pow, hX, hXX]
        congr 1; grind

/-- **GPU-007, forward transform.** The radix-2 device FFT returns the reference
transform for every modulus `0 < p`, every size `2^m`, every input (reduced or
not) and every `ω` with `ω^(2^(m-1)) = -1`. -/
theorem fft_eq_ntt (hp : 0 < p) (m ω : Nat) (hω : IsRoot2 p ω m) (a : List Nat)
    (h : a.length = 2 ^ m) : fft p ω a = ntt p ω a := by
  have : NeZero p := ⟨by omega⟩
  rw [fft, log2, h, Nat.log2_two_pow, fftAux_spec m ω a h hω.toF, ntt_spec, h]

/-! ## 3. The device inverse FFT equals the reference inverse -/

theorem ifft_eq_intt (hp : 0 < p) (m ω : Nat) (hω : IsRoot2 p ω m) (hinv : IsInv p ω (invM p ω))
    (a : List Nat) (h : a.length = 2 ^ m) : ifft p ω a = intt p ω a := by
  rw [ifft, intt, fft_eq_ntt hp m _ (hω.inv hp hinv) a h]

/-! ## 4 and 5. Coset extension -/

/-- The scaling step of `fftCosetExt`: coefficient `i` times `ζ^i`. -/
def cosetScale (q ζ : Nat) (a : List Nat) : List Nat :=
  (List.range a.length).zip a |>.map fun (i, ai) => mulM q ai (powM q ζ i)

/-- `fftCosetExt` is: scale, zero-pad, FFT. -/
theorem fftCosetExt_unfold (q ζ ωe ext : Nat) (a : List Nat) :
    fftCosetExt q ζ ωe ext a =
      fft q ωe (cosetScale q ζ a ++ List.replicate (a.length * ext - a.length) 0) := rfl

theorem length_cosetScale (q ζ : Nat) (a : List Nat) : (cosetScale q ζ a).length = a.length := by
  simp [cosetScale]

theorem getElem_cosetScale (q ζ : Nat) (a : List Nat) (i : Nat) (h : i < a.length) :
    (cosetScale q ζ a)[i]'(by rw [length_cosetScale]; exact h) = mulM q a[i] (powM q ζ i) := by
  simp [cosetScale]

theorem ev_scale_aux [NeZero p] (ζ : Nat) (x : Fin p) : ∀ (a : List Nat) (s : Nat),
    ev p ((List.range' s a.length).zip a |>.map fun (i, ai) => mulM p ai (powM p ζ i)) x =
      toF p ζ ^ s * ev p a (toF p ζ * x)
  | [], s => by
    simp only [List.length_nil, List.range'_zero, List.zip_nil_left, List.map_nil, ev_nil]
    grind
  | c :: t, s => by
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, ev_cons,
      ev_scale_aux ζ x t (s + 1), toF_mulM, toF_powM, Semiring.pow_succ]
    grind

/-- Scaling the coefficients by `ζ^i` substitutes `ζ x` for `x`. -/
theorem ev_cosetScale [NeZero p] (ζ : Nat) (a : List Nat) (x : Fin p) :
    ev p (cosetScale p ζ a) x = ev p a (toF p ζ * x) := by
  rw [cosetScale, List.range_eq_range', ev_scale_aux, Semiring.pow_zero]; grind

theorem length_scaled_padded (q ζ ext : Nat) (hext : 1 ≤ ext) (a : List Nat) :
    (cosetScale q ζ a ++ List.replicate (a.length * ext - a.length) 0).length =
      a.length * ext := by
  have := Nat.le_mul_of_pos_right a.length hext
  simp [length_cosetScale]; omega

/-- The reference coset transform is the reference NTT of the scaled, zero-padded
polynomial. No root hypothesis: both sides are polynomial evaluation. -/
theorem cosetExt_eq_ntt_scaled (hp : 0 < p) (ζ ωe ext : Nat) (hext : 1 ≤ ext) (a : List Nat) :
    cosetExt p ζ ωe ext a =
      ntt p ωe (cosetScale p ζ a ++ List.replicate (a.length * ext - a.length) 0) := by
  have : NeZero p := ⟨by omega⟩
  rw [ntt_spec, length_scaled_padded p ζ ext hext, cosetExt]
  refine List.map_congr_left fun k _ => ?_
  rw [evalPoly_eq, toF_mulM, toF_powM, ev_append_zeros, ev_cosetScale]

/-- **GPU-007, coset extension.** The device coset transform returns the reference one. -/
theorem fftCosetExt_eq (hp : 0 < p) (m ζ ωe ext : Nat) (hext : 1 ≤ ext) (hω : IsRoot2 p ωe m)
    (a : List Nat) (h : a.length * ext = 2 ^ m) :
    fftCosetExt p ζ ωe ext a = cosetExt p ζ ωe ext a := by
  rw [fftCosetExt_unfold, cosetExt_eq_ntt_scaled hp ζ ωe ext hext,
    fft_eq_ntt hp m ωe hω _ (by rw [length_scaled_padded p ζ ext hext, h])]

/-! ## 2. The inverse transform inverts the forward transform -/

/-- The geometric sum of `u^j u'^i` over `2^m` terms is `2^m` when `j = i` and
zero otherwise. -/
theorem geom_delta [NeZero p] {m : Nat} {u u' : Fin p} (hu : m = 0 ∨ u ^ (2 ^ (m - 1)) = -1)
    (huu : u * u' = 1) {i j : Nat} (hi : i < 2 ^ m) (hj : j < 2 ^ m) :
    gsum (2 ^ m) (fun k => (u ^ j * u' ^ i) ^ k) = if j = i then toF p (2 ^ m) else 0 := by
  have hu' : m = 0 ∨ u' ^ (2 ^ (m - 1)) = -1 := hu.imp id fun h => root_inv h huu
  have hone : ∀ e, u ^ e * u' ^ e = 1 := fun e => by rw [← CommSemiring.mul_pow, huu, one_pow']
  split
  · next h =>
    subst h
    rw [gsum_congr (g := fun _ => 1) (fun k _ => by rw [hone, one_pow']), gsum_one]
  · next h =>
    by_cases hlt : i < j
    · have : u ^ j * u' ^ i = u ^ (j - i) := by
        rw [show j = (j - i) + i from by omega, Semiring.pow_add, Nat.add_sub_cancel]
        have := hone i; grind
      rw [this]; exact geom_zero m u hu (j - i) (by omega) (by omega)
    · have : u ^ j * u' ^ i = u' ^ (i - j) := by
        rw [show i = (i - j) + j from by omega, Semiring.pow_add, Nat.add_sub_cancel]
        have := hone j; grind
      rw [this]; exact geom_zero m u' hu' (i - j) (by omega) (by omega)

/-- The core of both round trips: transform with `u`, scale by `c`, transform
with the inverse `u'`; coefficient `i` comes back multiplied by `c * 2^m`. -/
theorem inv_core [NeZero p] {m : Nat} {u u' : Fin p} (c : Fin p)
    (hu : m = 0 ∨ u ^ (2 ^ (m - 1)) = -1) (huu : u * u' = 1) (a : List Nat)
    (hl : a.length = 2 ^ m) (i : Nat) (hi : i < 2 ^ m) :
    ev p ((List.range (2 ^ m)).map fun k => (c * ev p a (u ^ k)).val) (u' ^ i) =
      c * toF p (a.getD i 0) * toF p (2 ^ m) := by
  rw [ev_tabulate]
  simp only [toF_of_val, ev_eq_gsum, hl]
  have hterm : ∀ k, c * gsum (2 ^ m) (fun j => toF p (a.getD j 0) * (u ^ k) ^ j) * (u' ^ i) ^ k =
      gsum (2 ^ m) (fun j => c * toF p (a.getD j 0) * (u ^ j * u' ^ i) ^ k) := by
    intro k
    rw [← gsum_mul_left, ← gsum_mul_right]
    refine gsum_congr fun j _ => ?_
    rw [CommSemiring.mul_pow, ← pow_mul' u k j, ← pow_mul' u j k, Nat.mul_comm k j]; grind
  rw [gsum_congr (fun k _ => hterm k), gsum_swap]
  rw [gsum_congr (g := fun j => c * toF p (a.getD j 0) * (if j = i then toF p (2 ^ m) else 0))
    (fun j hj => by rw [gsum_mul_left, geom_delta hu huu hi hj])]
  rw [gsum_single i hi (fun j _ hji => by simp only [hji, ↓reduceIte]; grind)]
  simp only [↓reduceIte]

theorem intt_spec [NeZero p] (ω : Nat) (a : List Nat) :
    intt p ω a = (List.range a.length).map fun k =>
      (toF p (invM p (a.length % p)) * ev p a (toF p (invM p ω) ^ k)).val := by
  rw [intt, ntt_spec, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, mulM_eq, toF_of_val]

theorem getD_eq_getElem (a : List Nat) (i : Nat) (h : i < a.length) : a.getD i 0 = a[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- `intt ∘ ntt` reduces the input modulo `p` and changes nothing else. -/
theorem intt_ntt (hp : 0 < p) (m ω : Nat) (hω : IsRoot2 p ω m) (hinv : IsInv p ω (invM p ω))
    (hn : IsInv p (2 ^ m % p) (invM p (2 ^ m % p))) (a : List Nat) (h : a.length = 2 ^ m) :
    intt p ω (ntt p ω a) = a.map (· % p) := by
  have : NeZero p := ⟨by omega⟩
  have hN : toF p (2 ^ m) * toF p (invM p (2 ^ m % p)) = 1 := by rw [← toF_mod]; exact hn.toF
  rw [intt_spec, length_ntt, ntt_spec, h]
  apply List.ext_getElem
  · simp [h]
  · intro i h1 _
    have hi : i < 2 ^ m := by simpa using h1
    have key := inv_core 1 hω.toF hinv.toF a h i hi
    simp only [Semiring.one_mul] at key
    simp only [List.getElem_map, List.getElem_range, key, getD_eq_getElem a i (by omega)]
    exact val_eq_mod p (by grind)

/-- `ntt ∘ intt` reduces the input modulo `p` and changes nothing else. -/
theorem ntt_intt (hp : 0 < p) (m ω : Nat) (hω : IsRoot2 p ω m) (hinv : IsInv p ω (invM p ω))
    (hn : IsInv p (2 ^ m % p) (invM p (2 ^ m % p))) (a : List Nat) (h : a.length = 2 ^ m) :
    ntt p ω (intt p ω a) = a.map (· % p) := by
  have : NeZero p := ⟨by omega⟩
  have hN : toF p (2 ^ m) * toF p (invM p (2 ^ m % p)) = 1 := by rw [← toF_mod]; exact hn.toF
  have hinv' : toF p (invM p ω) * toF p ω = 1 := by have := hinv.toF; grind
  have hlen : (intt p ω a).length = 2 ^ m := by simp [intt, length_ntt, h]
  rw [ntt_spec, hlen, intt_spec, h]
  apply List.ext_getElem
  · simp [h]
  · intro i h1 _
    have hi : i < 2 ^ m := by simpa using h1
    have key := inv_core (toF p (invM p (2 ^ m % p))) ((hω.inv hp hinv).toF) hinv' a h i hi
    simp only [List.getElem_map, List.getElem_range, key, getD_eq_getElem a i (by omega)]
    exact val_eq_mod p (by grind)

/-! ## 6. Coset round trip -/

/-- Coefficients → extended coset → coefficients is the identity (up to reduction). -/
theorem cosetToCoeff_cosetExt (hp : 0 < p) (m ζ ωe ext : Nat) (hext : 1 ≤ ext)
    (hω : IsRoot2 p ωe m) (hinv : IsInv p ωe (invM p ωe))
    (hn : IsInv p (2 ^ m % p) (invM p (2 ^ m % p))) (hζ : IsInv p ζ (invM p ζ))
    (a : List Nat) (h : a.length * ext = 2 ^ m) :
    cosetToCoeff p ζ ωe a.length (cosetExt p ζ ωe ext a) = a.map (· % p) := by
  have : NeZero p := ⟨by omega⟩
  have hle := Nat.le_mul_of_pos_right a.length hext
  have hlen := length_scaled_padded p ζ ext hext a
  have hone : ∀ e, toF p ζ ^ e * toF p (invM p ζ) ^ e = 1 := fun e => by
    rw [← CommSemiring.mul_pow, hζ.toF, one_pow']
  rw [cosetToCoeff, cosetExt_eq_ntt_scaled hp ζ ωe ext hext,
    intt_ntt hp m ωe hω hinv hn _ (by rw [hlen, h])]
  apply List.ext_getElem
  · simp [length_ntt, hlen, length_cosetScale]; omega
  · intro i h1 h2
    have hi : i < a.length := by simpa using h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_zip, List.getElem_range,
      List.getElem_append_left (as := cosetScale p ζ a) (h := by rw [length_cosetScale]; exact hi),
      getElem_cosetScale p ζ a i hi, mulM_eq, powM_eq, toF_mod, toF_of_val]
    have := hone i
    exact val_eq_mod p (by grind)

/-- **GPU-007, inverse coset transform.** The device model returns the reference value. -/
theorem fftCosetToCoeff_eq (hp : 0 < p) (m ζ ωe n : Nat) (hω : IsRoot2 p ωe m)
    (hinv : IsInv p ωe (invM p ωe)) (v : List Nat) (h : v.length = 2 ^ m) :
    fftCosetToCoeff p ζ ωe n v = cosetToCoeff p ζ ωe n v := by
  rw [fftCosetToCoeff, cosetToCoeff, ifft_eq_intt hp m ωe hω hinv v h]

end General

/-! ## 7. The hypotheses hold for the BLS12-381 roots of the golden vectors

Checked by the kernel (`decide +kernel`, GMP arithmetic), for every size
`2^1 … 2^32` (32 is the 2-adicity of `blsR - 1`). -/

theorem blsR_pos : 0 < blsR := by decide

/-- The three side conditions at size `2^k`, as one decidable statement. -/
def BlsSizeOk (k : Nat) : Prop :=
  IsRoot2 blsR (rootOfUnity blsR blsGen (2 ^ k)) k ∧
  IsInv blsR (rootOfUnity blsR blsGen (2 ^ k)) (invM blsR (rootOfUnity blsR blsGen (2 ^ k))) ∧
  IsInv blsR (2 ^ k % blsR) (invM blsR (2 ^ k % blsR))

instance (k : Nat) : Decidable (BlsSizeOk k) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem bls_sizes_ok_table : (List.range' 1 32).all (fun k => decide (BlsSizeOk k)) = true := by
  decide +kernel

theorem bls_size_ok (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) : BlsSizeOk k :=
  of_decide_eq_true
    (List.all_eq_true.mp bls_sizes_ok_table k (List.mem_range'_1.mpr ⟨hk.1, by omega⟩))

theorem bls_isRoot2 (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) :
    IsRoot2 blsR (rootOfUnity blsR blsGen (2 ^ k)) k := (bls_size_ok k hk).1

theorem bls_isInv_root (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) :
    IsInv blsR (rootOfUnity blsR blsGen (2 ^ k)) (invM blsR (rootOfUnity blsR blsGen (2 ^ k))) :=
  (bls_size_ok k hk).2.1

theorem bls_isInv_size (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) :
    IsInv blsR (2 ^ k % blsR) (invM blsR (2 ^ k % blsR)) := (bls_size_ok k hk).2.2

/-- The coset shift `7` of the golden vectors is invertible. -/
theorem bls_isInv_gen : IsInv blsR blsGen (invM blsR blsGen) := by decide +kernel

/-- The coset shift `ζ₃` of the golden vectors is invertible. -/
theorem bls_isInv_zeta3 : IsInv blsR Vectors.zeta3 (invM blsR Vectors.zeta3) := by decide +kernel

theorem fft_eq_ntt_bls (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) (a : List Nat) (h : a.length = 2 ^ k) :
    fft blsR (rootOfUnity blsR blsGen (2 ^ k)) a = ntt blsR (rootOfUnity blsR blsGen (2 ^ k)) a :=
  fft_eq_ntt blsR_pos k _ (bls_isRoot2 k hk) a h

theorem ifft_eq_intt_bls (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) (a : List Nat) (h : a.length = 2 ^ k) :
    ifft blsR (rootOfUnity blsR blsGen (2 ^ k)) a =
      intt blsR (rootOfUnity blsR blsGen (2 ^ k)) a :=
  ifft_eq_intt blsR_pos k _ (bls_isRoot2 k hk) (bls_isInv_root k hk) a h

theorem intt_ntt_bls (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) (a : List Nat) (h : a.length = 2 ^ k) :
    intt blsR (rootOfUnity blsR blsGen (2 ^ k)) (ntt blsR (rootOfUnity blsR blsGen (2 ^ k)) a) =
      a.map (· % blsR) :=
  intt_ntt blsR_pos k _ (bls_isRoot2 k hk) (bls_isInv_root k hk) (bls_isInv_size k hk) a h

theorem ntt_intt_bls (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) (a : List Nat) (h : a.length = 2 ^ k) :
    ntt blsR (rootOfUnity blsR blsGen (2 ^ k)) (intt blsR (rootOfUnity blsR blsGen (2 ^ k)) a) =
      a.map (· % blsR) :=
  ntt_intt blsR_pos k _ (bls_isRoot2 k hk) (bls_isInv_root k hk) (bls_isInv_size k hk) a h

/-- Coset extension to a domain of size `2^k`, any shift `ζ`. -/
theorem fftCosetExt_eq_bls (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) (ζ ext : Nat) (hext : 1 ≤ ext)
    (a : List Nat) (h : a.length * ext = 2 ^ k) :
    fftCosetExt blsR ζ (rootOfUnity blsR blsGen (2 ^ k)) ext a =
      cosetExt blsR ζ (rootOfUnity blsR blsGen (2 ^ k)) ext a :=
  fftCosetExt_eq blsR_pos k ζ _ ext hext (bls_isRoot2 k hk) a h

/-- Coset round trip for the two shifts the golden vectors use. -/
theorem cosetToCoeff_cosetExt_bls (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) (ζ ext : Nat) (hext : 1 ≤ ext)
    (hζ : ζ = blsGen ∨ ζ = Vectors.zeta3) (a : List Nat) (h : a.length * ext = 2 ^ k) :
    cosetToCoeff blsR ζ (rootOfUnity blsR blsGen (2 ^ k)) a.length
      (cosetExt blsR ζ (rootOfUnity blsR blsGen (2 ^ k)) ext a) = a.map (· % blsR) :=
  cosetToCoeff_cosetExt blsR_pos k ζ _ ext hext (bls_isRoot2 k hk) (bls_isInv_root k hk)
    (bls_isInv_size k hk) (hζ.elim (fun e => e ▸ bls_isInv_gen) (fun e => e ▸ bls_isInv_zeta3)) a h

theorem fftCosetToCoeff_eq_bls (k : Nat) (hk : 1 ≤ k ∧ k ≤ 32) (ζ n : Nat) (v : List Nat)
    (h : v.length = 2 ^ k) :
    fftCosetToCoeff blsR ζ (rootOfUnity blsR blsGen (2 ^ k)) n v =
      cosetToCoeff blsR ζ (rootOfUnity blsR blsGen (2 ^ k)) n v :=
  fftCosetToCoeff_eq blsR_pos k ζ _ n (bls_isRoot2 k hk) (bls_isInv_root k hk) v h

/-! ## 8. Non-vacuity: every hypothesis set has an instance

Modulus 17, size `2^3`, `ω = rootOfUnity 17 3 8 = 9`, coset shift 3, extension
factor 2. The hypotheses are decided; each conclusion comes from the general
theorem, and the inputs are arbitrary lists of the right length. -/

/-- All hypotheses used by the general theorems hold together at `p = 17`, `m = 3`. -/
theorem witness_hyps_F17 :
    0 < 17 ∧ IsRoot2 17 (rootOfUnity 17 3 8) 3 ∧
    IsInv 17 (rootOfUnity 17 3 8) (invM 17 (rootOfUnity 17 3 8)) ∧
    IsInv 17 (2 ^ 3 % 17) (invM 17 (2 ^ 3 % 17)) ∧ IsInv 17 3 (invM 17 3) := by decide +kernel

theorem witness_fft_eq_ntt (a : List Nat) (h : a.length = 2 ^ 3) :
    fft 17 (rootOfUnity 17 3 8) a = ntt 17 (rootOfUnity 17 3 8) a :=
  fft_eq_ntt witness_hyps_F17.1 3 _ witness_hyps_F17.2.1 a h

theorem witness_intt_ntt (a : List Nat) (h : a.length = 2 ^ 3) :
    intt 17 (rootOfUnity 17 3 8) (ntt 17 (rootOfUnity 17 3 8) a) = a.map (· % 17) :=
  intt_ntt witness_hyps_F17.1 3 _ witness_hyps_F17.2.1 witness_hyps_F17.2.2.1
    witness_hyps_F17.2.2.2.1 a h

theorem witness_ntt_intt (a : List Nat) (h : a.length = 2 ^ 3) :
    ntt 17 (rootOfUnity 17 3 8) (intt 17 (rootOfUnity 17 3 8) a) = a.map (· % 17) :=
  ntt_intt witness_hyps_F17.1 3 _ witness_hyps_F17.2.1 witness_hyps_F17.2.2.1
    witness_hyps_F17.2.2.2.1 a h

theorem witness_ifft_eq_intt (a : List Nat) (h : a.length = 2 ^ 3) :
    ifft 17 (rootOfUnity 17 3 8) a = intt 17 (rootOfUnity 17 3 8) a :=
  ifft_eq_intt witness_hyps_F17.1 3 _ witness_hyps_F17.2.1 witness_hyps_F17.2.2.1 a h

theorem witness_cosetExt_eq_ntt_scaled (a : List Nat) :
    cosetExt 17 3 (rootOfUnity 17 3 8) 2 a =
      ntt 17 (rootOfUnity 17 3 8)
        (cosetScale 17 3 a ++ List.replicate (a.length * 2 - a.length) 0) :=
  cosetExt_eq_ntt_scaled witness_hyps_F17.1 3 _ 2 (by decide) a

theorem witness_fftCosetExt_eq (a : List Nat) (h : a.length * 2 = 2 ^ 3) :
    fftCosetExt 17 3 (rootOfUnity 17 3 8) 2 a = cosetExt 17 3 (rootOfUnity 17 3 8) 2 a :=
  fftCosetExt_eq witness_hyps_F17.1 3 3 _ 2 (by decide) witness_hyps_F17.2.1 a h

theorem witness_cosetToCoeff_cosetExt (a : List Nat) (h : a.length * 2 = 2 ^ 3) :
    cosetToCoeff 17 3 (rootOfUnity 17 3 8) a.length (cosetExt 17 3 (rootOfUnity 17 3 8) 2 a) =
      a.map (· % 17) :=
  cosetToCoeff_cosetExt witness_hyps_F17.1 3 3 _ 2 (by decide) witness_hyps_F17.2.1
    witness_hyps_F17.2.2.1 witness_hyps_F17.2.2.2.1 witness_hyps_F17.2.2.2.2 a h

theorem witness_fftCosetToCoeff_eq (n : Nat) (v : List Nat) (h : v.length = 2 ^ 3) :
    fftCosetToCoeff 17 3 (rootOfUnity 17 3 8) n v = cosetToCoeff 17 3 (rootOfUnity 17 3 8) n v :=
  fftCosetToCoeff_eq witness_hyps_F17.1 3 3 _ n witness_hyps_F17.2.1 witness_hyps_F17.2.2.1 v h

/-! Closed instances: literal inputs (with non-canonical entries `20`, `35 ≥ 17`),
every hypothesis discharged, the conclusion obtained from the general theorem. -/

theorem witness_concrete :
    fft 17 (rootOfUnity 17 3 8) [20, 1, 4, 1, 5, 9, 2, 6] =
      ntt 17 (rootOfUnity 17 3 8) [20, 1, 4, 1, 5, 9, 2, 6] :=
  witness_fft_eq_ntt _ rfl

theorem witness_concrete_intt_ntt :
    intt 17 (rootOfUnity 17 3 8) (ntt 17 (rootOfUnity 17 3 8) [20, 1, 4, 1, 5, 9, 2, 35]) =
      [3, 1, 4, 1, 5, 9, 2, 1] :=
  witness_intt_ntt _ rfl

theorem witness_concrete_ntt_intt :
    ntt 17 (rootOfUnity 17 3 8) (intt 17 (rootOfUnity 17 3 8) [20, 1, 4, 1, 5, 9, 2, 35]) =
      [3, 1, 4, 1, 5, 9, 2, 1] :=
  witness_ntt_intt _ rfl

theorem witness_concrete_ifft :
    ifft 17 (rootOfUnity 17 3 8) [20, 1, 4, 1, 5, 9, 2, 35] =
      intt 17 (rootOfUnity 17 3 8) [20, 1, 4, 1, 5, 9, 2, 35] :=
  witness_ifft_eq_intt _ rfl

theorem witness_concrete_cosetExt_eq_ntt_scaled :
    cosetExt 17 3 (rootOfUnity 17 3 8) 2 [20, 2, 3, 35] =
      ntt 17 (rootOfUnity 17 3 8)
        (cosetScale 17 3 [20, 2, 3, 35] ++ List.replicate 4 0) :=
  witness_cosetExt_eq_ntt_scaled _

theorem witness_concrete_fftCosetExt :
    fftCosetExt 17 3 (rootOfUnity 17 3 8) 2 [20, 2, 3, 35] =
      cosetExt 17 3 (rootOfUnity 17 3 8) 2 [20, 2, 3, 35] :=
  witness_fftCosetExt_eq _ rfl

theorem witness_concrete_coset_round_trip :
    cosetToCoeff 17 3 (rootOfUnity 17 3 8) 4
      (cosetExt 17 3 (rootOfUnity 17 3 8) 2 [20, 2, 3, 35]) = [3, 2, 3, 1] :=
  witness_cosetToCoeff_cosetExt [20, 2, 3, 35] rfl

theorem witness_concrete_fftCosetToCoeff :
    fftCosetToCoeff 17 3 (rootOfUnity 17 3 8) 4 [20, 1, 4, 1, 5, 9, 2, 35] =
      cosetToCoeff 17 3 (rootOfUnity 17 3 8) 4 [20, 1, 4, 1, 5, 9, 2, 35] :=
  witness_fftCosetToCoeff_eq 4 _ rfl

end GpuSpec
