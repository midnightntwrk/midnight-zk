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

import GpuSpec.VectorsExt
import GpuSpec.PinsExt
import GpuSpec.NttProofs
import GpuSpec.MsmProofs

/-!
# Pins of the golden vector cases (contract v2)

For every case that `oracle --vectors` writes:

* the number of cases of each file and that the case names differ (a `.all`
  over an empty list passes, so every list is pinned non-empty by its length);
* the device models against the reference definitions on every value case;
* the decision of the entry gate for every decline case and every value case,
  with the expected reasons written here by hand from vectors/README.md (the
  generator computes them with `gate`, `gateMsm` and `gateShift`);
* the side conditions of `fft_eq_ntt_bls` for the threshold transforms.

The BLS12-381 checks use `#guard` (the compiled evaluator), like `Tests.lean`.
Pins on small numbers are also theorems closed by `decide +kernel`.
-/

namespace GpuSpec.Vectors

/-- The decision as text, for tables: `"run"` or the reason code. -/
def decisionCode (d : Option Reason) : String :=
  match d with
  | none => "run"
  | some r => r.code

/-- name, `min_k`, decision. -/
def row (name : String) (e : Expect) : String × Nat × String :=
  (name, e.minK, decisionCode e.decision)

/-! ## The generator of `randoms` (vectors/README.md, threshold.json) -/

#guard lcg 0 == 1442695040888963407
#guard lcg 1 == (6364136223846793005 + 1442695040888963407) % 2 ^ 64
-- one element takes four successive outputs, lowest limb first
#guard randoms blsR 5 1 ==
  [(lcg 5 + lcg (lcg 5) * 2 ^ 64 + lcg (lcg (lcg 5)) * 2 ^ 128 + lcg (lcg (lcg (lcg 5))) * 2 ^ 192)
    % blsR]
-- the second element starts from the fourth output of the first
#guard randoms blsR 5 2 == randoms blsR 5 1 ++ randoms blsR (lcg (lcg (lcg (lcg 5)))) 1
-- a shorter vector of the same seed is a prefix
#guard (randoms blsR 6000 40).take 33 == randoms blsR 6000 33

theorem randoms_fold_length (p : Nat) (l : List Nat) (acc : List Nat × Nat) :
    ((l.foldl (fun (acc : List Nat × Nat) _ =>
      let s1 := lcg acc.2
      let s2 := lcg s1
      let s3 := lcg s2
      let s4 := lcg s3
      ((s1 + s2 * 2 ^ 64 + s3 * 2 ^ 128 + s4 * 2 ^ 192) % p :: acc.1, s4)) acc).1).length =
      acc.1.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih]; simp; omega

/-- `randoms p seed n` has `n` elements. -/
theorem randoms_length (p seed n : Nat) : (randoms p seed n).length = n := by
  unfold randoms
  rw [List.length_reverse, randoms_fold_length]
  simp

/-! ## ntt.json -/

#guard nttCases.length == 10 && nttEdgeCases.length == 5 && nttAll.length == 15
#guard decide ((nttAll.map (·.name)).Nodup)
#guard nttAll.all fun c => c.input.all (· < blsR)

/-- The cases whose expectation is a value. -/
def nttValues : List NttCase := nttAll.filter fun c => (nttExpect c).decision.isNone

-- the table of the file: name, min_k, decision (written from the README)
#guard nttAll.map (fun c => row c.name (nttExpect c)) ==
  [("random-2^1", 1, "run"), ("random-2^2", 1, "run"), ("random-2^3", 1, "run"),
   ("random-2^4", 1, "run"), ("random-2^5", 1, "run"), ("random-2^6", 1, "run"),
   ("zero-2^3", 1, "run"), ("max-2^3", 1, "run"), ("delta-2^3", 1, "run"),
   ("const-2^3", 1, "run"), ("one-element", 1, "shape"), ("empty", 1, "shape"),
   ("length-3", 1, "shape"), ("length-6", 1, "shape"), ("length-7", 1, "shape")]
#guard nttAll.map (fun c => (c.input.length, c.logN)) ==
  [(2, 1), (4, 2), (8, 3), (16, 4), (32, 5), (64, 6), (8, 3), (8, 3), (8, 3), (8, 3), (1, 0),
   (0, 0), (3, 2), (6, 3), (7, 3)]
#guard nttValues.length == 10
-- the value cases are exactly `nttCases`; every edge case is a decline (ORACLE-27: also the
-- single element)
#guard nttValues.map (·.name) == nttCases.map (·.name)

-- device models = reference on every value case
#guard nttValues.all fun c => c.stock && nttRef c == ntt blsR c.omega c.input &&
  inttRef c == intt blsR c.omega c.input
#guard nttValues.all fun c => fft blsR c.omega c.input == ntt blsR c.omega c.input
#guard nttValues.all fun c => ifft blsR c.omega c.input == intt blsR c.omega c.input
#guard nttValues.all fun c => intt blsR c.omega (ntt blsR c.omega c.input) == c.input
-- a value case: the gate lets it through at its min_k and declines it at the default 14
#guard nttValues.all fun c =>
  gate (nttExpect c).minK maxLog true true c.input.length == none &&
  c.input.length < 2 ^ defaultMinK &&
  gate defaultMinK maxLog true true c.input.length == some .belowMinK
-- a decline case: `shape` from the gate at every min_k used (0, 1, 14). The stock function
-- takes the single element (its reference values are listed); it takes no other decline case
#guard (nttAll.filter fun c => (nttExpect c).decision.isSome).map (·.name) ==
  ["one-element", "empty", "length-3", "length-6", "length-7"]
#guard (nttAll.filter fun c => (nttExpect c).decision.isSome).all fun c =>
  [0, 1, defaultMinK].all (fun m => gate m maxLog true true c.input.length == some .shape) &&
  (c.name == "one-element" || (!c.stock && nttRef c == [] && inttRef c == []))
-- every omega is the root of the size 2^log_n; the length-1 root is 1 and the transform of
-- one element is the element
#guard nttAll.all fun c => c.omega == rootOfUnity blsR blsGen (2 ^ c.logN) &&
  powM blsR c.omega (2 ^ c.logN) == 1 &&
  (c.logN == 0 || powM blsR c.omega (2 ^ c.logN / 2) == blsR - 1)
#guard nttEdgeCases.head?.any fun c => c.name == "one-element" && c.omega == 1 &&
  c.input.length == 1 && nttRef c == c.input && inttRef c == c.input
-- ORACLE-27: the length 1 is a `shape` decline under every min_k (the kernel takes sizes
-- from 2), so the case lists min_k = 1 like every shape decline; the reference values of
-- the stock function stay in the file
#guard [0, 1, defaultMinK].all fun m => gate m maxLog true true 1 == some .shape
#guard nttEdgeCases.head?.any fun c => c.name == "one-element" && c.stock &&
  nttExpect c == { minK := 1, decision := some .shape } && !deviceSize maxLog c.input.length
-- the smallest transform the kernel runs has two elements
#guard gate 1 maxLog true true 2 == none && gate 0 maxLog true true 2 == none

/-! ## coset.json -/

#guard cosetCases.length == 8
#guard decide ((cosetCases.map (·.name)).Nodup)
#guard cosetCases.all fun c => c.input.all (· < blsR) && c.input.length == 2 ^ c.logN
#guard cosetCases.map (fun c => (row c.name (cosetExpect c), c.shift)) ==
  [(("shift7-2^2-x2", 1, "shape"), "generic"), (("zeta3-2^2-x2", 1, "run"), "zeta3"),
   (("shift7-2^3-x2", 1, "shape"), "generic"), (("zeta3-2^3-x2", 1, "run"), "zeta3"),
   (("shift7-2^2-x4", 1, "shape"), "generic"), (("zeta3-2^2-x4", 1, "run"), "zeta3"),
   (("shift7-2^4-x4", 1, "shape"), "generic"), (("zeta3-2^4-x4", 1, "run"), "zeta3")]
-- the shift name follows the shift gate; a generic shift is 7; `shape` comes from `gateShift`
#guard cosetCases.all fun c => (c.shift == "zeta3") == (gateShift blsR c.zeta == none) &&
  (c.shift == "generic") == (gateShift blsR c.zeta == some .shape) &&
  (c.shift == "generic") == (c.zeta == blsGen)
-- a value case runs at its min_k and declines with below-min-k at the default 14
#guard (cosetCases.filter fun c => (cosetExpect c).decision.isNone).all fun c =>
  cosetDecision (cosetExpect c).minK c == none && c.input.length * c.ext < 2 ^ defaultMinK &&
  cosetDecision defaultMinK c == some .belowMinK
-- a decline case declines with `shape` at every min_k (the shift test comes first)
#guard (cosetCases.filter fun c => (cosetExpect c).decision.isSome).all fun c =>
  [0, 1, defaultMinK].all fun m => cosetDecision m c == some .shape
-- device models = reference, for both shifts
#guard cosetCases.all fun c =>
  fftCosetExt blsR c.zeta c.omegaExt c.ext c.input == cosetExt blsR c.zeta c.omegaExt c.ext c.input
#guard cosetCases.all fun c =>
  let ext := cosetExt blsR c.zeta c.omegaExt c.ext c.input
  fftCosetToCoeff blsR c.zeta c.omegaExt c.input.length ext ==
    cosetToCoeff blsR c.zeta c.omegaExt c.input.length ext &&
  cosetToCoeff blsR c.zeta c.omegaExt c.input.length ext == c.input
-- omega_ext is a primitive (n · ext)-th root
#guard cosetCases.all fun c =>
  c.omegaExt == rootOfUnity blsR blsGen (2 ^ c.logN * c.ext) &&
  powM blsR c.omegaExt (2 ^ c.logN * c.ext) == 1 &&
  powM blsR c.omegaExt (2 ^ c.logN * c.ext / 2) == blsR - 1

/-! ## msm.json -/

#guard msmCases.length == 14 && msmDeclineCases.length == 2 && msmAll.length == 16
#guard decide ((msmAll.map (·.name)).Nodup)
#guard msmAll.all fun c => c.scalars.all (· < blsR) && c.bases.all (· < blsR) &&
  c.mask.all (· < blsR) && c.mask.length == c.scalars.length
#guard msmAll.map (fun c => row c.name (msmExpect c)) ==
  [("uniform", 1, "run"), ("zero", 1, "run"), ("repeated", 1, "run"),
   ("ninety-percent-zero", 1, "run"), ("below-2^16", 1, "run"), ("max", 1, "run"),
   ("one-point", 0, "run"), ("infinity-every-fourth-base", 1, "run"),
   ("infinity-all-bases", 1, "run"), ("zero-scalars-and-infinity-bases", 1, "run"),
   ("fold-boundary", 1, "run"), ("length-3", 1, "run"), ("length-31", 1, "run"),
   ("length-33", 1, "run"), ("empty", 1, "shape"), ("scalars-longer-than-bases", 1, "shape")]
#guard msmAll.map (fun c => (c.scalars.length, c.bases.length)) ==
  [(32, 32), (32, 32), (32, 32), (32, 32), (32, 32), (32, 32), (1, 1), (32, 32), (32, 32),
   (32, 32), (8, 8), (3, 3), (31, 31), (33, 33), (0, 0), (32, 31)]
-- the value cases are exactly `msmCases`
#guard (msmAll.filter fun c => (msmExpect c).decision.isNone).map (·.name) ==
  msmCases.map (·.name)
-- a value case: `gateMsm` lets it through at its min_k and declines it at the default 14
#guard msmCases.all fun c =>
  gateMsm (msmExpect c).minK maxLog true true c.scalars.length == none &&
  c.scalars.length == c.bases.length && c.scalars.length < 2 ^ defaultMinK &&
  gateMsm defaultMinK maxLog true true c.scalars.length == some .belowMinK
#guard gateMsm 1 maxLog true true 1 == some .belowMinK && gateMsm 0 maxLog true true 1 == none
-- the empty input: `shape` from `gateMsm` at every min_k
#guard [0, 1, defaultMinK].all fun m => gateMsm m maxLog true true 0 == some .shape
-- more scalars than bases: `shape` from `gateMsm2` at every min_k (32 scalars, 31 bases: the
-- lengths differ). `gateMsm` alone sees one length (32) and would let it through at
-- min_k = 1: the clause is the length test of `gateMsm2`.
#guard msmDeclineCases.all fun c =>
  [0, 1, defaultMinK].all fun m =>
    gateMsm2 m maxLog true true c.scalars.length c.bases.length == some .shape &&
    msmDecision m c == some .shape
#guard (msmDeclineCases.filter (·.name == "scalars-longer-than-bases")).map (fun c =>
    (c.scalars.length, c.bases.length,
     [0, 1, defaultMinK].map fun m => gateMsm2 m maxLog true true c.scalars.length c.bases.length))
  == [(32, 31, [some .shape, some .shape, some .shape])]
-- the vector decision is `gateMsm2` on the two lengths, for every case and every min_k used
#guard msmAll.all fun c => [0, 1, defaultMinK].all fun m =>
  msmDecision m c == gateMsm2 m maxLog true true c.scalars.length c.bases.length
-- every value case has equal lengths, so `gateMsm2` is `gateMsm` on it (`gateMsm2_eq`)
#guard msmCases.all fun c => c.scalars.length == c.bases.length
#guard msmDeclineCases.map (fun c => gateMsm 1 maxLog true true c.scalars.length) ==
  [some .shape, none]
-- its listed result is the reference value of the common prefix
#guard msmDeclineCases.all fun c =>
  msm blsR c.scalars c.bases == msm blsR (c.scalars.take c.bases.length) c.bases

/-! ### The case contents the README names -/

def msmCase (name : String) : MsmCase :=
  (msmAll.find? (·.name == name)).getD { name := "", scalars := [], bases := [], mask := [] }

#guard (msmCase "zero").scalars.all (· == 0)
#guard (msmCase "repeated").scalars.eraseDups.length == 1
#guard ((msmCase "ninety-percent-zero").scalars.filter (· == 0)).length == 28
#guard (msmCase "below-2^16").scalars.all (· < 2 ^ 16)
#guard (msmCase "max").scalars.all (· == blsR - 1)
#guard ((List.range 32).zip (msmCase "infinity-every-fourth-base").bases).all fun (i, b) =>
  (b == 0) == (i % 4 == 0)
#guard (msmCase "infinity-all-bases").bases.all (· == 0)
#guard let c := msmCase "zero-scalars-and-infinity-bases"
  ((c.scalars.zip c.bases).filter fun (s, b) => s == 0 && b == 0).length == 3 &&
  ((c.scalars.zip c.bases).filter fun (s, b) => s == 0 && b != 0).length == 8 &&
  ((c.scalars.zip c.bases).filter fun (s, b) => s != 0 && b == 0).length == 5
#guard (msmCase "fold-boundary").scalars == foldBoundaryScalars

/-! ### The fold boundary of the signed-digit method

`abs` folds a scalar above `(r-1)/2`: of the eight scalars, `(r+1)/2`, `r-1`, `2^254` and
`2^254 - 1` (`r` is about `1.8 · 2^254`, so `2^250 - 1` and `2^247 - 1` are below the
boundary). The vendored kernel compares top limbs only (`absTopLimb 224`), which leaves
`(r+1)/2` unfolded; the MSM result is the same. -/

theorem pin_foldBoundary :
    foldBoundaryScalars = [(blsR - 1) / 2, (blsR + 1) / 2, 1, blsR - 1, 2 ^ 254, 2 ^ 254 - 1,
      2 ^ 250 - 1, 2 ^ 247 - 1] ∧
    (blsR - 1) / 2 + (blsR + 1) / 2 = blsR ∧
    foldBoundaryScalars.map (absExact blsR) = [false, true, false, true, true, true, false, false] ∧
    foldBoundaryScalars.map (absTopLimb 224 blsR) =
      [false, false, false, true, true, true, false, false] ∧
    (∀ x ∈ foldBoundaryScalars, x < blsR) := by decide +kernel
#guard foldBoundaryScalars.map (absExact blsR) ==
  [false, true, false, true, true, true, false, false]
#guard foldBoundaryScalars.map (absTopLimb 224 blsR) ==
  [false, false, false, true, true, true, false, false]
#guard foldBoundaryScalars.all (· < blsR)
-- windows that are all ones: every 10-bit window of 2^250 - 1 (25 of them), every 13-bit
-- window of 2^247 - 1 (19), and for 2^254 - 1 every full window of both widths
#guard (List.range 25).all fun w => digit 10 w (2 ^ 250 - 1) == 2 ^ 10 - 1
#guard (List.range 19).all fun w => digit 13 w (2 ^ 247 - 1) == 2 ^ 13 - 1
#guard ((List.range 25).all fun w => digit 10 w (2 ^ 254 - 1) == 2 ^ 10 - 1) &&
  (List.range 19).all fun w => digit 13 w (2 ^ 254 - 1) == 2 ^ 13 - 1
-- each boundary scalar alone, both fold tests, both widths
#guard foldBoundaryScalars.all fun s => [10, 13].all fun c =>
  msmBooth blsR c 255 [s] [msmBases.headD 1] == msm blsR [s] [msmBases.headD 1] &&
  msmBoothBy (absTopLimb 224 blsR) blsR c 255 [s] [msmBases.headD 1] ==
    msm blsR [s] [msmBases.headD 1]

/-! ### Device models = reference on every value case -/

#guard msmCases.all fun c => msmBucket blsR 8 256 c.scalars c.bases == msm blsR c.scalars c.bases
#guard msmCases.all fun c => msmBucket blsR 13 256 c.scalars c.bases == msm blsR c.scalars c.bases
#guard msmCases.all fun c => msmBooth blsR 10 255 c.scalars c.bases == msm blsR c.scalars c.bases
#guard msmCases.all fun c => msmBooth blsR 13 255 c.scalars c.bases == msm blsR c.scalars c.bases
#guard msmCases.all fun c =>
  msmBoothBy (absTopLimb 224 blsR) blsR 10 255 c.scalars c.bases == msm blsR c.scalars c.bases
#guard msmCases.all fun c =>
  msmBoothBy (absTopLimb 224 blsR) blsR 13 255 c.scalars c.bases == msm blsR c.scalars c.bases
#guard msmCases.all fun c => msmMasked blsR c.mask c.scalars c.bases == msm blsR c.scalars c.bases
-- GPU-013 as the file states it: MSM(masked_scalars) - mask_result = result
#guard msmCases.all fun c =>
  subM blsR (msm blsR (maskScalars blsR c.scalars c.mask) c.bases) (msm blsR c.mask c.bases) ==
    msm blsR c.scalars c.bases

/-- The value cases over the shared base vector `msmBases`. -/
def msmShared : List MsmCase := msmCases.filter (·.bases == msmBases)

#guard msmShared.map (·.name) ==
  ["uniform", "zero", "repeated", "ninety-percent-zero", "below-2^16", "max"]
#guard msmBatch blsR (msmShared.map (·.scalars)) msmBases ==
  msmShared.map fun c => msm blsR c.scalars c.bases
-- the shorter cases over prefixes of the same vector batch with it too
#guard let pre := msmCases.filter fun c => c.bases == msmBases.take c.bases.length
  pre.length == 10 &&
  msmBatch blsR (pre.map (·.scalars)) msmBases == pre.map fun c => msm blsR c.scalars c.bases

/-! ## quotient.json -/

#guard quotientCases.length == 8
#guard decide ((quotientCases.map (·.name)).Nodup)
#guard quotientCases.map (fun c => (c.name, c.cols.size, c.cols.ratio, c.n, c.gates.length)) ==
  [("all-node-types", 16, 4, 4, 4), ("single-gate", 16, 4, 4, 1), ("rotations-wrap", 16, 4, 4, 3),
   ("domain-64-ratio-8", 64, 8, 8, 7), ("no-gate", 16, 4, 4, 0), ("zero-columns", 16, 4, 4, 4),
   ("two-instance-columns", 16, 4, 4, 3), ("domain-32-n-4", 32, 8, 4, 7)]
-- the number of instance columns of each case: one case has two
#guard quotientCases.map (·.cols.inst.length) == [1, 1, 1, 1, 1, 1, 2, 1]
-- the cases whose `n` differs from the ratio `N / n`: one (in every other case the two are
-- equal, and a vanishing exponent of `N / n` in place of `n` would not show)
#guard (quotientCases.filter fun c => c.n != c.cols.size / c.n).map (·.name) == ["domain-32-n-4"]
#guard quotientCases.all fun c =>
  (c.cols.fixed ++ c.cols.advice ++ c.cols.inst).all (fun col => col.length == c.cols.size &&
    col.all (· < blsR)) && c.cols.challenges.all (· < blsR) && c.y < blsR
-- device models = reference
#guard quotientCases.all fun c =>
  deviceNumerator blsR c.y c.cols c.gates == numerator blsR c.y c.cols c.gates
#guard quotientCases.all fun c => [1, 3, 5, 16, c.cols.size + 1].all fun t =>
  deviceNumeratorTiled blsR c.y c.cols c.gates t == numerator blsR c.y c.cols c.gates

def quotientCase (name : String) : QuotientCase :=
  (quotientCases.find? (·.name == name)).getD
    { name := "", y := 0, gates := [],
      cols := { fixed := [], advice := [], inst := [], challenges := [], size := 0, ratio := 0 } }

/-- The rotations of an expression. -/
def rotations : Expr → List Int
  | .fixed _ r | .advice _ r | .inst _ r => [r]
  | .neg e | .scaled e _ => rotations e
  | .sum a b | .prod a b => rotations a ++ rotations b
  | _ => []

-- rotations +2 and -3 wrap at both ends: the last point reads index 7, the first index 4
#guard let c := quotientCase "rotations-wrap"
  (c.gates.flatMap rotations).eraseDups == [2, -3] &&
  rotIndex c.cols 15 2 == 7 && rotIndex c.cols 8 2 == 0 && rotIndex c.cols 7 2 == 15 &&
  rotIndex c.cols 0 (-3) == 4 && rotIndex c.cols 11 (-3) == 15 && rotIndex c.cols 12 (-3) == 0
#guard let c := quotientCase "domain-64-ratio-8"
  (c.gates.flatMap rotations).eraseDups == [0, 1, -1, 2, -3] &&
  rotIndex c.cols 63 2 == 15 && rotIndex c.cols 0 (-3) == 40
#guard let c := quotientCase "no-gate"
  numerator blsR c.y c.cols c.gates == List.replicate 16 0
#guard let c := quotientCase "zero-columns"
  (c.cols.fixed ++ c.cols.advice ++ c.cols.inst).all (·.all (· == 0)) &&
  numerator blsR c.y c.cols c.gates != List.replicate 16 0  -- the constants remain

-- two instance columns with different data. The numerator is recomputed here from the
-- README sentences with plain list reads (no `evalE`): gates `i0[k] · i1[k + 4]`,
-- `i1[k] − i0[k − 4]` and `i1[k]` (rotation ±1 is ±4 points at ratio 4), Horner in `y`.
-- A reference that reads instance column 0 for every instance column fails this.
#guard let c := quotientCase "two-instance-columns"
  let i0 := c.cols.inst.getD 0 []
  let i1 := c.cols.inst.getD 1 []
  let at' := fun (col : List Nat) (k : Nat) => col.getD (k % 16) 0
  i0.length == 16 && i1.length == 16 && i0 != i1 && (List.range 16).all (fun k => i0.getD k 0 != i1.getD k 0) &&
  numerator blsR c.y c.cols c.gates == (List.range 16).map fun k =>
    let g0 := mulM blsR (at' i0 k) (at' i1 (k + 4))
    let g1 := subM blsR (at' i1 k) (at' i0 (k + 12))
    let g2 := at' i1 k
    addM blsR (mulM blsR (addM blsR (mulM blsR g0 c.y) g1) c.y) g2
#guard let c := quotientCase "two-instance-columns"
  numerator blsR 1 c.cols [.inst 1 0] == c.cols.inst.getD 1 [] &&
  numerator blsR 1 c.cols [.inst 0 0] == c.cols.inst.getD 0 [] &&
  numerator blsR 1 c.cols [.inst 1 0] != numerator blsR 1 c.cols [.inst 0 0]
-- n = 4 on 32 points: the quotient is the polynomial whose product with `x^4 − 1` is the
-- numerator at every coset point, and it is not the one for the exponent `N / n = 8`
#guard let c := quotientCase "domain-32-n-4"
  c.n == 4 && c.cols.size / c.n == 8 &&
  (c.points.map fun x => mulM blsR (evalPoly blsR c.coeffs x) (subM blsR (powM blsR x 4) 1)) ==
    numerator blsR c.y c.cols c.gates &&
  (c.points.map fun x => mulM blsR (evalPoly blsR c.coeffs x) (subM blsR (powM blsR x 8) 1)) !=
    numerator blsR c.y c.cols c.gates &&
  quotientCoeffs blsR c.zeta c.omegaExt 8 (numerator blsR c.y c.cols c.gates) != c.coeffs &&
  (c.gates.flatMap rotations).eraseDups == [0, 1, -1, 2, -3] &&
  rotIndex c.cols 31 2 == 15 && rotIndex c.cols 0 (-3) == 8

-- the quotient coefficients: the domain, the shift, and no zero denominator
-- (`invM p 0 = 0`: a zero denominator would give a value without a meaning)
#guard quotientCases.all fun c =>
  c.n * c.cols.ratio == c.cols.size && isPow2 c.cols.size &&
  powM blsR c.omegaExt c.cols.size == 1 && powM blsR c.omegaExt (c.cols.size / 2) == blsR - 1 &&
  c.zeta == zeta3 && gateShift blsR c.zeta == none
#guard quotientCases.all fun c => c.points.all fun x => subM blsR (powM blsR x c.n) 1 != 0
#guard quotientCases.all fun c => c.coeffs.length == c.cols.size && c.coeffs.all (· < blsR)
-- the meaning of the coefficients: the polynomial they give, evaluated at every coset point
-- and multiplied by x^n - 1, is the numerator
#guard quotientCases.all fun c =>
  (c.points.map fun x => mulM blsR (evalPoly blsR c.coeffs x) (subM blsR (powM blsR x c.n) 1)) ==
    numerator blsR c.y c.cols c.gates
-- GPU-079: the same coefficients from the tiled device numerator
#guard quotientCases.all fun c =>
  quotientCoeffs blsR c.zeta c.omegaExt c.n (deviceNumeratorTiled blsR c.y c.cols c.gates 5) ==
    c.coeffs

/-! ## gate.json -/

#guard gateCases.length == 69
#guard decide (gateCases.Nodup)
#guard gateCases.all fun c => c.maxLog == 28

/-- The decisions of the rows of one operation, in file order. -/
def gateDecisions (op : Kind) : List (Option Reason) :=
  (gateCases.filter (·.op == op)).map (·.decision)

/-- The inputs of the rows of one operation: length, `min_k`, device, reduced. -/
def gateInputs (op : Kind) : List (Nat × Nat × Bool × Bool) :=
  (gateCases.filter (·.op == op)).map fun c => (c.len, c.minK, c.device, c.reduced)

/-- The rows of every operation (written from vectors/README.md, gate.json). -/
def gateRows : List (Nat × Nat × Bool × Bool) :=
  [(0, 14, true, true), (1, 14, true, true), (3, 14, true, true), (6, 14, true, true),
   (7, 14, true, true), (8192, 14, true, true), (16383, 14, true, true), (16384, 14, true, true),
   (16385, 14, true, true), (268435456, 14, true, true), (268435457, 14, true, true),
   (536870912, 14, true, true),
   (16384, 14, false, true), (16384, 14, true, false), (16384, 14, false, false),
   (8192, 14, false, false), (16383, 14, false, false), (0, 14, false, false),
   (536870912, 14, false, false),
   (1, 1, true, true), (2, 1, true, true), (3, 1, true, true), (1, 0, true, true)]

/-- The transform decisions, by hand: a length that is 0 or 1 (ORACLE-27), not a power of two
or above 2^28 is `shape`; then a length below `2^min_k` is `below-min-k`; then no device; then
unreduced. The length 1 is `shape` under `min_k` 14, 1 and 0. -/
def transformExpected : List (Option Reason) :=
  [some .shape, some .shape, some .shape, some .shape, some .shape, some .belowMinK,
   some .shape, none, some .shape, none, some .shape, some .shape,
   some .noDevice, some .unreduced, some .noDevice, some .belowMinK, some .shape, some .shape,
   some .shape,
   some .shape, none, some .shape, some .shape]

/-- The MSM decisions, by hand: the same without the power-of-two test. -/
def msmExpected : List (Option Reason) :=
  [some .shape, some .belowMinK, some .belowMinK, some .belowMinK, some .belowMinK,
   some .belowMinK, some .belowMinK, none, none, none, some .shape, some .shape,
   some .noDevice, some .unreduced, some .noDevice, some .belowMinK, some .belowMinK,
   some .shape, some .shape,
   some .belowMinK, none, none, none]

theorem pin_gate_table :
    gateInputs .msm = gateRows ∧ gateInputs .ntt = gateRows ∧ gateInputs .intt = gateRows ∧
    gateDecisions .msm = msmExpected ∧ gateDecisions .ntt = transformExpected ∧
    gateDecisions .intt = transformExpected ∧
    (gateCases.filter (·.op == .quotient)).length = 0 := by decide +kernel
#guard gateInputs .msm == gateRows && gateInputs .ntt == gateRows && gateInputs .intt == gateRows
#guard gateDecisions .msm == msmExpected
#guard gateDecisions .ntt == transformExpected && gateDecisions .intt == transformExpected
#guard [Kind.msm, .ntt, .intt].map opName == ["msm", "fft", "ifft"]

/-! ## threshold.json -/

#guard thresholdMsmCases.length == 3 && thresholdNttCases.length == 2
#guard decide ((thresholdMsmCases.map (·.name) ++ thresholdNttCases.map (·.name)).Nodup)
#guard defaultMinK == 14 && maxLog == 28

theorem pin_threshold_decisions :
    thresholdMsmCases.map (·.n) = [2 ^ 14 - 1, 2 ^ 14, 2 ^ 14 + 1] ∧
    thresholdMsmCases.map (·.decision) = [some .belowMinK, none, none] ∧
    thresholdNttCases.map (·.logN) = [13, 14] ∧
    thresholdNttCases.map (·.decision) = [some .belowMinK, none] := by decide +kernel
#guard thresholdMsmCases.map (fun c => (c.n, c.decision)) ==
  [(16383, some .belowMinK), (16384, none), (16385, none)]
#guard thresholdNttCases.map (fun c => (c.logN, c.decision)) == [(13, some .belowMinK), (14, none)]

-- the side conditions of `fft_eq_ntt_bls`: the root of the size 2^k with 1 ≤ k ≤ 32
#guard thresholdNttCases.all fun c => 1 ≤ c.logN && c.logN ≤ 32 &&
  c.omega == rootOfUnity blsR blsGen (2 ^ c.logN) &&
  powM blsR c.omega (2 ^ c.logN) == 1 && powM blsR c.omega (2 ^ c.logN / 2) == blsR - 1

/-- The threshold transform outputs, computed with the radix-2 model, are the reference
transform (`fft_eq_ntt_bls`; the input has `2^k` elements by `randoms_length`). -/
theorem thresholdNtt_eq_ntt : ∀ c ∈ thresholdNttCases,
    thresholdNttOut c = ntt blsR c.omega c.input := by
  intro c hc
  simp only [thresholdNttCases, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl
  · exact fft_eq_ntt_bls 13 (by decide) _ (randoms_length _ _ _)
  · exact fft_eq_ntt_bls 14 (by decide) _ (randoms_length _ _ _)

-- the digest: Σ_k x[k] · 7^k
theorem pin_digest : digest 97 [1, 2, 3] = (1 + 2 * 7 + 3 * 49) % 97 ∧ digest 97 [] = 0 := by
  decide +kernel
#guard digest 97 [1, 2, 3] == (1 + 2 * 7 + 3 * 49) % 97
-- the same generator and model at a size where the reference runs
#guard let w := rootOfUnity blsR blsGen 64
  let out := fft blsR w (randoms blsR 7013 64)
  out == ntt blsR w (randoms blsR 7013 64) &&
  digest blsR out == sumM blsR ((List.range 64).zip out |>.map fun (k, x) =>
    mulM blsR x (powM blsR blsGen k))
-- a small MSM over the generated vectors: the bucket method agrees with the reference
#guard thresholdMsmCases.all fun c =>
  let s := randoms blsR c.scalarsSeed 16
  let g := randoms blsR c.basesSeed 16
  msmBucket blsR 8 256 s g == msm blsR s g

/-! ## datamove.json -/

open DataMove in
#guard permittedKinds.length == 5 && forbiddenKinds.length == 5 && plans.length == 3 &&
  VecKind.all.length == 10
#guard decide ((DataMove.VecKind.all.map kindName).Nodup)
#guard decide ((plans.map (·.name)).Nodup)
-- the kinds with their read-back codes (README, service op 4: 0 quotient coefficients,
-- 1 MSM points, 2 counters, 3 base-domain transform output, 4 extended, 5 zeroed region)
#guard permittedKinds.map (fun k => (kindName k, DataMove.copyCode k)) ==
  [("base-transform", some 3), ("quotient-coeffs", some 0), ("msm-point", some 1),
   ("counter", some 2), ("msm-buckets", some 1)]
#guard forbiddenKinds.map (fun k => (kindName k, DataMove.copyCode k)) ==
  [("scalars", none), ("bases", none), ("base-coeffs", none), ("extended", some 4),
   ("zeroed-region", some 5)]
#guard plans.map (fun p => (p.name, p.executable, p.gpu038)) ==
  [("spec", true, true), ("old-port", true, false), ("msm-buckets", true, true)]
#guard plans.map (fun p => (p.trace.map kindName, p.offending.map kindName)) ==
  [(["base-transform", "msm-point", "msm-point", "quotient-coeffs", "msm-point", "counter",
     "counter"], []),
   (["base-transform", "msm-point", "msm-point", "extended", "extended", "extended",
     "msm-point", "counter", "zeroed-region"],
    ["extended", "extended", "extended", "zeroed-region"]),
   (["msm-buckets"], [])]

/-- The plans of the file are the plans of `DataMove.lean`, and the fields are its terms. -/
theorem pin_datamove :
    plans.map (·.steps) = [DataMove.specPlan, DataMove.oldPortPlan, DataMove.msmBucketPlan] ∧
    plans.map (·.executable) = [true, true, true] ∧
    plans.map (·.gpu038) = [true, false, true] ∧
    plans.map (·.offending) = [[], [.extended, .extended, .extended, .zeroedRegion], []] ∧
    permittedKinds = [.baseTransform, .quotientCoeffs, .msmPoint, .counter, .msmBuckets] ∧
    forbiddenKinds = [.scalars, .bases, .baseCoeffs, .extended, .zeroedRegion] := by
  decide +kernel

/-- No kind outside the permitted set appears in the `spec` or `msm-buckets` trace; a plan's
`gpu038` is false exactly when it has an offending copy. -/
theorem pin_datamove_offending : ∀ p ∈ plans, p.gpu038 = p.offending.isEmpty := by
  decide +kernel

end GpuSpec.Vectors

/-! ## Audit of the new modules -/

/-- info: [] -/
#guard_msgs in
#audit_ns GpuSpec

/-- info: 'GpuSpec.Vectors.randoms_fold_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Vectors.randoms_fold_length

/-- info: 'GpuSpec.Vectors.randoms_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Vectors.randoms_length

/-- info: 'GpuSpec.Vectors.pin_foldBoundary' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Vectors.pin_foldBoundary

/-- info: 'GpuSpec.Vectors.pin_gate_table' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Vectors.pin_gate_table

/-- info: 'GpuSpec.Vectors.pin_threshold_decisions' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Vectors.pin_threshold_decisions

/-- info: 'GpuSpec.Vectors.thresholdNtt_eq_ntt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Vectors.thresholdNtt_eq_ntt

/-- info: 'GpuSpec.Vectors.pin_digest' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Vectors.pin_digest

/-- info: 'GpuSpec.Vectors.pin_datamove' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Vectors.pin_datamove

/-- info: 'GpuSpec.Vectors.pin_datamove_offending' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Vectors.pin_datamove_offending
