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
import GpuSpec.Audit
import GpuSpec.DataMove
import GpuSpec.Declines

/-!
# Pins for the tiled quotient, the reference numerator, data movement and declines

Each pin is written from a requirement or README sentence, with the expected
value worked out by hand in the comment above it. Small-field pins are checked
twice: `decide +kernel` and `#guard`. The end of the file reruns the namespace
audit over the new modules and pins the axioms of each new theorem.
-/

namespace GpuSpec

/-! ## The reference numerator (vectors/README.md, quotient.json)

Sentences: "A column read at point `i` with rotation `rot` reads index
`(i + rot · ratio) mod N`. The numerator at point `i` is Horner in `y` over the
gates in order: `acc = 0; for g in gates: acc = acc · y + g(i)`."

Example over F_17: N = 4, ratio = 2, y = 3,
advice column a = [1, 2, 3, 4], fixed column f = [5, 6, 7, 8],
gates g0 = a at rotation +1, g1 = f at rotation −1.

Read indices: rotation +1 reads (i + 1·2) mod 4, rotation −1 reads (i − 2) mod 4.
  i = 0: +1 → 2;  −1 → −2 mod 4 = 2
  i = 1: +1 → 3;  −1 → −1 mod 4 = 3
  i = 2: +1 → 4 mod 4 = 0;  −1 → 0
  i = 3: +1 → 5 mod 4 = 1;  −1 → 1
(With N = 4 and ratio 2 the two rotations read the same index, so this example
cannot tell +1 from −1; `ex8` below does.)

Numerator, acc = (0·3 + g0(i))·3 + g1(i) mod 17:
  i = 0: g0 = a[2] = 3, g1 = f[2] = 7:  3·3 + 7 = 16
  i = 1: g0 = a[3] = 4, g1 = f[3] = 8:  4·3 + 8 = 20 = 3 (mod 17)
  i = 2: g0 = a[0] = 1, g1 = f[0] = 5:  1·3 + 5 = 8
  i = 3: g0 = a[1] = 2, g1 = f[1] = 6:  2·3 + 6 = 12
Mutants. Without `· ratio`, point 0 reads a[1] = 2 and f[3] = 8: 2·3 + 8 = 14,
not 16. With the Horner order reversed, point 0 is 7·3 + 3 = 24 = 7, not 16. -/

def ex4 : Columns :=
  { fixed := [[5, 6, 7, 8]], advice := [[1, 2, 3, 4]], inst := [], challenges := [], size := 4,
    ratio := 2 }
def ex4Gates : List Expr := [.advice 0 1, .fixed 0 (-1)]

theorem pin_rotIndex_ex4 :
    (List.range 4).map (rotIndex ex4 · 1) = [2, 3, 0, 1] ∧
    (List.range 4).map (rotIndex ex4 · (-1)) = [2, 3, 0, 1] := by decide +kernel
#guard (List.range 4).map (rotIndex ex4 · 1) == [2, 3, 0, 1]
#guard (List.range 4).map (rotIndex ex4 · (-1)) == [2, 3, 0, 1]

theorem pin_numeratorAt_ex4 :
    numeratorAt 17 3 ex4 ex4Gates 0 = 16 ∧ numeratorAt 17 3 ex4 ex4Gates 1 = 3 ∧
    numeratorAt 17 3 ex4 ex4Gates 2 = 8 ∧ numeratorAt 17 3 ex4 ex4Gates 3 = 12 := by decide +kernel
#guard (List.range 4).map (numeratorAt 17 3 ex4 ex4Gates) == [16, 3, 8, 12]

theorem pin_numerator_ex4 : numerator 17 3 ex4 ex4Gates = [16, 3, 8, 12] := by decide +kernel
#guard numerator 17 3 ex4 ex4Gates == [16, 3, 8, 12]
#guard deviceNumerator 17 3 ex4 ex4Gates == [16, 3, 8, 12]

/-! Sign of the rotation and negative wrap: N = 8, ratio = 2, a = [1, …, 8].
  i = 1, rot −1: 1 − 2 = −1, mod 8 = 7        i = 1, rot +1: 1 + 2 = 3
  i = 0, rot −3: 0 − 6 = −6, mod 8 = 2        i = 7, rot +1: 7 + 2 = 9, mod 8 = 1
  i = 2, rot −2: 2 − 4 = −2, mod 8 = 6        i = 5, rot +1: 5 + 2 = 7
  rot 0 reads i. An empty domain (N = 0) reads index 0 (the definition's guard). -/

def ex8 : Columns :=
  { fixed := [], advice := [[1, 2, 3, 4, 5, 6, 7, 8]], inst := [], challenges := [], size := 8,
    ratio := 2 }

theorem pin_rotIndex_ex8 :
    rotIndex ex8 1 (-1) = 7 ∧ rotIndex ex8 1 1 = 3 ∧ rotIndex ex8 0 (-3) = 2 ∧
    rotIndex ex8 7 1 = 1 ∧ rotIndex ex8 2 (-2) = 6 ∧ rotIndex ex8 5 1 = 7 ∧
    rotIndex ex8 4 0 = 4 := by decide +kernel
#guard rotIndex ex8 1 (-1) == 7 && rotIndex ex8 1 1 == 3 && rotIndex ex8 0 (-3) == 2 &&
  rotIndex ex8 7 1 == 1 && rotIndex ex8 2 (-2) == 6 && rotIndex ex8 5 1 == 7 && rotIndex ex8 4 0 == 4

/-! ## GPU-079: tiles

`ex8` with the one gate "a at rotation +1" and tile size 3: the tiles are
[0, 1, 2], [3, 4, 5], [6, 7] (3 does not divide 8; the last tile is short).
The numerator at i is a[(i + 2) mod 8]: [3, 4, 5, 6, 7, 8, 1, 2].
  i = 5, the last point of tile 1, reads index 7, in tile 2 (across a tile border): a[7] = 8.
  i = 7, the last point of tile 2 and of the domain, reads index 9 mod 8 = 1, in
         tile 0 (across the domain end): a[1] = 2.
A kernel that wrapped the read inside its tile would read, at i = 5, index
3 + ((5 − 3 + 2) mod 3) = 4 and return a[4] = 5, not 8. -/

def ex8Gates : List Expr := [.advice 0 1]

theorem pin_tiled_ex8 : numeratorTiled 17 3 ex8 ex8Gates 3 = [3, 4, 5, 6, 7, 8, 1, 2] ∧
    deviceNumeratorTiled 17 3 ex8 ex8Gates 3 = [3, 4, 5, 6, 7, 8, 1, 2] := by decide +kernel
#guard numeratorTiled 17 3 ex8 ex8Gates 3 == [3, 4, 5, 6, 7, 8, 1, 2]
#guard deviceNumeratorTiled 17 3 ex8 ex8Gates 3 == [3, 4, 5, 6, 7, 8, 1, 2]

theorem pin_tile_border_ex8 :
    tileStarts 8 3 = [0, 3, 6] ∧
    evalTile (numeratorAt 17 3 ex8 ex8Gates) 8 3 3 = [6, 7, 8] ∧
    evalTile (numeratorAt 17 3 ex8 ex8Gates) 8 3 6 = [1, 2] ∧
    (deviceNumeratorTiled 17 3 ex8 ex8Gates 3)[5]? = some 8 ∧
    (deviceNumeratorTiled 17 3 ex8 ex8Gates 3)[7]? = some 2 := by decide +kernel
#guard tileStarts 8 3 == [0, 3, 6]
#guard evalTile (numeratorAt 17 3 ex8 ex8Gates) 8 3 3 == [6, 7, 8]
#guard evalTile (numeratorAt 17 3 ex8 ex8Gates) 8 3 6 == [1, 2]
#guard (deviceNumeratorTiled 17 3 ex8 ex8Gates 3)[5]? == some 8
#guard (deviceNumeratorTiled 17 3 ex8 ex8Gates 3)[7]? == some 2

-- every tile size from 1 to 10 (above the domain size 8) on both examples, and the empty domain
theorem pin_tiled_all_sizes : ∀ t : Fin 10,
    numeratorTiled 17 3 ex8 ex8Gates (t.val + 1) = numerator 17 3 ex8 ex8Gates ∧
    deviceNumeratorTiled 17 3 ex4 ex4Gates (t.val + 1) = [16, 3, 8, 12] ∧
    numeratorTiled 17 3 { ex4 with size := 0 } ex4Gates (t.val + 1) = [] := by decide +kernel
#guard (List.range 10).all fun t =>
  deviceNumeratorTiled 17 3 ex4 ex4Gates (t + 1) == [16, 3, 8, 12] &&
  numeratorTiled 17 3 ex8 ex8Gates (t + 1) == [3, 4, 5, 6, 7, 8, 1, 2]
#guard Vectors.quotientCases.all fun c => [1, 2, 3, 5, 7, 64].all fun t =>
  deviceNumeratorTiled blsR c.y c.cols c.gates t == numerator blsR c.y c.cols c.gates

/-! ### Instance columns (vectors/README.md: "`fixed`, `advice`, `instance` (lists of columns)")

Two instance columns with different values over F_17: N = 4, ratio = 1,
i0 = [1, 2, 3, 4], i1 = [5, 6, 7, 8]. A read of instance column `c` reads column
`c`: at point 2, column 1 gives 7 and column 0 gives 3; column 1 at rotation +1
from point 3 reads index (3 + 1) mod 4 = 0: 5; there is no column 2: 0.
Numerator with y = 3 and gates i0, i1: i0[k]·3 + i1[k] mod 17:
  k = 0: 1·3 + 5 = 8;  k = 1: 2·3 + 6 = 12;  k = 2: 3·3 + 7 = 16;  k = 3: 4·3 + 8 = 20 = 3.
Mutant: reading column 0 for every instance column gives 1·3 + 1 = 4 at point 0. -/

def exI : Columns :=
  { fixed := [], advice := [], inst := [[1, 2, 3, 4], [5, 6, 7, 8]], challenges := [], size := 4,
    ratio := 1 }

theorem pin_inst_columns :
    evalE 17 exI 2 (.inst 1 0) = 7 ∧ evalE 17 exI 2 (.inst 0 0) = 3 ∧
    evalE 17 exI 3 (.inst 1 1) = 5 ∧ evalE 17 exI 0 (.inst 1 (-1)) = 8 ∧
    evalE 17 exI 0 (.inst 2 0) = 0 ∧
    (List.range 4).map (evalE 17 exI · (.inst 1 0)) = [5, 6, 7, 8] ∧
    numerator 17 3 exI [.inst 0 0, .inst 1 0] = [8, 12, 16, 3] ∧
    deviceNumerator 17 3 exI [.inst 0 0, .inst 1 0] = [8, 12, 16, 3] := by decide +kernel
#guard evalE 17 exI 2 (.inst 1 0) == 7 && evalE 17 exI 2 (.inst 0 0) == 3
#guard numerator 17 3 exI [.inst 0 0, .inst 1 0] == [8, 12, 16, 3]
#guard deviceNumerator 17 3 exI [.inst 0 0, .inst 1 0] == [8, 12, 16, 3]

/-! ### Challenges (vectors/README.md: node `challenge` with field `index`)

Three distinct challenges over F_17: [3, 5, 7]; N = 4, ratio = 1, advice column
a = [1, 2, 3, 4]. A challenge leaf with index `k` reads challenge `k` at every
point: index 0 gives 3, index 1 gives 5, index 2 gives 7; index 3 is out of
range and gives 0.

Numerator with y = 2 and the gates g0 = challenge 0 · challenge 2 and
g1 = a + challenge 1:
  g0 = 3 · 7 = 21 = 4 (mod 17) at every point;
  g1(k) = a[k] + 5: 6, 7, 8, 9;
  acc = g0 · 2 + g1(k) = 8 + g1(k): 14, 15, 16, 17 = 0.
Mutant: reading challenge `k mod 2` gives 3 for index 2, so g0 = 3 · 3 = 9 and
point 0 is 9 · 2 + 6 = 24 = 7, not 14. -/

def exC : Columns :=
  { fixed := [], advice := [[1, 2, 3, 4]], inst := [], challenges := [3, 5, 7], size := 4,
    ratio := 1 }

theorem pin_challenges :
    evalE 17 exC 0 (.challenge 0) = 3 ∧ evalE 17 exC 0 (.challenge 1) = 5 ∧
    evalE 17 exC 0 (.challenge 2) = 7 ∧ evalE 17 exC 3 (.challenge 2) = 7 ∧
    evalE 17 exC 0 (.challenge 3) = 0 ∧ evalE 17 exC 2 (.challenge 4) = 0 ∧
    evalE 17 exC 1 (.prod (.challenge 0) (.challenge 2)) = 4 ∧
    numerator 17 2 exC [.prod (.challenge 0) (.challenge 2), .sum (.advice 0 0) (.challenge 1)]
      = [14, 15, 16, 0] ∧
    deviceNumerator 17 2 exC
      [.prod (.challenge 0) (.challenge 2), .sum (.advice 0 0) (.challenge 1)] = [14, 15, 16, 0] := by
  decide +kernel
#guard evalE 17 exC 0 (.challenge 2) == 7 && evalE 17 exC 0 (.challenge 0) == 3 &&
  evalE 17 exC 0 (.challenge 1) == 5 && evalE 17 exC 0 (.challenge 3) == 0
#guard numerator 17 2 exC [.prod (.challenge 0) (.challenge 2), .sum (.advice 0 0) (.challenge 1)]
  == [14, 15, 16, 0]

/-! ### The quotient coefficients (vectors/README.md: "divide point `k` by `x_k^n − 1`
with `x_k = zeta · omega_ext^k`, apply the inverse coset transform")

F_17, N = 8 points, n = 4 (so `N / n = 2 ≠ n`), shift zeta = 3, omega_ext = 9.
9 has order 8: 9² = 81 = 13, 9⁴ = 13² = 169 = 16 = −1, 9⁸ = 1. Numerator: all ones.

Points x_k = 3 · 9^k. Then x_k⁴ = 3⁴ · (9⁴)^k = 81 · (−1)^k = 13 · (−1)^k, so
  x_k⁴ − 1 = 12 for even k and −14 = 3 for odd k.
Inverses: 12 · 10 = 120 = 7 · 17 + 1, so 12⁻¹ = 10; 3 · 6 = 18 = 1, so 3⁻¹ = 6.
Divided values: [10, 6, 10, 6, 10, 6, 10, 6].

The polynomial with those values on the coset: d(x_k) = 8 + 2 · (−1)^k
(8 + 2 = 10, 8 − 2 = 6), and (−1)^k = x_k⁴ · 13⁻¹ with 13⁻¹ = 4 (13 · 4 = 52 = 1).
So d(x) = 8 + 2 · 4 · x⁴ = 8 + 8 x⁴: coefficients [8, 0, 0, 0, 8, 0, 0, 0].
Check: (8 + 8 x⁴)(x⁴ − 1) = 8 x⁸ − 8, and x_k⁸ = 13² = 16, so 8 · 16 − 8 = 120 = 1,
the numerator.

Mutant: with the exponent `N / n = 2` in place of `n = 4` the divisors are
x_k² − 1 with x_k² = 9 · 13^k: 8, 14, 7, 9, ... , not 12, 3, 12, 3, ... -/

theorem pin_quotientCoeffs_F17 :
    rootOfUnity 17 3 8 = 9 ∧ powM 17 9 4 = 16 ∧ powM 17 9 8 = 1 ∧
    (List.range 8).map (fun k => subM 17 (powM 17 (mulM 17 3 (powM 17 9 k)) 4) 1) =
      [12, 3, 12, 3, 12, 3, 12, 3] ∧
    invM 17 12 = 10 ∧ invM 17 3 = 6 ∧
    quotientCoeffs 17 3 9 4 (List.replicate 8 1) = [8, 0, 0, 0, 8, 0, 0, 0] ∧
    quotientCoeffs 17 3 9 4 (List.replicate 8 1) ≠ quotientCoeffs 17 3 9 2 (List.replicate 8 1) := by
  decide +kernel
#guard quotientCoeffs 17 3 9 4 (List.replicate 8 1) == [8, 0, 0, 0, 8, 0, 0, 0]
#guard quotientCoeffs 17 3 9 2 (List.replicate 8 1) != [8, 0, 0, 0, 8, 0, 0, 0]

-- t = 0 is not a tile size: no tile, the empty list, not the numerator
theorem pin_tiled_zero : numeratorTiled 17 3 ex4 ex4Gates 0 = [] ∧
    numeratorTiled 17 3 ex4 ex4Gates 0 ≠ numerator 17 3 ex4 ex4Gates ∧ tileStarts 4 0 = [] := by
  decide +kernel
#guard numeratorTiled 17 3 ex4 ex4Gates 0 == [] && deviceNumeratorTiled 17 3 ex4 ex4Gates 0 == []

-- GPU-079: the quotient coefficients do not depend on the tile size (F_17, ζ = 3, ω of order 8)
#guard (List.range 10).all fun t =>
  quotientCoeffs 17 3 (rootOfUnity 17 3 8) 4 (deviceNumeratorTiled 17 3 ex8 ex8Gates (t + 1)) ==
    quotientCoeffs 17 3 (rootOfUnity 17 3 8) 4 (numerator 17 3 ex8 ex8Gates)

/-! ## GPU-073: reasons and counts

Sentence: "… exactly one reason out of no-device, below-min-k, shape,
unreduced, memory, fault and device-error." vectors/README.md, op 3:
"reason: 0 no-device, 1 below-min-k, 2 shape, 3 unreduced, 4 memory, 5 fault,
6 device-error". -/

theorem pin_reason_codes : Reason.all.map Reason.code =
    ["no-device", "below-min-k", "shape", "unreduced", "memory", "fault", "device-error"] := by
  decide +kernel
#guard Reason.all.map Reason.code ==
  ["no-device", "below-min-k", "shape", "unreduced", "memory", "fault", "device-error"]
theorem pin_reason_index :
    Reason.noDevice.index = 0 ∧ Reason.belowMinK.index = 1 ∧ Reason.shape.index = 2 ∧
    Reason.unreduced.index = 3 ∧ Reason.memory.index = 4 ∧ Reason.fault.index = 5 ∧
    Reason.deviceError.index = 6 := by decide +kernel
#guard Reason.all.map Reason.index == [0, 1, 2, 3, 4, 5, 6]

/-- A device for the count pins: MSM calls decline with `memory`, a forward NTT
of an empty input declines with `shape`, every other call is answered. -/
def pinDev : RDevice := fun _ c =>
  match c.kind, c.input with
  | .msm, _ => .decline .memory
  | .ntt, [] => .decline .shape
  | _, i => .value i

/-- Two MSM calls, one empty NTT, one answered NTT, one answered quotient, a
draw and a squeeze. By the sentence: (msm, memory) = 2, (ntt, shape) = 1, every
other cell 0, the sum 3. `memory` and `shape` are fallback reasons, so (GPU-012)
3 fallbacks, no decline by design, and 3 CPU resolutions in the prover run. -/
def pinEvents : List Event :=
  [.op ⟨.msm, [1]⟩, .blind .caller, .op ⟨.ntt, []⟩, .op ⟨.ntt, [1, 2]⟩, .squeeze, .op ⟨.msm, [2]⟩,
   .op ⟨.quotient, [3]⟩]

theorem pin_counts :
    countDeclines pinDev pinEvents .msm .memory = 2 ∧
    countDeclines pinDev pinEvents .ntt .shape = 1 ∧
    (Kind.all.all fun k => Reason.all.all fun r =>
      (k = .msm ∧ r = .memory) || (k = .ntt ∧ r = .shape) || countDeclines pinDev pinEvents k r == 0)
      = true ∧
    (countDeclines pinDev pinEvents).total = 3 ∧
    declinedOps pinDev pinEvents = 3 ∧ fallbackOps pinDev pinEvents = 3 ∧
    expectedOps pinDev pinEvents = 0 ∧ (countDeclines pinDev pinEvents).fallbackTotal = 3 ∧
    (prove (fun c => c.input) pinDev.toDevice pinEvents [9] []).fallbacks = 3 := by decide +kernel
#guard countDeclines pinDev pinEvents .msm .memory == 2
#guard countDeclines pinDev pinEvents .ntt .shape == 1
#guard (countDeclines pinDev pinEvents).total == 3
#guard (prove (fun c => c.input) pinDev.toDevice pinEvents [9] []).fallbacks == 3

/-! ### GPU-012, GPU-085: fallback reasons and declines by design

The same events with a device whose MSM calls decline with `below-min-k` (small
MSMs, by design) and whose empty NTT declines with `shape`. By the sentences:
three declines are counted (GPU-073): (msm, below-min-k) = 2, (ntt, shape) = 1.
One of them is a fallback (the shape decline, GPU-012); two are by design and
are no fallback (GPU-085). The stock CPU code still resolves all three calls. -/

def pinDevE : RDevice := fun _ c =>
  match c.kind, c.input with
  | .msm, _ => .decline .belowMinK
  | .ntt, [] => .decline .shape
  | _, i => .value i

theorem pin_fallback_reasons :
    Reason.all.map Reason.isFallback = [false, false, true, true, true, true, true] ∧
    Reason.fallbacks = [.shape, .unreduced, .memory, .fault, .deviceError] ∧
    countDeclines pinDevE pinEvents .msm .belowMinK = 2 ∧
    countDeclines pinDevE pinEvents .ntt .shape = 1 ∧
    (countDeclines pinDevE pinEvents).total = 3 ∧
    declinedOps pinDevE pinEvents = 3 ∧ fallbackOps pinDevE pinEvents = 1 ∧
    expectedOps pinDevE pinEvents = 2 ∧ (countDeclines pinDevE pinEvents).fallbackTotal = 1 ∧
    (prove (fun c => c.input) pinDevE.toDevice pinEvents [9] []).fallbacks = 3 := by decide +kernel
#guard Reason.all.map Reason.isFallback == [false, false, true, true, true, true, true]
#guard fallbackOps pinDevE pinEvents == 1 && expectedOps pinDevE pinEvents == 2 &&
  declinedOps pinDevE pinEvents == 3
#guard (prove (fun c => c.input) pinDevE.toDevice pinEvents [9] []).fallbacks == 3

/-- GPU-012, GPU-085: the daemon's transition `Service.fault`, applied once for
each declined operation with the wire index of its reason. -/
def serviceDeclines (dev : RDevice) (s : Service.St) (ies : List (Event × Nat)) : Service.St :=
  ies.foldl (fun s ie =>
    match declineReason dev ie with
    | some r => Service.fault s r.index
    | none => s) s

theorem fault_reason (s : Service.St) (r : Reason) :
    (Service.fault s r.index).fallbacks = s.fallbacks + (if r.isFallback then 1 else 0) ∧
    (Service.fault s r.index).declined = s.declined + 1 := by
  cases r <;> simp [Service.fault, Reason.index, Reason.isFallback]

theorem service_fallbacks_foldl (dev : RDevice) : ∀ (ies : List (Event × Nat)) (s : Service.St),
    (serviceDeclines dev s ies).fallbacks =
      s.fallbacks + (ies.filter (isFallbackDecline dev)).length ∧
    (serviceDeclines dev s ies).declined = s.declined + (ies.filter (isDeclined dev)).length
  | [], s => by simp [serviceDeclines]
  | ie :: ies, s => by
    cases hr : declineReason dev ie with
    | none =>
      have ih := service_fallbacks_foldl dev ies s
      simp only [serviceDeclines, List.foldl_cons, hr] at ih ⊢
      simpa [List.filter_cons, isFallbackDecline, isDeclined, hr] using ih
    | some r =>
      have ih := service_fallbacks_foldl dev ies (Service.fault s r.index)
      have hf := fault_reason s r
      simp only [serviceDeclines, List.foldl_cons, hr] at ih ⊢
      cases hb : r.isFallback <;>
        simp [isFallbackDecline, isDeclined, hr, hb] at hf ⊢ <;> omega

/-- GPU-012, GPU-085, GPU-073: the service notion of a fallback is `fallbackOps`.
For every device and every event list, the daemon's transition applied to the
declines of the run raises the request's fallback count by the number of
declines with a fallback reason, and the total decline count by the number of
all declined operations. The prover run's `fallbacks` field (CPU resolutions)
is the second number (`declines_all_counted`). -/
theorem service_fallbacks_eq_fallbackOps (dev : RDevice) (evs : List Event) (s : Service.St) :
    (serviceDeclines dev s evs.zipIdx).fallbacks = s.fallbacks + fallbackOps dev evs ∧
    (serviceDeclines dev s evs.zipIdx).declined = s.declined + declinedOps dev evs :=
  service_fallbacks_foldl dev evs.zipIdx s

/-- On the pin device: from a proving request the daemon ends with 1 fallback and
3 declines, counted under below-min-k twice and shape once. -/
theorem pin_service_declines :
    let s := Service.runOps Service.cfg [1, 2 + 2000 + 200000]
    let t := serviceDeclines pinDevE s pinEvents.zipIdx
    t.fallbacks = 1 ∧ t.declined = 3 ∧ t.declines = [0, 2, 1, 0, 0, 0, 0] ∧ t.degraded = true := by
  decide +kernel

/-! ### GPU-007, GPU-008: a device that answers one occurrence and declines the next

The answer of a device may depend on the occurrence. Events: the quotient call on
`[3]`, an OS draw, the identical quotient call again, a squeeze. The device
answers the event at position 0 with the reference value and declines every
later event with `memory`. By the sentences the transcript is the CPU
transcript (`[3]`, `[1, 5]`, `[3]`, the squeeze: the declined call is resolved by
the stock function), with one fallback, counted under (quotient, memory). A
device that is a function of the call alone cannot do this: it answers both
occurrences or neither. -/

def pinDevOnce : RDevice := fun i c =>
  if i = 0 then .value c.input else .decline .memory

def pinEvents3 : List Event :=
  [.op ⟨.quotient, [3]⟩, .blind .os, .op ⟨.quotient, [3]⟩, .squeeze]

theorem pin_accept_then_decline :
    let ref : Call → List Nat := fun c => c.input
    let r := prove ref pinDevOnce.toDevice pinEvents3 [] [5]
    let cpu := prove ref cpuOnly pinEvents3 [] [5]
    pinDevOnce 0 ⟨.quotient, [3]⟩ = .value [3] ∧ pinDevOnce 2 ⟨.quotient, [3]⟩ = .decline .memory ∧
    r.proof.transcript.take 3 = [[3], [1, 5], [3]] ∧ r.proof.transcript.length = 4 ∧
    r.proof = cpu.proof ∧ r.osRng = [] ∧ r.fallbacks = 1 ∧ cpu.fallbacks = 2 ∧ r.pos = 4 ∧
    countDeclines pinDevOnce pinEvents3 .quotient .memory = 1 ∧
    declinedOps pinDevOnce pinEvents3 = 1 ∧ fallbackOps pinDevOnce pinEvents3 = 1 := by
  decide +kernel
#guard (prove (fun c => c.input) pinDevOnce.toDevice pinEvents3 [] [5]).fallbacks == 1
#guard (prove (fun c => c.input) pinDevOnce.toDevice pinEvents3 [] [5]).proof ==
  (prove (fun c => c.input) cpuOnly pinEvents3 [] [5]).proof
-- the other order: decline the first occurrence, answer the second
#guard (prove (fun c => c.input) (fun i c => if i = 0 then none else some c.input) pinEvents3 []
  [5]).fallbacks == 1

/-! ## GPU-014, GPU-016: two random sources around a declined quotient call

The stock prover draws the advice blinding from the caller's RNG, runs the
quotient, draws the quotient limb blinding from the OS source, and goes on with
the caller's RNG. Events: a caller draw, the quotient call on `[3]`, an OS draw,
a caller draw, a squeeze. Caller stream 9, 8, 7; OS stream 5, 6. The reference
value of a call is its input.

By the sentences, whatever the quotient hook answers: the caller's stream gives
9 then 8 (7 is left), the OS stream gives 5 (6 is left). A draw is recorded as
`[source tag, value]` with tag 0 for the caller and 1 for the OS source. The
transcript is `[0, 9]`, `[3]` (the reference value: the hook declined and the
stock function ran, GPU-008), `[1, 5]`, `[0, 8]`, then the squeeze of those four
entries. The toy hash folds `a ↦ 31·a + x + 1` from 7 over 0, 9, 3, 1, 5, 0, 8:
218, 6768, 209812, 6504174, 201629400, 6250511401, 193765853440.
One decline: one fallback (GPU-012). -/

/-- The quotient call declines with `memory`; every other call is answered. -/
def pinDevQ : RDevice := fun _ c =>
  match c.kind with
  | .quotient => .decline .memory
  | _ => .value c.input

def pinEvents2 : List Event :=
  [.blind .caller, .op ⟨.quotient, [3]⟩, .blind .os, .blind .caller, .squeeze]

theorem pin_two_sources :
    let r := prove (fun c => c.input) pinDevQ.toDevice pinEvents2 [9, 8, 7] [5, 6]
    r.proof.transcript = [[0, 9], [3], [1, 5], [0, 8], [193765853440]] ∧
    r.proof.drawn = 2 ∧ r.proof.drawnOs = 1 ∧ r.rng = [7] ∧ r.osRng = [6] ∧ r.fallbacks = 1 := by
  decide +kernel
#guard (prove (fun c => c.input) pinDevQ.toDevice pinEvents2 [9, 8, 7] [5, 6]).proof.transcript ==
  [[0, 9], [3], [1, 5], [0, 8], [193765853440]]
#guard (prove (fun c => c.input) pinDevQ.toDevice pinEvents2 [9, 8, 7] [5, 6]).rng == [7] &&
  (prove (fun c => c.input) pinDevQ.toDevice pinEvents2 [9, 8, 7] [5, 6]).osRng == [6]

/-- The same run with a hook that answers the quotient call with the reference
value: the same proof and the same streams, no fallback. With a hook that
answers with a wrong value (`[99]`, not honest) the transcript differs, and the
draws and both streams are still the same (`draws_independent_of_device`). With
the two blinding draws swapped between the sources the proof differs: the
source of a draw is part of the model. -/
theorem pin_two_sources_any_answer :
    let ref : Call → List Nat := fun c => c.input
    let declined := prove ref pinDevQ.toDevice pinEvents2 [9, 8, 7] [5, 6]
    let answered := prove ref (fun _ c => some c.input) pinEvents2 [9, 8, 7] [5, 6]
    let wrong := prove ref (fun _ _ => some [99]) pinEvents2 [9, 8, 7] [5, 6]
    let swapped := prove ref pinDevQ.toDevice
      [.blind .os, .op ⟨.quotient, [3]⟩, .blind .caller, .blind .caller, .squeeze] [9, 8, 7] [5, 6]
    answered.proof = declined.proof ∧ answered.rng = [7] ∧ answered.osRng = [6] ∧
    answered.fallbacks = 0 ∧
    wrong.proof.transcript.take 4 = [[0, 9], [99], [1, 5], [0, 8]] ∧
    wrong.proof.drawn = 2 ∧ wrong.proof.drawnOs = 1 ∧ wrong.rng = [7] ∧ wrong.osRng = [6] ∧
    swapped.proof.transcript.take 4 = [[1, 5], [3], [0, 9], [0, 8]] ∧
    swapped.proof ≠ declined.proof := by
  decide +kernel

/-- An empty source gives no value: the OS draw is skipped when the OS stream is
empty, and the caller's stream is not used in its place. -/
theorem pin_source_not_substituted :
    let r := prove (fun c => c.input) cpuOnly [.blind .os, .blind .caller] [9] []
    r.proof.transcript = [[0, 9]] ∧ r.proof.drawn = 1 ∧ r.proof.drawnOs = 0 ∧ r.rng = [] := by
  decide +kernel

/-! ## GPU-074, GPU-010: the gate at the default `min_k = 14`, `maxLog = 28`

  2^14 − 1 = 16383: at least one element and fewer than 2^14. MSM: below-min-k.
            Transform: not a power of two, so shape (the shape test runs first).
  2^14: a power of two, not below 2^14, not above 2^28: the kernel runs.
  2^13: a power of two below 2^14: below-min-k (also with no device: the
        below-min-k test runs before the no-device test).
  0: empty: shape.    2^28: runs.    2^29: above 2^28: shape.
  1: one element. Transform: shape (ORACLE-27: the kernel takes sizes from 2), under
     every min_k. MSM: a valid input, below-min-k at 14 and a run at min_k 0.
  2^14 with no device: no-device. With a device and an unreduced input: unreduced. -/

theorem pin_gate_14 :
    gateMsm 14 28 true true (2 ^ 14 - 1) = some .belowMinK ∧
    gate 14 28 true true (2 ^ 14 - 1) = some .shape ∧
    gate 14 28 true true (2 ^ 14) = none ∧ gateMsm 14 28 true true (2 ^ 14) = none ∧
    gate 14 28 true true (2 ^ 13) = some .belowMinK ∧
    gate 14 28 false false (2 ^ 13) = some .belowMinK ∧
    gate 14 28 true true 0 = some .shape ∧ gateMsm 14 28 true true 0 = some .shape ∧
    gate 14 28 true true (2 ^ 28) = none ∧ gate 14 28 true true (2 ^ 29) = some .shape ∧
    gateMsm 14 28 true true (2 ^ 28) = none ∧ gateMsm 14 28 true true (2 ^ 28 + 1) = some .shape ∧
    gate 14 28 false false (2 ^ 14) = some .noDevice ∧
    gate 14 28 true false (2 ^ 14) = some .unreduced ∧
    gate 14 28 true true 1 = some .shape ∧ gateMsm 14 28 true true 1 = some .belowMinK ∧
    -- ORACLE-27: one element is a shape decline for a transform under every min_k; two run
    gate 1 28 true true 1 = some .shape ∧ gate 0 28 true true 1 = some .shape ∧
    gate 0 28 false false 1 = some .shape ∧
    gate 1 28 true true 2 = none ∧ gate 0 28 true true 2 = none ∧
    gate 2 28 true true 2 = some .belowMinK ∧
    -- an MSM of one point is valid
    gateMsm 0 28 true true 1 = none ∧ gateMsm2 0 28 true true 1 1 = none := by
  decide +kernel
#guard gate 14 28 true true 1 == some .shape && gate 1 28 true true 1 == some .shape &&
  gate 0 28 true true 1 == some .shape && gate 0 28 true true 2 == none
#guard gateMsm 0 28 true true 1 == none
#guard gateMsm 14 28 true true (2 ^ 14 - 1) == some .belowMinK
#guard gate 14 28 true true (2 ^ 14 - 1) == some .shape
#guard gate 14 28 true true (2 ^ 14) == none && gateMsm 14 28 true true (2 ^ 14) == none
#guard gate 14 28 true true (2 ^ 13) == some .belowMinK
#guard gate 14 28 false false (2 ^ 13) == some .belowMinK
#guard gate 14 28 true true 0 == some .shape && gateMsm 14 28 true true 0 == some .shape
#guard gate 14 28 true true (2 ^ 28) == none && gate 14 28 true true (2 ^ 29) == some .shape
#guard gate 14 28 false false (2 ^ 14) == some .noDevice
#guard gate 14 28 true false (2 ^ 14) == some .unreduced

/-! ### GPU-010: the MSM gate on two lengths

The hook's first test is `n == 0 || n != bases.len()`: shape. 32 scalars and 31
bases (the vector case `scalars-longer-than-bases`): shape at every `min_k`.
31 scalars and 32 bases: the lengths differ, shape as well. 32 and 32 at
`min_k = 1`: the kernel runs; at `min_k = 14`: below-min-k. 0 and 0: shape (empty).
2^14 and 2^14 with no device: no-device; unreduced: unreduced. -/

theorem pin_gateMsm2 :
    gateMsm2 0 28 true true 32 31 = some .shape ∧ gateMsm2 1 28 true true 32 31 = some .shape ∧
    gateMsm2 14 28 true true 32 31 = some .shape ∧
    gateMsm2 1 28 true true 31 32 = some .shape ∧ gateMsm2 14 28 true true 31 32 = some .shape ∧
    gateMsm2 1 28 true true 32 32 = none ∧ gateMsm2 14 28 true true 32 32 = some .belowMinK ∧
    gateMsm2 1 28 true true 0 0 = some .shape ∧ gateMsm2 1 28 true true 0 1 = some .shape ∧
    gateMsm2 14 28 false true (2 ^ 14) (2 ^ 14) = some .noDevice ∧
    gateMsm2 14 28 true false (2 ^ 14) (2 ^ 14) = some .unreduced ∧
    gateMsm2 14 28 true true (2 ^ 14) (2 ^ 14) = none ∧
    gateMsm2 14 28 true true (2 ^ 14) (2 ^ 14 + 1) = some .shape ∧
    gateMsm2 14 28 false false (2 ^ 14 + 1) (2 ^ 14) = some .shape := by
  decide +kernel
#guard gateMsm2 0 28 true true 32 31 == some .shape && gateMsm2 1 28 true true 32 31 == some .shape
#guard gateMsm2 14 28 true true 32 31 == some .shape && gateMsm2 1 28 true true 31 32 == some .shape
#guard gateMsm2 1 28 true true 32 32 == none && gateMsm2 14 28 true true 32 32 == some .belowMinK
#guard gateMsm2 14 28 true true (2 ^ 14) (2 ^ 14) == none
-- mutant control: `gateMsm` alone (one length) lets the mismatched case through
#guard gateMsm 1 28 true true 32 == none

-- the power-of-two test of the gate and the bit test of `deviceSize` agree
#guard (List.range 5000).all fun n => isPow2 n == (n != 0 && n &&& (n - 1) == 0)
#guard (List.range 5000).all fun n => (gate 1 12 true true n == none) == deviceSize 12 n
-- ORACLE-27: also at min_k = 0 (`gate_none_iff_deviceSize`), and with a threshold
#guard (List.range 5000).all fun n => (gate 0 12 true true n == none) == deviceSize 12 n
#guard (List.range 5000).all fun n =>
  (gate 5 12 true true n == none) == (deviceSize 12 n && decide (2 ^ 5 ≤ n))

-- the gated hook: a decline returns the buffer; the fallback is the reference
-- value even with a kernel that returns rubbish
theorem pin_gatedHook :
    gatedHook 2 4 true (fun _ => true) (fun _ => [0]) [5, 6] = (false, [5, 6]) ∧
    runInPlace (List.map (· * 2)) (gatedHook 2 4 true (fun _ => true) (fun _ => [0])) [5, 6]
      = [10, 12] ∧
    gatedHook 2 4 true (fun _ => true) (List.map (· * 2)) [1, 2, 3, 4] = (true, [2, 4, 6, 8]) := by
  decide +kernel

/-! ### GPU-010: the coset shift

The kernel takes a primitive cube root of unity. In F_7: 2^3 = 8 = 1 and 2 ≠ 1,
so 2 is accepted; 1 is not primitive; 3^3 = 27 = 6 ≠ 1. In F_17 there is no
primitive cube root (3 does not divide 16); 3 (the coset shift of the F_17
pins in Tests.lean) is a shape decline. BLS12-381 Fr: 7^((r−1)/3) is accepted,
the generator 7 itself is not. -/

theorem pin_gateShift_small :
    gateShift 7 2 = none ∧ gateShift 7 4 = none ∧ gateShift 7 1 = some .shape ∧
    gateShift 7 3 = some .shape ∧ gateShift 7 8 = some .shape ∧ gateShift 17 3 = some .shape := by
  decide +kernel
#guard gateShift 7 2 == none && gateShift 7 4 == none && gateShift 7 1 == some .shape &&
  gateShift 7 3 == some .shape && gateShift 7 8 == some .shape && gateShift 17 3 == some .shape
#guard gateShift blsR (powM blsR 7 ((blsR - 1) / 3)) == none
#guard gateShift blsR 7 == some .shape
#guard gateShift blsR 1 == some .shape
#guard gateShift blsR Vectors.zeta3 == none

end GpuSpec

/-! ## GPU-038: copy kinds on the wire

vectors/README.md, op 4: "permitted: 0 quotient coefficients, 1 MSM points,
2 counters, 3 base-domain transform output; refused: 4 extended-domain vector,
5 contents of a zeroed region, and above". Code 1 is "MSM result points and the
partial bucket sums of the vendored MSM": two kinds share it. -/

namespace GpuSpec.DataMove

/-- The code of each kind, kind by kind (two kinds share code 1, so the table is
stated per kind and not as a function of the code). -/
theorem pin_copyCode_table :
    copyCode .quotientCoeffs = some 0 ∧ copyCode .msmPoint = some 1 ∧
    copyCode .msmBuckets = some 1 ∧ copyCode .counter = some 2 ∧
    copyCode .baseTransform = some 3 ∧ copyCode .extended = some 4 ∧
    copyCode .zeroedRegion = some 5 ∧ copyCode .scalars = none ∧ copyCode .bases = none ∧
    copyCode .baseCoeffs = none := by decide +kernel

/-- For every kind with a code, `permitted` agrees with the README table
(codes 0 to 3) and with the service oracle's refusal of op 4. Stated per kind:
`msmPoint` and `msmBuckets` both have code 1 and both are permitted. -/
theorem pin_copyCode : ∀ k c, copyCode k = some c →
    (permitted k = true ↔ c ≤ 3) ∧
    (permitted k = false ↔
      Service.opRefusals (Service.init Vectors.cfgDefault) (4 + 100 * c) =
        [.readbackNotPermitted]) := by
  intro k c h
  cases k <;> simp [copyCode] at h <;> subst h <;> decide +kernel

/-- No permitted kind lacks a wire code; the kinds without one are the three the
host uploads and never reads back. -/
theorem pin_no_code :
    VecKind.all.filter (fun k => permitted k && (copyCode k).isNone) = [] ∧
    VecKind.all.filter (fun k => (copyCode k).isNone) = [.scalars, .bases, .baseCoeffs] := by
  decide +kernel

/-! ### GPU-084: the host copy of the bucket sums is zeroed before it is released

By the sentence: the vendored MSM copies its bucket sums to the host, reduces
them, zeroes the host copy and then releases it. The plan with `zeroHost 50`
then `free 50 host` meets the requirement. The same plan with the ordinary
release alone does not (the released memory still holds the sums); the plan
that does neither leaves a live un-zeroed copy. Zeroing after the release cannot
run (there is no host copy to zero). -/

theorem pin_gpu084 :
    msmBucketPlan = [.upload 2, .kernel .msmBucketRows [2, 0] 50, .download 50,
      .hostCompute .bucketReduce [50] 51, .zeroHost 50, .free 50 .host, .free 2 .device,
      .free 50 .device] ∧
    msmBucketPlanFreeOnly = [.upload 2, .kernel .msmBucketRows [2, 0] 50, .download 50,
      .hostCompute .bucketReduce [50] 51, .free 50 .host, .free 2 .device, .free 50 .device] ∧
    msmBucketPlanNoZero = [.upload 2, .kernel .msmBucketRows [2, 0] 50, .download 50,
      .hostCompute .bucketReduce [50] 51, .free 2 .device, .free 50 .device] ∧
    decide (Gpu084 init msmBucketPlan) = true ∧
    decide (Gpu084 init msmBucketPlanFreeOnly) = false ∧
    decide (Gpu084 init msmBucketPlanNoZero) = false ∧
    -- the host copy after the download, after the zeroing, after the release
    ((exec init (msmBucketPlan.take 3)).bind fun σ => get σ 50) =
      some { kind := .msmBuckets, host := true, device := true, zeroed := false } ∧
    ((exec init (msmBucketPlan.take 5)).bind fun σ => get σ 50) =
      some { kind := .msmBuckets, host := true, device := true, zeroed := true } ∧
    ((exec init (msmBucketPlan.take 6)).bind fun σ => get σ 50) =
      some { kind := .msmBuckets, host := false, device := true, zeroed := false } ∧
    -- zeroing after the release does not run; zeroing without a release is accepted
    exec init [.upload 2, .kernel .msmBucketRows [2, 0] 50, .download 50, .free 50 .host,
      .zeroHost 50] = none ∧
    decide (Gpu084 init [.upload 2, .kernel .msmBucketRows [2, 0] 50, .download 50,
      .zeroHost 50]) = true ∧
    -- a second download after the zeroing brings un-zeroed sums back
    decide (Gpu084 init [.upload 2, .kernel .msmBucketRows [2, 0] 50, .download 50,
      .zeroHost 50, .download 50]) = false := by decide +kernel
/-- GPU-084, GPU-038: zero, then reduce, then release does not run (the reduction
would read zeros); and a plan that does not run is no evidence for GPU-038. -/
theorem pin_zero_first_and_rule038 :
    exec init msmBucketPlanZeroFirst = none ∧
    (exec init (msmBucketPlanZeroFirst.take 4)).isSome = true ∧
    step ((exec init (msmBucketPlanZeroFirst.take 4)).getD [])
      (.hostCompute .bucketReduce [50] 51) = none ∧
    -- the same step runs before the zeroing
    ((exec init (msmBucketPlanZeroFirst.take 3)).bind fun σ =>
      step σ (.hostCompute .bucketReduce [50] 51)).isSome = true ∧
    decide (Gpu084 init msmBucketPlanZeroFirst) = false ∧
    decide (Rule038 init [.download 999]) = false ∧
    decide (Gpu038 (trace init [.download 999])) = true ∧
    decide (Rule038 init specPlan) = true ∧ decide (Rule038 init msmBucketPlan) = true ∧
    decide (Rule038 init oldPortPlan) = false ∧ decide (Rule038 init []) = true := by
  decide +kernel
#guard !decide (Rule038 init [.download 999]) && decide (Rule038 init specPlan)
#guard (exec init msmBucketPlanZeroFirst).isNone

#guard decide (Gpu084 init msmBucketPlan) && !decide (Gpu084 init msmBucketPlanFreeOnly) &&
  !decide (Gpu084 init msmBucketPlanNoZero)

#guard (trace init specPlan).map (·.2) ==
  [.baseTransform, .msmPoint, .msmPoint, .quotientCoeffs, .msmPoint, .counter, .counter]
#guard offending (trace init oldPortPlan) ==
  [(20, .extended), (21, .extended), (23, .extended), (40, .zeroedRegion)]
#guard (exec init (stripForbidden init oldPortPlan)).isNone
#guard (exec init specPlan).isSome && (exec init oldPortPlan).isSome
#guard (exec init msmBucketPlan).isSome && trace init msmBucketPlan == [(50, .msmBuckets)]
-- a download of a coset extension is an extended download: the kind comes from the operation
#guard decide (¬ Gpu038 (trace init [.upload 1, .kernel .cosetExtend [1] 10, .download 10]))
#guard trace init [.upload 1, .kernel .cosetExtend [1] 10, .download 10] == [(10, .extended)]
-- a download of a buffer that is not on the device stops the plan
#guard (exec init [.download 1]).isNone && (exec init [.kernel .cosetExtend [1] 10]).isNone
-- the name 1 exists; with a fresh name the same step runs
#guard (exec init [.hostCompute .report [2] 1]).isNone &&
  (exec init [.hostCompute .report [2] 60]).isSome

/-! ### GPU-038: the kind of a created buffer comes from the operation

The table, from the sentences of the requirement and the design: a base-domain
fft or ifft takes one base-domain vector and gives a base transform; the coset
extension takes one and gives an extended vector; the numerator takes extended
vectors (at least one) and gives an extended vector; division and inverse takes
one extended vector and gives the quotient coefficients; the MSM takes scalars
and bases, in that order, and gives one point (the vendored MSM: its bucket rows);
the count takes a zeroed region and gives a counter; reading the counters takes
nothing. Any other input kinds: the step cannot run (`none`). -/

theorem pin_devOp_out :
    DevOp.out .fft [.baseCoeffs] = some .baseTransform ∧
    DevOp.out .ifft [.baseCoeffs] = some .baseTransform ∧
    DevOp.out .cosetExtend [.baseCoeffs] = some .extended ∧
    DevOp.out .numerator [.extended] = some .extended ∧
    DevOp.out .numerator [.extended, .extended, .extended] = some .extended ∧
    DevOp.out .divideAndInverse [.extended] = some .quotientCoeffs ∧
    DevOp.out .extendedInverse [.extended] = some .extended ∧
    DevOp.out .msm [.scalars, .bases] = some .msmPoint ∧
    DevOp.out .msmBucketRows [.scalars, .bases] = some .msmBuckets ∧
    DevOp.out .zero [.extended, .extended] = some .zeroedRegion ∧
    DevOp.out .countNonzero [.zeroedRegion] = some .counter ∧
    DevOp.out .readCounters [] = some .counter ∧
    -- inputs an operation does not take
    DevOp.out .fft [.extended] = none ∧ DevOp.out .fft [] = none ∧
    DevOp.out .fft [.baseCoeffs, .baseCoeffs] = none ∧ DevOp.out .ifft [.extended] = none ∧
    DevOp.out .cosetExtend [.extended] = none ∧ DevOp.out .numerator [] = none ∧
    DevOp.out .numerator [.extended, .baseCoeffs] = none ∧
    DevOp.out .divideAndInverse [.baseCoeffs] = none ∧
    DevOp.out .msm [.bases, .scalars] = none ∧ DevOp.out .msm [.scalars] = none ∧
    DevOp.out .msmBucketRows [.scalars] = none ∧ DevOp.out .countNonzero [.extended] = none ∧
    DevOp.out .readCounters [.counter] = none := by decide +kernel

theorem pin_hostOp_out :
    HostOp.out .cosetExtendCpu [.baseCoeffs] = some .extended ∧
    HostOp.out .numeratorCpu [.extended, .extended] = some .extended ∧
    HostOp.out .extendedInverseCpu [.extended] = some .extended ∧
    HostOp.out .bucketReduce [.msmBuckets] = some .msmPoint ∧
    HostOp.out .scalarsOf [.baseTransform] = some .scalars ∧
    HostOp.out .scalarsOf [.quotientCoeffs] = some .scalars ∧
    HostOp.out .challenge [.msmPoint, .msmPoint] = some .scalars ∧
    HostOp.out .countNonzeroCpu [.zeroedRegion] = some .counter ∧
    HostOp.out .report [.scalars, .msmPoint, .counter, .counter] = some .counter ∧
    HostOp.out .numeratorCpu [] = none ∧ HostOp.out .bucketReduce [.msmPoint] = none ∧
    HostOp.out .scalarsOf [.bases] = none ∧ HostOp.out .challenge [] = none ∧
    HostOp.out .challenge [.extended] = none ∧ HostOp.out .report [.extended] = none ∧
    HostOp.out .countNonzeroCpu [.counter] = none := by decide +kernel

/-- Run from `init`: the created buffer has the operation's kind (buffer 10 after
an fft of the advice column 1 is a base transform; after a coset extension it is
extended). A step whose input kinds the operation does not take stops the plan:
an fft of an extended vector, an MSM with the bases first, a coset extension of
scalars. The mislabel of the old model (an extended vector downloaded as a base
transform) has no plan: `fft` on the extended buffer 20 does not run, and the
download of buffer 20 itself is traced as `extended`. -/
theorem pin_kind_derived :
    ((exec init [.upload 1, .kernel .fft [1] 10]).bind fun σ => get σ 10) =
      some { kind := .baseTransform, host := false, device := true } ∧
    ((exec init [.upload 1, .kernel .cosetExtend [1] 10]).bind fun σ => get σ 10) =
      some { kind := .extended, host := false, device := true } ∧
    exec init [.upload 3, .kernel .cosetExtend [3] 20, .kernel .fft [20] 21] = none ∧
    firstFailure init [.upload 3, .kernel .cosetExtend [3] 20, .kernel .fft [20] 21, .download 21]
      = some (2, .kernel .fft [20] 21) ∧
    exec init [.upload 2, .kernel .msm [0, 2] 12] = none ∧
    (exec init [.upload 2, .kernel .msm [2, 0] 12]).isSome = true ∧
    exec init [.upload 2, .kernel .cosetExtend [2] 20] = none ∧
    trace init [.upload 3, .kernel .cosetExtend [3] 20, .download 20] = [(20, .extended)] ∧
    trace init (quotientHook ++ [.download 22]) = [(23, .quotientCoeffs), (22, .extended)] := by
  decide +kernel
#guard (exec init [.upload 3, .kernel .cosetExtend [3] 20, .kernel .fft [20] 21]).isNone
#guard trace init (quotientHook ++ [.download 22]) == [(23, .quotientCoeffs), (22, .extended)]
-- every buffer the fixed port creates, with its derived kind
#guard ((exec init specPlan).map fun σ =>
    [10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 25, 30, 40, 41, 99].map fun b =>
      (get σ b).map (·.kind)) ==
  some [some .baseTransform, some .scalars, some .msmPoint, some .msmPoint, some .scalars,
    some .extended, some .extended, some .extended, some .quotientCoeffs, some .scalars,
    some .msmPoint, some .counter, some .zeroedRegion, some .counter, some .counter]

end GpuSpec.DataMove

/-! ## Service: direct pins for the two written counters and the context flag

Each pin applies the transition itself, so a mutant that deletes a counter write
fails here and not only on the vectors. -/

namespace GpuSpec.Service

/-- GPU-038: a device-to-host copy of kind 4 (above 3) is counted in
`badReadbacks`, for every state. -/
theorem readback_bad_counted (s : St) :
    (readback s 4).badReadbacks = s.badReadbacks + 1 := rfl

/-- A copy of kind 3 (permitted) is not. -/
theorem readback_ok_not_counted (s : St) :
    (readback s 3).badReadbacks = s.badReadbacks := rfl

/-- Every kind: counted exactly when it is above 3, and every copy is counted in
`readbacks`. -/
theorem readback_counters (s : St) (k : Nat) :
    (readback s k).badReadbacks = s.badReadbacks + (if k > 3 then 1 else 0) ∧
    (readback s k).readbacks = s.readbacks + 1 := ⟨rfl, rfl⟩

/-- A proving request (arrive, admit with 20 and 20 free). Kind 4: the count goes
from 0 to 1 and `invReadback` fails; kind 3: it stays 0. -/
theorem pin_readback_direct : let s := runOps cfg [1, 2 + 2000 + 200000]
    s.badReadbacks = 0 ∧ (readback s 4).badReadbacks = 1 ∧ (readback s 5).badReadbacks = 1 ∧
    (readback s 3).badReadbacks = 0 ∧ (readback s 0).badReadbacks = 0 ∧
    (readback s 4).readbacks = 1 ∧ (readback s 3).readbacks = 1 ∧
    invReadback (readback s 4) = false ∧ invReadback (readback s 3) = true := by decide +kernel
#guard (readback (runOps cfg [1, 2 + 2000 + 200000]) 4).badReadbacks == 1
#guard (readback (runOps cfg [1, 2 + 2000 + 200000]) 3).badReadbacks == 0

/-- GPU-039: the served branch counts a proof served without a verifier accept,
for every state. -/
theorem serve_unverified (s : St) :
    (serve s).unverifiedReturned = s.unverifiedReturned + (if s.verifyOk then 0 else 1) := rfl

/-- GPU-039: the served branch counts the verifier's accept, where it is consumed. -/
theorem serve_verifyAccepts (s : St) :
    (serve s).verifyAccepts = s.verifyAccepts + (if s.verifyOk then 1 else 0) := rfl

/-- The end of the proof stores the answer and counts nothing. -/
theorem finish_verifyAccepts (s : St) (ok : Bool) :
    (finish s ok).verifyAccepts = s.verifyAccepts ∧ (finish s ok).verifyOk = ok := ⟨rfl, rfl⟩

/-- The served branch serves one proof. -/
theorem serve_served (s : St) : (serve s).served = s.served + 1 := rfl

/-- `reply` uses `serve` in its last branch and nowhere else. -/
theorem reply_serve (s : St) (hw : s.wipeOk = true)
    (hd : (s.acceptance && (s.degraded || decide (0 < s.fallbacks))) = false)
    (hv : s.verifyOk = true) : reply s = afterReply (serve s) s.overBound 0 := by
  simp [reply, hw, hd, hv]

/-- A wiped request whose proof the verifier refused (op 6 with a = 0, then a
confirmed wipe): `verifyOk = false`. Applying `serve` to it raises
`unverifiedReturned` from 0 to 1 and breaks `invVerified`; `reply` does not serve
it (GPU-040), so the count stays 0. With an accept (op 106) `serve` leaves 0. -/
theorem pin_serve_unverified :
    let s := runOps cfg [1, 2 + 2000 + 200000, 6, 107]
    let t := runOps cfg [1, 2 + 2000 + 200000, 106, 107]
    s.verifyOk = false ∧ s.phase = wiped ∧ s.unverifiedReturned = 0 ∧
    (serve s).unverifiedReturned = 1 ∧ invVerified (serve s) = false ∧
    (reply s).unverifiedReturned = 0 ∧ (reply s).served = 0 ∧
    t.verifyOk = true ∧ (serve t).unverifiedReturned = 0 ∧ (serve t).served = 1 ∧
    (reply t).unverifiedReturned = 0 ∧ (reply t).served = 1 ∧
    reply t = afterReply (serve t) t.overBound 0 := by decide +kernel
#guard (serve (runOps cfg [1, 2 + 2000 + 200000, 6, 107])).unverifiedReturned == 1
#guard (serve (runOps cfg [1, 2 + 2000 + 200000, 106, 107])).unverifiedReturned == 0

/-- GPU-031: a start state with a context (`ctx := true`) before the first device
operation fails `invCtx`, and so `Inv`; the start state itself passes. `invCtx`
can fail. -/
theorem pin_ctx_at_start :
    invCtx { init cfg with ctx := true } = false ∧ Inv { init cfg with ctx := true } = false ∧
    stepRefusals { init cfg with ctx := true } 1 = [.outsideStateDomain] ∧
    invCtx (init cfg) = true ∧ Inv (init cfg) = true := by decide +kernel
#guard !Inv { init cfg with ctx := true } && Inv (init cfg)

end GpuSpec.Service

/-! ## Audit of the new modules

`Audit.lean` runs before these modules exist, so the namespace audit is run
again here, and the axioms of every new theorem are pinned. -/

/-- info: [] -/
#guard_msgs in
#audit_ns GpuSpec

/-- info: 'GpuSpec.tiledEval_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.tiledEval_prefix

/-- info: 'GpuSpec.tiles_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.tiles_cover

/-- info: 'GpuSpec.tiledEval_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.tiledEval_eq

/-- info: 'GpuSpec.tiledEval_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.tiledEval_zero

/-- info: 'GpuSpec.numeratorTiled_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.numeratorTiled_eq

/-- info: 'GpuSpec.deviceNumeratorTiled_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.deviceNumeratorTiled_eq

/-- info: 'GpuSpec.numeratorTiled_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.numeratorTiled_zero

/-- info: 'GpuSpec.deviceNumeratorTiled_point' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.deviceNumeratorTiled_point

/-- info: 'GpuSpec.quotientCoeffs_tiled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.quotientCoeffs_tiled

/-- info: 'GpuSpec.DataMove.VecKind.all_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.VecKind.all_complete

/-- info: 'GpuSpec.DataMove.Gpu038.nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.Gpu038.nil

/-- info: 'GpuSpec.DataMove.Gpu038.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.Gpu038.append

/-- info: 'GpuSpec.DataMove.emitted_download' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.emitted_download

/-- info: 'GpuSpec.DataMove.step_download_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.step_download_some

/-- info: 'GpuSpec.DataMove.mem_emitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.mem_emitted

/-- info: 'GpuSpec.DataMove.gpu038_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.gpu038_iff

/-- info: 'GpuSpec.DataMove.exec_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.exec_append

/-- info: 'GpuSpec.DataMove.trace_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.trace_append

/-- info: 'GpuSpec.DataMove.gpu038_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.gpu038_append

/-- info: 'GpuSpec.DataMove.gpu038_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.gpu038_prefix

/-- info: 'GpuSpec.DataMove.specPlan_executable' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.DataMove.specPlan_executable

/-- info: 'GpuSpec.DataMove.specPlan_gpu038' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.specPlan_gpu038

/-- info: 'GpuSpec.DataMove.specPlan_noExtended' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.specPlan_noExtended

/-- info: 'GpuSpec.DataMove.specPlan_trace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.specPlan_trace

/-- info: 'GpuSpec.DataMove.specPlan_host_clean' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.specPlan_host_clean

/-- info: 'GpuSpec.DataMove.oldPortPlan_executable' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.DataMove.oldPortPlan_executable

/-- info: 'GpuSpec.DataMove.oldPortPlan_violates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.oldPortPlan_violates

/-- info: 'GpuSpec.DataMove.oldPortPlan_extended' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.oldPortPlan_extended

/-- info: 'GpuSpec.DataMove.oldPortPlan_offending' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.oldPortPlan_offending

/-- info: 'GpuSpec.DataMove.zeroCheck_onDevice_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.zeroCheck_onDevice_ok

/-- info: 'GpuSpec.DataMove.permitted_not_constant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.permitted_not_constant

/-- info: 'GpuSpec.DataMove.permitted_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.permitted_set

/-- info: 'GpuSpec.DataMove.oldPort_stripped_not_executable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.oldPort_stripped_not_executable

/-- info: 'GpuSpec.DataMove.specPlan_strip_id' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.specPlan_strip_id

/-- info: 'GpuSpec.DataMove.msmBucketPlan_executable' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlan_executable

/-- info: 'GpuSpec.DataMove.msmBucketPlan_gpu038' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlan_gpu038

/-- info: 'GpuSpec.DataMove.msmBucketPlan_trace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlan_trace

/-- info: 'GpuSpec.DataMove.msmBucketPlan_violates_before' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlan_violates_before

/-- info: 'GpuSpec.DataMove.msmBucketPlan_gpu084' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlan_gpu084

/-- info: 'GpuSpec.DataMove.msmBucketPlanNoZero_violates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlanNoZero_violates

/-- info: 'GpuSpec.DataMove.gpu084_needs_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.gpu084_needs_run


/-- info: 'GpuSpec.Reason.all_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Reason.all_complete

/-- info: 'GpuSpec.Reason.all_nodup' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Reason.all_nodup

/-- info: 'GpuSpec.Kind.all_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Kind.all_complete

/-- info: 'GpuSpec.Kind.all_nodup' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Kind.all_nodup

/-- info: 'GpuSpec.Reason.index_order' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Reason.index_order

/-- info: 'GpuSpec.Reason.code_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Reason.code_injective

/-- info: 'GpuSpec.RHonest.toDevice' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.RHonest.toDevice

/-- info: 'GpuSpec.Counts.total_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Counts.total_bump

/-- info: 'GpuSpec.count_one_reason' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.count_one_reason

/-- info: 'GpuSpec.count_no_decline' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.count_no_decline

/-- info: 'GpuSpec.countStep_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.countStep_total

/-- info: 'GpuSpec.count_foldl_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.count_foldl_total

/-- info: 'GpuSpec.count_foldl_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.count_foldl_cell

/-- info: 'GpuSpec.countDeclines_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.countDeclines_cell

/-- info: 'GpuSpec.fallbacks_foldl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fallbacks_foldl

/-- info: 'GpuSpec.declines_all_counted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.declines_all_counted

/-- info: 'GpuSpec.prove_any_reasons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.prove_any_reasons

/-- info: 'GpuSpec.prove_reason_independent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.prove_reason_independent

/-- info: 'GpuSpec.isPow2_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.isPow2_iff

/-- info: 'GpuSpec.gate_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.gate_shape

/-- info: 'GpuSpec.gate_below_min_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.gate_below_min_k

/-- info: 'GpuSpec.gate_below_min_k_needs_config' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.gate_below_min_k_needs_config

/-- info: 'GpuSpec.gateMsm_below_min_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.gateMsm_below_min_k

/-- info: 'GpuSpec.gate_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.gate_none_iff

/-- info: 'GpuSpec.gateMsm_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.gateMsm_none_iff

/-- info: 'GpuSpec.gate_none_deviceSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.gate_none_deviceSize

/-- info: 'GpuSpec.gate_len_one_agrees' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.gate_len_one_agrees
/-- info: 'GpuSpec.gate_below_min_k_needs_two' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.gate_below_min_k_needs_two
/-- info: 'GpuSpec.deviceSize_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.deviceSize_iff
/-- info: 'GpuSpec.gate_none_iff_deviceSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.gate_none_iff_deviceSize

/-- info: 'GpuSpec.gate_declines_before_write' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.gate_declines_before_write

/-- info: 'GpuSpec.gatedHook_honest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.gatedHook_honest

/-- info: 'GpuSpec.gatedHook_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.gatedHook_run

/-- info: 'GpuSpec.pin_rotIndex_ex4' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.pin_rotIndex_ex4

/-- info: 'GpuSpec.pin_numeratorAt_ex4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_numeratorAt_ex4

/-- info: 'GpuSpec.pin_numerator_ex4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_numerator_ex4

/-- info: 'GpuSpec.pin_rotIndex_ex8' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.pin_rotIndex_ex8

/-- info: 'GpuSpec.pin_tiled_ex8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_tiled_ex8

/-- info: 'GpuSpec.pin_tile_border_ex8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_tile_border_ex8

/-- info: 'GpuSpec.pin_tiled_all_sizes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_tiled_all_sizes

/-- info: 'GpuSpec.pin_tiled_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_tiled_zero

/-- info: 'GpuSpec.pin_reason_codes' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.pin_reason_codes

/-- info: 'GpuSpec.pin_reason_index' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.pin_reason_index

/-- info: 'GpuSpec.pin_counts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_counts

/-- info: 'GpuSpec.pin_gate_14' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.pin_gate_14

/-- info: 'GpuSpec.pin_gatedHook' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.pin_gatedHook

/-- info: 'GpuSpec.pin_gateShift_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.pin_gateShift_small

/-- info: 'GpuSpec.DataMove.pin_copyCode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.pin_copyCode

/-- info: 'GpuSpec.DataMove.pin_no_code' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.pin_no_code

/-- info: 'GpuSpec.DataMove.zeroCheck_readback_violates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.zeroCheck_readback_violates

/-- info: 'GpuSpec.DataMove.extended_readback_violates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.extended_readback_violates

/-- info: 'GpuSpec.DataMove.zeroCheck_readback_offending' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.zeroCheck_readback_offending

/-! ### Two random sources, the two-length MSM gate, derived kinds, the written counters -/

/-- info: 'GpuSpec.prove_foldl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.prove_foldl

/-- info: 'GpuSpec.proveStep_draws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.proveStep_draws

/-- info: 'GpuSpec.draws_foldl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.draws_foldl

/-- info: 'GpuSpec.draws_independent_of_device' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.draws_independent_of_device

/-- info: 'GpuSpec.gateMsm2_mismatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.gateMsm2_mismatch

/-- info: 'GpuSpec.gateMsm2_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.gateMsm2_eq

/-- info: 'GpuSpec.gateMsm2_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.gateMsm2_none_iff

/-- info: 'GpuSpec.pin_two_sources' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_two_sources

/-- info: 'GpuSpec.pin_two_sources_any_answer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_two_sources_any_answer

/-- info: 'GpuSpec.pin_source_not_substituted' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.pin_source_not_substituted

/-- info: 'GpuSpec.pin_gateMsm2' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.pin_gateMsm2

/-- info: 'GpuSpec.DataMove.get_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.get_cons

/-- info: 'GpuSpec.DataMove.extended_only_from' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.extended_only_from

/-- info: 'GpuSpec.DataMove.extendedOp_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.extendedOp_out

/-- info: 'GpuSpec.DataMove.extendedOp_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.extendedOp_iff

/-- info: 'GpuSpec.DataMove.step_kind_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.step_kind_stable

/-- info: 'GpuSpec.DataMove.exec_kind_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.exec_kind_stable

/-- info: 'GpuSpec.DataMove.made_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.made_step

/-- info: 'GpuSpec.DataMove.kind_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.kind_determined

/-- info: 'GpuSpec.DataMove.plan_kind_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.plan_kind_determined

/-- info: 'GpuSpec.DataMove.makesExtended_made' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.makesExtended_made

/-- info: 'GpuSpec.DataMove.exec_append_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.exec_append_some

/-- info: 'GpuSpec.DataMove.trace_download_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.trace_download_mem

/-- info: 'GpuSpec.DataMove.mislabel_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.mislabel_impossible

/-- info: 'GpuSpec.DataMove.pin_devOp_out' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.DataMove.pin_devOp_out

/-- info: 'GpuSpec.DataMove.pin_hostOp_out' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.DataMove.pin_hostOp_out

/-- info: 'GpuSpec.DataMove.pin_kind_derived' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.pin_kind_derived

/-- info: 'GpuSpec.Service.readback_bad_counted' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.readback_bad_counted

/-- info: 'GpuSpec.Service.readback_ok_not_counted' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.readback_ok_not_counted

/-- info: 'GpuSpec.Service.readback_counters' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.readback_counters

/-- info: 'GpuSpec.Service.pin_readback_direct' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_readback_direct

/-- info: 'GpuSpec.Service.serve_unverified' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.serve_unverified

/-- info: 'GpuSpec.Service.serve_served' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.serve_served

/-- info: 'GpuSpec.Service.reply_serve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.reply_serve

/-- info: 'GpuSpec.Service.pin_serve_unverified' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_serve_unverified

/-- info: 'GpuSpec.Service.pin_ctx_at_start' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_ctx_at_start

/-! ### Fallback reasons (GPU-012, GPU-085), positional devices, GPU-084 erasure, the lifetime cap -/

/-- info: 'GpuSpec.proveStep_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.proveStep_pos

/-- info: 'GpuSpec.Reason.isFallback_index' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Reason.isFallback_index

/-- info: 'GpuSpec.Reason.fallbacks_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Reason.fallbacks_eq

/-- info: 'GpuSpec.Counts.fallbackTotal_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Counts.fallbackTotal_bump

/-- info: 'GpuSpec.countStep_fallbackTotal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.countStep_fallbackTotal

/-- info: 'GpuSpec.count_foldl_fallbackTotal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.count_foldl_fallbackTotal

/-- info: 'GpuSpec.decline_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.decline_split

/-- info: 'GpuSpec.fallbacks_by_reason' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fallbacks_by_reason

/-- info: 'GpuSpec.proveStep_fallbacks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.proveStep_fallbacks

/-- info: 'GpuSpec.pin_fallback_reasons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_fallback_reasons

/-- info: 'GpuSpec.fault_reason' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fault_reason

/-- info: 'GpuSpec.service_fallbacks_foldl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.service_fallbacks_foldl

/-- info: 'GpuSpec.service_fallbacks_eq_fallbackOps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.service_fallbacks_eq_fallbackOps

/-- info: 'GpuSpec.pin_service_declines' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_service_declines

/-- info: 'GpuSpec.pin_accept_then_decline' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_accept_then_decline

/-- info: 'GpuSpec.DataMove.msmBucketPlan_buckets_on_host' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlan_buckets_on_host

/-- info: 'GpuSpec.DataMove.msmBucketPlanFreeOnly_violates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlanFreeOnly_violates

/-- info: 'GpuSpec.DataMove.gpu084_unzeroed_free_violates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.gpu084_unzeroed_free_violates

/-- info: 'GpuSpec.DataMove.specPlan_no_bucket_sums' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.specPlan_no_bucket_sums

/-- info: 'GpuSpec.DataMove.pin_copyCode_table' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.pin_copyCode_table

/-- info: 'GpuSpec.DataMove.pin_gpu084' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.pin_gpu084

/-- info: 'GpuSpec.Service.recent_length_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.recent_length_le

/-- info: 'GpuSpec.Service.recent_no_window' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.recent_no_window

/-- info: 'GpuSpec.Service.expected_decline_no_fallback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.expected_decline_no_fallback

/-- info: 'GpuSpec.Service.expected_decline_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.expected_decline_step

/-- info: 'GpuSpec.Service.fallback_decline' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.fallback_decline

/-- info: 'GpuSpec.Service.lifetime_cap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.lifetime_cap

/-- info: 'GpuSpec.Service.pin_production_expected_decline' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_production_expected_decline

/-- info: 'GpuSpec.Service.pin_bench_expected_decline' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_bench_expected_decline

/-- info: 'GpuSpec.Service.pin_acceptance_expected_decline' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_acceptance_expected_decline

/-- info: 'GpuSpec.Service.pin_decline_all_reasons' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_decline_all_reasons

/-- info: 'GpuSpec.Service.pin_restart_lifetime_any_tick' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_restart_lifetime_any_tick

/-! ### Verifier accepts at the reply, counters in phase proved, quotient references, Rule038 -/

/-- info: 'GpuSpec.pin_inst_columns' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_inst_columns

/-- info: 'GpuSpec.pin_quotientCoeffs_F17' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.pin_quotientCoeffs_F17

/-- info: 'GpuSpec.Service.serve_verifyAccepts' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.serve_verifyAccepts

/-- info: 'GpuSpec.Service.finish_verifyAccepts' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.finish_verifyAccepts

/-- info: 'GpuSpec.Service.recordFailure_verifyAccepts' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.recordFailure_verifyAccepts

/-- info: 'GpuSpec.Service.recordFailures_verifyAccepts' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.recordFailures_verifyAccepts

/-- info: 'GpuSpec.Service.afterReply_verifyAccepts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.afterReply_verifyAccepts

/-- info: 'GpuSpec.Service.reply_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.reply_verify

/-- info: 'GpuSpec.Service.verify_counted_only_when_served' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.verify_counted_only_when_served

/-- info: 'GpuSpec.Service.verify_count_other_ops' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.verify_count_other_ops

/-- info: 'GpuSpec.Service.pin_readback_proved' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_readback_proved

/-- info: 'GpuSpec.Service.pin_wipe_fail_no_verify' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_wipe_fail_no_verify

/-- info: 'GpuSpec.Service.pin_acceptance_refusal_no_verify' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_acceptance_refusal_no_verify

/-- info: 'GpuSpec.Service.pin_verify_counted_at_reply' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.pin_verify_counted_at_reply

/-- info: 'GpuSpec.DataMove.specPlan_rule038' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.specPlan_rule038

/-- info: 'GpuSpec.DataMove.oldPortPlan_not_rule038' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.oldPortPlan_not_rule038

/-- info: 'GpuSpec.DataMove.rule038_needs_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.rule038_needs_run

/-- info: 'GpuSpec.DataMove.msmBucketPlan_rule038' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.msmBucketPlan_rule038

/-- info: 'GpuSpec.DataMove.zeroed_input_not_executable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.zeroed_input_not_executable

/-- info: 'GpuSpec.DataMove.zero_before_reduce_not_executable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.zero_before_reduce_not_executable

/-- info: 'GpuSpec.DataMove.pin_zero_first_and_rule038' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.DataMove.pin_zero_first_and_rule038

/-! ### Challenges, the breaker characterisation, arrival classes, the acceptance refusal -/

/-- info: 'GpuSpec.pin_challenges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.pin_challenges

/-- info: 'GpuSpec.Service.breaker_opens_at_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.breaker_opens_at_limit

/-- info: 'GpuSpec.Service.recordFailure_breaker_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.recordFailure_breaker_congr

/-- info: 'GpuSpec.Service.arrive_failure_classes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.arrive_failure_classes

/-- info: 'GpuSpec.Service.recordFailure_counters' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.recordFailure_counters

/-- info: 'GpuSpec.Service.recordFailures_counters' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.recordFailures_counters

/-- info: 'GpuSpec.Service.acceptance_degraded_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.acceptance_degraded_refused

/-- info: 'GpuSpec.Service.acceptance_degraded_refused_needs_side' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.Service.acceptance_degraded_refused_needs_side
