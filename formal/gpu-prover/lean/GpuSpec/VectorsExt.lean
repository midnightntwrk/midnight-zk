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
import GpuSpec.Declines
import GpuSpec.DataMove

/-!
# Golden vector cases, contract v2

What `vectors/README.md` (format `midnight-gpu-vectors/2`) adds to the value
cases of `Vectors.lean`:

* the expected decision of every arithmetic case (`expect`, `min_k`, `reason`),
  computed by the entry gate of `Declines.lean` (`gate`, `gateMsm`, `gateMsm2`,
  `gateShift`), never typed in;
* the cases the stock transform does not take (decline cases) and the
  length-1 transform;
* the families `gate.json` (the gate as a table), `threshold.json` (cases at
  the default threshold `2^14`) and `datamove.json` (GPU-038 as data).

Expected values come from the reference definitions. The one exception is the
transform output of `threshold.json`: see `thresholdNttOut`.
-/

namespace GpuSpec.Vectors

/-! ## Expected decisions -/

/-- The largest transform and MSM size the kernels take: `2^28`. -/
def maxLog : Nat := 28

/-- The default threshold (GPU-074): inputs below `2^14` elements decline. -/
def defaultMinK : Nat := 14

/-- The expectation of a case: the `min_k` to run it under and the decision of the gate at
that `min_k` (`none`: the kernel runs and gives the listed values). -/
structure Expect where
  minK : Nat
  decision : Option Reason
  deriving Repr, DecidableEq

/-- The expectation from a gate `g` (a function of `min_k`; device present, reduced input).
`min_k` is 1, the lowest threshold above "no threshold", when the gate at 1 does not answer
`below-min-k`. It does for an MSM of a single element (`1 < 2^1`): such a case runs under
`min_k = 0`. A transform of a single element is a `shape` decline (ORACLE-27) and lists 1. -/
def expectOf (g : Nat → Option Reason) : Expect :=
  if g 1 = some .belowMinK then { minK := 0, decision := g 0 } else { minK := 1, decision := g 1 }

/-- `"value"` or `"decline"`. -/
def Expect.word (e : Expect) : String := if e.decision.isNone then "value" else "decline"

/-! ## ntt.json -/

/-- The cases outside `nttCases`: the length-1 transform (a `shape` decline by ORACLE-27; the
stock function takes it, so its reference values are listed), and
the inputs the stock function does not take: the empty input and the lengths 3, 6 and 7.
`logN` is the `log_n` the caller passes (the next power of two) and `omega` the root of
that size. -/
def nttEdgeCases : List NttCase :=
  let p := blsR
  let root := fun k => rootOfUnity p blsGen (2 ^ k)
  [ { name := "one-element", logN := 0, omega := root 0, input := randoms p 1100 1 },
    { name := "empty", logN := 0, omega := root 0, input := [] },
    { name := "length-3", logN := 2, omega := root 2, input := randoms p 1103 3 },
    { name := "length-6", logN := 3, omega := root 3, input := randoms p 1106 6 },
    { name := "length-7", logN := 3, omega := root 3, input := randoms p 1107 7 } ]

/-- Every case of `ntt.json`, in file order. -/
def nttAll : List NttCase := nttCases ++ nttEdgeCases

/-- The transform gate on the input length. -/
def nttExpect (c : NttCase) : Expect :=
  expectOf fun minK => gate minK maxLog true true c.input.length

/-- Does the stock function take the input (its length is `2^log_n`)? -/
def NttCase.stock (c : NttCase) : Bool := c.input.length == 2 ^ c.logN

/-- The reference forward transform, or `[]` when the stock function does not take the input. -/
def nttRef (c : NttCase) : List Nat := if c.stock then ntt blsR c.omega c.input else []

/-- The reference inverse transform, or `[]` when the stock function does not take the input. -/
def inttRef (c : NttCase) : List Nat := if c.stock then intt blsR c.omega c.input else []

/-! ## coset.json -/

/-- `"zeta3"` for the prover's shift `7^((r-1)/3)`, `"generic"` for any other shift. -/
def CosetCase.shift (c : CosetCase) : String := if c.zeta = zeta3 then "zeta3" else "generic"

/-- The shift test first (GPU-010), then the transform gate on the extended length `n · ext`,
the size of the transform the kernel runs. -/
def cosetDecision (minK : Nat) (c : CosetCase) : Option Reason :=
  match gateShift blsR c.zeta with
  | some r => some r
  | none => gate minK maxLog true true (c.input.length * c.ext)

def cosetExpect (c : CosetCase) : Expect := expectOf fun minK => cosetDecision minK c

/-! ## msm.json -/

/-- The cases the device MSM declines: the empty input, and a scalar vector longer than the
base vector. -/
def msmDeclineCases : List MsmCase :=
  let p := blsR
  [ { name := "empty", scalars := [], bases := [], mask := [] },
    { name := "scalars-longer-than-bases", scalars := randoms p 11 32, bases := msmBases.take 31,
      mask := randoms p 9 32 } ]

/-- Every case of `msm.json`, in file order. -/
def msmAll : List MsmCase := msmCases ++ msmDeclineCases

/-- The MSM decision: `gateMsm2` of `Declines.lean` on the scalar count and the base count,
and nothing else. The clause "more scalars than bases is a `shape` decline" of
vectors/README.md is the gate's length test (`gateMsm2_mismatch`). -/
def msmDecision (minK : Nat) (c : MsmCase) : Option Reason :=
  gateMsm2 minK maxLog true true c.scalars.length c.bases.length

def msmExpect (c : MsmCase) : Expect := expectOf fun minK => msmDecision minK c

/-! ## quotient.json: the quotient coefficients -/

/-- The base domain size `n = N / ratio`. -/
def QuotientCase.n (c : QuotientCase) : Nat := c.cols.size / c.cols.ratio

/-- A primitive `N`-th root for the extended domain of the case. -/
def QuotientCase.omegaExt (c : QuotientCase) : Nat := rootOfUnity blsR blsGen c.cols.size

/-- The coset shift of the quotient pipeline: the prover's shift `zeta3`. -/
def QuotientCase.zeta (_ : QuotientCase) : Nat := zeta3

/-- The extended coset points `x_k = zeta · omega_ext^k`. -/
def QuotientCase.points (c : QuotientCase) : List Nat :=
  (List.range c.cols.size).map fun k => mulM blsR c.zeta (powM blsR c.omegaExt k)

/-- The reference quotient coefficients of the case's reference numerator. -/
def QuotientCase.coeffs (c : QuotientCase) : List Nat :=
  quotientCoeffs blsR c.zeta c.omegaExt c.n (numerator blsR c.y c.cols c.gates)

/-! ## gate.json -/

/-- The operation names of `gate.json`. The quotient has no gate row. -/
def opName : Kind → String
  | .msm => "msm"
  | .ntt => "fft"
  | .intt => "ifft"
  | .quotient => "quotient"

structure GateCase where
  op : Kind
  len : Nat
  minK : Nat
  maxLog : Nat
  device : Bool
  reduced : Bool
  deriving Repr, DecidableEq

/-- The decision of a row: `gateMsm` for the MSM, `gate` for the transforms. -/
def GateCase.decision (c : GateCase) : Option Reason :=
  match c.op with
  | .msm => gateMsm c.minK c.maxLog c.device c.reduced c.len
  | _ => gate c.minK c.maxLog c.device c.reduced c.len

/-- The lengths of the table under the default configuration: 0, 1, non-powers of two, the
default threshold (`2^13`, `2^14 - 1`, `2^14`, `2^14 + 1`) and the largest size (`2^28`,
`2^28 + 1`, `2^29`). -/
def gateLens : List Nat :=
  [0, 1, 3, 6, 7, 2 ^ 13, 2 ^ 14 - 1, 2 ^ 14, 2 ^ 14 + 1, 2 ^ 28, 2 ^ 28 + 1, 2 ^ 29]

/-- For each operation: every length of `gateLens` with a device and a reduced input; then
the order of the checks (shape, below-min-k, no-device, unreduced) on inputs that fail
several of them; then the thresholds 1 and 0 that the short cases of the other files use. -/
def gateCases : List GateCase :=
  ([Kind.msm, .ntt, .intt] : List Kind).flatMap fun op =>
    let row := fun (len minK : Nat) (device reduced : Bool) =>
      ({ op, len, minK, maxLog, device, reduced } : GateCase)
    gateLens.map (fun len => row len defaultMinK true true) ++
    [ row (2 ^ 14) defaultMinK false true,       -- no device
      row (2 ^ 14) defaultMinK true false,       -- unreduced
      row (2 ^ 14) defaultMinK false false,      -- no-device before unreduced
      row (2 ^ 13) defaultMinK false false,      -- below-min-k before no-device
      row (2 ^ 14 - 1) defaultMinK false false,
      row 0 defaultMinK false false,             -- shape before everything
      row (2 ^ 29) defaultMinK false false,
      row 1 1 true true, row 2 1 true true, row 3 1 true true, row 1 0 true true ]

/-! ## threshold.json -/

structure ThresholdMsm where
  name : String
  n : Nat
  scalarsSeed : Nat
  basesSeed : Nat
  deriving Repr

/-- MSM at the default threshold: one below, at, one above. The three cases share the bases
seed, so their base vectors are prefixes of one another. -/
def thresholdMsmCases : List ThresholdMsm :=
  [ { name := "msm-2^14-1", n := 2 ^ 14 - 1, scalarsSeed := 5001, basesSeed := 6000 },
    { name := "msm-2^14", n := 2 ^ 14, scalarsSeed := 5002, basesSeed := 6000 },
    { name := "msm-2^14+1", n := 2 ^ 14 + 1, scalarsSeed := 5003, basesSeed := 6000 } ]

/-- The reference MSM of the generated vectors. -/
def ThresholdMsm.result (c : ThresholdMsm) : Nat :=
  msm blsR (randoms blsR c.scalarsSeed c.n) (randoms blsR c.basesSeed c.n)

/-- The decision under the default `min_k`. -/
def ThresholdMsm.decision (c : ThresholdMsm) : Option Reason :=
  gateMsm defaultMinK maxLog true true c.n

structure ThresholdNtt where
  name : String
  logN : Nat
  inputSeed : Nat
  deriving Repr

def thresholdNttCases : List ThresholdNtt :=
  [ { name := "ntt-2^13", logN := 13, inputSeed := 7013 },
    { name := "ntt-2^14", logN := 14, inputSeed := 7014 } ]

def ThresholdNtt.omega (c : ThresholdNtt) : Nat := rootOfUnity blsR blsGen (2 ^ c.logN)

def ThresholdNtt.input (c : ThresholdNtt) : List Nat := randoms blsR c.inputSeed (2 ^ c.logN)

/-- The forward transform of a threshold case. This is the one expected value that does not
come from a reference definition: the reference `ntt` takes `n^2` multiplications (2^28 at
`2^14`), so the radix-2 model `fft` computes it. `GpuSpec.fft_eq_ntt_bls` proves
`fft = ntt` for every input of length `2^k`, `1 ≤ k ≤ 32`, at the root
`rootOfUnity blsR blsGen (2^k)`; `VectorPins.thresholdNtt_eq_ntt` applies it to these cases. -/
def thresholdNttOut (c : ThresholdNtt) : List Nat := fft blsR c.omega c.input

/-- `Σ_k xs[k] · 7^k mod p`, with a running power of 7. -/
def digest (p : Nat) (xs : List Nat) : Nat :=
  (xs.foldl (fun (acc : Nat × Nat) x => (addM p acc.1 (mulM p x acc.2), mulM p acc.2 blsGen))
    (0, 1 % p)).1

def ThresholdNtt.decision (c : ThresholdNtt) : Option Reason :=
  gate defaultMinK maxLog true true (2 ^ c.logN)

/-! ## datamove.json -/

/-- The kind names of `datamove.json`. -/
def kindName : DataMove.VecKind → String
  | .scalars => "scalars"
  | .bases => "bases"
  | .baseCoeffs => "base-coeffs"
  | .baseTransform => "base-transform"
  | .extended => "extended"
  | .quotientCoeffs => "quotient-coeffs"
  | .msmPoint => "msm-point"
  | .counter => "counter"
  | .zeroedRegion => "zeroed-region"
  | .msmBuckets => "msm-buckets"

/-- The kinds GPU-038 lets a device-to-host copy carry, in the order of `VecKind.all`. -/
def permittedKinds : List DataMove.VecKind := DataMove.VecKind.all.filter DataMove.permitted

def forbiddenKinds : List DataMove.VecKind :=
  DataMove.VecKind.all.filter fun k => !DataMove.permitted k

structure Plan where
  name : String
  steps : List DataMove.Step
  deriving Repr

def plans : List Plan :=
  [ { name := "spec", steps := DataMove.specPlan },
    { name := "old-port", steps := DataMove.oldPortPlan },
    { name := "msm-buckets", steps := DataMove.msmBucketPlan } ]

/-- Every step of the plan can run from the start store. -/
def Plan.executable (p : Plan) : Bool := (DataMove.exec DataMove.init p.steps).isSome

/-- GPU-038 on the plan: it runs and every device-to-host copy is permitted (`Rule038`). -/
def Plan.gpu038 (p : Plan) : Bool :=
  decide (DataMove.Rule038 DataMove.init p.steps)

/-- The kinds copied to the host, in order. -/
def Plan.trace (p : Plan) : List DataMove.VecKind :=
  (DataMove.trace DataMove.init p.steps).map (·.2)

/-- The kinds of the copies GPU-038 forbids, in order. -/
def Plan.offending (p : Plan) : List DataMove.VecKind :=
  (DataMove.offending (DataMove.trace DataMove.init p.steps)).map (·.2)

end GpuSpec.Vectors
