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

import GpuSpec.Quotient
import GpuSpec.Msm
import GpuSpec.Service

/-!
# Golden vector cases

Pure data for the vector files that `oracle --vectors DIR` writes. Every
expected value is computed by the reference definitions (`ntt`, `intt`,
`cosetExt`, `cosetToCoeff`, `msm`, `numerator`, `Service.stepOp`), never by
the device models. `Tests.lean` checks the device models against the same
cases.

The lists of this module are the value cases on which the stock transform
runs (`Tests.lean` runs every device model over them). The decline cases, the
length-1 transform, the expected decisions (`expect`, `min_k`, `reason`) and
the families gate, threshold and datamove are in `VectorsExt.lean`.
-/

namespace GpuSpec.Vectors

/-- A deterministic generator of field elements (a 64-bit LCG, then reduced). -/
def lcg (seed : Nat) : Nat := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def randoms (p seed n : Nat) : List Nat :=
  ((List.range n).foldl (fun (acc : List Nat × Nat) _ =>
    let s1 := lcg acc.2
    let s2 := lcg s1
    let s3 := lcg s2
    let s4 := lcg s3
    ((s1 + s2 * 2 ^ 64 + s3 * 2 ^ 128 + s4 * 2 ^ 192) % p :: acc.1, s4)) ([], seed)).1.reverse

structure NttCase where
  name : String
  logN : Nat
  omega : Nat
  input : List Nat
  deriving Repr

/-- NTT cases over BLS12-381 Fr: random inputs at every size 2^1 .. 2^6 and the
edge inputs (zero, all p - 1, a delta, a constant) at 2^3. -/
def nttCases : List NttCase :=
  let p := blsR
  let rnd := (List.range 6).map fun i =>
    let n := 2 ^ (i + 1)
    { name := s!"random-2^{i + 1}", logN := i + 1, omega := rootOfUnity p blsGen n,
      input := randoms p (1000 + i) n }
  let w8 := rootOfUnity p blsGen 8
  rnd ++ [
    { name := "zero-2^3", logN := 3, omega := w8, input := List.replicate 8 0 },
    { name := "max-2^3", logN := 3, omega := w8, input := List.replicate 8 (p - 1) },
    { name := "delta-2^3", logN := 3, omega := w8, input := 1 :: List.replicate 7 0 },
    { name := "const-2^3", logN := 3, omega := w8, input := List.replicate 8 5 } ]

structure CosetCase where
  name : String
  logN : Nat
  ext : Nat
  zeta : Nat
  omegaExt : Nat
  input : List Nat
  deriving Repr

/-- Two shifts: the generator 7, and the cube root of unity `7^((r-1)/3)`. -/
def zeta3 : Nat := powM blsR blsGen ((blsR - 1) / 3)

def cosetCases : List CosetCase :=
  let p := blsR
  (([(2, 2), (3, 2), (2, 4), (4, 4)] : List (Nat × Nat)).flatMap fun (lg, ext) =>
    let n := 2 ^ lg
    [ { name := s!"shift7-2^{lg}-x{ext}", logN := lg, ext, zeta := blsGen,
        omegaExt := rootOfUnity p blsGen (n * ext), input := randoms p (2000 + lg * 10 + ext) n },
      { name := s!"zeta3-2^{lg}-x{ext}", logN := lg, ext, zeta := zeta3,
        omegaExt := rootOfUnity p blsGen (n * ext), input := randoms p (3000 + lg * 10 + ext) n } ])

structure MsmCase where
  name : String
  scalars : List Nat
  bases : List Nat
  mask : List Nat
  deriving Repr

/-- The base vector that the 32-element MSM cases share. -/
def msmBases : List Nat := randoms blsR 7 32

/-- The scalars at the fold boundary of the signed-digit method (`abs` turns a scalar above
`(r-1)/2` into `r - s`): `(r-1)/2` (the last scalar that is not folded), `(r+1)/2` (the first
one that is; the kernel's top-limb test leaves it unfolded), `1`, `r-1` (folds to 1), `2^254`
(the top bit of a reduced scalar alone), and scalars whose windows are all ones: `2^254 - 1`
(every window of every width), `2^250 - 1` (25 windows of 10 bits) and `2^247 - 1` (19
windows of 13 bits). -/
def foldBoundaryScalars : List Nat :=
  [(blsR - 1) / 2, (blsR + 1) / 2, 1, blsR - 1, 2 ^ 254, 2 ^ 254 - 1, 2 ^ 250 - 1, 2 ^ 247 - 1]

/-- MSM value cases over the toy group `Z_r` (see vectors/README.md for the map to G1). Every
case has one mask element for each scalar. -/
def msmCases : List MsmCase :=
  let p := blsR
  let n := 32
  let mask := randoms p 9 n
  let bases := msmBases
  let uniform := randoms p 11 n
  let fourthZero := (List.range n).zip bases |>.map fun (i, b) => if i % 4 = 0 then 0 else b
  let bases33 := randoms p 7 33
  let mask33 := randoms p 9 33
  [ { name := "uniform", scalars := uniform, bases, mask },
    { name := "zero", scalars := List.replicate n 0, bases, mask },
    { name := "repeated", scalars := List.replicate n (uniform.headD 1), bases, mask },
    { name := "ninety-percent-zero", scalars := (List.range n).map
        (fun i => if i % 10 = 0 then uniform.getD i 0 else 0), bases, mask },
    { name := "below-2^16", scalars := (randoms p 13 n).map (· % 2 ^ 16), bases, mask },
    { name := "max", scalars := List.replicate n (p - 1), bases, mask },
    { name := "one-point", scalars := [uniform.headD 1], bases := [bases.headD 1],
      mask := [mask.headD 1] },
    { name := "infinity-every-fourth-base", scalars := uniform, bases := fourthZero, mask },
    { name := "infinity-all-bases", scalars := uniform, bases := List.replicate n 0, mask },
    { name := "zero-scalars-and-infinity-bases", scalars := (List.range n).zip uniform |>.map
        (fun (i, s) => if i % 3 = 0 then 0 else s), bases := fourthZero, mask },
    { name := "fold-boundary", scalars := foldBoundaryScalars,
      bases := bases.take foldBoundaryScalars.length,
      mask := mask.take foldBoundaryScalars.length },
    { name := "length-3", scalars := randoms p 15 3, bases := bases33.take 3,
      mask := mask33.take 3 },
    { name := "length-31", scalars := randoms p 16 31, bases := bases33.take 31,
      mask := mask33.take 31 },
    { name := "length-33", scalars := randoms p 17 33, bases := bases33, mask := mask33 } ]

structure QuotientCase where
  name : String
  y : Nat
  cols : Columns
  gates : List Expr
  deriving Repr

/-- Constraint systems on an extended domain. The first case (16 points, n = 4, ratio 4)
reaches every expression node type. -/
def quotientCases : List QuotientCase :=
  let p := blsR
  let N := 16
  let cols : Columns :=
    { fixed := [randoms p 21 N, randoms p 22 N], advice := [randoms p 23 N, randoms p 24 N],
      inst := [randoms p 25 N], challenges := randoms p 26 2, size := N, ratio := 4 }
  let gates : List Expr :=
    [ .prod (.fixed 0 0) (.sum (.advice 0 0) (.neg (.advice 1 1))),
      .sum (.scaled (.prod (.advice 0 (-1)) (.inst 0 0)) 3) (.const 5),
      .prod (.fixed 1 0) (.sum (.advice 1 0) (.challenge 1)),
      .neg (.prod (.challenge 0) (.sum (.fixed 0 1) (.const (p - 1)))) ]
  -- rotations +2 and -3: with ratio 4 they move a read by 8 and by -12 points, so reads
  -- wrap at the end of the domain (+2) and at its start (-3)
  let wrapGates : List Expr :=
    [ .sum (.advice 0 2) (.fixed 0 (-3)),
      .prod (.inst 0 2) (.advice 1 (-3)),
      .sum (.fixed 1 2) (.neg (.inst 0 (-3))) ]
  let N64 := 64
  let cols64 : Columns :=
    { fixed := [randoms p 31 N64, randoms p 32 N64],
      advice := [randoms p 33 N64, randoms p 34 N64],
      inst := [randoms p 35 N64], challenges := randoms p 36 2, size := N64, ratio := 8 }
  let zero := List.replicate N 0
  let colsZero : Columns :=
    { fixed := [zero, zero], advice := [zero, zero], inst := [zero],
      challenges := randoms p 26 2, size := N, ratio := 4 }
  -- two instance columns with different data: every gate reads column 1, alone, next to
  -- column 0 and at rotations +1 and -1
  let colsInst2 : Columns := { cols with inst := [randoms p 25 N, randoms p 38 N] }
  let instGates : List Expr :=
    [ .prod (.inst 0 0) (.inst 1 1),
      .sum (.inst 1 0) (.neg (.inst 0 (-1))),
      .inst 1 0 ]
  -- 32 points with ratio 8: n = 4 and N / n = 8 differ, so the exponent of the vanishing
  -- polynomial `x^n - 1` is told apart from the ratio
  let N32 := 32
  let cols32 : Columns :=
    { fixed := [randoms p 41 N32, randoms p 42 N32],
      advice := [randoms p 43 N32, randoms p 44 N32],
      inst := [randoms p 45 N32], challenges := randoms p 46 2, size := N32, ratio := 8 }
  [ { name := "all-node-types", y := (randoms p 27 1).headD 2, cols, gates },
    { name := "single-gate", y := 9, cols, gates := [.sum (.advice 0 0) (.const 1)] },
    { name := "rotations-wrap", y := (randoms p 28 1).headD 2, cols, gates := wrapGates },
    { name := "domain-64-ratio-8", y := (randoms p 37 1).headD 2, cols := cols64,
      gates := gates ++ wrapGates },
    { name := "no-gate", y := (randoms p 29 1).headD 2, cols, gates := [] },
    { name := "zero-columns", y := (randoms p 30 1).headD 2, cols := colsZero, gates },
    { name := "two-instance-columns", y := (randoms p 39 1).headD 2, cols := colsInst2,
      gates := instGates },
    { name := "domain-32-n-4", y := (randoms p 47 1).headD 2, cols := cols32,
      gates := gates ++ wrapGates } ]

/-! ## Service traces -/

structure Trace where
  name : String
  config : Service.Config
  ops : List Nat
  deriving Repr

/-- The configuration of the directed traces: `Service.defaultConfig` (GPU-081:
evict policy; 3 restarts in 600 s; breaker 3 failures in 600 s, cooldown 600 s). -/
def cfgDefault : Service.Config := Service.defaultConfig

def op (c a b : Nat) : Nat := c + 100 * a + 10000 * b

/-- One full GPU request: arrive, admit with `a`/`b`, finish, wipe, reply. -/
def request (a b : Nat) : List Nat := [op 1 0 0, op 2 a b, op 6 1 0, op 7 1 0, op 8 0 0]

/-- Time passes: `secs` seconds (op 11, `a + 100 * b`). -/
def tick (secs : Nat) : Nat := op 11 (secs % 100) (secs / 100)

def traces : List Trace :=
  [ { name := "ladder-gpu", config := cfgDefault, ops := request 20 20 },
    { name := "ladder-wait", config := cfgDefault, ops := request 3 14 },
    { name := "ladder-evict", config := cfgDefault, ops := request 3 3 },
    { name := "ladder-cpu", config := cfgDefault, ops := request 1 1 },
    { name := "keep-then-evict", config := { cfgDefault with keep := true },
      ops := request 20 20 ++ request 6 6 ++ [op 13 0 0] ++ request 6 6 },
    -- GPU-027: the evict step from a keep state with the key copies on the device
    { name := "keep-evict-step", config := { cfgDefault with keep := true },
      ops := request 20 20 ++ request 3 3 },
    { name := "queue-and-busy", config := cfgDefault,
      ops := [op 1 0 0, op 1 0 0, op 1 0 0, op 2 20 20, op 6 1 0, op 7 1 0, op 8 0 0,
              op 2 20 20, op 6 1 0, op 7 1 0, op 8 0 0] },
    { name := "verify-refused", config := cfgDefault,
      ops := [op 1 0 0, op 2 20 20, op 6 0 0, op 7 1 0, op 8 0 0] },
    { name := "wipe-unconfirmed", config := cfgDefault,
      ops := [op 1 0 0, op 1 0 0, op 2 20 20, op 6 1 0, op 7 0 0, op 8 0 0, op 1 0 0] },
    { name := "fault-and-readback", config := { cfgDefault with bench := true },
      ops := [op 1 0 0, op 2 20 20, op 4 0 0, op 4 1 0, op 4 2 0, op 3 5 0, op 6 1 0,
              op 7 1 0, op 8 0 0] },
    { name := "restart-limit", config := cfgDefault,
      ops := [op 9 0 0, op 10 0 0, op 11 10 0, op 9 0 0, op 10 0 0, op 11 10 0, op 9 0 0,
              op 10 0 0, op 11 10 0, op 9 0 0, op 10 0 0, op 1 0 0] },
    { name := "restart-window", config := { cfgDefault with limit := 1 },
      ops := [op 9 0 0, op 10 0 0, op 11 0 7, op 9 0 0, op 10 0 0, op 9 0 0, op 10 0 0] },
    { name := "overbound-restart", config := cfgDefault,
      ops := [op 1 0 0, op 2 20 20, op 14 0 0, op 6 1 0, op 7 1 0, op 8 0 0, op 10 0 0] },
    { name := "wsl-lease", config := { cfgDefault with wsl := true, budget := 16 },
      ops := request 0 0 ++ [op 12 1 0] ++ request 0 0 ++
             [op 1 0 0, op 2 0 0, op 5 0 0, op 6 1 0, op 7 1 0, op 8 0 0] },
    { name := "wsl-tight-budget", config := { cfgDefault with wsl := true, budget := 4 },
      ops := [op 12 1 0] ++ request 0 0 },
    { name := "no-device", config := { cfgDefault with device := false }, ops := request 20 20 },
    -- GPU-075: three failures at once open the breaker for 600 s; a restarted daemon
    -- is not contacted at 599 s and is contacted again at exactly 600 s
    { name := "breaker-open-cooldown", config := cfgDefault,
      ops := [op 9 0 0, op 1 0 0, op 1 0 0, op 1 0 0, op 10 0 0, op 1 0 0, tick 599, op 1 0 0,
              tick 1] ++ request 20 20 },
    -- GPU-075: the third failure 600 s after the first two does not open the breaker
    { name := "breaker-window-expiry", config := cfgDefault,
      ops := [op 9 0 0, op 1 0 0, op 1 0 0, tick 600, op 1 0 0, op 1 0 0, op 1 0 0, op 1 0 0] },
    -- GPU-076: a served proof clears two recorded failures; two more do not open it
    { name := "breaker-reset-on-served", config := cfgDefault,
      ops := [op 9 0 0, op 1 0 0, op 1 0 0, op 10 0 0] ++ request 20 20 ++
             [op 9 0 0, op 1 0 0, op 1 0 0, op 10 0 0, op 1 0 0] },
    -- GPU-078: acceptance mode, steps evict and cpu: a degraded error and no phase
    { name := "acceptance-evict", config := { cfgDefault with acceptance := true },
      ops := [op 1 0 0, op 2 3 3, op 6 1 0, op 8 0 0, op 1 0 0, op 2 1 1, op 8 0 0] ++
             request 20 20 },
    -- GPU-078, GPU-012: acceptance mode, a decline with a fallback reason (2 shape) during
    -- the proof: a degraded error
    { name := "acceptance-decline", config := { cfgDefault with acceptance := true },
      ops := [op 1 0 0, op 2 20 20, op 3 2 0, op 6 1 0, op 7 1 0, op 8 0 0] },
    -- GPU-085, GPU-078: acceptance mode, declines by design only (0 no-device, 1 below-min-k):
    -- counted, no fallback, not degraded; the proof is served
    { name := "expected-decline-accepted", config := { cfgDefault with acceptance := true },
      ops := [op 1 0 0, op 2 20 20, op 3 0 0, op 3 1 0, op 6 1 0, op 7 1 0, op 8 0 0] },
    -- GPU-073: each of the seven reasons once; reason 7 is refused. GPU-085, GPU-012: the
    -- reasons 0 and 1 are no fallback, the reasons 2 to 6 are one fallback each
    { name := "decline-reasons", config := cfgDefault,
      ops := [op 1 0 0, op 2 20 20] ++ (List.range 8).map (fun r => op 3 r 0) ++
             [op 6 1 0, op 7 1 0, op 8 0 0] },
    -- GPU-038, GPU-036: kinds 0 to 3 are counted, kinds 4 and 5 are refused
    { name := "readback-kinds", config := cfgDefault,
      ops := [op 1 0 0, op 2 20 20] ++ (List.range 6).map (fun k => op 4 k 0) ++
             [op 6 1 0, op 7 1 0, op 8 0 0] },
    -- GPU-082, GPU-030: under keep the tables go at the wipe, the key copies stay
    { name := "keep-tables-freed", config := { cfgDefault with keep := true },
      ops := request 20 20 ++ [op 13 0 0] },
    -- GPU-083: a container cap has no window (`window := 0`): the fourth exit, two days
    -- after the third restart, stays stopped
    { name := "container-restart-cap", config := { cfgDefault with window := 0 },
      ops := [op 9 0 0, op 10 0 0, op 9 0 0, op 10 0 0, op 9 0 0, op 10 0 0, tick 172800,
              op 9 0 0, op 10 0 0, op 1 0 0] },
    -- GPU-021, GPU-077: at 7 s a crash with one request in flight and one waiting;
    -- then a restart, a request with a read-back, a decline (memory) and its end
    { name := "crash-with-waiting", config := cfgDefault,
      ops := [tick 7, op 1 0 0, op 1 0 0, op 2 20 20, op 9 0 0, op 10 0 0, tick 5, op 1 0 0,
              op 2 20 20, op 4 3 0, op 3 4 0, op 6 1 0, op 7 1 0, op 8 0 0] },
    -- GPU-036, GPU-038: the zero-check count is read while the request is proved: a
    -- read-back of counters (kind 2) after the end of the proof and before the wipe; the
    -- other permitted kinds are not enabled there
    { name := "zero-check-count", config := cfgDefault,
      ops := [op 1 0 0, op 2 20 20, op 6 1 0, op 4 2 0, op 4 0 0, op 4 1 0, op 4 3 0, op 7 1 0,
              op 8 0 0] },
    -- GPU-081: the configuration that names nothing
    { name := "default-policy", config := Service.defaultConfig, ops := request 20 20 } ]

end GpuSpec.Vectors
