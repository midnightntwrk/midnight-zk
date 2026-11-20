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
# Prime field arithmetic

Elements are natural numbers below the modulus `p`. Every operation reduces
its result. The oracle uses two moduli: small primes for exhaustive checks and
the BLS12-381 scalar field modulus `r` for the golden vectors.
-/

namespace GpuSpec

/-- The BLS12-381 scalar field modulus (the field of midnight-proofs' `Fq`). -/
def blsR : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The multiplicative generator that halo2-style code uses for BLS12-381 Fr. -/
def blsGen : Nat := 7

/-- The 2-adicity of `blsR - 1`. -/
def blsTwoAdicity : Nat := 32

def addM (p a b : Nat) : Nat := (a + b) % p
def subM (p a b : Nat) : Nat := (a % p + p - b % p) % p
def mulM (p a b : Nat) : Nat := (a * b) % p
def negM (p a : Nat) : Nat := subM p 0 a

/-- Square and multiply. `e` halves at every call. -/
def powM (p b e : Nat) : Nat :=
  if h : e = 0 then 1 % p
  else
    let half := powM p b (e / 2)
    let sq := mulM p half half
    if e % 2 = 1 then mulM p sq b else sq
termination_by e
decreasing_by omega

/-- Inverse by Fermat's little theorem (`p` prime, `a ≠ 0`). -/
def invM (p a : Nat) : Nat := powM p a (p - 2)

/-- A primitive `n`-th root of unity from a generator `g` of the multiplicative
group, for `n` dividing `p - 1`. -/
def rootOfUnity (p g n : Nat) : Nat := powM p g ((p - 1) / n)

/-- Sum of a list in the field. -/
def sumM (p : Nat) (xs : List Nat) : Nat := xs.foldl (addM p) 0

end GpuSpec
