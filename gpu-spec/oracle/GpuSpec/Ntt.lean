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
# NTT, inverse NTT and coset transforms

Reference definitions are the transform formulas, evaluated term by term
(quadratic time). The device model is a radix-2 Cooley-Tukey FFT, the
algorithm class the GPU kernels run. GPU-007 asks the device to return the
reference value or decline; `Tests.lean` checks the FFT against the formulas.

Conventions (the golden vectors state every parameter they use):
* `ntt p ω a` : `out[k] = Σ_j a[j] ω^(j k)`.
* `intt p ω a` : `out[k] = n⁻¹ Σ_j a[j] ω^(-j k)`.
* `cosetExt p ζ ωe ext a` (coefficients to the extended coset): `a` has `n`
  coefficients; the result has `n * ext` values `out[k] = Σ_i a[i] (ζ ωe^k)^i`.
* `cosetToCoeff p ζ ωe n v` (extended coset to coefficients): the inverse,
  truncated to `n` coefficients.
-/

namespace GpuSpec

/-- The reference forward transform. -/
def ntt (p ω : Nat) (a : List Nat) : List Nat :=
  (List.range a.length).map fun k =>
    sumM p ((List.range a.length).zip a |>.map fun (j, aj) => mulM p aj (powM p ω (j * k)))

/-- The reference inverse transform. -/
def intt (p ω : Nat) (a : List Nat) : List Nat :=
  let n := a.length
  let ninv := invM p (n % p)
  (ntt p (invM p ω) a).map (mulM p ninv)

/-- Evaluate a polynomial (coefficients, lowest first) at `x`. -/
def evalPoly (p : Nat) (a : List Nat) (x : Nat) : Nat :=
  a.foldr (fun c acc => addM p c (mulM p acc x)) 0

/-- The reference coefficient-to-extended-coset transform. -/
def cosetExt (p ζ ωe ext : Nat) (a : List Nat) : List Nat :=
  (List.range (a.length * ext)).map fun k => evalPoly p a (mulM p ζ (powM p ωe k))

/-- The reference extended-coset-to-coefficient transform, truncated to `n`. -/
def cosetToCoeff (p ζ ωe n : Nat) (v : List Nat) : List Nat :=
  let c := intt p ωe v
  let zinv := invM p ζ
  ((List.range v.length).zip c |>.map fun (i, ci) => mulM p ci (powM p zinv i)).take n

/-! ## Device model: radix-2 FFT -/

def evens : List Nat → List Nat
  | a :: _ :: t => a :: evens t
  | [a] => [a]
  | [] => []

def odds : List Nat → List Nat
  | _ :: b :: t => b :: odds t
  | _ => []

/-- Recursive radix-2 FFT with `fuel` levels (`fuel = log2 n`). -/
def fftAux (p : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, a => a.map (· % p)
  | fuel + 1, ω, a =>
    if a.length ≤ 1 then a.map (· % p)
    else
      let w2 := mulM p ω ω
      let e := fftAux p fuel w2 (evens a)
      let o := fftAux p fuel w2 (odds a)
      let half := a.length / 2
      let tw := (List.range half).zip o |>.map fun (k, ok) => mulM p (powM p ω k) ok
      let lo := (e.zip tw).map fun (x, t) => addM p x t
      let hi := (e.zip tw).map fun (x, t) => subM p x t
      lo ++ hi

def log2 (n : Nat) : Nat := Nat.log2 n

/-- The device forward transform (radix-2; `a.length` a power of two). -/
def fft (p ω : Nat) (a : List Nat) : List Nat := fftAux p (log2 a.length) ω a

def ifft (p ω : Nat) (a : List Nat) : List Nat :=
  let ninv := invM p (a.length % p)
  (fft p (invM p ω) a).map (mulM p ninv)

/-- The device coset transform: scale by `ζ^i`, zero-pad, FFT. -/
def fftCosetExt (p ζ ωe ext : Nat) (a : List Nat) : List Nat :=
  let scaled := (List.range a.length).zip a |>.map fun (i, ai) => mulM p ai (powM p ζ i)
  fft p ωe (scaled ++ List.replicate (a.length * ext - a.length) 0)

/-- The device inverse coset transform. -/
def fftCosetToCoeff (p ζ ωe n : Nat) (v : List Nat) : List Nat :=
  let c := ifft p ωe v
  let zinv := invM p ζ
  ((List.range v.length).zip c |>.map fun (i, ci) => mulM p ci (powM p zinv i)).take n

/-- A size the device kernels take: a power of two from 2 to 2^maxLog
(GPU-010: anything else is declined before any buffer changes). -/
def deviceSize (maxLog n : Nat) : Bool := 2 ≤ n && n ≤ 2 ^ maxLog && n &&& (n - 1) == 0

end GpuSpec
