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
# Quotient numerator

The quotient numerator of a halo2-style prover is, at every point of the
extended domain, `Σ_j y^(m-1-j) · gate_j(row)`, where each gate is an
expression over fixed, advice and instance columns at rotations, challenges and
constants. The CPU evaluates the expression tree. The device evaluates a
compiled straight-line program (a stack machine here; a register graph on the
GPU). GPU-007 asks the device to return the CPU value; `compile_correct`
proves that the compiled program computes the tree's value for every
expression, every row and every column assignment.

The expression node types are those of halo2's `Expression`: constant,
fixed, advice, instance, challenge, negation, sum, product, scaled.
-/

namespace GpuSpec

inductive Expr where
  | const (c : Nat)
  | fixed (col : Nat) (rot : Int)
  | advice (col : Nat) (rot : Int)
  | inst (col : Nat) (rot : Int)
  | challenge (i : Nat)
  | neg (e : Expr)
  | sum (a b : Expr)
  | prod (a b : Expr)
  | scaled (e : Expr) (c : Nat)
  deriving Repr, DecidableEq

/-- Column values on the extended domain and the challenges. `ratio` is the
extension factor: a rotation by `rot` rows is a shift by `rot * ratio` points. -/
structure Columns where
  fixed : List (List Nat)
  advice : List (List Nat)
  inst : List (List Nat)
  challenges : List Nat
  size : Nat
  ratio : Nat
  deriving Repr

/-- The extended-domain index of row `i` rotated by `rot`. -/
def rotIndex (cs : Columns) (i : Nat) (rot : Int) : Nat :=
  if cs.size = 0 then 0 else (((i : Int) + rot * (cs.ratio : Int)) % (cs.size : Int)).toNat

def colAt (cols : List (List Nat)) (c i : Nat) : Nat := (cols.getD c []).getD i 0

/-- The reference: evaluate the tree at extended-domain point `i`. -/
def evalE (p : Nat) (cs : Columns) (i : Nat) : Expr → Nat
  | .const c => c % p
  | .fixed c r => colAt cs.fixed c (rotIndex cs i r) % p
  | .advice c r => colAt cs.advice c (rotIndex cs i r) % p
  | .inst c r => colAt cs.inst c (rotIndex cs i r) % p
  | .challenge k => cs.challenges.getD k 0 % p
  | .neg e => negM p (evalE p cs i e)
  | .sum a b => addM p (evalE p cs i a) (evalE p cs i b)
  | .prod a b => mulM p (evalE p cs i a) (evalE p cs i b)
  | .scaled e c => mulM p (evalE p cs i e) c

/-! ## Device model: compiled straight-line program -/

inductive Instr where
  | push (e : Expr)   -- a leaf: constant, column read or challenge
  | neg
  | add
  | mul
  | scale (c : Nat)
  deriving Repr, DecidableEq

def compile : Expr → List Instr
  | .neg e => compile e ++ [.neg]
  | .sum a b => compile a ++ compile b ++ [.add]
  | .prod a b => compile a ++ compile b ++ [.mul]
  | .scaled e c => compile e ++ [.scale c]
  | leaf => [.push leaf]

def exec1 (p : Nat) (cs : Columns) (i : Nat) (st : List Nat) : Instr → List Nat
  | .push e => evalE p cs i e :: st
  | .neg => match st with
    | a :: r => negM p a :: r
    | [] => []
  | .add => match st with
    | b :: a :: r => addM p a b :: r
    | _ => []
  | .mul => match st with
    | b :: a :: r => mulM p a b :: r
    | _ => []
  | .scale c => match st with
    | a :: r => mulM p a c :: r
    | [] => []

def exec (p : Nat) (cs : Columns) (i : Nat) (prog : List Instr) (st : List Nat) : List Nat :=
  prog.foldl (exec1 p cs i) st

theorem exec_append (p : Nat) (cs : Columns) (i : Nat) (xs ys : List Instr) (st : List Nat) :
    exec p cs i (xs ++ ys) st = exec p cs i ys (exec p cs i xs st) := by
  simp [exec, List.foldl_append]

/-- GPU-007 (quotient): the compiled program computes the tree's value, for every
expression, every point and every column assignment. -/
theorem compile_correct (p : Nat) (cs : Columns) (i : Nat) :
    ∀ (e : Expr) (st : List Nat), exec p cs i (compile e) st = evalE p cs i e :: st
  | .const _, _ => rfl
  | .fixed _ _, _ => rfl
  | .advice _ _, _ => rfl
  | .inst _ _, _ => rfl
  | .challenge _, _ => rfl
  | .neg e, st => by
    simp only [compile, exec_append, compile_correct p cs i e]; rfl
  | .sum a b, st => by
    simp only [compile, exec_append, compile_correct p cs i a, compile_correct p cs i b]; rfl
  | .prod a b, st => by
    simp only [compile, exec_append, compile_correct p cs i a, compile_correct p cs i b]; rfl
  | .scaled e c, st => by
    simp only [compile, exec_append, compile_correct p cs i e]; rfl

/-- The reference numerator at point `i`: Horner in `y` over the gates. -/
def numeratorAt (p y : Nat) (cs : Columns) (gates : List Expr) (i : Nat) : Nat :=
  gates.foldl (fun acc g => addM p (mulM p acc y) (evalE p cs i g)) 0

/-- The device numerator at point `i`: the same fold over compiled programs. -/
def deviceNumeratorAt (p y : Nat) (cs : Columns) (progs : List (List Instr)) (i : Nat) : Nat :=
  progs.foldl (fun acc pr => addM p (mulM p acc y) ((exec p cs i pr []).headD 0)) 0

def numerator (p y : Nat) (cs : Columns) (gates : List Expr) : List Nat :=
  (List.range cs.size).map (numeratorAt p y cs gates)

def deviceNumerator (p y : Nat) (cs : Columns) (gates : List Expr) : List Nat :=
  (List.range cs.size).map (deviceNumeratorAt p y cs (gates.map compile))

/-- GPU-007 (quotient): the device numerator equals the reference numerator on
every point of the extended domain. -/
theorem deviceNumerator_eq (p y : Nat) (cs : Columns) (gates : List Expr) :
    deviceNumerator p y cs gates = numerator p y cs gates := by
  unfold deviceNumerator numerator
  congr 1
  funext i
  unfold deviceNumeratorAt numeratorAt
  rw [List.foldl_map]
  congr 1
  funext acc g
  rw [compile_correct]
  rfl

/-! ## Quotient coefficients

The optional quotient-coefficients hook returns `h = numerator / Z_H` in
coefficient form, where `Z_H(X) = X^n - 1`. The reference divides at every
extended coset point and applies the inverse coset transform. -/

def quotientCoeffs (p ζ ωe n : Nat) (num : List Nat) : List Nat :=
  let pts := (List.range num.length).map fun k => mulM p ζ (powM p ωe k)
  let divided := (num.zip pts).map fun (v, x) => mulM p v (invM p (subM p (powM p x n) 1))
  cosetToCoeff p ζ ωe num.length divided

/-! ## Tiled evaluation (GPU-079)

The device may evaluate the extended domain in tiles of `t` points: tile `j`
covers the indices `j·t .. min((j+1)·t, N) - 1`, so the last tile is shorter
when `t` does not divide `N`. Each tile is evaluated on its own and the tile
outputs are concatenated in order. A point of a tile is evaluated with
`numeratorAt` at its index in the whole domain: a column read with a rotation
reads index `(i + rot · ratio) mod N` of the whole column, never an index
inside the tile. GPU-079 asks that the result does not depend on `t`.

`t = 0` is not a tile size. The tile loop below then has no tile
(`(N + 0 - 1) / 0 = 0` in Lean) and returns `[]` (`tiledEval_zero`); it does
not loop. The theorems need `0 < t`. -/

/-- The start index of every tile: `0, t, 2t, …`, `⌈n / t⌉` of them. -/
def tileStarts (n t : Nat) : List Nat := (List.range ((n + t - 1) / t)).map (· * t)

/-- One tile: `f` at the indices `s .. min (s + t, n) - 1`. -/
def evalTile (f : Nat → Nat) (n t s : Nat) : List Nat := (List.range' s (min t (n - s))).map f

/-- The tile loop: evaluate tile after tile, append each tile's output. -/
def tiledEval (f : Nat → Nat) (n t : Nat) : List Nat :=
  (tileStarts n t).foldl (fun out s => out ++ evalTile f n t s) []

/-- The reference numerator, evaluated tile by tile (tile size `t`). -/
def numeratorTiled (p y : Nat) (cs : Columns) (gates : List Expr) (t : Nat) : List Nat :=
  tiledEval (numeratorAt p y cs gates) cs.size t

/-- The device numerator (compiled programs), evaluated tile by tile. -/
def deviceNumeratorTiled (p y : Nat) (cs : Columns) (gates : List Expr) (t : Nat) : List Nat :=
  tiledEval (deviceNumeratorAt p y cs (gates.map compile)) cs.size t

/-- After `k` tiles the loop holds the first `min (k·t) n` points. -/
theorem tiledEval_prefix (f : Nat → Nat) (n t k : Nat) :
    ((List.range k).map (· * t)).foldl (fun out s => out ++ evalTile f n t s) [] =
      (List.range (min (k * t) n)).map f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, evalTile]
    rw [← List.map_append]
    congr 1
    rw [List.range_eq_range', List.range_eq_range']
    have hs : (k + 1) * t = k * t + t := Nat.succ_mul k t
    by_cases h : k * t ≤ n
    · have h1 : min (k * t) n = k * t := Nat.min_eq_left h
      have h2 : min ((k + 1) * t) n = k * t + min t (n - k * t) := by omega
      rw [h1, h2, ← List.range'_append_1, Nat.zero_add]
    · have h1 : min (k * t) n = n := by omega
      have h2 : min ((k + 1) * t) n = n := by omega
      have h3 : min t (n - k * t) = 0 := by omega
      rw [h1, h2, h3]; simp

/-- The tiles cover the domain: `⌈n / t⌉ · t ≥ n`. -/
theorem tiles_cover (n t : Nat) (ht : 0 < t) : n ≤ (n + t - 1) / t * t := by
  have h1 := Nat.div_add_mod (n + t - 1) t
  have h2 := Nat.mod_lt (n + t - 1) ht
  have h3 : t * ((n + t - 1) / t) = (n + t - 1) / t * t := Nat.mul_comm _ _
  omega

/-- Tiling changes nothing, for every function, every domain size (0, sizes
that `t` does not divide, sizes below `t`) and every tile size `t ≥ 1`. -/
theorem tiledEval_eq (f : Nat → Nat) (n t : Nat) (ht : 0 < t) :
    tiledEval f n t = (List.range n).map f := by
  unfold tiledEval tileStarts
  rw [tiledEval_prefix, Nat.min_eq_right (tiles_cover n t ht)]

/-- `t = 0`: the loop has no tile and returns the empty list. -/
theorem tiledEval_zero (f : Nat → Nat) (n : Nat) : tiledEval f n 0 = [] := by
  simp [tiledEval, tileStarts]

/-- GPU-079: the tiled reference numerator is the untiled one, for every tile size. -/
theorem numeratorTiled_eq (p y : Nat) (cs : Columns) (gates : List Expr) :
    ∀ t, 0 < t → numeratorTiled p y cs gates t = numerator p y cs gates :=
  fun t ht => tiledEval_eq _ _ t ht

/-- GPU-079, GPU-007: the tiled device numerator is the untiled reference numerator. -/
theorem deviceNumeratorTiled_eq (p y : Nat) (cs : Columns) (gates : List Expr) (t : Nat)
    (ht : 0 < t) : deviceNumeratorTiled p y cs gates t = numerator p y cs gates := by
  rw [← deviceNumerator_eq]
  exact tiledEval_eq _ _ t ht

/-- `t = 0` gives `[]` for both, whatever the domain: not the numerator when `cs.size > 0`. -/
theorem numeratorTiled_zero (p y : Nat) (cs : Columns) (gates : List Expr) :
    numeratorTiled p y cs gates 0 = [] ∧ deviceNumeratorTiled p y cs gates 0 = [] :=
  ⟨tiledEval_zero _ _, tiledEval_zero _ _⟩

/-- Rotation across tile borders: the value the tiled device kernel returns at
point `i` is the untiled reference value at `i`, whose column reads go to
`rotIndex cs i rot` in the whole domain. This holds for the last point of a
tile and the last point of the domain like for any other point. -/
theorem deviceNumeratorTiled_point (p y : Nat) (cs : Columns) (gates : List Expr) (t i : Nat)
    (ht : 0 < t) (hi : i < cs.size) :
    (deviceNumeratorTiled p y cs gates t)[i]? = some (numeratorAt p y cs gates i) ∧
    (numeratorTiled p y cs gates t)[i]? = some (numeratorAt p y cs gates i) := by
  rw [deviceNumeratorTiled_eq p y cs gates t ht, numeratorTiled_eq p y cs gates t ht]
  simp [numerator, hi]

/-- GPU-079: the quotient coefficients over the tiled device numerator (and over
the tiled reference numerator) are those of the untiled evaluation. -/
theorem quotientCoeffs_tiled (p ζ ωe n y : Nat) (cs : Columns) (gates : List Expr) (t : Nat)
    (ht : 0 < t) :
    quotientCoeffs p ζ ωe n (deviceNumeratorTiled p y cs gates t) =
      quotientCoeffs p ζ ωe n (numerator p y cs gates) ∧
    quotientCoeffs p ζ ωe n (numeratorTiled p y cs gates t) =
      quotientCoeffs p ζ ωe n (numerator p y cs gates) := by
  rw [deviceNumeratorTiled_eq p y cs gates t ht, numeratorTiled_eq p y cs gates t ht]
  exact ⟨rfl, rfl⟩

end GpuSpec
