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

import Lean.Data.Json
import GpuSpec.Vectors
import GpuSpec.VectorsExt

/-!
# Oracle executable

Three modes:

* default: one `kink-implementation/1` request on stdin, one answer on stdout.
  Inputs: `{"config": Config, "ops": [op, ...]}`. The answer is
  `{"end": "final", "cells": {"s": St}}` after every operation, or
  `{"end": "could-not-apply", "reason": CODES}` with the codes of the first
  refusal (several codes sorted and joined by `|`).
* `--step`: JSON Lines. Each line `{"state": {"s": St}, "op": N}` gets
  `{"state": {"s": St}}` (the state after `Service.stepOp`), `{"refused": CODES}`
  for a decoded line that the spec refuses, or `{"error": TEXT}` for a line
  that does not decode.
* `--vectors DIR`: writes the golden vector files into DIR.

The codec holds no spec logic: refusals come from `Service.stepRefusals` and
`Service.configRefusals`, transitions from `Service.stepOp`.
-/

open Lean GpuSpec GpuSpec.Service

/-! ## Strict decoding

The decoder accepts one form of each value and refuses everything else, so a
malformed request cannot reach the spec as a different request:

* a request line is at most 64 KiB;
* numbers are integers: a fraction or an exponent is refused before parsing
  (an exponent such as `1e100000` also costs seconds to expand);
* a decimal string is canonical: `0`, or an optional `-` and digits with no
  leading zero (`"05"` and `"1_000"` are refused);
* each object has exactly the expected keys.

A decode error is reported as `error`. A request inside the format but outside
the spec's domain is a refusal, reported separately.
-/

def maxLine : Nat := 65536

/-- Refuse a fraction or an exponent in any number outside a string. -/
def integerNumbersOnly (t : String) : Except String Unit := Id.run do
  let mut inStr := false
  let mut esc := false
  let mut inNum := false
  for c in t.toList do
    if inStr then
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
    else if c == '"' then inStr := true; inNum := false
    else if c.isDigit || c == '-' then inNum := true
    else if inNum && (c == '.' || c == 'e' || c == 'E' || c == '+') then
      return .error "numbers must be integers (no fraction or exponent)"
    else inNum := false
  return .ok ()

/-! Lean 4.35 stores objects in a TreeMap and overwrites duplicate keys.
Check decoded keys before insertion. Reuse Lean's scalar and string decoders. -/
namespace StrictJson
open Std.Internal.Parsec Std.Internal.Parsec.String

mutual
  partial def value : Parser Json := do
    let c ← peek!
    if c == '{' then
      skip; ws
      if (← peek!) == '}' then
        skip; ws
        return Json.obj ∅
      return Json.obj (← object ∅)
    else if c == '[' then
      skip; ws
      if (← peek!) == ']' then
        skip; ws
        return Json.arr #[]
      return Json.arr (← array #[])
    else
      Json.Parser.anyCore

  partial def object (fields : Std.TreeMap.Raw String Json) :
      Parser (Std.TreeMap.Raw String Json) := do
    Json.Parser.lookahead (· == '"') "\""; skip
    let key ← Json.Parser.str
    if fields.contains key then fail s!"duplicate JSON key: {key}"
    ws; Json.Parser.lookahead (· == ':') ":"; skip; ws
    let item ← value
    let separator ← any
    if separator == '}' then
      ws
      return fields.insert key item
    else if separator == ',' then
      ws
      object (fields.insert key item)
    else
      fail "unexpected character in object"

  partial def array (items : Array Json) : Parser (Array Json) := do
    let item ← value
    let separator ← any
    if separator == ']' then
      ws
      return items.push item
    else if separator == ',' then
      ws
      array (items.push item)
    else
      fail "unexpected character in array"
end

def parse (text : String) : Except String Json :=
  Parser.run (do ws; let result ← value; eof; return result) text
end StrictJson

def parseLine (t : String) : Except String Json := do
  if t.utf8ByteSize > maxLine then throw s!"request longer than {maxLine} bytes"
  integerNumbersOnly t
  StrictJson.parse t

def canonicalDecimal (t : String) : Bool :=
  !t.isEmpty && t.all Char.isDigit && (t == "0" || !t.startsWith "0")

/-- A natural number field: a JSON integer, or a canonical decimal string. -/
def asNat (k : String) : Json → Except String Nat
  | .str t =>
    if !canonicalDecimal t then .error s!"{k}: not a canonical decimal natural: {t}"
    else match t.toNat? with
      | some i => .ok i
      | none => .error s!"{k}: not a decimal natural: {t}"
  | .num n =>
    if n.exponent != 0 || n.mantissa < 0 then .error s!"{k}: not a natural number"
    else .ok n.mantissa.toNat
  | v => .error s!"{k}: not a natural number: {v.compress}"

def getNat (j : Json) (k : String) : Except String Nat := do asNat k (← j.getObjVal? k)

def getBool (j : Json) (k : String) : Except String Bool := do
  match ← j.getObjVal? k with
  | .bool b => pure b
  | v => throw s!"{k}: not a boolean: {v.compress}"

def getNatList (j : Json) (k : String) : Except String (List Nat) := do
  match ← j.getObjVal? k with
  | .arr xs => xs.toList.mapM (asNat k)
  | v => throw s!"{k}: not an array: {v.compress}"

def exactKeys (j : Json) (what : String) (keys : List String) : Except String Unit := do
  let obj ← j.getObj?
  let got := (obj.toArray.map (·.1)).toList
  if got.length != keys.length || !(got.all keys.contains) then
    throw s!"{what}: keys must be exactly {keys}, got {got}"

/-! ## State codec -/

def natFields : List (String × (St → Nat)) :=
  [("perProof", St.perProof), ("resident", St.resident), ("reduced", St.reduced),
   ("budget", St.budget), ("limit", St.limit), ("window", St.window),
   ("brLimit", St.brLimit), ("brWindow", St.brWindow), ("brCooldown", St.brCooldown),
   ("phase", St.phase),
   ("waiting", St.waiting), ("step", St.step), ("admNeed", St.admNeed),
   ("admFree", St.admFree), ("fallbacks", St.fallbacks), ("clock", St.clock),
   ("requests", St.requests), ("served", St.served), ("clientCpu", St.clientCpu),
   ("errors", St.errors), ("busyReplies", St.busyReplies),
   ("degradedServed", St.degradedServed), ("readbacks", St.readbacks),
   ("badReadbacks", St.badReadbacks), ("unverifiedReturned", St.unverifiedReturned),
   ("brOpenUntil", St.brOpenUntil), ("verifyAccepts", St.verifyAccepts),
   ("declined", St.declined), ("breakerSkips", St.breakerSkips),
   ("degradedRefused", St.degradedRefused)]

def boolFields : List (String × (St → Bool)) :=
  [("keep", St.keep), ("wsl", St.wsl), ("device", St.device), ("bench", St.bench),
   ("acceptance", St.acceptance), ("up", St.up), ("stopped", St.stopped), ("onDev", St.onDev), ("tables", St.tables),
   ("dirty", St.dirty), ("ctx", St.ctx), ("devUsed", St.devUsed), ("devWork", St.devWork),
   ("degraded", St.degraded), ("leaseLost", St.leaseLost), ("overBound", St.overBound),
   ("verifyOk", St.verifyOk), ("wipeOk", St.wipeOk), ("lockHeld", St.lockHeld),
   ("cold", St.cold), ("runFailed", St.runFailed)]

def listFields : List (String × (St → List Nat)) :=
  [("restartTimes", St.restartTimes), ("brFails", St.brFails), ("declines", St.declines)]

def stKeys : List String :=
  natFields.map (·.1) ++ boolFields.map (·.1) ++ listFields.map (·.1)

def stJson (s : St) : Json :=
  Json.mkObj ((natFields.map fun (k, f) => (k, toJson (f s))) ++
    (boolFields.map fun (k, f) => (k, toJson (f s))) ++
    (listFields.map fun (k, f) => (k, toJson (f s))))

def stOfJson (j : Json) : Except String St := do
  exactKeys j "state.s" stKeys
  let n := getNat j
  let b := getBool j
  let l := getNatList j
  pure { perProof := ← n "perProof", resident := ← n "resident", reduced := ← n "reduced",
         budget := ← n "budget", keep := ← b "keep", wsl := ← b "wsl", device := ← b "device",
         limit := ← n "limit", window := ← n "window", bench := ← b "bench",
         acceptance := ← b "acceptance", brLimit := ← n "brLimit", brWindow := ← n "brWindow",
         brCooldown := ← n "brCooldown",
         up := ← b "up", stopped := ← b "stopped", phase := ← n "phase",
         waiting := ← n "waiting", onDev := ← b "onDev", tables := ← b "tables",
         dirty := ← b "dirty", ctx := ← b "ctx", devUsed := ← b "devUsed",
         devWork := ← b "devWork", step := ← n "step", admNeed := ← n "admNeed",
         admFree := ← n "admFree", fallbacks := ← n "fallbacks", degraded := ← b "degraded",
         leaseLost := ← b "leaseLost", overBound := ← b "overBound",
         verifyOk := ← b "verifyOk", wipeOk := ← b "wipeOk", lockHeld := ← b "lockHeld",
         cold := ← b "cold", clock := ← n "clock", restartTimes := ← l "restartTimes",
         brFails := ← l "brFails", brOpenUntil := ← n "brOpenUntil",
         requests := ← n "requests", served := ← n "served", clientCpu := ← n "clientCpu",
         errors := ← n "errors", busyReplies := ← n "busyReplies",
         degradedServed := ← n "degradedServed", readbacks := ← n "readbacks",
         badReadbacks := ← n "badReadbacks", unverifiedReturned := ← n "unverifiedReturned",
         verifyAccepts := ← n "verifyAccepts", declines := ← l "declines",
         declined := ← n "declined", breakerSkips := ← n "breakerSkips",
         degradedRefused := ← n "degradedRefused",
         runFailed := ← b "runFailed" }

def wrapSt (s : St) : Json := Json.mkObj [("s", stJson s)]

def unwrapSt (j : Json) : Except String St := do
  exactKeys j "state" ["s"]
  stOfJson (← j.getObjVal? "s")

def configKeys : List String :=
  ["perProof", "resident", "reduced", "budget", "keep", "wsl", "device", "limit", "window", "bench",
   "acceptance", "brLimit", "brWindow", "brCooldown"]

def configOfJson (j : Json) : Except String Config := do
  exactKeys j "config" configKeys
  let n := getNat j
  let b := getBool j
  pure { perProof := ← n "perProof", resident := ← n "resident", reduced := ← n "reduced",
         budget := ← n "budget", keep := ← b "keep", wsl := ← b "wsl", device := ← b "device",
         limit := ← n "limit", window := ← n "window", bench := ← b "bench",
         acceptance := ← b "acceptance", brLimit := ← n "brLimit", brWindow := ← n "brWindow",
         brCooldown := ← n "brCooldown" }

def configJson (c : Config) : Json :=
  Json.mkObj [("perProof", toJson c.perProof), ("resident", toJson c.resident),
    ("reduced", toJson c.reduced), ("budget", toJson c.budget), ("keep", toJson c.keep),
    ("wsl", toJson c.wsl), ("device", toJson c.device), ("limit", toJson c.limit),
    ("window", toJson c.window), ("bench", toJson c.bench),
    ("acceptance", toJson c.acceptance), ("brLimit", toJson c.brLimit),
    ("brWindow", toJson c.brWindow), ("brCooldown", toJson c.brCooldown)]

def codes (rs : List Refusal) : List String := (rs.map Refusal.code).mergeSort (· ≤ ·)

def reason (rs : List Refusal) : String := "|".intercalate (codes rs)

/-! ## Default mode -/

/-- Run the operations; stop at the first refusal. -/
def runChecked (s : St) : List Nat → Except (List Refusal) St
  | [] => .ok s
  | op :: ops =>
    match stepRefusals s op with
    | [] => runChecked (stepOp s op) ops
    | rs => .error rs

def answer (req : Json) : Except String Json := do
  exactKeys req "request" ["protocol", "inputs"]
  let proto ← req.getObjValAs? String "protocol"
  if proto != "kink-implementation/1" then throw s!"unsupported protocol {proto}"
  let inputs ← req.getObjVal? "inputs"
  exactKeys inputs "inputs" ["config", "ops"]
  let c ← configOfJson (← inputs.getObjVal? "config")
  let ops ← getNatList inputs "ops"
  match configRefusals c with
  | [] =>
    match runChecked (init c) ops with
    | .ok s => return Json.mkObj [("end", "final"), ("cells", wrapSt s)]
    | .error rs => return Json.mkObj [("end", "could-not-apply"), ("reason", reason rs)]
  | rs => return Json.mkObj [("end", "could-not-apply"), ("reason", reason rs)]

/-! ## Step mode -/

def stepAnswer (line : String) : Json :=
  match (do
      let j ← parseLine line
      exactKeys j "request" ["state", "op"]
      let s ← unwrapSt (← j.getObjVal? "state")
      let op ← getNat j "op"
      pure (s, op)) with
  | .error e => Json.mkObj [("error", toJson e)]
  | .ok (s, op) =>
    match stepRefusals s op with
    | [] => Json.mkObj [("state", wrapSt (stepOp s op))]
    | rs => Json.mkObj [("refused", toJson (codes rs))]

partial def stepLoop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  if line.trimAscii.isEmpty then return (← stepLoop stdin stdout)
  stdout.putStrLn (stepAnswer line).compress
  stdout.flush
  stepLoop stdin stdout

/-! ## Vector export -/

/-- Field elements go out as canonical decimal strings (they exceed 64 bits). -/
def fe (x : Nat) : Json := Json.str (toString x)
def feList (xs : List Nat) : Json := Json.arr (xs.map fe).toArray

def field : Json :=
  Json.mkObj [("name", "bls12-381-fr"), ("modulus", fe blsR), ("generator", fe blsGen)]

/-- The format tag of the arithmetic vector files (vectors/README.md). -/
def vectorFormat : String := "midnight-gpu-vectors/2"

/-- The top level of an arithmetic vector file: `format`, `kind`, `field`, then `rest`. -/
def vectorFile (kind : String) (rest : List (String × Json)) : Json :=
  Json.mkObj
    ([("format", Json.str vectorFormat), ("kind", Json.str kind), ("field", field)] ++ rest)

def reasonJson (r : Reason) : Json := Json.str r.code

/-- `expect`, `min_k`, and `reason` on a decline. -/
def expectFields (e : Vectors.Expect) : List (String × Json) :=
  [("expect", Json.str e.word), ("min_k", toJson e.minK)] ++
  match e.decision with
  | some r => [("reason", reasonJson r)]
  | none => []

/-- `expect` and, on a decline, `reason`, for a decision under a stated `min_k`. `yes` is
the word for "the kernel runs". -/
def decisionFields (yes : String) (d : Option Reason) : List (String × Json) :=
  match d with
  | some r => [("expect", Json.str "decline"), ("reason", reasonJson r)]
  | none => [("expect", Json.str yes)]

/-! The file builders take `Unit` and are compiled without closed-term extraction: a
constant of type `Json` (or an extracted closed subterm) is computed when the process
starts, in every mode, so `--step` and the default mode would pay for the vectors. -/
section VectorFiles
set_option compiler.extract_closed false

def nttJson (_ : Unit) : Json :=
  vectorFile "ntt" [("cases", Json.arr (Vectors.nttAll.map fun c =>
    Json.mkObj ([("name", Json.str c.name), ("log_n", toJson c.logN), ("omega", fe c.omega),
      ("input", feList c.input), ("ntt", feList (Vectors.nttRef c)),
      ("intt", feList (Vectors.inttRef c))] ++ expectFields (Vectors.nttExpect c))).toArray)]

def cosetJson (_ : Unit) : Json :=
  vectorFile "coset" [("cases", Json.arr (Vectors.cosetCases.map fun c =>
    let ext := cosetExt blsR c.zeta c.omegaExt c.ext c.input
    Json.mkObj ([("name", Json.str c.name), ("log_n", toJson c.logN), ("ext", toJson c.ext),
      ("zeta", fe c.zeta), ("omega_ext", fe c.omegaExt), ("coeffs", feList c.input),
      ("extended", feList ext),
      ("back_to_coeffs", feList (cosetToCoeff blsR c.zeta c.omegaExt c.input.length ext)),
      ("shift", Json.str c.shift)] ++ expectFields (Vectors.cosetExpect c))).toArray)]

def msmJson (_ : Unit) : Json :=
  vectorFile "msm" [
    ("group", "toy: Z_r under addition; base i is the discrete log of a G1 point"),
    ("cases", Json.arr (Vectors.msmAll.map fun c =>
      Json.mkObj ([("name", Json.str c.name), ("scalars", feList c.scalars),
        ("bases", feList c.bases), ("result", fe (msm blsR c.scalars c.bases)),
        ("mask", feList c.mask), ("masked_scalars", feList (maskScalars blsR c.scalars c.mask)),
        ("mask_result", fe (msm blsR c.mask c.bases))] ++
        expectFields (Vectors.msmExpect c))).toArray)]

partial def exprJson : GpuSpec.Expr → Json
  | .const c => Json.mkObj [("node", "constant"), ("value", fe c)]
  | .fixed c r => Json.mkObj [("node", "fixed"), ("column", toJson c), ("rotation", toJson r)]
  | .advice c r => Json.mkObj [("node", "advice"), ("column", toJson c), ("rotation", toJson r)]
  | .inst c r => Json.mkObj [("node", "instance"), ("column", toJson c), ("rotation", toJson r)]
  | .challenge i => Json.mkObj [("node", "challenge"), ("index", toJson i)]
  | .neg e => Json.mkObj [("node", "negated"), ("arg", exprJson e)]
  | .sum a b => Json.mkObj [("node", "sum"), ("left", exprJson a), ("right", exprJson b)]
  | .prod a b => Json.mkObj [("node", "product"), ("left", exprJson a), ("right", exprJson b)]
  | .scaled e c => Json.mkObj [("node", "scaled"), ("arg", exprJson e), ("scalar", fe c)]

def quotientJson (_ : Unit) : Json :=
  vectorFile "quotient-numerator" [("cases", Json.arr (Vectors.quotientCases.map fun c =>
    Json.mkObj [("name", c.name), ("y", fe c.y), ("extended_size", toJson c.cols.size),
      ("ratio", toJson c.cols.ratio),
      ("fixed", Json.arr (c.cols.fixed.map feList).toArray),
      ("advice", Json.arr (c.cols.advice.map feList).toArray),
      ("instance", Json.arr (c.cols.inst.map feList).toArray),
      ("challenges", feList c.cols.challenges),
      ("gates", Json.arr (c.gates.map exprJson).toArray),
      ("numerator", feList (numerator blsR c.y c.cols c.gates)),
      ("n", toJson c.n), ("zeta", fe c.zeta), ("omega_ext", fe c.omegaExt),
      ("quotient_coeffs", feList c.coeffs)]).toArray)]

def gateJson (_ : Unit) : Json :=
  vectorFile "gate" [("cases", Json.arr (Vectors.gateCases.map fun c =>
    Json.mkObj ([("op", Json.str (Vectors.opName c.op)), ("len", toJson c.len),
      ("min_k", toJson c.minK), ("max_log", toJson c.maxLog), ("device", toJson c.device),
      ("reduced", toJson c.reduced)] ++ decisionFields "run" c.decision)).toArray)]

def thresholdJson (_ : Unit) : Json :=
  vectorFile "threshold" [
    ("msm", Json.arr (Vectors.thresholdMsmCases.map fun c =>
      Json.mkObj ([("name", Json.str c.name), ("n", toJson c.n),
        ("scalars_seed", toJson c.scalarsSeed), ("bases_seed", toJson c.basesSeed),
        ("result", fe c.result)] ++ decisionFields "value" c.decision)).toArray),
    ("ntt", Json.arr (Vectors.thresholdNttCases.map fun c =>
      let out := Vectors.thresholdNttOut c
      Json.mkObj ([("name", Json.str c.name), ("log_n", toJson c.logN), ("omega", fe c.omega),
        ("input_seed", toJson c.inputSeed), ("digest", fe (Vectors.digest blsR out)),
        ("first", feList (out.take 4)), ("last", feList (out.drop (out.length - 4)))] ++
        decisionFields "value" c.decision)).toArray)]

/-- A kind with its read-back code of the service op 4 (`null`: the op has no code for it). -/
def kindJson (k : DataMove.VecKind) : Json :=
  Json.mkObj [("kind", Json.str (Vectors.kindName k)),
    ("code", match DataMove.copyCode k with
      | some c => toJson c
      | none => Json.null)]

def kindNames (ks : List DataMove.VecKind) : Json :=
  Json.arr (ks.map fun k => Json.str (Vectors.kindName k)).toArray

def datamoveJson (_ : Unit) : Json :=
  vectorFile "datamove" [
    ("permitted", Json.arr (Vectors.permittedKinds.map kindJson).toArray),
    ("forbidden", Json.arr (Vectors.forbiddenKinds.map kindJson).toArray),
    ("plans", Json.arr (Vectors.plans.map fun p =>
      Json.mkObj [("name", Json.str p.name), ("executable", toJson p.executable),
        ("gpu038", toJson p.gpu038), ("trace", kindNames p.trace),
        ("offending", kindNames p.offending)]).toArray)]

end VectorFiles

def traceJson (t : Vectors.Trace) : Json :=
  let states := (t.ops.foldl (fun (acc : List St) o => stepOp (acc.headD (init t.config)) o :: acc)
    [init t.config]).reverse
  let refused := t.ops.zip (states.take t.ops.length) |>.map fun (o, s) => codes (stepRefusals s o)
  Json.mkObj [("format", "midnight-gpu-vectors/2"), ("kind", "service-trace"),
    ("name", t.name), ("config", configJson t.config), ("ops", toJson t.ops),
    ("refused", toJson refused),
    ("states", Json.arr (states.map stJson).toArray)]

def writeJson (path : System.FilePath) (j : Json) : IO Unit :=
  IO.FS.writeFile path (j.pretty 100 ++ "\n")

def exportVectors (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (dir / "service")
  writeJson (dir / "ntt.json") (nttJson ())
  writeJson (dir / "coset.json") (cosetJson ())
  writeJson (dir / "msm.json") (msmJson ())
  writeJson (dir / "quotient.json") (quotientJson ())
  writeJson (dir / "gate.json") (gateJson ())
  writeJson (dir / "threshold.json") (thresholdJson ())
  writeJson (dir / "datamove.json") (datamoveJson ())
  for t in Vectors.traces do
    writeJson (dir / "service" / s!"{t.name}.json") (traceJson t)

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  match args with
  | ["--step"] => stepLoop stdin stdout; return 0
  | ["--vectors", dir] => exportVectors dir; return 0
  | [] =>
    let input ← stdin.readToEnd
    match parseLine input >>= answer with
    | .ok out => stdout.putStrLn out.compress; return 0
    | .error e => IO.eprintln s!"oracle: {e}"; return 2
  | _ => IO.eprintln "usage: oracle [--step | --vectors DIR]"; return 2
