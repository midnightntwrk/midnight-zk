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
# Data movement between host and device (GPU-038, GPU-036, GPU-084)

A small-step machine over named buffers. A buffer has a kind and a set of
locations (host, device) that hold it. A plan is a list of steps; a step whose
precondition fails stops the plan (`exec` gives `none`). Every device-to-host
copy that runs is appended to a trace with the kind of the copied buffer.

GPU-038 is a predicate on that trace: every copied kind is permitted. The
ruling of 2026-11-17 adds "the partial bucket sums of the vendored MSM" to the
permitted set and adds GPU-084: the host copy of those sums is zeroed before
its memory is released. Erasure is observable in the machine: a host copy has a
`zeroed` flag, set by `zeroHost` and by nothing else; `free b host` releases the
memory and does not zero it. `Gpu084` asks that every release of a host copy of
bucket sums finds it zeroed, and that no un-zeroed copy is left at the end.

Kinds are derived, not declared. A step that creates a buffer names an
operation from a closed list (`DevOp` on the device, `HostOp` on the host). The
kind of the new buffer is `DevOp.out` / `HostOp.out` of the operation and the
kinds of its inputs, and a step whose input kinds the operation does not take
cannot run. So a plan cannot label an extended vector `baseTransform`
(`kind_determined`, `extended_only_from`, `mislabel_impossible`). The one
declaration left is the kind of the buffers the host holds at the start
(`init`): they are uploads from the host, made by no step of the plan.

Limits of the model. The plans below are written from the prose description of
the port, not extracted from the code, and the operation of each step is the
plan author's reading of that description.
-/

namespace GpuSpec.DataMove

inductive Loc where
  | host | device
  deriving Repr, DecidableEq

inductive VecKind where
  | scalars          -- MSM scalars
  | bases            -- MSM bases (the SRS slice)
  | baseCoeffs       -- a base-domain vector, 2^k values
  | baseTransform    -- the output of a base-domain fft or ifft
  | extended         -- any vector of 2^ext_k values on the extended domain
  | quotientCoeffs   -- the first `len` coefficients of h
  | msmPoint         -- one MSM result point
  | counter          -- counters, the zero-check count
  | zeroedRegion     -- the contents of a wiped region
  | msmBuckets       -- the partial bucket sums (bucket rows) of the vendored MSM
  deriving Repr, DecidableEq

def VecKind.all : List VecKind :=
  [.scalars, .bases, .baseCoeffs, .baseTransform, .extended, .quotientCoeffs, .msmPoint, .counter,
   .zeroedRegion, .msmBuckets]

theorem VecKind.all_complete (k : VecKind) : k ∈ VecKind.all := by cases k <;> decide

/-- GPU-038 (wording of 2026-11-17): the kinds that may be copied to the host. -/
def permitted : VecKind → Bool
  | .baseTransform | .msmPoint | .msmBuckets | .quotientCoeffs | .counter => true
  | _ => false

/-- GPU-038 as worded before the ruling: no clause for the bucket sums. -/
def permittedBefore : VecKind → Bool
  | .msmBuckets => false
  | k => permitted k

/-- The device computations. The list is closed: a kernel step names one. -/
inductive DevOp where
  | fft              -- base-domain forward transform
  | ifft             -- base-domain inverse transform
  | cosetExtend      -- coefficient form to the extended coset
  | numerator        -- the quotient numerator on the extended coset
  | divideAndInverse -- division by the vanishing polynomial and transform back
  | extendedInverse  -- extended-size inverse transform (the old port's hook)
  | msm              -- one MSM, the result point
  | msmBucketRows    -- the vendored MSM up to its bucket rows
  | zero             -- wipe regions
  | countNonzero     -- count the non-zero regions of a wipe
  | readCounters     -- the device counters
  deriving Repr, DecidableEq

/-- The host computations. -/
inductive HostOp where
  | cosetExtendCpu     -- stock coefficient form to the extended coset
  | numeratorCpu       -- stock numerator (and division) on extended vectors
  | extendedInverseCpu -- stock extended-size inverse transform
  | bucketReduce       -- the host half of the vendored MSM: bucket rows to the point
  | scalarsOf          -- scalars (limbs) made from a coefficient vector the host holds
  | challenge          -- transcript state after absorbing commitments
  | countNonzeroCpu    -- count the non-zero words of zeroed contents
  | report             -- the proof and the report from scalars, points and counters
  deriving Repr, DecidableEq

/-- The kind a device operation gives for the kinds of its inputs, in order.
`none`: the operation does not take those inputs, and the step cannot run. -/
def DevOp.out (op : DevOp) (ks : List VecKind) : Option VecKind :=
  match op with
  | .fft => if ks = [.baseCoeffs] then some .baseTransform else none
  | .ifft => if ks = [.baseCoeffs] then some .baseTransform else none
  | .cosetExtend => if ks = [.baseCoeffs] then some .extended else none
  | .numerator => if ks ≠ [] ∧ ∀ k ∈ ks, k = .extended then some .extended else none
  | .divideAndInverse => if ks = [.extended] then some .quotientCoeffs else none
  | .extendedInverse => if ks = [.extended] then some .extended else none
  | .msm => if ks = [.scalars, .bases] then some .msmPoint else none
  | .msmBucketRows => if ks = [.scalars, .bases] then some .msmBuckets else none
  | .zero => some .zeroedRegion
  | .countNonzero => if ks = [.zeroedRegion] then some .counter else none
  | .readCounters => if ks = [] then some .counter else none

/-- The same for a host operation. -/
def HostOp.out (op : HostOp) (ks : List VecKind) : Option VecKind :=
  match op with
  | .cosetExtendCpu => if ks = [.baseCoeffs] then some .extended else none
  | .numeratorCpu => if ks ≠ [] ∧ ∀ k ∈ ks, k = .extended then some .extended else none
  | .extendedInverseCpu => if ks = [.extended] then some .extended else none
  | .bucketReduce => if ks = [.msmBuckets] then some .msmPoint else none
  | .scalarsOf =>
    if ks = [.baseTransform] ∨ ks = [.quotientCoeffs] ∨ ks = [.extended] then some .scalars
    else none
  | .challenge => if ks ≠ [] ∧ ∀ k ∈ ks, k = .msmPoint then some .scalars else none
  | .countNonzeroCpu => if ks = [.zeroedRegion] then some .counter else none
  | .report =>
    if ∀ k ∈ ks, k = .scalars ∨ k = .msmPoint ∨ k = .counter then some .counter else none

/-- The device operations whose output is an extended-domain vector. -/
def DevOp.extendedOp : DevOp → Bool
  | .cosetExtend | .numerator | .extendedInverse => true
  | _ => false

/-- The host operations whose output is an extended-domain vector. -/
def HostOp.extendedOp : HostOp → Bool
  | .cosetExtendCpu | .numeratorCpu | .extendedInverseCpu => true
  | _ => false

/-- A buffer: its kind, where it is held, and whether the host copy has been
zeroed (`zeroHost`). A new host copy (a download, a host computation) is not
zeroed; releasing the host copy (`free b host`) clears the flag with the copy. -/
structure Buf where
  kind : VecKind
  host : Bool
  device : Bool
  zeroed : Bool := false
  deriving Repr, DecidableEq

def Buf.holds (x : Buf) : Loc → Bool
  | .host => x.host
  | .device => x.device

def Buf.clear (x : Buf) : Loc → Buf
  | .host => { x with host := false, zeroed := false }
  | .device => { x with device := false }

/-- Buffer name to buffer. The first entry of a name is the live one. -/
abbrev Store := List (Nat × Buf)

def get (σ : Store) (b : Nat) : Option Buf := (σ.find? (·.1 == b)).map (·.2)

def holds (σ : Store) (l : Loc) (b : Nat) : Bool :=
  match get σ b with
  | some x => x.holds l
  | none => false

/-- The kinds of the named buffers, in order (a name with no buffer is left out;
a step that runs has a buffer for every input). -/
def kinds (σ : Store) (ins : List Nat) : List VecKind :=
  ins.filterMap fun b => (get σ b).map (·.kind)

/-- Does the host hold a copy of the buffer that still has its data (not zeroed)? -/
def hostReadable (σ : Store) (b : Nat) : Bool :=
  match get σ b with
  | some x => x.host && !x.zeroed
  | none => false

inductive Step where
  | upload (b : Nat)                                         -- host to device
  | download (b : Nat)                                       -- device to host (traced)
  | kernel (op : DevOp) (ins : List Nat) (out : Nat)         -- device computation
  | hostCompute (op : HostOp) (ins : List Nat) (out : Nat)   -- host computation
  | free (b : Nat) (loc : Loc)
  | zeroHost (b : Nat)                                       -- zero the host copy (it stays allocated)
  deriving Repr, DecidableEq

/-- One step, or `none` when its precondition fails. A created buffer needs a
fresh name, so a name keeps one kind for the whole plan (`exec_kind_stable`).
The kind of a created buffer is the operation's output kind for the kinds of
the inputs; the step does not run when the operation gives none. A host
computation reads its inputs: it does not run when the host copy of an input
has been zeroed (`zeroed_input_not_executable`). -/
def step (σ : Store) : Step → Option Store
  | .upload b =>
    match get σ b with
    | some x => if x.host then some ((b, { x with device := true }) :: σ) else none
    | none => none
  | .download b =>
    match get σ b with
    | some x => if x.device then some ((b, { x with host := true, zeroed := false }) :: σ) else none
    | none => none
  | .kernel op ins out =>
    if ins.all (holds σ .device) && (get σ out).isNone then
      match op.out (kinds σ ins) with
      | some k => some ((out, { kind := k, host := false, device := true }) :: σ)
      | none => none
    else none
  | .hostCompute op ins out =>
    if ins.all (hostReadable σ) && (get σ out).isNone then
      match op.out (kinds σ ins) with
      | some k => some ((out, { kind := k, host := true, device := false }) :: σ)
      | none => none
    else none
  | .free b l =>
    match get σ b with
    | some x => if x.holds l then some ((b, x.clear l) :: σ) else none
    | none => none
  | .zeroHost b =>
    match get σ b with
    | some x => if x.host then some ((b, { x with zeroed := true }) :: σ) else none
    | none => none

/-- The device-to-host copy a step makes in store `σ`: name and kind. -/
def emitted (σ : Store) : Step → List (Nat × VecKind)
  | .download b =>
    match get σ b with
    | some x => if x.device then [(b, x.kind)] else []
    | none => []
  | _ => []

/-- Run a plan. `none`: some step's precondition failed. -/
def exec (σ : Store) : List Step → Option Store
  | [] => some σ
  | s :: rest =>
    match step σ s with
    | some σ' => exec σ' rest
    | none => none

/-- The device-to-host copies of the executed prefix of a plan (the plan stops
at the first step that cannot run). -/
def trace (σ : Store) : List Step → List (Nat × VecKind)
  | [] => []
  | s :: rest =>
    match step σ s with
    | some σ' => emitted σ s ++ trace σ' rest
    | none => []

/-- The index and the step at which a plan stops, if it stops. -/
def firstFailure (σ : Store) : List Step → Option (Nat × Step)
  | [] => none
  | s :: rest =>
    match step σ s with
    | some σ' => (firstFailure σ' rest).map fun (i, t) => (i + 1, t)
    | none => some (0, s)

/-- GPU-038: every device-to-host copy has a permitted kind. -/
def Gpu038 (tr : List (Nat × VecKind)) : Prop := ∀ e ∈ tr, permitted e.2 = true

/-- GPU-038, last clause: no extended-domain vector is copied to the host. -/
def NoExtended (tr : List (Nat × VecKind)) : Prop := ∀ e ∈ tr, e.2 ≠ VecKind.extended

instance (tr : List (Nat × VecKind)) : Decidable (Gpu038 tr) := by unfold Gpu038; infer_instance

/-- GPU-038 as a rule on a plan: the plan runs to its end and every
device-to-host copy has a permitted kind. `Gpu038` alone is a predicate on the
trace and holds for the empty trace of a plan that does not run
(`rule038_needs_run`); a plan is evidence for the requirement only with this
rule. -/
def Rule038 (σ : Store) (plan : List Step) : Prop :=
  (exec σ plan).isSome = true ∧ Gpu038 (trace σ plan)

instance (σ : Store) (plan : List Step) : Decidable (Rule038 σ plan) := by
  unfold Rule038; infer_instance
instance (tr : List (Nat × VecKind)) : Decidable (NoExtended tr) := by
  unfold NoExtended; infer_instance

/-- The copies of a trace that GPU-038 forbids. -/
def offending (tr : List (Nat × VecKind)) : List (Nat × VecKind) := tr.filter (!permitted ·.2)

/-- Does the host hold a live buffer of kind `k`? -/
def hostHolds (σ : Store) (k : VecKind) : Bool :=
  σ.any fun e => match get σ e.1 with
    | some x => x.host && x.kind == k
    | none => false

/-- Does the host hold a live copy of kind `k` that has not been zeroed? -/
def hostHoldsUnzeroed (σ : Store) (k : VecKind) : Bool :=
  σ.any fun e => match get σ e.1 with
    | some x => x.host && !x.zeroed && x.kind == k
    | none => false

/-- GPU-084: does the step release a host copy of bucket sums that was not zeroed? -/
def badFree (σ : Store) : Step → Bool
  | .free b .host =>
    match get σ b with
    | some x => x.kind == .msmBuckets && x.host && !x.zeroed
    | none => false
  | _ => false

/-- No step of the run releases an un-zeroed host copy of bucket sums. -/
def freesOk (σ : Store) : List Step → Bool
  | [] => true
  | s :: rest =>
    match step σ s with
    | some σ' => !badFree σ s && freesOk σ' rest
    | none => true

/-- GPU-084: the plan runs to its end, every release of a host copy of bucket
sums finds that copy zeroed, and at the end the host holds no un-zeroed copy of
bucket sums. An ordinary `free b host` in place of `zeroHost b` does not meet
it (`msmBucketPlanFreeOnly_violates`). -/
def Gpu084 (σ : Store) (plan : List Step) : Prop :=
  match exec σ plan with
  | some σ' => freesOk σ plan = true ∧ hostHoldsUnzeroed σ' .msmBuckets = false
  | none => False

instance (σ : Store) (plan : List Step) : Decidable (Gpu084 σ plan) := by
  unfold Gpu084; split <;> infer_instance

/-! ## General facts (every plan, every start store) -/

theorem Gpu038.nil : Gpu038 [] := fun _ h => by cases h

theorem Gpu038.append {a b : List (Nat × VecKind)} : Gpu038 (a ++ b) ↔ Gpu038 a ∧ Gpu038 b := by
  simp only [Gpu038, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

/-- A download that can run is traced with the kind of its buffer. -/
theorem emitted_download (σ : Store) (b : Nat) (x : Buf) (hg : get σ b = some x)
    (hd : x.device = true) : emitted σ (.download b) = [(b, x.kind)] := by
  simp [emitted, hg, hd]

theorem step_download_some (σ : Store) (b : Nat) (x : Buf) (hg : get σ b = some x)
    (hd : x.device = true) :
    step σ (.download b) = some ((b, { x with host := true, zeroed := false }) :: σ) := by
  simp [step, hg, hd]

/-- Every traced copy comes from a `download` step whose buffer is on the device. -/
theorem mem_emitted (σ : Store) (s : Step) (e : Nat × VecKind) (he : e ∈ emitted σ s) :
    ∃ x, s = .download e.1 ∧ get σ e.1 = some x ∧ x.device = true ∧ e.2 = x.kind := by
  cases s with
  | download b =>
    simp only [emitted] at he
    cases hg : get σ b with
    | none => simp [hg] at he
    | some x =>
      by_cases hd : x.device = true
      · simp [hg, hd] at he
        subst he
        exact ⟨x, rfl, hg, hd, rfl⟩
      · simp [hg, hd] at he
  | _ => simp [emitted] at he

/-- GPU-038 for any plan: the trace is permitted exactly when every `download`
step that the run reaches with its buffer on the device copies a permitted
kind. The property is about the positions of the plan, not about two examples. -/
theorem gpu038_iff (plan : List Step) : ∀ (σ : Store),
    Gpu038 (trace σ plan) ↔
      ∀ pre b rest σ' x, plan = pre ++ Step.download b :: rest → exec σ pre = some σ' →
        get σ' b = some x → x.device = true → permitted x.kind = true := by
  induction plan with
  | nil =>
    intro σ
    constructor
    · intro _ pre b rest σ' x hp
      cases pre <;> simp at hp
    · intro _; exact Gpu038.nil
  | cons s r ih =>
    intro σ
    cases hs : step σ s with
    | none =>
      simp only [trace, hs]
      constructor
      · intro _ pre b rest σ' x hp he hg hd
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hp
          simp only [exec, Option.some.injEq] at he
          subst he
          rw [hp.1, step_download_some σ b x hg hd] at hs
          cases hs
        | cons s' pre' =>
          simp only [List.cons_append, List.cons.injEq] at hp
          rw [← hp.1] at he
          simp [exec, hs] at he
      · intro _; exact Gpu038.nil
    | some σ1 =>
      simp only [trace, hs]
      rw [Gpu038.append, ih σ1]
      constructor
      · intro ⟨h0, h1⟩ pre b rest σ' x hp he hg hd
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hp
          simp only [exec, Option.some.injEq] at he
          subst he
          have := h0 (b, x.kind) (by rw [hp.1, emitted_download σ b x hg hd]; simp)
          exact this
        | cons s' pre' =>
          simp only [List.cons_append, List.cons.injEq] at hp
          rw [← hp.1] at he
          simp only [exec, hs] at he
          exact h1 pre' b rest σ' x hp.2 he hg hd
      · intro h
        constructor
        · intro e he
          obtain ⟨x, hsd, hg, hd, hk⟩ := mem_emitted σ s e he
          rw [hk]
          exact h [] e.1 r σ x (by simp [hsd]) rfl hg hd
        · intro pre b rest σ' x hp he hg hd
          exact h (s :: pre) b rest σ' x (by simp [hp]) (by simp [exec, hs, he]) hg hd

theorem exec_append (p q : List Step) : ∀ σ : Store,
    exec σ (p ++ q) = (exec σ p).bind fun σ' => exec σ' q := by
  induction p with
  | nil => intro σ; rfl
  | cons s r ih =>
    intro σ
    cases hs : step σ s with
    | none => simp [exec, hs]
    | some σ1 => simp [exec, hs, ih σ1]

theorem trace_append (p q : List Step) : ∀ σ : Store,
    trace σ (p ++ q) = trace σ p ++ (match exec σ p with
      | some σ' => trace σ' q
      | none => []) := by
  induction p with
  | nil => intro σ; rfl
  | cons s r ih =>
    intro σ
    cases hs : step σ s with
    | none => simp [trace, exec, hs]
    | some σ1 => simp [trace, exec, hs, ih σ1]

/-- GPU-038 splits over `++`: the first part is permitted, and so is the second
part from the store the first part leaves. -/
theorem gpu038_append (σ : Store) (p q : List Step) :
    Gpu038 (trace σ (p ++ q)) ↔
      Gpu038 (trace σ p) ∧ ∀ σ', exec σ p = some σ' → Gpu038 (trace σ' q) := by
  rw [trace_append, Gpu038.append]
  cases he : exec σ p with
  | none => simp [Gpu038.nil]
  | some σ1 => simp

/-- A longer plan cannot repair a forbidden copy of its prefix. -/
theorem gpu038_prefix (σ : Store) (p q : List Step) (h : Gpu038 (trace σ (p ++ q))) :
    Gpu038 (trace σ p) := ((gpu038_append σ p q).mp h).1

/-! ## Kinds are derived (GPU-038)

The kind of a buffer a plan creates is `DevOp.out` / `HostOp.out` of the
operation and the kinds of its inputs; a name keeps its kind for the whole run;
so a download of a buffer made by an extended-output operation is always traced
as `extended`, and such a plan never satisfies GPU-038. -/

theorem get_cons (σ : Store) (a b : Nat) (x : Buf) :
    get ((a, x) :: σ) b = if a = b then some x else get σ b := by
  by_cases h : a = b <;> simp [get, h]

/-- The buffer a step creates in store `σ`: its name and its kind, from the
operation and the kinds of the inputs. `none`: the step creates no buffer. -/
def made (σ : Store) : Step → Option (Nat × VecKind)
  | .kernel op ins out => (op.out (kinds σ ins)).map fun k => (out, k)
  | .hostCompute op ins out => (op.out (kinds σ ins)).map fun k => (out, k)
  | _ => none

/-- GPU-038: no device operation gives an extended-domain vector except the
coset extension, the numerator and the extended-size inverse transform, and no
host operation except their stock (host) forms. -/
theorem extended_only_from :
    (∀ (op : DevOp) ks, op.out ks = some .extended →
      op = .cosetExtend ∨ op = .numerator ∨ op = .extendedInverse) ∧
    (∀ (op : HostOp) ks, op.out ks = some .extended →
      op = .cosetExtendCpu ∨ op = .numeratorCpu ∨ op = .extendedInverseCpu) := by
  constructor <;> intro op ks h <;> cases op <;> simp [DevOp.out, HostOp.out] at h ⊢

/-- Those operations give nothing else: an output of `cosetExtend`, `numerator`
or `extendedInverse` (device), or of their host forms, is `extended` whatever
the inputs. No choice of inputs relabels it. -/
theorem extendedOp_out :
    (∀ (op : DevOp) ks k, op.extendedOp = true → op.out ks = some k → k = .extended) ∧
    (∀ (op : HostOp) ks k, op.extendedOp = true → op.out ks = some k → k = .extended) := by
  constructor <;> intro op ks k he h <;> cases op <;>
    simp [DevOp.extendedOp, HostOp.extendedOp, DevOp.out, HostOp.out] at he h <;>
    exact h.2.symm

/-- `extendedOp` is exactly the list of `extended_only_from`. -/
theorem extendedOp_iff :
    (∀ op : DevOp, op.extendedOp = true ↔
      op = .cosetExtend ∨ op = .numerator ∨ op = .extendedInverse) ∧
    (∀ op : HostOp, op.extendedOp = true ↔
      op = .cosetExtendCpu ∨ op = .numeratorCpu ∨ op = .extendedInverseCpu) := by
  constructor <;> intro op <;> cases op <;> simp [DevOp.extendedOp, HostOp.extendedOp]

/-- A step keeps the kind of every buffer the store holds. -/
theorem step_kind_stable (σ σ' : Store) (s : Step) (b : Nat) (x : Buf)
    (hs : step σ s = some σ') (hg : get σ b = some x) :
    ∃ y, get σ' b = some y ∧ y.kind = x.kind := by
  have same : ∀ (c : Nat) (x0 y : Buf), get σ c = some x0 → y.kind = x0.kind →
      ∃ z, get ((c, y) :: σ) b = some z ∧ z.kind = x.kind := by
    intro c x0 y h0 hk
    rw [get_cons]
    by_cases hc : c = b
    · subst hc; rw [h0] at hg; cases hg; simp [hk]
    · simp [hc, hg]
  have fresh : ∀ (c : Nat) (y : Buf), get σ c = none →
      ∃ z, get ((c, y) :: σ) b = some z ∧ z.kind = x.kind := by
    intro c y h0
    rw [get_cons]
    by_cases hc : c = b
    · subst hc; rw [h0] at hg; cases hg
    · simp [hc, hg]
  cases s with
  | upload c =>
    simp only [step] at hs
    split at hs
    · rename_i x0 h0
      split at hs
      · cases hs; exact same c x0 _ h0 rfl
      · cases hs
    · cases hs
  | download c =>
    simp only [step] at hs
    split at hs
    · rename_i x0 h0
      split at hs
      · cases hs; exact same c x0 _ h0 rfl
      · cases hs
    · cases hs
  | kernel op ins out =>
    simp only [step] at hs
    split at hs
    · rename_i hc
      split at hs
      · cases hs
        exact fresh out _ (by simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc; exact hc.2)
      · cases hs
    · cases hs
  | hostCompute op ins out =>
    simp only [step] at hs
    split at hs
    · rename_i hc
      split at hs
      · cases hs
        exact fresh out _ (by simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc; exact hc.2)
      · cases hs
    · cases hs
  | free c l =>
    simp only [step] at hs
    split at hs
    · rename_i x0 h0
      split at hs
      · cases hs; exact same c x0 _ h0 (by cases l <;> rfl)
      · cases hs
    · cases hs
  | zeroHost c =>
    simp only [step] at hs
    split at hs
    · rename_i x0 h0
      split at hs
      · cases hs; exact same c x0 _ h0 rfl
      · cases hs
    · cases hs

/-- A name keeps its kind for the whole run of a plan. -/
theorem exec_kind_stable (plan : List Step) : ∀ (σ σ' : Store) (b : Nat) (x : Buf),
    exec σ plan = some σ' → get σ b = some x → ∃ y, get σ' b = some y ∧ y.kind = x.kind := by
  induction plan with
  | nil => intro σ σ' b x he hg; cases he; exact ⟨x, hg, rfl⟩
  | cons s r ih =>
    intro σ σ' b x he hg
    cases hs : step σ s with
    | none => simp [exec, hs] at he
    | some σ1 =>
      simp only [exec, hs] at he
      obtain ⟨y, hy, hk⟩ := step_kind_stable σ σ1 s b x hs hg
      obtain ⟨z, hz, hk'⟩ := ih σ1 σ' b y he hy
      exact ⟨z, hz, hk'.trans hk⟩

/-- A step that creates a buffer gives it the kind `made` computes. -/
theorem made_step (σ σ' : Store) (s : Step) (b : Nat) (k : VecKind)
    (hs : step σ s = some σ') (hm : made σ s = some (b, k)) :
    ∃ x, get σ' b = some x ∧ x.kind = k := by
  cases s with
  | kernel op ins out =>
    simp only [step] at hs
    cases ho : op.out (kinds σ ins) with
    | none => simp [made, ho] at hm
    | some k0 =>
      simp only [made, ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp only [ho] at hs
      split at hs
      · cases hs; exact ⟨{ kind := k0, host := false, device := true }, by simp [get_cons], rfl⟩
      · cases hs
  | hostCompute op ins out =>
    simp only [step] at hs
    cases ho : op.out (kinds σ ins) with
    | none => simp [made, ho] at hm
    | some k0 =>
      simp only [made, ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp only [ho] at hs
      split at hs
      · cases hs; exact ⟨{ kind := k0, host := true, device := false }, by simp [get_cons], rfl⟩
      · cases hs
  | _ => simp [made] at hm

/-- GPU-038: the kind of every buffer a step creates is a function of the
operation and the kinds of its inputs. A name that has no buffer before the
step and has one after it was made by a `kernel` or `hostCompute` step, and its
kind is `DevOp.out` / `HostOp.out` of the operation on the input kinds (`made`).
No step declares a kind. -/
theorem kind_determined (σ σ' : Store) (s : Step) (b : Nat) (y : Buf)
    (hs : step σ s = some σ') (h0 : get σ b = none) (h1 : get σ' b = some y) :
    made σ s = some (b, y.kind) := by
  have old : ∀ (c : Nat) (x0 z : Buf), get σ c = some x0 → σ' = (c, z) :: σ → False := by
    intro c x0 z hc he
    rw [he, get_cons] at h1
    by_cases hcb : c = b
    · subst hcb; rw [hc] at h0; cases h0
    · simp [hcb, h0] at h1
  cases s with
  | upload c =>
    simp only [step] at hs
    split at hs
    · rename_i x0 hc
      split at hs
      · cases hs; exact (old c x0 _ hc rfl).elim
      · cases hs
    · cases hs
  | download c =>
    simp only [step] at hs
    split at hs
    · rename_i x0 hc
      split at hs
      · cases hs; exact (old c x0 _ hc rfl).elim
      · cases hs
    · cases hs
  | free c l =>
    simp only [step] at hs
    split at hs
    · rename_i x0 hc
      split at hs
      · cases hs; exact (old c x0 _ hc rfl).elim
      · cases hs
    · cases hs
  | zeroHost c =>
    simp only [step] at hs
    split at hs
    · rename_i x0 hc
      split at hs
      · cases hs; exact (old c x0 _ hc rfl).elim
      · cases hs
    · cases hs
  | kernel op ins out =>
    simp only [step] at hs
    split at hs
    · cases ho : op.out (kinds σ ins) with
      | none => simp [ho] at hs
      | some k =>
        simp only [ho, Option.some.injEq] at hs
        subst hs
        rw [get_cons] at h1
        by_cases hob : out = b
        · subst hob; simp at h1; subst h1; simp [made, ho]
        · simp [hob, h0] at h1
    · cases hs
  | hostCompute op ins out =>
    simp only [step] at hs
    split at hs
    · cases ho : op.out (kinds σ ins) with
      | none => simp [ho] at hs
      | some k =>
        simp only [ho, Option.some.injEq] at hs
        subst hs
        rw [get_cons] at h1
        by_cases hob : out = b
        · subst hob; simp at h1; subst h1; simp [made, ho]
        · simp [hob, h0] at h1
    · cases hs

/-- The same for a whole plan: every buffer that the run of a plan adds to the
store was made by one `kernel` or `hostCompute` step of the plan, and its kind is
that operation's output kind for the kinds its inputs had at that step. -/
theorem plan_kind_determined (plan : List Step) : ∀ (σ σ' : Store) (b : Nat) (y : Buf),
    exec σ plan = some σ' → get σ b = none → get σ' b = some y →
      ∃ pre s rest σ1, plan = pre ++ s :: rest ∧ exec σ pre = some σ1 ∧
        made σ1 s = some (b, y.kind) := by
  induction plan with
  | nil => intro σ σ' b y he h0 h1; cases he; rw [h0] at h1; cases h1
  | cons s r ih =>
    intro σ σ' b y he h0 h1
    cases hs : step σ s with
    | none => simp [exec, hs] at he
    | some σ1 =>
      simp only [exec, hs] at he
      cases hg : get σ1 b with
      | none =>
        obtain ⟨pre, t, rest, σ2, hp, hx, hm⟩ := ih σ1 σ' b y he hg h1
        exact ⟨s :: pre, t, rest, σ2, by simp [hp], by simp [exec, hs, hx], hm⟩
      | some x =>
        obtain ⟨z, hz, hk⟩ := exec_kind_stable r σ1 σ' b x he hg
        rw [hz] at h1; cases h1
        exact ⟨[], s, r, σ, rfl, rfl, by rw [hk]; exact kind_determined σ σ1 s b x hs h0 hg⟩

/-- Does the step create the buffer `out` with an extended-output operation? -/
def Step.makesExtended : Step → Nat → Bool
  | .kernel op _ o, out => o == out && op.extendedOp
  | .hostCompute op _ o, out => o == out && op.extendedOp
  | _, _ => false

theorem makesExtended_made (σ σ' : Store) (s : Step) (out : Nat)
    (hs : step σ s = some σ') (hm : s.makesExtended out = true) :
    made σ s = some (out, .extended) := by
  cases s with
  | kernel op ins o =>
    simp only [Step.makesExtended, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨rfl, he⟩ := hm
    simp only [step] at hs
    cases ho : op.out (kinds σ ins) with
    | none => simp [ho] at hs
    | some k => simp [made, ho, extendedOp_out.1 op _ k he ho]
  | hostCompute op ins o =>
    simp only [Step.makesExtended, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨rfl, he⟩ := hm
    simp only [step] at hs
    cases ho : op.out (kinds σ ins) with
    | none => simp [ho] at hs
    | some k => simp [made, ho, extendedOp_out.2 op _ k he ho]
  | _ => simp [Step.makesExtended] at hm

theorem exec_append_some (p q : List Step) (σ σ' : Store) (h : exec σ (p ++ q) = some σ') :
    ∃ σ1, exec σ p = some σ1 ∧ exec σ1 q = some σ' := by
  rw [exec_append] at h
  cases hp : exec σ p with
  | none => simp [hp] at h
  | some σ1 => exact ⟨σ1, rfl, by simpa [hp] using h⟩

/-- A download that the run reaches with its buffer on the device is in the
trace, with the kind of the buffer. -/
theorem trace_download_mem (σ σ1 : Store) (pre rest : List Step) (b : Nat) (x : Buf)
    (he : exec σ pre = some σ1) (hg : get σ1 b = some x) (hd : x.device = true) :
    (b, x.kind) ∈ trace σ (pre ++ .download b :: rest) := by
  rw [trace_append, he]
  simp [trace, step_download_some σ1 b x hg hd, emitted_download σ1 b x hg hd]

/-- GPU-038: a plan cannot relabel an extended vector. In every store, a plan
that runs, creates a buffer with `cosetExtend`, `numerator` or `extendedInverse`
(or a host form of them) and later downloads that buffer has the copy in its
trace as `extended`, and so does not satisfy `Gpu038` (nor `NoExtended`). There
is no executable plan, from `init` or from any other store, that downloads such
a buffer under a permitted kind. -/
theorem mislabel_impossible (σ : Store) (pre mid rest : List Step) (s : Step) (out : Nat)
    (hs : s.makesExtended out = true)
    (hx : (exec σ (pre ++ s :: mid ++ .download out :: rest)).isSome = true) :
    (out, VecKind.extended) ∈ trace σ (pre ++ s :: mid ++ .download out :: rest) ∧
    ¬ Gpu038 (trace σ (pre ++ s :: mid ++ .download out :: rest)) ∧
    ¬ NoExtended (trace σ (pre ++ s :: mid ++ .download out :: rest)) := by
  obtain ⟨σ', he⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨σ3, hpre, he⟩ := exec_append_some _ _ _ _ he
  obtain ⟨σ1, h1, h13⟩ := exec_append_some _ _ _ _ hpre
  cases hst : step σ1 s with
  | none => simp [exec, hst] at h13
  | some σ2 =>
    simp only [exec, hst] at h13
    obtain ⟨x2, hx2, hk2⟩ := made_step σ1 σ2 s out .extended hst
      (makesExtended_made σ1 σ2 s out hst hs)
    obtain ⟨x3, hx3, hk3⟩ := exec_kind_stable mid σ2 σ3 out x2 h13 hx2
    have hdev : x3.device = true := by
      cases hd : x3.device with
      | true => rfl
      | false => simp [exec, step, hx3, hd] at he
    have hmem := trace_download_mem σ σ3 (pre ++ s :: mid) rest out x3 hpre hx3 hdev
    rw [hk3.trans hk2] at hmem
    exact ⟨hmem, fun h => (by have := h _ hmem; cases this), fun h => h _ hmem rfl⟩

/-! ## One prove: buffers and hooks

Names: 0 the SRS bases (resident on the device), 1 an advice column in
coefficient form, 2 MSM scalars, 3 and 4 the 2^k coefficient vectors that the
quotient reads. Created names are 10 and above. -/

def init : Store :=
  [(0, { kind := .bases, host := true, device := true }),
   (1, { kind := .baseCoeffs, host := true, device := false }),
   (2, { kind := .scalars, host := true, device := false }),
   (3, { kind := .baseCoeffs, host := true, device := false }),
   (4, { kind := .baseCoeffs, host := true, device := false })]

/-- Base-domain fft/ifft hook: the result is written into the caller's host buffer. -/
def fftHook (inp out : Nat) : List Step :=
  [.upload inp, .kernel .fft [inp] out, .download out, .free inp .device,
   .free out .device]

/-- MSM hook as the hook contract states it: one point comes back. -/
def msmHook (sc out : Nat) : List Step :=
  [.upload sc, .kernel .msm [sc, 0] out, .download out, .free sc .device, .free out .device]

/-- Quotient hook: coset extension, numerator, division and inverse transform
all on the device; only the quotient coefficients come back. -/
def quotientHook : List Step :=
  [.upload 3, .upload 4, .kernel .cosetExtend [3] 20, .kernel .cosetExtend [4] 21,
   .kernel .numerator [20, 21] 22, .kernel .divideAndInverse [22] 23, .download 23]

def countersRead : List Step := [.kernel .readCounters [] 30, .download 30]

/-- GPU-036: wipe, count the non-zero regions on the device, read the count. -/
def zeroCheckOnDevice : List Step :=
  [.kernel .zero [20, 21, 22] 40, .kernel .countNonzero [40] 41, .download 41,
   .free 20 .device, .free 21 .device, .free 22 .device, .free 40 .device]

/-- The port after its fix. Host steps consume every downloaded result: 11 the
scalars made from the transform output, 14 the transcript state after the two
commitments, 24 the quotient limbs, 99 the proof and the report. -/
def specPlan : List Step :=
  fftHook 1 10 ++ [.hostCompute .scalarsOf [10] 11] ++ msmHook 11 12 ++ msmHook 2 13 ++
  [.hostCompute .challenge [12, 13] 14] ++ quotientHook ++ [.hostCompute .scalarsOf [23] 24] ++
  msmHook 24 25 ++ countersRead ++ zeroCheckOnDevice ++ [.hostCompute .report [14, 25, 30, 41] 99]

/-- Old coset hook `coeff_to_extended`: the extended vector goes back to the host. -/
def cosetHook (inp out : Nat) : List Step :=
  [.upload inp, .kernel .cosetExtend [inp] out, .download out]

/-- Old extended inverse transform hook: extended-size output goes back to the host. -/
def extInverseHook (inp out : Nat) : List Step :=
  [.upload inp, .kernel .extendedInverse [inp] out, .download out]

/-- Old zero-check in check mode: the zeroed contents are read on the host. -/
def zeroCheckReadback : List Step :=
  [.kernel .zero [20, 21, 23] 40, .download 40, .hostCompute .countNonzeroCpu [40] 41]

/-- The port before the fix (reading of the description: the coset hook and the
extended inverse hook run on the device, the stock host code between them
computes the numerator and the division from the extended vectors). -/
def oldPortPlan : List Step :=
  fftHook 1 10 ++ [.hostCompute .scalarsOf [10] 11] ++ msmHook 11 12 ++ msmHook 2 13 ++
  [.hostCompute .challenge [12, 13] 14] ++ cosetHook 3 20 ++ cosetHook 4 21 ++
  [.hostCompute .numeratorCpu [20, 21] 22] ++ extInverseHook 22 23 ++
  [.hostCompute .scalarsOf [23] 24] ++ msmHook 24 25 ++ countersRead ++ zeroCheckReadback ++
  [.hostCompute .report [14, 25, 30, 41] 99]

/-- The old plan with the forbidden downloads taken out (the forbidden ones are
found by running the plan). -/
def stripForbidden (σ : Store) : List Step → List Step
  | [] => []
  | s :: rest =>
    match step σ s with
    | some σ' =>
      if (emitted σ s).all (permitted ·.2) then s :: stripForbidden σ' rest
      else stripForbidden σ' rest
    | none => s :: rest

/-- What sppark's MSM does (`msm/pippenger.cuh`, `invoke`): the bucket rows are
copied to the host (`DtoH(res, d_buckets, …)`), host threads finish the
reduction (`collect`, `integrate_row`), then the host has the point. GPU-084:
the host copy of the rows is zeroed after the reduction and before its memory
is released. -/
def msmBucketPlan : List Step :=
  [.upload 2, .kernel .msmBucketRows [2, 0] 50, .download 50, .hostCompute .bucketReduce [50] 51,
   .zeroHost 50, .free 50 .host, .free 2 .device, .free 50 .device]

/-- The same with an ordinary release and no zeroing: the stock allocator's
`free`, which leaves the sums in the released memory. -/
def msmBucketPlanFreeOnly : List Step := msmBucketPlan.filter (· != .zeroHost 50)

/-- The same with neither the zeroing nor the release: the host copy stays live. -/
def msmBucketPlanNoZero : List Step :=
  msmBucketPlan.filter fun s => s != .zeroHost 50 && s != .free 50 .host

/-! ## Theorems on the plans (kernel-checked by `decide`) -/

/-- Every precondition of the fixed port holds: no host computation needs a
vector that is only on the device. -/
theorem specPlan_executable : (exec init specPlan).isSome = true := by decide

/-- GPU-038 for the fixed port. -/
theorem specPlan_gpu038 : Gpu038 (trace init specPlan) := by decide

/-- GPU-038 for the fixed port, as a rule: the plan runs and every copy is permitted. -/
theorem specPlan_rule038 : Rule038 init specPlan := by decide

/-- The old port runs and breaks the rule. -/
theorem oldPortPlan_not_rule038 :
    (exec init oldPortPlan).isSome = true ∧ ¬ Rule038 init oldPortPlan := by decide

/-- A plan that does not run is no evidence: `[download 999]` stops at its first
step (there is no buffer 999), its trace is empty and `Gpu038` holds for the
empty trace, but the rule does not hold. -/
theorem rule038_needs_run :
    exec init [.download 999] = none ∧ trace init [.download 999] = [] ∧
    Gpu038 (trace init [.download 999]) ∧ ¬ Rule038 init [.download 999] := by decide

theorem specPlan_noExtended : NoExtended (trace init specPlan) := by decide

/-- The copies of the fixed port, in order: transform output, three MSM points,
quotient coefficients, counters, the zero-check count. -/
theorem specPlan_trace : trace init specPlan =
    [(10, .baseTransform), (12, .msmPoint), (13, .msmPoint), (23, .quotientCoeffs),
     (25, .msmPoint), (30, .counter), (41, .counter)] := by decide

/-- At the end of the fixed port's plan the host holds no extended vector and no
zeroed contents. The statement is about the final store only: it does not say
that no intermediate store holds one. That no extended vector or zeroed region
is ever copied to the host during the plan is `specPlan_noExtended` and
`specPlan_trace` (the trace lists every device-to-host copy of the run). -/
theorem specPlan_host_clean : ∀ σ, exec init specPlan = some σ →
    hostHolds σ .extended = false ∧ hostHolds σ .zeroedRegion = false := by decide

theorem oldPortPlan_executable : (exec init oldPortPlan).isSome = true := by decide

/-- The old port breaks GPU-038. The offending copies: the two coset outputs
(20, 21), the extended inverse output (23) and the zeroed contents (40). -/
theorem oldPortPlan_violates : ¬ Gpu038 (trace init oldPortPlan) := by decide

theorem oldPortPlan_extended : ¬ NoExtended (trace init oldPortPlan) := by decide

theorem oldPortPlan_offending : offending (trace init oldPortPlan) =
    [(20, .extended), (21, .extended), (23, .extended), (40, .zeroedRegion)] := by decide

/-- GPU-036, GPU-038: a zero-check that reads a zeroed region back is a
forbidden copy, in every store that holds the region on the device and whatever
the plan does afterwards. -/
theorem zeroCheck_readback_violates (σ : Store) (b : Nat) (x : Buf) (rest : List Step)
    (hg : get σ b = some x) (hd : x.device = true) (hk : x.kind = .zeroedRegion) :
    ¬ Gpu038 (trace σ (.download b :: rest)) := by
  intro h
  have hp := (gpu038_iff _ σ).mp h [] b rest σ x rfl rfl hg hd
  rw [hk] at hp
  cases hp

/-- The same for an extended-domain vector. -/
theorem extended_readback_violates (σ : Store) (b : Nat) (x : Buf) (rest : List Step)
    (hg : get σ b = some x) (hd : x.device = true) (hk : x.kind = .extended) :
    ¬ Gpu038 (trace σ (.download b :: rest)) ∧ ¬ NoExtended (trace σ (.download b :: rest)) := by
  have ht : (b, VecKind.extended) ∈ trace σ (.download b :: rest) := by
    simp [trace, step_download_some σ b x hg hd, emitted_download σ b x hg hd, hk]
  refine ⟨fun h => ?_, fun h => h _ ht rfl⟩
  have hp := h _ ht
  cases hp

/-- On the fixed port's buffers: reading the zeroed region (40) back is the one
offending copy. -/
theorem zeroCheck_readback_offending :
    offending (trace init (quotientHook ++ [.kernel .zero [20, 21, 22] 40, .download 40]))
      = [(40, .zeroedRegion)] := by decide

/-- The device zero-check copies one counter and nothing else. -/
theorem zeroCheck_onDevice_ok :
    trace init (quotientHook ++ zeroCheckOnDevice) = [(23, .quotientCoeffs), (41, .counter)] := by
  decide

/-! ### Non-vacuity -/

theorem permitted_not_constant : permitted .counter = true ∧ permitted .extended = false ∧
    permitted .zeroedRegion = false ∧ permitted .scalars = false ∧ permitted .bases = false ∧
    permitted .baseCoeffs = false := by decide

/-- The permitted set, in full. -/
theorem permitted_set : VecKind.all.filter permitted =
    [.baseTransform, .quotientCoeffs, .msmPoint, .counter, .msmBuckets] := by decide

/-- Taking the forbidden downloads out of the old plan leaves a plan that obeys
GPU-038 as far as it runs, but it does not run: it stops at the stock host code
that computes the numerator from the two extended vectors (step 21,
`hostCompute numeratorCpu [20, 21] 22`), which are now only on the device. The fix
had to move the coset transforms and that host code into the quotient hook. -/
theorem oldPort_stripped_not_executable :
    exec init (stripForbidden init oldPortPlan) = none ∧
    firstFailure init (stripForbidden init oldPortPlan) =
      some (21, .hostCompute .numeratorCpu [20, 21] 22) ∧
    Gpu038 (trace init (stripForbidden init oldPortPlan)) ∧
    (stripForbidden init oldPortPlan).length + 4 = oldPortPlan.length := by decide

/-- The fixed plan has nothing to strip. -/
theorem specPlan_strip_id : stripForbidden init specPlan = specPlan := by decide

/-! ### The vendored MSM (GPU-038 bucket clause, GPU-084) -/

theorem msmBucketPlan_executable : (exec init msmBucketPlan).isSome = true := by decide

/-- GPU-038 (wording of 2026-11-17): the bucket sums are a permitted copy. -/
theorem msmBucketPlan_gpu038 : Gpu038 (trace init msmBucketPlan) := by decide

/-- The same as a rule: the plan runs and the bucket sums are a permitted copy. -/
theorem msmBucketPlan_rule038 : Rule038 init msmBucketPlan := by decide

theorem msmBucketPlan_trace : trace init msmBucketPlan = [(50, .msmBuckets)] := by decide

/-- Under the wording before the ruling the same plan was a violation: bucket
rows are not MSM result points. -/
theorem msmBucketPlan_violates_before :
    ¬ ∀ e ∈ trace init msmBucketPlan, permittedBefore e.2 = true := by decide

/-- GPU-084: the plan zeroes the host copy of the bucket sums and then releases
it; the release finds it zeroed and nothing un-zeroed is left. -/
theorem msmBucketPlan_gpu084 : Gpu084 init msmBucketPlan := by decide

/-- The plan is not vacuous for GPU-084: the bucket sums do reach the host (the
store before the zeroing step holds an un-zeroed host copy). -/
theorem msmBucketPlan_buckets_on_host :
    ((exec init (msmBucketPlan.take 4)).map fun σ => hostHoldsUnzeroed σ .msmBuckets) = some true := by
  decide

/-- GPU-084: an ordinary release without zeroing violates the requirement. The
plan runs, obeys GPU-038 and leaves no host copy at the end, exactly like the
zeroing plan; the release of the un-zeroed copy is what fails. -/
theorem msmBucketPlanFreeOnly_violates :
    (exec init msmBucketPlanFreeOnly).isSome = true ∧ Gpu038 (trace init msmBucketPlanFreeOnly) ∧
    ((exec init msmBucketPlanFreeOnly).map fun σ => hostHolds σ .msmBuckets) = some false ∧
    freesOk init msmBucketPlanFreeOnly = false ∧
    ¬ Gpu084 init msmBucketPlanFreeOnly := by decide

/-- With neither the zeroing nor the release the plan still runs and still obeys
GPU-038, but the host keeps a live un-zeroed copy of the bucket sums: GPU-084
fails. -/
theorem msmBucketPlanNoZero_violates :
    (exec init msmBucketPlanNoZero).isSome = true ∧ Gpu038 (trace init msmBucketPlanNoZero) ∧
    freesOk init msmBucketPlanNoZero = true ∧
    ¬ Gpu084 init msmBucketPlanNoZero := by decide

/-- GPU-084 for every plan and every store: a `free b host` that the run reaches
while the host copy of `b` holds un-zeroed bucket sums violates the requirement,
whatever the plan does before and after. -/
theorem gpu084_unzeroed_free_violates (σ σ1 : Store) (pre rest : List Step) (b : Nat) (x : Buf)
    (he : exec σ pre = some σ1) (hg : get σ1 b = some x) (hk : x.kind = .msmBuckets)
    (hh : x.host = true) (hz : x.zeroed = false) :
    ¬ Gpu084 σ (pre ++ .free b .host :: rest) := by
  have hf : ∀ (p : List Step) (τ τ1 : Store), exec τ p = some τ1 →
      freesOk τ (p ++ .free b .host :: rest) = (freesOk τ p && freesOk τ1 (.free b .host :: rest)) := by
    intro p
    induction p with
    | nil => intro τ τ1 h; cases h; simp [freesOk]
    | cons s r ih =>
      intro τ τ1 h
      cases hs : step τ s with
      | none => simp [exec, hs] at h
      | some τ' =>
        simp only [exec, hs] at h
        simp [freesOk, hs, ih τ' τ1 h, Bool.and_assoc]
  have hbad : freesOk σ1 (.free b .host :: rest) = false := by
    simp [freesOk, step, hg, Buf.holds, hh, badFree, hk, hz]
  intro h
  unfold Gpu084 at h
  split at h
  · rw [hf pre σ σ1 he, hbad] at h; simp at h
  · exact h

/-- A host computation cannot read a zeroed buffer: in every store, a
`hostCompute` step with an input whose host copy has been zeroed does not run. -/
theorem zeroed_input_not_executable (σ : Store) (op : HostOp) (ins : List Nat) (out b : Nat)
    (x : Buf) (hg : get σ b = some x) (hz : x.zeroed = true) (hb : b ∈ ins) :
    step σ (.hostCompute op ins out) = none := by
  have h : ins.all (hostReadable σ) = false := by
    apply Bool.eq_false_iff.mpr
    intro hall
    have := List.all_eq_true.mp hall b hb
    simp [hostReadable, hg, hz] at this
  simp [step, h]

/-- The vendored MSM with the zeroing step before the host reduction: zero, then
reduce, then release. -/
def msmBucketPlanZeroFirst : List Step :=
  [.upload 2, .kernel .msmBucketRows [2, 0] 50, .download 50, .zeroHost 50,
   .hostCompute .bucketReduce [50] 51, .free 50 .host, .free 2 .device, .free 50 .device]

/-- GPU-084: zeroing before the reduction is not a way to meet the requirement.
The reduction would read zeros, so the plan does not run: it stops at the
`bucketReduce` step (index 4), and `Gpu084` does not hold for it. -/
theorem zero_before_reduce_not_executable :
    exec init msmBucketPlanZeroFirst = none ∧
    firstFailure init msmBucketPlanZeroFirst = some (4, .hostCompute .bucketReduce [50] 51) ∧
    ¬ Gpu084 init msmBucketPlanZeroFirst ∧ ¬ Rule038 init msmBucketPlanZeroFirst := by decide

/-- GPU-084 is not met by a plan that does not run to its end. -/
theorem gpu084_needs_run : ¬ Gpu084 init [.zeroHost 50] := by decide

/-- The hook-contract MSM (`msmHook`, used in `specPlan`) returns one point and
never creates a buffer of bucket sums, on the host or on the device. So GPU-084
has nothing to say about `specPlan`: `Gpu084 init specPlan` would hold only
because there is nothing to zero. The former theorem `specPlan_gpu084` stated
that vacuous fact as if it were evidence for the requirement; it is dropped and
replaced by this statement of why the requirement does not apply. The evidence
for GPU-084 is `msmBucketPlan_gpu084` with its two violating variants. -/
theorem specPlan_no_bucket_sums : ∀ σ, exec init specPlan = some σ →
    σ.all (fun e => e.2.kind != .msmBuckets) = true := by decide

/-- The read-back kind code of the service op 4 (vectors/README.md), where the
table has one. Code 1 stands for MSM result points and for the partial bucket
sums of the vendored MSM: the two kinds share the code on the wire and are apart
as kinds (`msmPoint`, `msmBuckets`). Every permitted kind has a code. -/
def copyCode : VecKind → Option Nat
  | .quotientCoeffs => some 0
  | .msmPoint => some 1
  | .msmBuckets => some 1
  | .counter => some 2
  | .baseTransform => some 3
  | .extended => some 4
  | .zeroedRegion => some 5
  | _ => none

end GpuSpec.DataMove
