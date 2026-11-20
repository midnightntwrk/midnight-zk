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
import Lean
import GpuSpec.Tests
import GpuSpec.ServiceProofs

/-!
# Audit

Two checks, both pinned with `#guard_msgs`, so any change fails the build.

* `#print axioms` on each theorem of the requirement table. Only `propext`,
  `Classical.choice` and `Quot.sound` may appear. `sorryAx`, a new `axiom`, or
  any `_native` axiom (`native_decide`, `decide +native`, `bv_decide`) changes
  the message.
* `#audit_ns GpuSpec` lists every declaration that the compiled oracle runs
  differently from what the kernel checks: `implemented_by`, `extern`, `csimp`,
  `unsafe`, `partial`, `partial_fixpoint`, `opaque` and `axiom`.

`Main` does not import this module. The newer modules pin their own theorems the
same way: `AuditNtt.lean`, `MsmProofs.lean`, `PinsExt.lean` and `VectorPins.lean`;
`PinsExt` and `VectorPins` rerun `#audit_ns GpuSpec` with every module imported.
-/

open Lean Elab Command

elab "#audit_ns " ns:ident : command => do
  let env ← getEnv
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.toList do
    let inModule := match env.getModuleIdxFor? n with
      | some i => ns.getId.isPrefixOf (env.header.moduleNames[i.toNat]!)
      | none => false
    if (ns.getId.isPrefixOf n || inModule) && !(n matches .str _ "_unsafe_rec") then
      if (Compiler.getImplementedBy? env n).isSome then bad := bad.push s!"implemented_by {n}"
      if isExtern env n then bad := bad.push s!"extern {n}"
      if ci.isUnsafe then bad := bad.push s!"unsafe {n}"
      if (Lean.Elab.PartialFixpoint.eqnInfoExt.find? env n).isSome then
        bad := bad.push s!"partial_fixpoint {n}"
      if ci.isPartial then bad := bad.push s!"partial {n}"
      if (Compiler.CSimp.ext.getState env).map.contains n then bad := bad.push s!"csimp {n}"
      match ci with
      | .axiomInfo _ => bad := bad.push s!"axiom {n}"
      | .opaqueInfo _ => bad := bad.push s!"opaque {n}"
      | _ => pure ()
  logInfo m!"{bad.qsort (· < ·)}"

/-- info: [] -/
#guard_msgs in
#audit_ns GpuSpec

/-! ## Axioms of each theorem -/

/-- info: 'GpuSpec.msmRaw_mask_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.msmRaw_mask_mod

/-- info: 'GpuSpec.sub_add_cancel_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.sub_add_cancel_mod

/-- info: 'GpuSpec.msmMasked_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.msmMasked_eq

/-- info: 'GpuSpec.exec_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.exec_append

/-- info: 'GpuSpec.compile_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.compile_correct

/-- info: 'GpuSpec.deviceNumerator_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.deviceNumerator_eq

/-- info: 'GpuSpec.resolve_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.resolve_eq

/-- info: 'GpuSpec.proveStep_honest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.proveStep_honest

/-- info: 'GpuSpec.proveStep_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.proveStep_congr

/-- info: 'GpuSpec.prove_any_schedule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.prove_any_schedule

/-- info: 'GpuSpec.prove_two_devices' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.prove_two_devices

/-- info: 'GpuSpec.runInPlace_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.runInPlace_eq

/-- info: 'GpuSpec.install_twice' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.install_twice

/-- info: 'GpuSpec.fft_eq_ntt_F5_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fft_eq_ntt_F5_all

/-- info: 'GpuSpec.dirtyDecline_breaks' does not depend on any axioms -/
#guard_msgs in
#print axioms GpuSpec.dirtyDecline_breaks

/-- info: 'GpuSpec.Service.inv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.inv_init

/-- info: 'GpuSpec.Service.inv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.inv_step

/-- info: 'GpuSpec.Service.inv_foldl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.inv_foldl

/-- info: 'GpuSpec.Service.inv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.inv_run

/-- info: 'GpuSpec.Service.stepRefusals_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.stepRefusals_nil

/-- info: 'GpuSpec.Service.breaker_open_skips' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.breaker_open_skips

/-- info: 'GpuSpec.Service.served_clears_failures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.served_clears_failures

/-- info: 'GpuSpec.Service.served_then_restart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.served_then_restart

/-- info: 'GpuSpec.Service.busy_no_failure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.busy_no_failure

/-- info: 'GpuSpec.Service.acceptance_no_degraded_proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.acceptance_no_degraded_proof

/-- info: 'GpuSpec.Service.decline_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.decline_counted

/-- info: 'GpuSpec.Service.wipe_frees_tables' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GpuSpec.Service.wipe_frees_tables

/-- info: 'GpuSpec.Service.wipe_frees_tables_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.wipe_frees_tables_step

/-- info: 'GpuSpec.Service.wipe_fail_retires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.wipe_fail_retires

/-- info: 'GpuSpec.Service.restart_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.restart_cap

/-- info: 'GpuSpec.Service.breaker_recordFailure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.breaker_recordFailure

/-- info: 'GpuSpec.Service.breaker_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.breaker_apply

/-- info: 'GpuSpec.Service.countAt_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.countAt_sum

/-- info: 'GpuSpec.Service.countAt_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.countAt_getD

/-- info: 'GpuSpec.Service.reply_served' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.Service.reply_served
