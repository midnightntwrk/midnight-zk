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

import GpuSpec.NttProofs

/-!
# Axiom audit of the NTT theorems

`#print axioms` of each general transform theorem, its BLS12-381 anchor and its
witness, pinned with `#guard_msgs` as in `Audit.lean`. Only `propext`,
`Classical.choice` and `Quot.sound` may appear.
-/

/-- info: 'GpuSpec.fft_eq_ntt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fft_eq_ntt

/-- info: 'GpuSpec.intt_ntt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.intt_ntt

/-- info: 'GpuSpec.ntt_intt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.ntt_intt

/-- info: 'GpuSpec.IsRoot2.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.IsRoot2.inv

/-- info: 'GpuSpec.ifft_eq_intt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.ifft_eq_intt

/-- info: 'GpuSpec.fftCosetExt_unfold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fftCosetExt_unfold

/-- info: 'GpuSpec.cosetExt_eq_ntt_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.cosetExt_eq_ntt_scaled

/-- info: 'GpuSpec.fftCosetExt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fftCosetExt_eq

/-- info: 'GpuSpec.cosetToCoeff_cosetExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.cosetToCoeff_cosetExt

/-- info: 'GpuSpec.fftCosetToCoeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fftCosetToCoeff_eq

/-- info: 'GpuSpec.bls_size_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.bls_size_ok

/-- info: 'GpuSpec.bls_isInv_gen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.bls_isInv_gen

/-- info: 'GpuSpec.bls_isInv_zeta3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.bls_isInv_zeta3

/-- info: 'GpuSpec.fft_eq_ntt_bls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fft_eq_ntt_bls

/-- info: 'GpuSpec.intt_ntt_bls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.intt_ntt_bls

/-- info: 'GpuSpec.ntt_intt_bls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.ntt_intt_bls

/-- info: 'GpuSpec.ifft_eq_intt_bls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.ifft_eq_intt_bls

/-- info: 'GpuSpec.fftCosetExt_eq_bls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fftCosetExt_eq_bls

/-- info: 'GpuSpec.cosetToCoeff_cosetExt_bls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.cosetToCoeff_cosetExt_bls

/-- info: 'GpuSpec.fftCosetToCoeff_eq_bls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.fftCosetToCoeff_eq_bls

/-- info: 'GpuSpec.p0_counterexample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.p0_counterexample

/-- info: 'GpuSpec.p0_counterexample_coset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.p0_counterexample_coset

/-- info: 'GpuSpec.witness_hyps_F17' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.witness_hyps_F17

/-- info: 'GpuSpec.witness_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.witness_concrete

/-- info: 'GpuSpec.witness_concrete_intt_ntt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.witness_concrete_intt_ntt

/-- info: 'GpuSpec.witness_concrete_coset_round_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GpuSpec.witness_concrete_coset_round_trip
