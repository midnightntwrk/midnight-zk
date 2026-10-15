# Protogalaxy IVC on the fflonk + Pippenger stack

Experimental branch `iquerejeta/protogalaxy-ivc`. It builds an IVC whose step circuit runs a
Protogalaxy folding verifier instead of a full in-circuit SNARK verifier, on top of the Rust
Pippenger MSM and the in-circuit fflonk verifier, and measures it against the existing
SNARK-verifier IVC.

Plan: `.claude/plans/protogalaxy-ivc-plan.md` (local, git-ignored). One section per plan step
below, each committed together with the step it documents.

## Pinned inputs

| Name | Ref | Commit | Role |
|---|---|---|---|
| main | `main` = `origin/main` | `fac0b168` | both A-inputs are based on it |
| Pippenger MSM | `giles-msm-pippenger` = `origin/giles-msm-pippenger` | `7437f05f` | 29 commits over main: Rust Pippenger G1 MSM, blst MSM for the verifier |
| fflonk gadget | `origin/irakoton/fflonk-gadget-v2` | `a12cb0b6` | 10 commits over main, 13 files, in-circuit fflonk verifier; no file overlap with the Pippenger branch |
| Accordion | `balbas/accordion` (= local `accordion`) | `f021bb2e` | one-shot Protogalaxy ("Accordion"); 12 commits over `ad9b63e6` |
| Old folding-IVC PoC | `iquerejeta/protogalaxy` | `cf33413e` | "REVERT - trying incremental prover/verifier. unsuccessful"; reference only |

Machine for every measurement: Apple M1 Pro, 10 cores, 16 GB RAM, rustc 1.90.0.

## [A.1] Base branch: Pippenger MSM + fflonk gadget
Commit: 59777c89 (merge) + this commit (doc)   Date: 2026-10-15   Machine: M1 Pro 10c/16GB   Features: none / truncated-challenges

### What and why
`git checkout -b iquerejeta/protogalaxy-ivc 7437f05f && git merge --no-ff a12cb0b6`. Clean merge, no
conflicts (the two branches touch disjoint files). This is the base every later step builds on.

### How to reproduce (from the repo root unless stated)
```
cargo build --release --workspace --examples
cargo test --release -p midnight-proofs
cargo test --release -p midnight-circuits verifier
cargo test --release -p midnight-zk-stdlib
cd aggregation && cargo run --release --features truncated-challenges --example ivc
```

### Results
| Command | Result | Wall time |
|---|---|---|
| build workspace + examples | ok | cached |
| test `midnight-proofs` | 65 passed | 5 s |
| test `midnight-circuits verifier` | 3 passed | 92 s |
| test `midnight-zk-stdlib` | 37 passed | 173 s |
| example `ivc` (no features) | not runnable: `required-features = ["truncated-challenges"]` | – |
| example `ivc` (`truncated-challenges`, default K/N, 3 steps) | verifies; ≈12.5 s prove / ≈27 ms verify per step | 89 s |

### Interpretation
The merge is behaviour-preserving: all bounded tests pass and the existing IVC still verifies with the
Pippenger prover MSM and blst verifier MSM. The `ivc` example can only be run with
`truncated-challenges` (Cargo `required-features`), so every IVC measurement in this document uses that
feature; the "without" runs of the plan are not possible for this example.

### Deviations from the plan, open problems
- Plan 0.3 asks to run `ivc` with and without `truncated-challenges`; only "with" is possible (see above).

## [A.2] fflonk with T_MAX = 8 as the branch default
Date: 2026-10-15   Machine: M1 Pro 10c/16GB   Features: truncated-challenges (ivc example)

### What and why
Phase C wants few, large commitments (fflonk chunking, see plan section 5), so fflonk becomes the global
PCS of the branch:
- `zk_stdlib/src/pcs.rs`: `DefaultPCS = Fflonk<KZGCommitmentScheme<Bls12>, 3>`.
- `circuits/src/verifier/types.rs`: `BlstrsEmulation::PCS = InCircuitFflonk<InCircuitKZG<Self>, 3>`.
  The compiler accepts the `PCS::OffCircuitPCS == DefaultPCS` coupling as is.
- `circuits/src/verifier/verifier_gadget.rs`: `test_verify_proof` passes `log2_t_max = 3` (SRS room).
SRS loading needed no change: `load_srs::<DefaultPCS>` already loads `2^(k + 3)` points.

### How to reproduce
```
cargo test --release -p midnight-circuits verifier
cargo test --release -p midnight-zk-stdlib
CHANGE_VK=BREAKING cargo test --release -p midnight-zk-stdlib --test check_vks   # regenerates the VKs
cd aggregation && /usr/bin/time -l cargo run --release --features truncated-challenges --example ivc
```

### Results
| Test | Result |
|---|---|
| `midnight-proofs` | 65 passed |
| `midnight-circuits verifier` | 3 passed |
| `midnight-zk-stdlib` | all pass except `check_vk_cred_enrollment`, `check_vk_cred_full` (see below) |

`ivc` example, default `K = 18`, `N = 1000`, Midnight SRS `2^21`, 3 steps (contended: test suites and an
editor running):

| | KZG (A.1) | fflonk T_MAX=8 |
|---|---|---|
| setup | 14.4 s | 385.7 s |
| step 0 prove | 13.6 s | 199.1 s |
| steps 1–2 prove | 12.5 s | 18.4 s |
| verify | ≈27 ms | 26–45 ms |
| peak RSS | – | 2.48 GB |

Regenerated files (Q5): `zk_stdlib/tests/static_vks/*Vk` for BitcoinSigExample, BitcoinThresholdECDSA,
CredentialProperty, EccExample, EthereumSigExample, HybridMtExample, MembershipExample,
NativeGadgetExample, PoseidonExample, RSASignatureCircuit, SchnorrExample, ShaPreImageCircuit; and
`zk_stdlib/goldenfiles/examples/*` (cost-model proof `size` only, e.g. Poseidon 2768 → 2192 bytes).

### Interpretation
The switch is functionally clean. Steady-state proving is ≈1.5× slower than KZG (18.4 s vs 12.5 s),
plausibly the fflonk prover's larger combined polynomials (degree `t·n`) plus the larger in-circuit
verifier. The one-off costs (setup ×27, first step ×15) are far out of line with that and are not explained
yet; they are investigated in A.3 at K = 16 before being trusted as a baseline.

### Deviations from the plan, open problems
- `check_vk_cred_enrollment` / `check_vk_cred_full`: `k = 17` circuits now need a Filecoin SRS of `2^20`
  points; only up to `2^19` exists. Not run on this branch; their static VKs are not regenerated.
- `single_circuit_aggregation` / `multi_circuit_aggregation` examples: not run on this branch (plan A.2).
- Setup / step-0 slowdown under fflonk: open, see A.3.

## [A.3] Baseline: SNARK-verifier IVC, N = 1, and commitment census
Date: 2026-10-15   Machine: M1 Pro 10c/16GB   Features: truncated-challenges   **Contended** (video calls running)

### What and why
`aggregation/examples/ivc.rs`: `K = 17`, `N = 1`, `STEPS = 10`, Midnight SRS. This is the baseline
Phase C is compared against. The commitment census (temporary prints, kept out of the commit; patch at
`.claude/plans/reports/census_print.patch`) gives the inputs of the C.0 estimate.

### How to reproduce
```
cd aggregation && /usr/bin/time -l cargo run --release --features truncated-challenges --example ivc
```

### Results
| | Value |
|---|---|
| k / rows / table rows | 17 / 70,895 / 122,899 |
| keygen (`ivc::setup`) | 203.1 s (one-off, see interpretation) |
| step 0 prove | 100.5 s (one-off, see interpretation) |
| per-step prove, mean of steps 2–10 | 9.10 s (range 8.28–9.97) |
| verify | ≈16.6 ms (11–25) |
| proof size (cost model) | 4,432 bytes |
| peak RSS | 3.14 GB |

Commitment census of the IVC circuit (`cs.degree() = 5`):

| Group | Polynomials |
|---|---|
| fixed + selectors + permutation σ (phase 0, VK) | 49 |
| phase 1: 15 advice + 2 logup multiplicities | 17 |
| phase 2: 6 permutation `Z` + 3 logup helpers + 2 logup accumulators + 1 trash | 12 |
| quotient | 4 |

| T_MAX | fixed | `c_var` (ph1 + ph2) | quotient |
|---|---|---|---|
| 1 (KZG) | 49 | 29 (17 + 12) | 4 |
| 8 | 7 | 5 (3 + 2) | 1 |
| 16 | 4 | 3 (2 + 1) | 1 |
| 32 | 2 | **2 (1 + 1)** | 1 |
| 64, 128 | 1 | 2 (1 + 1) | 1 |

Gate identities 29, permutation sets 6, lookups 2 (3 helper chunks), trashcans 1 →
`nb_y = 29 + 13 + 7 + 1 = 50`, `nb_theta = 16` (widest lookup table).

### Interpretation
- **K = 16 is impossible** for this circuit even at `N = 1`: 70,895 rows > 2^16. The SNARK verifier
  alone is ≈70k rows, so the baseline is `k = 17`. The table rows (122,899) do not set `k`: the
  decomposition table is sized by `k − 1` bits and is chosen to fit (61,459 rows at `k = 16`).
  Compared to the 2026-08 measurement (238,477 rows, `k = 18`, KZG), the fflonk in-circuit verifier
  is ≈3.4× smaller, mostly because it does far fewer in-circuit MSM bases (7 + 5 + 1 commitments instead of 49 + 29 + 4).
- **Setup and step 0 are one-off costs of fflonk's residue bases.** `sample` shows both dominated by
  `g_to_lagrange` (a G1 FFT, `recursive_butterfly_arithmetic` over `Fp` Montgomery multiplications).
  `ParamsKZG::residue_bases(t, n, i)` computes, lazily and cached, one size-`n` G1 FFT per residue
  `i < t` for every chunk size `t` it meets. Setup meets `t ∈ {8, 1}` (49 fixed polys);
  step 0 meets the new sizes `t = 4` (phase 2: 12 = 8 + 4; quotient: 4). Later steps hit the cache.
  Not a per-step cost; it could be precomputed/serialised with the SRS (Phase D candidate).
- `c_var` reaches its minimum of 2 at `T_MAX = 32` (`SRS = 2^(k+5)`); with `T_MAX = 8` it is 5.
  This is the input for C.0.

### Deviations from the plan, open problems
- `K = 17` instead of 16 (does not fit, see above); Midnight SRS `2^20` instead of Filecoin.
- The local `examples/assets/midnight-srs-2p20` was truncated (27 MB instead of 201 MB); regenerated by
  `ParamsKZG::downsize(20)` of `midnight-srs-2p21` (assets are not tracked by git).
- Only `truncated-challenges` runs (A.1). Timings are contended; re-run in a quiet window before C.4.

## [B.1] Vector theta/y challenges
Commits: `6eb37149` ([B.1a], native) + this commit ([B.1b], in-circuit + doc)   Date: 2026-10-15
Machine: M1 Pro 10c/16GB   Features: truncated-challenges (IVC example)   **Contended** (video calls running)

### What and why
Folding needs the constraint polynomial affine in every challenge, so the single `theta` (lookup
tuple compression) and single `y` (identity batching), both used through powers by Horner's rule,
become vectors of independent challenges, in the native prover (`prover.rs`, `bench/prover.rs`,
`evaluation.rs`, `logup/prover.rs`), the native verifier (`verifier.rs`, `plonk/mod.rs`,
`logup.rs`) and the in-circuit verifier (`verifier_gadget.rs`, `expressions/{mod,lookup}.rs`).
- `theta[i]` multiplies position `i` of every lookup tuple (table and inputs): `Σᵢ θᵢ·eᵢ`.
- `y[k]` multiplies identity `k` of the flat identity list, in forward order: gate polynomials,
  permutation (`2·sets + 1`), per lookup (boundary, one helper per chunk, accumulator), trashcans.
- Counts: `ConstraintSystem::nb_theta_challenges()` (widest lookup tuple, 0 without lookups) and
  `nb_y_challenges()` (number of identities), the single source of truth for prover, verifier and
  gadget. Squeezed with `Transcript::squeeze_challenges(n)` / `TranscriptGadget::squeeze_challenges`.
- Squeeze order: phase-1 commits → `theta[0..nb_theta]` → beta → gamma → trash_challenge →
  phase-2 commits → `y[0..nb_y]` → unchanged. All challenges random (no `θ₀ = y₀ = 1`).
- Trash keeps its scalar `trash_challenge` with Horner (it is a separate committed column, not a
  folded identity coefficient).
- Evaluator: `ValueSource::{Theta, Y}(usize)`, new `Calculation::LinearCombination` lowered to
  the existing `MulAdd` flat op; the values buffer gets `n_theta + n_y` challenge slots per graph.
  Both counts are asserted against the identity list (`evaluate_identities`,
  `evaluate_numerator`, gadget).
- Gadget: `y` batching stays one `add_and_mul` per identity (`acc − y_k·id_k`); lookup tuples
  use `compress_expressions_indexed` (one `mul` then one `mul_add` per further term).

### How to reproduce
From the repo root:
```
cargo build --release --workspace --examples
cargo test --release -p midnight-proofs
cargo test --release -p midnight-circuits verifier
cargo test --release -p midnight-zk-stdlib --no-fail-fast
CHANGE_VK=BREAKING cargo test --release -p midnight-zk-stdlib --test check_vks
```
IVC example, with the census patch applied temporarily (`git apply
.claude/plans/reports/census_print.patch`, reverted with `git checkout aggregation/src/ivc/setup.rs`):
```
cd aggregation && /usr/bin/time -l cargo run --release --features truncated-challenges --example ivc
```

### Results
| Test | Result |
|---|---|
| workspace build (release, examples) | ok |
| `midnight-proofs` | ok (lib 50, plonk_api 3, adversarial 9, vk_serialization 2, doc 1) |
| `midnight-circuits verifier` | ok (3: transcript gadget, KZG and fflonk proof verification) |
| `midnight-zk-stdlib` | lib 4, check_vks 12/14, serialization 8, doc 9 ok; `public_inputs_test` fails (pre-existing, see below) |
| VK goldenfiles (`CHANGE_VK=BREAKING`) | no file changed |
| `examples/ivc`, K = 17, N = 1, 10 steps, truncated-challenges | all steps verify |

IVC circuit (`cs.degree() = 5`; census unchanged from A.3: `nb_theta = 16`, `nb_y = 50`):

| | A.3 (scalar) | B.1 (vector) | Δ |
|---|---|---|---|
| rows (k = 17) | 70,895 | 71,546 | +651 (+0.92%) |
| table rows | 122,899 | 122,899 | 0 |
| proof size (cost model) | 4,432 B | 4,432 B | 0 |
| keygen (`ivc::setup`) | 203.1 s | 188.4 s | contended |
| step 0 prove | 100.5 s | 92.0 s | contended |
| per-step prove, mean of steps 2–10 | 9.10 s (8.28–9.97) | 8.46 s (7.33–10.54) | contended |
| verify | ≈16.6 ms | ≈17.6 ms (8–34) | |
| peak RSS | 3.14 GB | 3.08 GB | |

### Interpretation
- The row increase is almost exactly the extra transcript squeezes: `(16 − 1) + (50 − 1) = 64`
  more Poseidon squeezes, ≈10 rows each (inferred from the delta, not measured separately); the remainder is one extra `mul` per
  compressed lookup tuple (`Σᵢ θᵢ·eᵢ` needs `l` operations instead of Horner's `l − 1`). The `y`
  batching costs the same one operation per identity as Horner did. Well inside "a few %".
- Not truncating `theta`/`y` under `truncated-challenges` is what keeps this small: a truncated
  element costs a full bit decomposition in-circuit, i.e. 64 decompositions here, and these
  challenges never scale curve points, so truncation would buy nothing.
- Native prover cost is unchanged in kind (one multiply-add per identity per row, as before);
  timings are within the noise of a contended machine. Proof bytes are unchanged (challenges are
  not part of the proof) and so are the VKs, hence no goldenfile regeneration.

### Deviations from the plan, open problems
- **theta/y are not truncated under `truncated-challenges`** (the plan said "each element is
  squeezed truncated"). Same as before this step; see Interpretation for the cost argument.
- Width-1 lookups are now compressed as `θ₀·e₀` (previously `e₀`, no theta). Consistent across
  prover, verifier and gadget; costs one squeeze and one `mul` per tuple in-circuit. A circuit
  without lookups squeezes no `theta` (`nb_theta = 0`); one without identities would squeeze no `y`.
- Two commits (`[B.1a]` native, `[B.1b]` gadget + doc) instead of one; `[B.1a]` alone compiles
  and passes the `midnight-proofs` tests but its in-circuit verifier is out of sync.
- `public_inputs_test` (`zk_stdlib/tests/public_inputs.rs`) fails: cost-model proof size 4,096 vs
  actual 4,448 bytes. **Pre-existing**: it fails identically at `0ddf00b7` (presumably since the
  fflonk default of A.2; the cost model does not model fflonk proof sizes). Not touched here.
- `check_vk_cred_enrollment` / `check_vk_cred_full` skipped (need a `2^20` Filecoin SRS, see A.2).
- K = 17 instead of 16 (see A.3). IVC example run only with `truncated-challenges` (as in A.1/A.3).

## [B.2] Commit-phases-only prover/verifier helpers
Commit: this commit   Date: 2026-10-15   Machine: M1 Pro 10c/16GB   Features: truncated-challenges (IVC example)   **Contended** (video calls running)

### What and why
Phase C's per-step prover never runs `create_proof` (0.4.7): it synthesises the step witness,
commits phases 1 and 2, derives the challenges and folds. Its native folding verifier reads a
fresh instance's commitments and challenges without verifying a proof. This step exposes both
halves on the current phase-group API (re-implementing accordion's `c751601f` / `33267dda`).
- Prover, `proofs/src/plonk/prover.rs`:
  `pub(crate) fn commit_phases(params, pk, circuit, [nb_committed_instances,] instances, transcript, rng) -> Result<CommittedTrace<'a, F, CS>, Error>`.
  It is the former body of `compute_trace` minus the final `into_coeff`: witness, phase-1 commit
  (advice + logup multiplicities), `theta⃗, beta, gamma, trash`, phase-2 commit (permutation `Z`,
  logup helpers/aggregator, trash), `y⃗`; the transcript is left right after `y⃗`.
  `compute_trace` (hence `create_proof`) is now `commit_phases(..)?.trace.into_coeff(domain)`:
  same operations in the same order, so proof bytes and VKs are unchanged.
- `proofs/src/plonk/traces.rs`: `ProverTrace<'a, F, B = Coeff>` is generic in the
  representation of its phase-1/2 polynomials (Lagrange after the commit phases, coefficients
  for the proof), with `ProverTrace<'a, F, LagrangeCoeff>::into_coeff`. New
  `pub(crate) struct CommittedTrace<'a, F, CS> { trace: ProverTrace<'a, F, LagrangeCoeff>, phase1_commitment, phase2_commitment }`
  (the folding prover's fresh instance; Lagrange form, so folding needs no FFT, as in `c751601f`).
- `argument::prover::Committed::commit` now also returns the commitment it writes
  (`Result<(Self, CS::Commitment), Error>`; two call sites in `bench/prover.rs` adapted).
- Verifier: the existing `pub fn parse_trace` (`verifier.rs`) already is the "read commit phases"
  counterpart and `verify_proof`/`prepare` already go through it, so no refactor was needed. Added
  `pub fn VerifierTrace::{phase1_commitment, phase2_commitment}(&self) -> &CS::Commitment` and
  `pub(crate) fn argument::verifier::Committed::commitment`. Challenges are the existing
  `pub(crate)` fields of `VerifierTrace`. Accordion's per-argument accessors (`33267dda`: logup,
  permutation, trash `Committed`) have no counterpart: main commits each phase as one labelled
  group, i.e. one `CS::Commitment` per phase (fflonk: one per chunk inside it).

### How to reproduce
From the repo root:
```
cargo test --release -p midnight-proofs --lib commit_phases
cargo build --release --workspace --examples
cargo test --release -p midnight-proofs
cargo test --release -p midnight-circuits verifier
cargo test --release -p midnight-zk-stdlib --no-fail-fast
cd aggregation && cargo run --release --features truncated-challenges --example ivc
```

### Results
New tests in `proofs/src/plonk/commit_phases_tests.rs` (circuit `b = a²` on 16 rows, `a` range-
checked by a lookup, `b₀` copied to a public input; `nb_theta = 1`, `nb_y > 1`), run for KZG and
for fflonk `T_MAX = 8` (`commit_phases_match_verifier_{kzg,fflonk}`), with and without
`committed-instances`/`truncated-challenges`. Each checks: re-committing the returned Lagrange
polynomials gives the returned commitments; `parse_trace` on the same bytes gives equal
commitments and equal `theta⃗, beta, gamma, trash, y⃗`; one more squeeze from either transcript
agrees (same transcript state); `create_proof` for the same circuit verifies.

| Test | Result |
|---|---|
| workspace build (release, examples) | ok, no warnings |
| `midnight-proofs` | ok (lib 52 incl. the 2 new, plonk_api 3, adversarial 9, vk_serialization 2, doc 1) |
| `midnight-circuits verifier` | ok (3) |
| `midnight-zk-stdlib --no-fail-fast` | lib 4, check_vks 12/14, serialization 8, doc 9 ok; known failures only (see below) |
| goldenfiles / VKs | no file changed |
| `examples/ivc`, K = 17, N = 1, truncated-challenges | all 10 steps verify; step 0 prove 92.9 s, steps 1–9 7.8–9.4 s, verify 15–22 ms, peak RSS 2.92 GB (contended) |

### Interpretation
Pure refactor plus accessors: no new arithmetic, the commit phases and the proof are the same
operations as before, so `create_proof` costs the same (the `into_coeff` moved, it was not
duplicated). For Phase C, `commit_phases` is exactly the per-step
prover's "fresh instance" (C.1), and `parse_trace` + the commitment accessors is the native
folding verifier's input; neither computes a quotient, opens anything or touches coset FFTs.

### Deviations from the plan, open problems
- No new verifier function: `parse_trace` already stops after `y⃗` (the quotient commitments are
  read in `verify_algebraic_constraints`), so the "read commit phases" helper is `parse_trace`
  plus two accessors.
- `CommittedTrace::{phase1,phase2}_commitment` carry `#[allow(dead_code)]` until C.1 reads them
  (only the test reads them now). `commit_phases` is `pub(crate)`: the IVC code in `aggregation/`
  will call the C.1 folding API in `proofs/`, not this helper; make it `pub` then if needed.
- `bench/prover.rs` keeps its own instrumented copy of the commit phases (as before; it mirrors
  `create_proof`); it was only adapted to the new `commit` return type.
- Known issue found while running B.1 tests: `zk_stdlib/tests/public_inputs.rs::public_inputs_test`
  fails since A.2 (cost-model proof size 4,096 vs actual 4,448 bytes).
  `proofs/src/dev/cost_model.rs::circuit_model_with` models a KZG/SHPLONK proof layout (one
  commitment per quotient limb, multiopen = 2 commitments + one scalar per point set), not
  fflonk's. The A.2 run did not reveal it because cargo stopped after the failing `check_vks`
  binary. Consequence: cost-model `size` (goldenfiles, A.3's 4,432 bytes) is not the real fflonk
  proof size; C.4 measures real proof bytes. Not fixed on this branch.
- `check_vk_cred_enrollment` / `check_vk_cred_full` fail as before (need a `2^20` Filecoin SRS, A.2).
