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

## [C.0] Estimate gate for the folding step circuit
Date: 2026-10-15   No code; estimate from the A.3 census and B.1 counts.

### What and why
Before building Phase C, estimate the folding-IVC step circuit (scalar-e Protogalaxy verifier in-circuit,
no SNARK verifier) and check it beats the baseline (B.1 re-measure: 71,546 rows, `k = 17`).
Plan revision (2026-10-15): `T_MAX ∈ {8, 16}` only; one-shot Protogalaxy (B.3–B.5) dropped: no IVC step
produces a full proof, only phase-1/2 commitments plus the folding messages; the only full proof is the
final decider.

### Model
```
rows ≈ c_var·M                       # [γ](C_i − acc_i); M = 9,300 (128-bit γ) or 12,100 (full-width γ)
     + 95·3·c_var                    # hash acc in/out + fresh commitments
     + 12·2·S                        # hash the accumulator scalars in/out
     + 12·(log n + d + nb_theta + nb_y)   # F, K coefficients + challenges through the transcript
     + 5,000                         # vk, PI, genesis select, scalar folding, transition (N = 1)
S = |PI| + nb_theta + nb_y + 3 + log n + 1 = 2 + 16 + 50 + 3 + 16 + 1 = 88
```
Inputs: `c_var` 5 (`T_MAX = 8`) / 3 (`T_MAX = 16`) from A.3; `nb_theta = 16`, `nb_y = 50` (B.1);
`log n = 16` (target `k`); `d ≈ 8` (identity degree 5 plus challenge degree, exact value computed in C.1).
The ladder/base constants are the 2026-08 measurements of `windowed_msm` (unchanged since).

### Results
| `T_MAX` | `c_var` | γ | commitment folding | rest | total rows | `k` |
|---|---|---|---|---|---|---|
| 8 | 5 | 128-bit | 46,500 | 9,617 | **≈56,100** | 16 |
| 16 | 3 | 128-bit | 27,900 | 9,047 | **≈36,900** | 16 |
| 8 | 5 | full | 60,500 | 9,617 | ≈70,100 | 17 |
| 16 | 3 | full | 36,300 | 9,047 | ≈45,300 | 16 |
| baseline (SNARK verifier) | – | – | – | – | 71,546 | 17 |

`k = 15` is out of reach in all rows (the decomposition table alone is ≈30.7k rows at `k = 15` and the
circuit is > 32,768). The SRS for `k = 16` is `2^19` (`T_MAX = 8`) or `2^20` (`T_MAX = 16`); both exist.

### Interpretation
- The gate passes: with truncated γ (the IVC example already requires `truncated-challenges`) both
  choices land at `k = 16`, half the baseline's domain. Commitment folding is 83% (`T_MAX = 8`) or 76%
  (`T_MAX = 16`) of the circuit; everything else together is < 10k rows.
- **Choice: `T_MAX = 8`** (branch default; 16 does not change `k`). Margin to `2^16` is ≈9.4k rows (14%),
  inside the uncertainty of the "5,000 rest" term; if C.2 measures > 65.5k rows, switch to `T_MAX = 16`
  (−18.6k rows) rather than going to `k = 17`.
- Without truncation, `T_MAX = 8` would hit `k = 17` and lose the domain advantage, so 128-bit γ matters.
- The optimistic scalar-multiplication check (plan 5.5) would save ≈1.5k rows at `c_var = 5` (−3%);
  kept as an optional ablation in C.2.

### Deviations from the plan, open problems
- Baseline is `k = 17`, not 16 (A.3), so the comparison is `k = 16` folding vs `k = 17` SNARK verifier.
- `d` is an estimate; C.1 computes `d_total` exactly.

## [C.1] Native running-accumulator folding + decider
Commits: `eb4bf78c` ([C.1a], pub(crate) helpers), `4f0ca47d` ([C.1b], quotient helpers), this commit
([C.1c], protogalaxy module + doc)   Date: 2026-10-15   Machine: M1 Pro 10c/16GB
Features: none (tests), truncated-challenges (IVC example)   **Contended** (load average 10–18 during timings)

### What and why
Native side of the folding IVC (plan 0.4.4, scalar-e Protogalaxy, 2-to-1): a fresh instance is the
B.2 commit phases only (partial proof), folded into a running accumulator; the only full proof is
the decider of the final accumulator. Code: `proofs/src/plonk/protogalaxy/` (public module
`midnight_proofs::plonk::protogalaxy`):

| File | Content |
|---|---|
| `instance.rs` | `Challenges`, `FoldingInstance` (verifier view of an instance), `Accumulator`; transcript encoding; folding of the public data |
| `prover.rs` | `commit_instance` → `ProverInstance`; `ProverAccumulator::{init, fold, accumulator}` |
| `verifier.rs` | `read_instance`; `Accumulator::{init, fold}`; transcript steps shared with the prover (`fold_public`) |
| `trace.rs` | `fold_trace` (Lagrange-form trace, `acc + x·(fresh − acc)`), `evaluate_rows` (`fᵢ` on every row of `H`, B.1 evaluator, no FFT) |
| `degree.rs` | `folding_degree(cs)` = `d_total` |
| `poly.rs` | `pow_vector`, perturbator `F` (bottom-up tree, `O(n)`), interpolation, `L₀`, `Z`, `e'` |
| `decider_prover.rs`, `decider_verifier.rs` | `prove_relaxed_trace`, `verify_relaxed_trace` |
| `tests.rs` | chain of 4 folds + decider (KZG and fflonk), negative tests, timings |

Shared-path changes ([C.1a], [C.1b], mechanical, no change in proof bytes or VKs):
`PolynomialCommitmentScheme::fold_commitments` (KZG per labelled point; fflonk delegates: folding
commutes with `g = Σ_j X^j f_j(X^t)`); `Polynomial::fold`, `argument::prover::Committed::fold`;
`Evaluator::evaluate_numerator` generic in the representation of the committed polynomials
(conversion closure; Lagrange in, Lagrange out for folding); `verifier::instance_evals`,
`argument::verifier::Committed::new`; `keygen::compute_lagrange_polys(domain, cs)`;
`prover::scaled_quotient_poly`, `verifier::scaled_quotient_commitment`.

**Accumulator layout** (`Accumulator`, verifier side): `FoldingInstance { phase1_commitment,
phase2_commitment (CS::Commitment each; fflonk: one point per chunk of ≤ T_MAX polys), instances:
Vec<Vec<F>> (PI per instance column), challenges: { θ⃗, β, γ, trash, y⃗ } }`, `betas: Vec<F>`
(`log n`), `error: F`. Prover side (`ProverAccumulator`) adds the folded `ProverTrace` in Lagrange
form (phase-1/2 polynomials, instance values and polynomials, challenges). Fixed/VK commitments
are never folded (the folded trace keeps a reference to the proving key's phase-0 group).

**Initialisation (choice)**: the first fresh instance becomes the accumulator. Fresh transcript,
absorb the instance (phase-1 commitment, phase-2 commitment, PI column by column), squeeze `β`,
`β⃗ = (β, β², β⁴, …)`, `e = 0`. Sound: `Σᵢ powᵢ(β⃗)·fᵢ = Σᵢ βⁱ·fᵢ`, a polynomial of degree `< n` in a
`β` squeezed after the instance (and hence its challenges) is fixed, so a non-satisfying instance
passes with probability `≤ (n − 1)/|F|`. In-circuit cost for C.2: one extra sponge over the fresh
instance (same encoding as the fold absorbs), one squeeze, `log n` squarings, and a genesis select
(step 1 inits, later steps fold). Rejected: cf33413e's trivial accumulator (identity commitments:
`acc + γ(C − acc)` with `acc = O` needs complete addition in the foreign ECC chip, plan 5.5), and
"`β⃗ = 0`" (only checks row 0, unsound).

**Folding transcript** (fresh `T::init()` per round; C.2 must replicate it with Poseidon):
1. absorb accumulator: phase-1 commitment, phase-2 commitment, PI (column by column, no lengths),
   `θ⃗`, `β`, `γ`, `trash`, `y⃗`, `β⃗`, `e`;
2. absorb fresh instance: phase-1 commitment, phase-2 commitment, PI (its challenges are not
   absorbed: they are derived from its own transcript = vk, PI, commitments; the circuit must
   replay that transcript);
3. squeeze `δ`, `δ⃗ = (δ, δ², δ⁴, …)`;
4. prover writes `F_1 … F_{log n}` (`F_0 = e` implicit, replaces the `F(0) = e` check);
5. squeeze `α`; `β⃗* = β⃗ + α·δ⃗`;
6. prover writes `K_0 … K_{d_total − 2}`;
7. squeeze `γ` (truncated to 128 bits under `truncated-challenges`);
8. `e' = F(α)·(1 − γ) + γ(γ − 1)·K(γ)`; commitments, PI and challenges `acc + γ·(fresh − acc)`.

The vk is not absorbed: it is fixed for the whole IVC (the step circuit pins it, e.g. via
`vk_repr` in its PI); the fresh instance's own transcript starts with it.

**Prover per round**: `fᵢ(acc)` over `H` (Lagrange, B.1 evaluator), `F` by the `O(n)` tree; then
`G(x) = Σᵢ powᵢ(β⃗*)·fᵢ(fold(acc, fresh, x))` at `x = 2..d_total` and `K` interpolated from
`K(x) = (G(x) − F(α)(1 − x))/(x(x − 1))` (`G(0) = F(α)` and `G(1) = 0` are the other two of the
`d_total + 1` points); finally the trace is folded at `γ`. That is `d_total` row evaluations and
`d_total` trace folds per round, no FFT, no MSM. `debug_assert!(F(0) == e)`; debug builds also
evaluate `G` on `0..=d_total + 1` and assert the degree-`(d_total + 1)` coefficient vanishes
(checked to fire with `d_total − 1`).

**`d_total`** (`folding_degree`, computed once from the constraint system): per identity, its
degree in all folded variables (advice and instance values, `θ⃗, β, γ, trash`; fixed columns and
selectors are constants), plus 1 for `y_k`; max over identities. Gates: expression degree;
permutation: `1 + |chunk|`; logup helper: `1 + Σ_inputs (1 + deg)` (each compressed input
`Σ θᵢeᵢ + β` has degree `1 + max deg eᵢ`), accumulator `(1 + deg s) + (1 + deg t)`; trash: Horner
in `trash`, `max_j (m − 1 − j + deg e_j)`.

**Decider** (grand sum, plan C.1 revised): prover commits `S` (after `β⃗`, `e` are absorbed) with
`S(ω⁰) = 0`, `S(ω^{i+1}) = S(ωⁱ) + W(ωⁱ)·f(ωⁱ)`, `W = Σᵢ powᵢ(β⃗)·Lᵢ`, and proves on all of `H`
(true `L₀`, `L_{n−1}`): `L₀·S = 0` and `S(ωX) − S(X) − W(X)·f(X) + e·L_{n−1}(X) = 0`, combined
with a fresh `ζ`; quotient on a domain built for `cs.degree() + 1` (`cs.degree()` limbs, one
more than a plonk proof); opened with the PCS multi-open together with `S` at `x` and `ωx`.
Transcript: vk, accumulator (as in folding), `[S]`, `ζ`, quotient limbs, `x`, phase-0/1/2
evaluations, `S(x)`, `S(ωx)`, multi-open. Verifier: `f(x)` from the openings with the folded
challenges (`evaluate_identities`), `W(x)`, `L₀(x)`, `L_{n−1}(x)` natively in `O(n)` (barycentric,
one batch inversion of `n` elements), no MSM beyond the PCS.

### How to reproduce
From the repo root:
```
cargo test --release -p midnight-proofs --lib protogalaxy             # 8 tests (KZG + fflonk T_MAX = 8)
cargo test -p midnight-proofs --lib protogalaxy                       # debug: F(0) = e, degree check
cargo test --release -p midnight-proofs --lib fold_timings -- --ignored --nocapture   # k = 14
cargo build --release --workspace --examples
cargo test --release -p midnight-proofs
cargo test --release -p midnight-circuits verifier
cargo test --release -p midnight-zk-stdlib --no-fail-fast
cd aggregation && /usr/bin/time -l cargo run --release --features truncated-challenges --example ivc
```
`d_total` of the IVC circuit: a throw-away example (not committed) calling
`folding_degree` on `ZkStdLib::configure(cs, (arch, 16))` with the `examples/ivc` arch
(`poseidon`, `bls12_381`, 9 arith cols, 8 pow2range cols).

### Results
Test circuit (`tests.rs`): `b = a²` gate, `a ∈ [1, 16]` lookup, `b₀` copied to a public input,
16 used rows; instance `i` uses a shifted witness. `fold_chain`: init with instance 0, fold
instances 1–4, at every step assert prover and verifier accumulators equal (commitments, PI,
challenges, `β⃗`, `e`), `fᵢ = 0` on every row of `H` for each honest fresh instance, and
`e' = Σᵢ powᵢ(β⃗*)·fᵢ(ω')` recomputed from the folded trace; then decider prove + verify.

| Test | KZG | fflonk `T_MAX = 8` |
|---|---|---|
| 4 folds + decider (k = 6) | verifies | verifies |
| last fresh instance with one wrong `b` (gate broken on one row) | decider rejects | decider rejects |
| decider on the init accumulator / with `e + 1` | accepts / rejects | accepts / rejects |
| debug build (asserts `F(0) = e` and `deg G ≤ d_total`) | ok | ok |
| degree check with `d_total − 1` (manual sanity, not committed) | fires | – |

Suite: workspace build ok; `midnight-proofs` ok (lib 60 + 1 ignored, plonk_api 3, adversarial 9,
vk_serialization 2, doc 1); `midnight-circuits verifier` ok (3); `midnight-zk-stdlib` known failures
only (`check_vk_cred_enrollment`, `check_vk_cred_full`: no 2^20 SRS; `public_inputs_test`: cost model
vs fflonk, B.2); no goldenfile/VK changed (`CHANGE_VK` not needed). `examples/ivc`
(truncated-challenges, K = 17): all 10 steps verify, step 0 prove 95.8 s, steps 1–9 7.5–10.4 s,
verify 15–66 ms, peak RSS 3.04 GB, 427 s total (contended).

`d_total`: test circuit **4**; IVC circuit (`cs.degree() = 5`, `nb_y = 50`) **13**:

| identity group | folded degree (+1 for `y`) |
|---|---|
| gates | ≤ 3 (4) |
| permutation sets (3 columns per chunk) | 4 (5) |
| logup helper, chunk of 4 inputs of degree 1 (tuple `(tag, value)`) | `1 + 4·(1 + 1)` = 9 (10) |
| trash, Horner over 8 expressions of degree 5 | `7 + 5` = 12 (**13**) |

Per-fold prover, test circuit at k = 14 (2^14 rows, 2 advice columns; mean of 4 folds; **contended**,
load average 10–18):

| | KZG | fflonk `T_MAX = 8` |
|---|---|---|
| commit instance (synthesis + phase-1/2 commits) | 16.5 ms | 19.6 ms |
| fold (prover), total | 24.2 ms | 21.9 ms |
| — one `evaluate_rows` (×`d_total` = 4 per fold) | 3.7 ms | 3.5 ms |
| — one `fold_trace` (×4 per fold) | 1.0 ms | 0.9 ms |
| — rest (perturbator, `pow`, interpolation) | ≈ 5 ms | ≈ 4 ms |
| fold (native verifier) | 0.72 ms | 0.29 ms |
| decider prove / verify | 211 ms / 5.1 ms | 319 ms / 4.8 ms |
| decider proof size | 952 B | 1,112 B |

### Interpretation
- Prover and verifier agree by construction (both fold the public data with `fold_public`), and the
  tests show the protocol is complete over 4 rounds with a non-trivial lookup, copy constraint and
  public input, for both PCS, and that a single wrong witness cell in a fresh instance is caught by the
  decider (the folding verifier itself cannot detect it, as expected).
- A fold costs `d_total` full row evaluations plus `d_total` trace copies, with no FFT and no MSM: at
  k = 14 for this tiny circuit it is about 1.5× the commit phases. For the IVC circuit the commit phases
  (17 + 12 polynomials, MSMs) dominate more, but the evaluation count is **13**, not the ≈ 8 assumed in
  C.0. The in-circuit effect is small (5 more `K` coefficients, ≈ 60 rows); the prover effect is ~1.6×
  more identity evaluations per fold than assumed.
- `d_total = 13` comes from folding the challenges: the trash identity is Horner in the scalar trash
  challenge (degree 7 in it), and each logup input factor `(Σθᵢeᵢ + β)` has degree 2 in folded variables
  instead of 1 in plonk. Cheapest fixes (Phase D, not done): a vector trash challenge (one per
  expression, like `θ⃗`/`y⃗`; trash → 6, `d_total` → 10, then logup dominates), and/or smaller logup
  chunks for the folding circuit (helper degree `1 + 2·inputs`).
- Decider: grand sum needs no degree bound, so it inherits plonk's soundness argument (quotient check at
  random `x`); its only extra costs are one committed column, one quotient limb and an `O(n)` field loop
  in the verifier (5 ms at k = 14 including the PCS check).

### Deviations from the plan, open problems
- Decider identities written as two instead of three: `S(ωX) − S − W·f + e·L_{n−1} = 0` on all of `H`
  is exactly the plan's `(1 − L_{n−1})(S(ωX) − S − W·f)` and `L_{n−1}(S + W·f − e)` pair (at the last row
  `S(ω^n) = S(ω⁰) = 0`), and avoids multiplying `W·f` by a degree-`(n−1)` Lagrange polynomial (which would
  need two extra quotient limbs). `L₀·S = 0` kept. Same relation, no protocol change.
- `F_0` is not sent (set to `e`), equivalent to the verifier check `F(0) = e`.
- The prover computes `K` from `G` at `2..=d_total` only; `G(0) = F(α)` and `G(1) = 0` are implied
  (honest fresh instance). The degree check is a `debug_assertions` path (2 extra evaluations of `G`).
- Torsion/subgroup: natively, commitments are read with `from_compressed`, which rejects points outside
  the prime-order subgroup, so folded commitments stay in it. In-circuit (C.2) fresh commitments are
  assigned without subgroup check; the final native verifier must therefore subgroup-check (or decode
  via the transcript) the accumulator commitments it receives from the IVC before running the decider.
- The decider is not zero-knowledge (`S` unblinded; folded witness opened). The vk is not absorbed by
  the folding transcript (fixed for the IVC; the fresh transcripts start with it).
- Committed instances (`committed-instances` feature) are not supported by folding (0 passed through).
- `ProverAccumulator` keeps both the folded trace and the public accumulator (challenges and PI are
  duplicated; both folded with the same `γ`).
