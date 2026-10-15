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
