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
