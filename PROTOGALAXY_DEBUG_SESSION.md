# Protogalaxy Debug Session — State as of 2026-05-15

## Goal
Make `aggregation/examples/protogalaxy.rs` pass end-to-end: fold 4 SHA-256 preimage proofs into a single accumulator, then verify. Final `.verify()` call fails with `OpeningError`.

## Repository / Branch
Branch: `iquerejeta/protogalaxy`
Working directory: `/Users/queremendi/iohk/midnight/midnight-zk`
Run example from `zk_stdlib/` directory (SRS assets live there).

---

## Architecture Summary

The proof is in `proofs/src/plonk/protogalaxy/`:
- `prover.rs` — `ProtogalaxyProver::fold()`, `finalise_folded_proof()`
- `verifier.rs` — `ProtogalaxyVerifier::fold()`, `verify_folded()`
- `utils.rs` — `batch_traces`, `fold_traces`, `linear_combination`, `FoldingProverTrace`, `FoldingLogupTrace`

Key support in `proofs/src/plonk/`:
- `evaluation.rs` — `evaluate_numerator::<B>` (LagrangeCoeff or ExtendedLagrangeCoeff)
- `linearization/prover.rs` — `compute_linearization_poly`
- `linearization/verifier.rs` — `compute_linearization_commitment`
- `poly/domain.rs` — `EvaluationDomain`, `coeff_to_extended`, `extended_to_coeff`, `lagrange_to_coeff`, `extended_to_lagrange`

---

## The Protocol (what we're implementing)

**Protogalaxy folding of k=NB_FOLDED=4 PLONK instances:**

1. Compute k standard PLONK traces (advice, perm, logup, trash polys)
2. Sample beta_pg (the "evaluation beta" challenge)
3. Precompute l0_lag, l_last_lag, l_active_lag, perm_pk_lag in LagrangeCoeff form
4. Create dk_domain = `EvaluationDomain::new(cs.degree()=6, NB_FOLDED.trailing_zeros()=2)` → n=4, ext_len=32
5. `batch_traces`: lift traces to dk-ext coset domain
6. For each dk-ext coset point t: `g_unbatched[t][j] = nu(lifted[t])(ω^j)` via `evaluate_numerator::<LagrangeCoeff>`
7. Compute G(X) = Σ_j beta_coeff[j] * G_j(X), K = G / Z_dk, commit K
8. Sample gamma (folding challenge), write K(gamma) to transcript
9. Compute error_terms[j] = G_j(gamma) via IFFT from dk-ext coset values + eval_polynomial
10. Fold traces: `folded = fold_traces(dk_domain, traces, gamma)` = Σ L_i(gamma) * traces[i]
11. Commit error polynomial E (Lagrange form, E[j] = error_terms[j])
12. Run finalise_folded_proof: computes h = (nu_folded - E) / Z_n, does standard PLONK proof

**Mathematical invariants that must hold:**
- `E[j] = G_j(gamma) = nu(trace(gamma))(ω^j) = nu_folded[j]` ← **THIS FAILS**
- `E(beta_pg) = Z_dk(gamma) * K(gamma)` (checked in SHPLONK)
- `lin_poly(x) = -C + E(x)` (linearization check)

---

## Key Data Structures

**`FoldingProverTrace<F>`** (in `utils.rs`):
- `advice_polys: Vec<Polynomial<F, LagrangeCoeff>>` — n values each
- `instance_polys: Vec<Polynomial<F, LagrangeCoeff>>`
- `lookups: Vec<FoldingLogupTrace<F>>` — logup polys in Coeff form
- `trash_polys: Vec<Polynomial<F, Coeff>>`
- `perm_polys: Vec<Polynomial<F, Coeff>>` — permutation product polys
- `challenges: Vec<F>`, `beta: F`, `gamma: F`, `theta: Vec<F>`, `trash_challenge: F`, `y: Vec<F>` (all scalar challenges)

Implements `Add<&FoldingProverTrace>` and `Mul<F>` (component-wise), used in `linear_combination`.

---

## What's Been Implemented

All the infrastructure is in place:
- `into_folding_trace`: converts ProverTrace → FoldingProverTrace (advice to LagrangeCoeff, rest in Coeff)
- `batch_traces` + `fold_traces`: correct Lagrange interpolation on dk-domain
- `linear_combination`: Horner's method for `Σ s_i * e_i` (algebraically verified correct)
- `FoldingProverTrace` Add + Mul correctly fold all components
- Verifier `fold_verifier_traces`: folds commitments + challenges at gamma
- Verifier `verify_folded`: runs PLONK verification with error correction

All code compiles and runs; the failure is purely mathematical.

---

## Root Cause Investigation

### Primary failure
`E[j] ≠ nu_folded[j]` for **1725 / 8192** rows (rows 24+ in SHA-256, where actual computation starts).

Where:
- `E[j] = error_terms[j]` = G_j(gamma) computed via IFFT from dk-ext coset evaluations
- `nu_folded[j]` = `nu(folded)(ω^j)` = direct evaluation of constraint at row j on folded trace

### Chain of consequences
1. `E[j] ≠ nu_folded[j]` → `nu_folded - E` has nonzero values at circuit rows
2. `(nu_folded - E)` is NOT divisible by Z_n (circuit vanishing poly)
3. `h = (nu_folded - E) / Z_n` is "wrong" (division has remainder R)
4. Prover's linearization poly: `lin_poly(x) = -C + E(x) + R(x)` (extra remainder term)
5. Verifier expects `lin_com.eval = -C + E(x)` (no remainder)
6. Mismatch → SHPLONK opening fails → `OpeningError`

### Debug diagnostics added (Steps 9-10 of prover.rs)

All added as a `// DEBUG` block in `ProtogalaxyProver::fold()`:

1. **L0 roundtrip check** (before Step 5): `coeff → ext → coeff → eval_polynomial(beta_pg)` — **PASSES** ✓
2. **Mismatch count**: 1725/8192 rows
3. **First mismatch j=24**:
   - `g_unbatched[0][j] = 0x4d53...` (constraint at dk-ext coset pt 0)
   - `G_j(coset_0) = 0x4d53...` ← matches (VACUOUS — IFFT reproduces input)
   - `E[j] = 0x5d91...` (IFFT + eval at gamma)
   - `nu_folded[j] = 0x41ff...` (direct eval — **DIFFERENT**)
4. **G_j at natural dk-domain points** (newly added):
   - `G_j(omega_dk^0) = G_j(1) = 0x4423... ≠ 0` ← **SHOULD BE ZERO for valid instances!**
   - `G_j(omega_dk^1,2,3)` also non-zero
5. **nu(traces[0])(omega^24) = 0** ← instances ARE valid ✓
6. **Advice consistency**: `folded.advice[0][j] == Σ L_i(gamma) * traces[i].advice[0][j]` — **PASSES** ✓

---

## Current Hypothesis: Pruned FFT Bug

**The key contradiction:**
- `nu(traces[0])(omega^j) = 0` (valid instance) → G_j(omega_dk^0 = 1) should be 0
- But IFFT-recovered polynomial evaluates to non-zero at 1

Since advice folding is correct, and degree analysis says G_j has degree ≤ 18 < ext_len=32 (so aliasing shouldn't occur), the most likely cause is:

**`coeff_to_extended` in `batch_traces` is producing WRONG coset evaluations.**

The `coeff_to_extended` function uses a specialized **pruned DIF FFT** (`fft_coeff_to_extended`) for efficiency:

```rust
pub fn coeff_to_extended(&self, mut a: Polynomial<F, Coeff>) -> Polynomial<F, ExtendedLagrangeCoeff> {
    let n_real = a.values.len();  // = 4 for dk_domain
    self.distribute_powers_zeta(&mut a.values, true);
    a.values.resize(self.extended_len(), F::ZERO);
    fft_coeff_to_extended(
        &mut a.values,
        &self.twiddles.extended_omega,
        self.extended_k,
        n_real,  // = 4 ← exploits zero-padding structure
    );
}
```

The standard IFFT in `extended_to_coeff` is correct (L0 roundtrip passes). But `fft_coeff_to_extended` is a DIFFERENT function from the standard FFT. If it has a bug for small `n_real` (like 4) relative to the extended domain (32), the coset evaluations `L_i(ZETA * omega_ext^t)` could be wrong. This would cascade to wrong `lifted[t]` → wrong `g_unbatched[t][j]` → wrong IFFT output.

**BUT WAIT**: The L0 roundtrip check (`coeff_to_extended → extended_to_coeff → eval_polynomial`) passes. This means `fft_coeff_to_extended` → IFFT is internally consistent. However, it doesn't prove that `fft_coeff_to_extended` gives the MATHEMATICALLY CORRECT coset evaluations.

### Alternative hypothesis: degree analysis is wrong

The degree of G_j in the folding variable X could exceed 18 if:
- `theta` challenges (multiple) get multiplied together: `theta_0(X) * theta_1(X) * ... * advice(X)` 
- OR challenges combine in unexpected ways

**LogUp constraint analysis**: If the SHA-256 circuit has a lookup constraint where theta appears multiple times multiplied (e.g., `theta_0 * theta_1 * advice` as degree-9 in X), and then multiplied by z_agg (degree 3) etc., the total could approach 9+3=12 or higher for complex constraints. However, cs.degree()=6 bounds the circuit-variable degree, and each polynomial-in-Z factor contributes degree 3 in X, so max degree = 6*3=18.

**UNLESS** cs.degree() counts challenges differently. Need to verify.

---

## How the Verifier Works (for fixing context)

The verifier:
1. Reads K_commitment (no check)
2. Squeezes gamma
3. Reads K(gamma) from transcript
4. Computes `z_dk_at_gamma * K(gamma)` = expected `E(beta_pg)` value
5. Folds verifier traces at gamma (linear combination of commitments)
6. Reads E_commitment
7. Runs standard PLONK verification with folded commitments
8. Adds E(x) to lin_com.eval: `lin_com.eval += error_at_x`
9. Adds SHPLONK query: E at x (expected = error_at_x) and E at beta_pg (expected = z_dk*K_gamma)

---

## Prover's finalise_folded_proof (why lin_poly(x) is wrong)

The prover:
```rust
let nu = compute_nu_poly(pk, &trace);  // ExtendedLagrangeCoeff form of nu(folded)
let error_ext = domain.coeff_to_extended(error_coeff.clone());  // E in extended form
let nu_corrected = nu - &error_ext;  // Should be divisible by Z_n IF E=nu_folded pointwise
let quotient_limbs = compute_h_poly(params, domain, nu_corrected, transcript)?;
// ... compute expressions (partially evaluated identities) ...
let (lin_poly_non_constant_part, constant_term) = compute_linearization_poly(
    expressions, pk, &y, xn, splitting_factor, quotient_limbs
);
```

If `nu_corrected = nu - E` is NOT divisible by Z_n (because E ≠ nu_folded), then the quotient h is computed with a remainder R, and lin_poly(x) = -C + E(x) + R(x) ≠ -C + E(x).

---

## Debug Printouts (currently in code)

### prover.rs `ProtogalaxyProver::fold()`, Steps 4-5 region:
```
[DEBUG] L0 direct / L0 roundtrip / L0 roundtrip match
```

### prover.rs between Steps 9 and 10:
```
[DEBUG] E[j]==nu_folded[j] mismatches: N/8192 rows
[DEBUG] j=24: g_unbatched[0][j]
[DEBUG] j=24: G_j(coset_0) from coeff / coset0 eval match
[DEBUG] j=24: E[j] (interp) / nu_folded[j]
[DEBUG] j=24: G_j(omega_dk^0..3) (4 natural dk points, should be 0 for valid instances)
[DEBUG] j=24: nu(traces[0])(omega^j) / is_zero (should be true)
[DEBUG] j=24: folded.advice[0][j] / expected Σ L_i*a_i[j] / advice consistency
```

### prover.rs `finalise_folded_proof()`:
```
[PROVER] beta/gamma/trash_challenge/y[0]/instance_evals
[PROVER] lin_poly(x) / error_at_x / error_at_beta_pg / constant_term / -constant_term / lin_poly(x)+E(x)
[PROVER] total queries
```

### verifier.rs `verify_folded()`:
```
[VERIFIER] beta/gamma/trash_challenge/y[0]/instance_evals (should match prover's)
[VERIFIER] lin_com.eval (before/after +E(x)) / error_at_x / e_at_beta_pg / total queries
```

---

## Immediate Next Investigation Steps

### Step 1: Verify fft_coeff_to_extended vs standard FFT

Add a check in the debug block: take L_0's coefficient form, compute `coeff_to_extended(L_0_coeff)` (pruned FFT path) and also manually compute `L_0(ZETA * omega_ext^t)` by evaluating the polynomial. Compare.

If they differ → pruned FFT is wrong.

### Step 2: Verify coset evaluations of L_0

Add: for i=0, manually evaluate `L_0(ZETA * omega_ext^t)` for t=0..3 using `eval_polynomial` on L_0_coeff, and compare to `lagrange_polys[0].values[0..3]`.

If they differ → `fft_coeff_to_extended` is wrong.

### Step 3: Alternative — bypass batch_traces for G_j

Instead of going through `batch_traces` (which uses `coeff_to_extended`), compute G_j(gamma) DIRECTLY:
- Evaluate Lagrange basis L_i(gamma) using `eval_polynomial` for each i
- Compute `gamma_trace = linear_combination(buf, traces, L_at_gamma)` (same as fold_traces)
- `E[j] = nu(gamma_trace)(omega^j)` = nu_folded[j] (by definition, same as fold_traces)

This BYPASSES the dk-ext evaluation and goes directly to gamma. But this would make E[j] = nu_folded[j] by construction, fixing the mismatch.

HOWEVER: this means E[j] ≠ G_j(gamma) (in our current system), which means the SHPLONK check for E at beta_pg would fail. UNLESS we also recompute K correctly.

Wait, actually: if we use E[j] = nu_folded[j] directly, and nu_folded[j] = G_j(gamma) by MATHEMATICAL DEFINITION, then they should be equal. If they differ, there's a bug in either E computation OR nu_folded computation.

The fact that `G_j(1) ≠ 0` from IFFT suggests the IFFT-path gives wrong G_j(gamma). The direct path (nu_folded) should give the CORRECT G_j(gamma).

**So Option A (use nu_folded directly as E) would be MATHEMATICALLY CORRECT**, provided the G_j POLYNOMIAL is correctly computed elsewhere (for K=G/Z_dk). The K computation uses the g_poly array (dot product with beta_coeffs), not the IFFT path. So K might still be correct.

Let me verify: if we use E[j] = nu_folded[j] and the K commitment is still computed from g_poly (which uses the BATCHED g_unbatched values), will the SHPLONK check E(beta_pg) = Z_dk(gamma) * K(gamma) pass?

For this to pass: `E(beta_pg) = sum_j L_j(beta_pg) * nu_folded[j]` must equal `Z_dk(gamma) * K(gamma) = G(gamma)`.

`G(gamma) = sum_j beta_coeff[j] * G_j(gamma) = sum_j L_j(beta_pg) * G_j(gamma)`.

If `nu_folded[j] = G_j(gamma)`: `E(beta_pg) = sum_j L_j(beta_pg) * G_j(gamma) = G(gamma)`. ✓

So Option A IS correct if `nu_folded[j] = G_j(gamma)`, which is what SHOULD be true. The issue is that our IFFT path gives wrong G_j(gamma), but the direct path (nu_folded) should give the correct value.

### Recommended Fix: Option A

Replace error_terms computation in Step 8 with:
```rust
// Instead of IFFT-based G_j(gamma):
let error_terms: Vec<F> = nu_folded.values.clone();
```

Where `nu_folded` is already computed in the DEBUG block. But this requires restructuring the code slightly (compute nu_folded BEFORE committing to E, not just for debugging).

**But wait**: `nu_folded` is computed in the DEBUG block AFTER Step 9 (fold_traces). We need E BEFORE committing in Step 10. And fold_traces happens at Step 9, after E is already committed. Let me re-check the step order...

Looking at the prover code:
- Step 8: compute error_terms
- Step 9: `folded = fold_traces(...)`
- Step 10: `error_lagrange = Polynomial { values: error_terms }; commit(error_lagrange)`

So fold_traces (Step 9) happens BEFORE committing E (Step 10). Therefore we CAN compute E from folded:
```rust
// Step 9: fold traces
let folded = fold_traces(&dk_domain, &traces_refs, &gamma);

// New Step 9.5: compute E directly from nu(folded)
let error_terms = compute_nu_lagrange(pk, &folded, &l0_lag, ...);  // returns Vec<F>

// Step 10: commit E
```

This requires computing `evaluate_numerator::<LagrangeCoeff>` on the folded trace, which we're already doing in the DEBUG block.

---

## Files to Focus On

- **`proofs/src/plonk/protogalaxy/prover.rs`**: Main file with all the logic. Has debug blocks. ~600 lines.
- **`proofs/src/plonk/protogalaxy/utils.rs`**: batch_traces, fold_traces, linear_combination. ~290 lines.
- **`proofs/src/plonk/protogalaxy/verifier.rs`**: Verifier. ~500 lines.
- **`proofs/src/poly/domain.rs`**: EvaluationDomain with fft_coeff_to_extended, extended_to_coeff. Look for `fft_coeff_to_extended` function.
- **`proofs/src/plonk/evaluation.rs`**: evaluate_numerator. Large file (~1400 lines).
- **`aggregation/examples/protogalaxy.rs`**: Test harness.
- **`aggregation/examples/circuits/sha_preimage.rs`**: The circuit being folded.

---

## Concrete Next Steps (priority order)

1. **Find `fft_coeff_to_extended`** in domain.rs or wherever it's defined. Check if it's equivalent to standard FFT or has a special correctness condition.

2. **Test Option A**: Replace `error_terms` computation with `nu_folded` values directly:
   - Move `nu_folded` computation to BEFORE Step 10 (it's already computing it after Step 9 in the DEBUG block, just restructure)
   - If this makes the SHPLONK pass for E@x and E@beta_pg, it confirms the IFFT path is wrong

3. **If Option A fixes the lin_poly mismatch but fails the beta_pg check**: the K polynomial (computed from g_poly in Step 7) is inconsistent with E. Need to recompute K from the corrected E values.

4. **If Option A works end-to-end**: clean up all debug prints and commit.

---

## Observation About L0 Roundtrip

The L0 roundtrip check (`coeff_to_extended → extended_to_coeff → eval_polynomial`) passes. This only means the IFFT is the inverse of `fft_coeff_to_extended`. It does NOT verify that `fft_coeff_to_extended` gives CORRECT evaluations. Specifically:
- A buggy `fft_coeff_to_extended` that consistently applies some wrong transform could pass the roundtrip check (since `extended_to_coeff` undoes whatever `fft_coeff_to_extended` does, whether correct or not)
- To verify correctness, we need to compare `coeff_to_extended(L_0_coeff).values[t]` with manually computed `eval_polynomial(L_0_coeff, ZETA * omega_ext^t)` for some t.

---

## Running the Example

```bash
cd /Users/queremendi/iohk/midnight/midnight-zk/zk_stdlib
cargo run --example protogalaxy -p midnight-aggregation
```

---

## Resolution (2026-05-18)

### True Root Cause: Domain Aliasing

The initial hypothesis (pruned FFT bug in `fft_coeff_to_extended`) was **wrong**.

Three targeted debug checks were added to the prover:

| Check | Result |
|-------|--------|
| **A** `coeff_to_extended(L0)` matches `eval_polynomial(L0, coset_point_t)` at all 16 pts | ✓ PASS |
| **B** Partition of unity: `Σ_i L_i(coset_t) = 1` for all t | ✓ PASS |
| **C** K consistent with nu_folded: `Σ_j β_j·nu_folded[j] = Z_dk(γ)·K(γ)` | ✓ PASS |

The real bug: **`ext_len = 16`, but `degree(G_j) ≤ cs.degree()·(NB_FOLDED-1) = 6·3 = 18 > 15`**.

The 16-point IFFT cannot uniquely recover a degree-18 polynomial. It returns an *aliased* polynomial that:
- agrees with G_j on the 16 coset points (hence Check A passes)
- diverges from G_j everywhere else, including at γ

This explains `G_j(ω_dk^0) ≠ 0` from the IFFT path: the aliased polynomial has spurious non-zero evaluations at the dk-domain natural points, even though the true G_j vanishes there.

K is unaffected because `degree(K) = degree(G/Z_dk) ≤ 18 - 4 = 14 < 16` — no aliasing.

### Fix Applied (Option A)

Replace the IFFT-based `error_terms` computation with the direct identity:

```
G_j(γ) = nu(Σ_i L_i(γ)·traces[i])(ω^j) = nu(folded)(ω^j)
```

**Code change** in `ProtogalaxyProver::fold()`:
1. Move `fold_traces` before the error_terms computation (steps 8 and 9 swapped).
2. Compute `nu_folded = evaluate_numerator(folded)` directly.
3. `error_terms = nu_folded.values` — bypasses the IFFT path entirely.

The K commitment and SHPLONK check `E(β_pg) = Z_dk(γ)·K(γ)` remain valid (confirmed by Check C).

The old IFFT code is preserved as a comment in `prover.rs` with a note on the aliasing bug.
