# Plan: multi-instance (same-circuit) proving via batched multiopen

**Status:** Engineering plan / design only — no code changed by this document.
**Goal:** Extend the `midnight-proofs` PLONK prover/verifier so a single proof can cover **K instances of one circuit** sharing one proving key, with all polynomial openings batched into one KZG multiopen. This is the true "Option (A)": it reduces per-proof overhead and total proof size **and** cuts prover work versus K independent proofs (unlike IVC aggregation, which adds prover work).
**Blast radius:** `proofs/src/plonk/{prover.rs, verifier.rs, evaluation.rs, mod.rs}`, `proofs/src/plonk/{permutation,logup,trash}/prover.rs`, the bench mirror `proofs/src/plonk/bench/prover.rs`, and the `zk_stdlib` wrappers (`zk_stdlib/src/interface.rs`, `utils/plonk_api.rs`).

> ⚠️ **Soundness-critical.** This modifies the core proving protocol. Every step below must be reviewed by a cryptographer and validated with adversarial tests before merge. A passing round-trip test does **not** establish soundness.

---

## 1. Why this is not just "restore upstream halo2"

Upstream halo2 already supported multiple circuit instances (`create_proof(circuits: &[C], instances: &[&[&[F]]])` building `Vec<InstanceSingle>`/`Vec<AdviceSingle>`). This fork removed that **and** diverged in ways that make re-adding it non-mechanical:

- **Linearization-polynomial design.** The quotient is built via `evaluate_numerator` (`evaluation.rs`) + `partially_evaluate_identities` + `compute_linearization_poly` (`mod.rs`) over a *single* set of advice/instance cosets, and the proof opens one `lin_poly_non_constant_part`. Multi-instance means the numerator must accumulate every instance's gate/permutation/lookup contributions and the linearization polynomial must span all instances' committed polynomials. This is the crux and the highest-risk change.
- **Logup lookups** (`logup::prover`), not stock halo2 lookups — per-instance lookup sets, θ/β sharing.
- **Trash argument** (`trash::prover`) — per-instance.
- **Feature interactions:** `single-h-commitment`, `committed-instances`, `truncated-challenges`, `fewer-point-sets`.
- **Bench-prover mirror.** `proofs/src/plonk/bench/prover.rs` duplicates `compute_trace`/`finalise_proof`; the code comment requires it to stay in sync. Every prover change is done twice.

---

## 2. What is shared vs per-instance

Because all K instances use the **same circuit and proving key**, the split is:

| Data | Scope | Notes |
|---|---|---|
| `pk`, fixed columns, selectors, permutation `pk` cosets, `l0/l_last/l_active_row` | shared | committed once; opened once |
| Challenges θ, β, γ, y, x | shared | one Fiat–Shamir transcript |
| Instance columns (`InstanceSingle`) | per-instance | `Vec<InstanceSingle>` |
| Advice columns (`AdviceSingle`) | per-instance | each circuit synthesized separately |
| Logup lookups, permutation product, trash | per-instance | one set per instance |
| Quotient numerator ν(X) | combined | sum of per-instance identities under shared y |
| Linearization poly | combined | one poly spanning all instances |
| Multiopen queries | union | all instances' advice/instance/perm/lookup + shared fixed/perm-pk + one linearization |

Blinding must be sampled **independently per instance** (no reuse across instances), or zero-knowledge breaks.

---

## 3. Prover change map (`proofs/src/plonk/prover.rs`)

### 3.1 Public API

```rust
pub fn create_proof<F, CS, T, C: Circuit<F>>(
    params, pk,
    circuits: &[C],                 // was: circuit: &C
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[&[F]]],          // was: &[&[F]]  (outer = per instance)
    transcript, rng,
) -> Result<(), Error>
```

`K == 1` must reduce to exactly today's transcript layout (byte-for-byte) so existing proofs/keys stay valid — enforce with a golden test.

### 3.2 `compute_trace`

- Validate all K instances against `pk.vk.cs.num_instance_columns`.
- Hash `pk.vk` into the transcript **once** (unchanged).
- Build `Vec<InstanceSingle>` via `compute_instances` per instance.
- Build `Vec<AdviceSingle>` via `parse_advices` per circuit. **Write every instance's advice commitments to the transcript before squeezing θ.** (Ordering is soundness-critical — see §5.)
- Logup: for each instance compute multiplicities (θ shared), write all commitments, then squeeze β, γ.
- Permutation: `permutation.compute` per instance; write all; interleave with logup exactly as today (permutation commitments first, then logup).
- Trash: per instance, after `trash_challenge`.
- Return a `ProverTrace` holding `Vec<AdviceSingle>`, `Vec<InstanceSingle>`, and per-instance `lookups`/`permutations`/`trashcans`, plus the shared challenges.

### 3.3 Quotient / numerator (`evaluate_numerator`, `evaluation.rs`) — the crux

`evaluate_numerator` currently takes one `advice`/`instance` slice and returns one numerator. Change to accumulate across instances:

- Loop over instances; for each, evaluate custom gates, permutation, logup, trash contributions into the running numerator.
- Preserve the existing per-identity y-powering. Decide the **cross-instance separation**: either (a) reuse the same y across instances relying on the permutation/lookup arguments being independent per instance (matches upstream halo2, where each instance's constraints are folded under the same y schedule but over disjoint committed polys), or (b) introduce explicit per-instance y-offsets. Option (a) is standard; (b) is a deviation requiring its own soundness argument. **Pick (a) unless review says otherwise.**
- `compute_h_poly` is unchanged: it divides the (now combined) numerator by the vanishing poly. Confirm the numerator degree with K instances still fits the domain / `single-h-commitment` SRS bound (`g_monomial_size`).

### 3.4 Linearization + evals + queries (`finalise_proof`)

- `write_evals_to_transcript`: emit advice/instance evals **per instance** (canonical order: instance 0 advice evals, instance 1 advice evals, …), fixed evals once.
- `partially_evaluate_identities` / `compute_linearization_poly`: extend to consume per-instance evals and produce one linearization poly covering all instances (the constant/non-constant split stays; the debug identity `L'(x) == -C` must still hold).
- `compute_queries`: chain per-instance advice/instance/permutation/lookup/trash queries, then shared fixed + permutation-pk queries, then the single linearization query.
- `CS::multi_open` over the combined query set — this is where the KZG batching win materializes (all openings share one random linear combination).

### 3.5 Blinding

`sample_blindings` must produce independent blinding vectors per instance for advice, lookup multiplicities, permutation, and logup. Audit every `F::random` site for accidental cross-instance reuse.

---

## 4. Verifier change map (`proofs/src/plonk/verifier.rs`)

Mirror the prover. `prepare` / `verify_algebraic_constraints` currently take `instances: &[&[F]]` and one advice-commitment vector.

- Signature → `instances: &[&[&[F]]]` (+ per-instance committed-instance commitments).
- Read K advice-commitment sets and hash them before θ (same order as prover).
- Read per-instance evals in the same canonical order.
- Reconstruct the combined algebraic identity across instances (mirror §3.3's choice exactly).
- Feed all instances' queries into the same dual-MSM / multiopen check (`prepare` returns a `Guard`/dual-MSM that the caller batch-checks — one pairing check total).

The `batch_verify` path in `zk_stdlib` already batches *separate* proofs; here we additionally batch *within* one proof. Keep both.

---

## 5. Fiat–Shamir transcript ordering (soundness-critical spec)

The single shared transcript must be written/squeezed in exactly this order; prover and verifier must agree:

1. `vk` hash (once).
2. Committed-instance commitments, all instances, in instance order (if feature on).
3. All instances' advice commitments (instance-major).
4. squeeze **θ**.
5. All instances' logup multiplicity commitments.
6. squeeze **β**, then **γ**.
7. All instances' permutation-product commitments, then all instances' logup helper/aggregator commitments (preserve the current permutation-before-logup order, extended across instances).
8. squeeze **trash_challenge**; all instances' trash commitments.
9. squeeze **y**.
10. quotient commitment(s) (`compute_h_poly`).
11. squeeze **x**.
12. per-instance instance/advice evals, then fixed evals, then permutation-common, per-instance permutation/lookup/trash evals.
13. multiopen.

Any reordering silently changes the protocol and can break soundness — lock this down first and test the K=1 path byte-for-byte against current output.

---

## 6. `zk_stdlib` layer

- `interface.rs`: add a real batched prover that calls the multi-instance `create_proof` once and returns a **single** `Vec<u8>`:
  ```rust
  pub fn prove_batch<R: Relation, H>(params, pk, relation, instances: &[R::Instance], witnesses: Vec<R::Witness>, rng) -> Result<Vec<u8>, R::Error>
  ```
  This *replaces* the current `batch_prove` semantics (which returns `Vec<Vec<u8>>` — parallel independent proofs, not aggregation). Keep the old one under a clear name (`prove_each_parallel`) or remove it.
- Add the matching `verify_batch` that checks one proof against K instances.
- `BlstPLONK::prove`/`verify` (`utils/plonk_api.rs`) forward the new `circuits`/`instances` shapes.
- `MidnightCircuit` construction: build K circuits sharing the `pk`; `nb_public_inputs` bookkeeping must be per-instance-consistent (it's identical across instances since same circuit).

---

## 7. Constraints and limits

- **Same circuit, same `k`, same pk** — this is the defining restriction (that's what makes it Option A, not B).
- **PI / degree budget:** each instance contributes its own public inputs; confirm the combined proof still respects `VERIFIER_MAX_DEGREE`-class limits on the consumer side and that the numerator degree fits the domain (and the `single-h-commitment` SRS bound).
- **Bench mirror:** replicate all prover changes in `proofs/src/plonk/bench/prover.rs`.
- **Feature matrix:** exercise `truncated-challenges`, `committed-instances`, `single-h-commitment`, `fewer-point-sets` in every combination the production stack ships.

---

## 8. Testing and soundness validation

Ordered by increasing assurance:

1. **K=1 golden test:** multi-instance path with K=1 produces byte-identical transcript/proof to the current single-instance `create_proof`. Guards backward compatibility.
2. **Round-trip:** K∈{2,3,8} instances of a real circuit → one proof → `verify_batch` passes; proof size sublinear in K vs K separate proofs.
3. **Cross-instance soundness (negative):** tamper one instance's witness/public input → verification must fail. Swap two instances' evals → fail. Reuse instance 0's advice for instance 1 → fail.
4. **Blinding/ZK:** statistically check no cross-instance blinding reuse (independent transcripts across randomness seeds).
5. **Differential:** verify a multi-instance proof rejects if any single-instance sub-proof would have been invalid.
6. **Property tests** over random circuits/instance counts, all feature combinations.
7. **Bench mirror parity** test.
8. **Mandatory external review:** a cryptographer signs off on §3.3 (numerator aggregation), §4, and §5 (transcript order) before merge; ideally an independent re-derivation of the multi-instance soundness argument.

---

## 9. Risks

- **Numerator/linearization aggregation (§3.3)** is the highest risk: getting the cross-instance combination or y-schedule wrong can be unsound while still verifying on honest inputs.
- **Transcript ordering (§5)** — silent soundness breakage if prover/verifier diverge.
- **Feature-flag combinatorics** — `single-h-commitment` + `committed-instances` + `truncated-challenges` interactions.
- **Bench-mirror drift.**
- **Downstream:** consumers (`zkir`, ledger) still need a transaction-format change to carry one proof per repeated-circuit group; that is separate work (see the ledger integration design), but note this path *reduces* prover CPU where aggregation increases it.

---

## 10. Sequencing

1. Lock the transcript-ordering spec (§5) and the K=1 golden test harness.
2. Prover: `compute_trace` → `Vec<AdviceSingle>/Vec<InstanceSingle>` + commitment ordering (§3.2). Keep numerator single-instance behind a temporary assert(K==1) to isolate.
3. Verifier mirror for the K=1 path; confirm byte-identical.
4. Numerator + linearization aggregation (§3.3/§3.4) for K>1 — the crux; pair-programmed / reviewed.
5. Verifier K>1; negative tests (§8.3).
6. Feature-matrix + bench mirror + property tests.
7. `zk_stdlib` `prove_batch`/`verify_batch`; deprecate/rename the misleading `batch_prove`.
8. External cryptographer review, then downstream wiring.

The cryptography is well-understood in principle (this is how upstream halo2 multi-instance works); the cost and risk are concentrated in the fork's linearization design (§3.3) and the transcript discipline (§5).
