//! Bundling policy for fflonk: how the polynomials in a `commit` call are
//! partitioned into sub-bundles of size `t ≤ T_MAX` each.
//!
//! ## The ordering invariant (load-bearing — read before modifying)
//!
//! `partition` is called from two places with **different input orderings**,
//! and both must produce the same per-bundle slot assignment for the protocol
//! to be sound:
//!
//! - [`commit`](super::FflonkScheme::commit) receives labels in the order
//!   the caller passes them (typically `Advice(0), Advice(1), …` for the
//!   advice phase — already canonical, but this isn't guaranteed by the
//!   trait).
//! - [`multi_open`](super::FflonkScheme::multi_open) receives the *distinct
//!   labels appearing in `queries`*, in first-occurrence order. Queries are
//!   emitted in the chain order of `compute_queries`, which doesn't
//!   necessarily match the canonical-key sort within any one family.
//!
//! If `partition` preserved input order, the two callers would build
//! different `g(X) = Σ_i X^i f_i(X^t)` polynomials (different slot ↔ label
//! mapping), the prover's commitment and the verifier's reconstruction
//! would disagree, and the proof would fail to verify on honest inputs.
//!
//! The fix: `partition` sorts each bundlable label family by a **canonical
//! key derived from the label value itself**. This makes `partition` a pure
//! function of the *set* of labels, invariant to the order they appear in
//! the input slice.
//!
//! ## What the partition output's ORDER does *not* affect
//!
//! The order in which sub-bundles are emitted (e.g., advice bundles before
//! permutation-accumulator bundles, or vice versa) used to leak into
//! `multi_open`'s singleton-collection loop, which iterated the partition
//! output to build `singleton_queries`. That made the prover-side
//! `commitment_map` order in `construct_intermediate_sets` depend on
//! `partition`'s family-emission order, while the verifier built its
//! `commitment_map` in natural query-emission order — divergence whenever
//! `partition` reordered across families.
//!
//! Resolved: `multi_open` now walks `queries` directly (in their natural
//! emission order) to build `singleton_queries`, mirroring the verifier's
//! `bundle_expansion::classify_verifier_queries`. The partition output is
//! consulted only to identify which labels live in a `t > 1` bundle (so
//! those queries flow through the bundle-expansion path instead). The
//! cross-family emission order in the partition output is therefore no
//! longer load-bearing — it remains deterministic for testability but is
//! a free parameter for adding new families.
//!
//! `T_MAX = 2^T_MAX_LOG` is the scheme-wide const generic of
//! [`FflonkScheme`](super::FflonkScheme), so both sides agree on `t_max`
//! without consulting the SRS. Any change to the partition strategy is a
//! *protocol-level* change (commitments produced differ) and must be
//! versioned together with VK updates.
//!
//! ## Bundling policy
//! - **Bundlable families** (`Advice`, `CommittedInstance`,
//!   `PermutationAccumulator`, `LogupHelper`, `LogupMultiplicities`,
//!   `LogupAggregator`) are grouped per-family, sorted by their family's
//!   canonical key (`usize` index for the numeric variants, lexicographic
//!   `String` for the named `Logup*` variants), and chunked into sub-bundles
//!   of size `≤ t_max`.
//! - **Non-bundlable labels** are committed as their own singleton
//!   sub-bundles (`t = 1`).
//!
//! ## Why `QuotientPiece` and simple-selector `Fixed` stay singletons
//!
//! Both feed `plonk::linearization::verifier::compute_linearization_commitment`,
//! which scalar-multiplies each commitment's group element individually:
//! `quotient_limb_commitments[k] * x^{k(n-1)}` for the quotient pieces,
//! and `vk.fixed_commitments[idx] * eval` for **simple-selector** columns
//! only (per `partially_evaluate_identities`'s `.filter(|s| s.is_simple())`
//! when populating the `Option<usize>` field). A multi-poly fflonk bundle
//! exposes only the combined group element
//! `[g(τ)]_1 = Σ_k τ^k h_k(τ^t)`, from which the individual `[h_k(τ)]_1`s
//! cannot be recovered. Bundling these without first rewriting linearization
//! would break soundness.
//!
//! Non-selector fixed columns (lookup tables, generic precomputed columns)
//! are *not* touched by linearization — they're opened through
//! `compute_queries`'s `fixed_queries` chain and could be bundled. That
//! lives at keygen time and is a separate workstream (it changes the VK
//! shape).
//!
//! ## `LogupHelper` labels
//!
//! `LogupHelper(name, chunk)` carries both the argument name and the
//! chunk index — every helper polynomial has a unique label, so cross-arg
//! and within-arg helper bundling are both well-defined.
//!
//! ## Sparsity caveat for `LagrangeDelta`-basis families
//!
//! `PermutationAccumulator`, `LogupMultiplicities`, and `LogupAggregator`
//! are committed in the `LagrangeDelta` / `LagrangeDoubleDelta` bases
//! introduced by PR #379. At `t = 1` the bundle commits against the
//! basis-appropriate SRS slice (no conversion, sparsity preserved). At
//! `t > 1` the current implementation converts to `Coeff` (see the TODO
//! in `FflonkScheme::commit`'s `t > 1` branch), which **erases the
//! Δ-sparsity**. The basis-aware fflonk SRS from the multibase paper
//! (§2.1 / §2.3) is the eventual replacement.
//!
//! ## Deferred follow-ups
//!
//! 1. Adopt the basis-aware fflonk SRS (multibase paper §2.1 / §2.3) so
//!    `t > 1` preserves the Δ-sparsity for permutation / logup phases.
//! 2. Rewrite linearization to consume openings rather than per-poly
//!    commitments, unblocking `QuotientPiece` and simple-selector `Fixed`
//!    bundling.
//! 3. Split `vk.fixed_commitments` into simple-selector vs. non-selector
//!    regions and bundle the non-selector half at keygen.
//! 4. Phase-merging: collapse phases whose commits don't depend on a
//!    later-squeezed challenge into one batched commit (paper §2.3
//!    enables heterogeneous bundles across bases).
//! 5. Per-phase variable `t` (decoupling sub-bundle sizes from the
//!    protocol-level `T_MAX`).

use std::collections::BTreeMap;

use crate::poly::query::PolynomialLabel;

/// Which bundlable family a label belongs to, for partition's purposes.
/// `Ord` is what drives BTreeMap iteration order in [`partition`] — that
/// order is deterministic for testability but no longer load-bearing (see
/// module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum BundleFamily {
    Advice,
    CommittedInstance,
    PermutationAccumulator,
    LogupHelper,
    LogupMultiplicities,
    LogupAggregator,
}

/// Classify a label into its bundlable family, or `None` if it should be
/// committed as a singleton (`t = 1`) sub-bundle.
pub(super) fn bundle_family(label: &PolynomialLabel) -> Option<BundleFamily> {
    match label {
        PolynomialLabel::Advice(_) => Some(BundleFamily::Advice),
        PolynomialLabel::CommittedInstance(_) => Some(BundleFamily::CommittedInstance),
        PolynomialLabel::PermutationAccumulator(_) => Some(BundleFamily::PermutationAccumulator),
        PolynomialLabel::LogupHelper(..) => Some(BundleFamily::LogupHelper),
        PolynomialLabel::LogupMultiplicities(_) => Some(BundleFamily::LogupMultiplicities),
        PolynomialLabel::LogupAggregator(_) => Some(BundleFamily::LogupAggregator),
        _ => None,
    }
}

/// Sort a bin of label-indices by the family's canonical key. Load-bearing
/// — see module docs. Mixing variants within one bin is impossible by
/// construction (each bin is one family).
fn sort_canonically(indices: &mut [usize], labels: &[PolynomialLabel], family: BundleFamily) {
    match family {
        BundleFamily::Advice => indices.sort_by_key(|&idx| match &labels[idx] {
            PolynomialLabel::Advice(i) => *i,
            _ => unreachable!(),
        }),
        BundleFamily::CommittedInstance => indices.sort_by_key(|&idx| match &labels[idx] {
            PolynomialLabel::CommittedInstance(i) => *i,
            _ => unreachable!(),
        }),
        BundleFamily::PermutationAccumulator => indices.sort_by_key(|&idx| match &labels[idx] {
            PolynomialLabel::PermutationAccumulator(i) => *i,
            _ => unreachable!(),
        }),
        BundleFamily::LogupHelper => indices.sort_by(|&a, &b| match (&labels[a], &labels[b]) {
            (PolynomialLabel::LogupHelper(na, ja), PolynomialLabel::LogupHelper(nb, jb)) => {
                na.cmp(nb).then(ja.cmp(jb))
            }
            _ => unreachable!(),
        }),
        BundleFamily::LogupMultiplicities => {
            indices.sort_by(|&a, &b| match (&labels[a], &labels[b]) {
                (
                    PolynomialLabel::LogupMultiplicities(na),
                    PolynomialLabel::LogupMultiplicities(nb),
                ) => na.cmp(nb),
                _ => unreachable!(),
            })
        }
        BundleFamily::LogupAggregator => {
            indices.sort_by(|&a, &b| match (&labels[a], &labels[b]) {
                (PolynomialLabel::LogupAggregator(na), PolynomialLabel::LogupAggregator(nb)) => {
                    na.cmp(nb)
                }
                _ => unreachable!(),
            })
        }
    }
}

/// Chunk one family's indices into sub-bundles of size `≤ t_max`,
/// appending each chunk to `result`. Trailing chunks may have fewer than
/// `t_max` entries; their logical bundle size is `real_count.next_power_of_two()`
/// (with pad slots downstream).
fn chunk_family(result: &mut Vec<Vec<usize>>, family_indices: &[usize], t_max: usize) {
    let mut start = 0usize;
    while start < family_indices.len() {
        let take = (family_indices.len() - start).min(t_max);
        result.push(family_indices[start..start + take].to_vec());
        start += take;
    }
}

/// Sub-bundle partition of `labels`. Returns a list of index-vecs into
/// `labels`; each inner vec is one sub-bundle, with indices in canonical
/// order (slot `i` inside a bundle is well-defined and shared between
/// prover and verifier — see the module-level "ordering invariant" docs).
///
/// **Output order**: bundlable families first (each sorted by its canonical
/// key, with families themselves ordered by [`BundleFamily`]'s `Ord`),
/// then singletons in input order. This cross-family order is deterministic
/// but not load-bearing (see module docs) — the singleton path is driven
/// by query order in `multi_open` regardless.
///
/// `t_max` is the scheme-wide bundling ceiling (`2^T_MAX_LOG`). The SRS
/// check (`g_monomial_size ≥ t_max · n`) lives at the call site (commit),
/// not here.
///
/// # Panics
/// If `labels` is empty or `t_max == 0`.
pub(super) fn partition(t_max: usize, labels: &[PolynomialLabel]) -> Vec<Vec<usize>> {
    assert!(!labels.is_empty(), "partition: labels must be non-empty");
    assert!(t_max > 0, "partition: t_max must be > 0");

    let mut bins: BTreeMap<BundleFamily, Vec<usize>> = BTreeMap::new();
    let mut singleton_indices: Vec<usize> = Vec::new();
    for (idx, label) in labels.iter().enumerate() {
        match bundle_family(label) {
            Some(family) => bins.entry(family).or_default().push(idx),
            None => singleton_indices.push(idx),
        }
    }

    for (&family, indices) in bins.iter_mut() {
        sort_canonically(indices, labels, family);
    }

    let mut result: Vec<Vec<usize>> = Vec::new();
    for (_, indices) in bins {
        chunk_family(&mut result, &indices, t_max);
    }
    for idx in singleton_indices {
        result.push(vec![idx]);
    }
    result
}

/// Logical bundle size for a sub-bundle with `real_count` real polynomials
/// at scheme cap `t_max`. Round real_count up to the next power of two,
/// capped at `t_max`, clamped to at least 1. Pad slots are
/// `[real_count, t_logical)`.
pub(super) fn bundle_t(real_count: usize, t_max: usize) -> usize {
    real_count.next_power_of_two().min(t_max).max(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn advice(n: usize) -> Vec<PolynomialLabel> {
        (0..n).map(PolynomialLabel::Advice).collect()
    }

    #[test]
    fn advice_only_chunks_by_t_max() {
        let p = partition(4, &advice(4));
        assert_eq!(p, vec![vec![0, 1, 2, 3]]);
    }

    #[test]
    fn advice_splits_when_exceeds_t_max() {
        let p = partition(4, &advice(10));
        assert_eq!(p, vec![vec![0, 1, 2, 3], vec![4, 5, 6, 7], vec![8, 9]]);
    }

    #[test]
    fn advice_sorted_by_index() {
        let labels = vec![
            PolynomialLabel::Advice(3),
            PolynomialLabel::Advice(0),
            PolynomialLabel::Advice(2),
            PolynomialLabel::Advice(1),
        ];
        let p = partition(4, &labels);
        assert_eq!(p, vec![vec![1, 3, 2, 0]]);
    }

    #[test]
    fn singletons_isolated_from_advice() {
        let labels = vec![
            PolynomialLabel::Fixed(0),
            PolynomialLabel::Advice(0),
            PolynomialLabel::Advice(1),
            PolynomialLabel::Quotient,
        ];
        let p = partition(4, &labels);
        assert_eq!(p, vec![vec![1, 2], vec![0], vec![3]]);
    }

    #[test]
    fn t_max_one_means_all_singletons() {
        let p = partition(1, &advice(4));
        assert_eq!(p, vec![vec![0], vec![1], vec![2], vec![3]]);
    }

    #[test]
    fn perm_acc_in_own_bundle() {
        let labels = vec![
            PolynomialLabel::PermutationAccumulator(2),
            PolynomialLabel::PermutationAccumulator(0),
            PolynomialLabel::PermutationAccumulator(1),
        ];
        let p = partition(4, &labels);
        // Sorted by inner index: [PermAcc(0)=idx 1, PermAcc(1)=idx 2, PermAcc(2)=idx 0]
        assert_eq!(p, vec![vec![1, 2, 0]]);
    }

    #[test]
    fn logup_multiplicities_sorted_by_name() {
        let labels = vec![
            PolynomialLabel::LogupMultiplicities("zzz".into()),
            PolynomialLabel::LogupMultiplicities("aaa".into()),
            PolynomialLabel::LogupMultiplicities("mmm".into()),
        ];
        let p = partition(4, &labels);
        // Sorted by name: aaa (idx 1), mmm (idx 2), zzz (idx 0)
        assert_eq!(p, vec![vec![1, 2, 0]]);
    }

    #[test]
    fn families_emit_in_bundlefamily_ord() {
        // Advice + PermAcc + Logup* + singleton: each family gets its own bundle,
        // emitted in BundleFamily Ord order, then singletons in input order.
        let labels = vec![
            PolynomialLabel::LogupAggregator("x".into()),
            PolynomialLabel::Fixed(0),
            PolynomialLabel::PermutationAccumulator(0),
            PolynomialLabel::Advice(0),
        ];
        let p = partition(4, &labels);
        assert_eq!(
            p,
            vec![
                vec![3], // Advice
                vec![2], // PermutationAccumulator
                vec![0], // LogupAggregator
                vec![1], // Fixed (singleton)
            ]
        );
    }

    #[test]
    fn advice_trailing_bundle_is_padded() {
        let p = partition(16, &advice(3));
        assert_eq!(p, vec![vec![0, 1, 2]]);
        assert_eq!(bundle_t(3, 16), 4);
    }

    #[test]
    fn advice_partial_trailing_bundle() {
        let p = partition(16, &advice(19));
        let mut expected = vec![(0..16).collect::<Vec<_>>()];
        expected.push(vec![16, 17, 18]);
        assert_eq!(p, expected);
        assert_eq!(bundle_t(16, 16), 16);
        assert_eq!(bundle_t(3, 16), 4);
    }

    #[test]
    fn advice_exact_power_of_two_trailing() {
        let p = partition(4, &advice(6));
        assert_eq!(p, vec![vec![0, 1, 2, 3], vec![4, 5]]);
        assert_eq!(bundle_t(2, 4), 2);
    }
}
