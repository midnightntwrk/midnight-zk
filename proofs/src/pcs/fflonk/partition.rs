//! Bundling policy for fflonk: how the polynomials of a `commit` call are
//! partitioned into bundles of size `t ≤ t_max` each.
//!
//! `t_max` is the prover's effective bundling ceiling, capped by
//! [`FFLONK_T_MAX_LOG`](super::FFLONK_T_MAX_LOG); it travels to the verifier on
//! the transcript (for `multi_open`) and through the per-bundle sizes of the
//! serialized commitment (for `commit`). Any change to the partition strategy
//! is a protocol-level change: the commitments produced differ.
//!
//! ## Bundling policy
//!
//! - Bundlable families (`Advice`, `PermutationAccumulator`, `LogupHelper`,
//!   `LogupMultiplicities`, `LogupAggregator`, `Trash`) are grouped per-family,
//!   sorted by label, and chunked into bundles of size `≤ t_max`.
//! - Non-bundlable labels are committed as their own singleton bundles (`t =
//!   1`).
//!
//! Polynomials whose standalone commitment the protocol still needs stay
//! singletons; `poly_is_combinable` lists the reason per label.
//!
//! ## Requirements on a bundlable family
//!
//! `multi_open` re-derives the bundles by partitioning every label it is
//! queried on, so a family must satisfy both of:
//!
//! - It is committed in a single `commit_many` call, which is what makes that
//!   global partition agree with the per-call one.
//! - Every one of its polynomials is queried. A committed but unqueried member
//!   is absent from the partition `multi_open` derives, shifting the chunk
//!   boundaries away from the committed ones. For `Advice` this would take a
//!   column that appears in no gate expression and in no copy constraint, since
//!   `advice_queries` is filled only by `query_advice` and permutation columns
//!   are always queried at the current rotation. A violation is rejected by
//!   `bundle_expansion::check_bundle_layout`, never silently accepted.

use std::mem;

use crate::poly::query::PolynomialLabel;

/// Indicates whether a polynomial can be bundled by fflonk, i.e. whether the
/// protocol never needs its commitment on its own. A bundle exposes only the
/// combined group element, so every other label is committed as a singleton:
///
/// - `CommittedInstance`: committed out-of-band, one `CS::commit` per column,
///   and handed to the verifier as separate commitments, so a bundle spanning
///   several of them has nothing to correspond to.
/// - `Fixed`: `compute_linearization_commitment` scales the individual
///   simple-selector commitment `vk.fixed_commitments[i]`. Also an in-circuit
///   fixed base.
/// - `PermutationFixed`: not folded into linearisation, but still an in-circuit
///   fixed base, which maps one label to one curve point.
/// - `Quotient`, `QuotientPiece`: linearisation folds each limb with its own
///   scalar `(1 - x^n) * s^i`.
/// - `Linearization`: never committed, the verifier rebuilds it as an MSM.
/// - `Custom`: scheme-internal single commitments, such as `multi_open`'s batch
///   polynomial and opening proof.
/// - `NoLabel`: carries no polynomial identity, e.g. a collapsed MSM.
///
/// TODO: this function should be removed once linearisation and fflonk are made
/// compatible.
pub(super) fn poly_is_combinable(label: &PolynomialLabel) -> bool {
    matches!(
        label,
        PolynomialLabel::Advice(_)
            | PolynomialLabel::PermutationAccumulator(_)
            | PolynomialLabel::LogupHelper(..)
            | PolynomialLabel::LogupMultiplicities(_)
            | PolynomialLabel::LogupAggregator(_)
            | PolynomialLabel::Trash(_)
    )
}

/// Chunk one family's indices into bundles of size `<= t_max`, appending
/// each chunk to `result`. Trailing chunks may have fewer than `t_max` entries;
/// their logical bundle size is the next power of two.
fn chunk_family(result: &mut Vec<Vec<usize>>, family_indices: &[usize], t_max: usize) {
    // Always true in practice, but the property is required for termination.
    assert!(t_max > 0);

    let mut start = 0usize;
    while start < family_indices.len() {
        let take = (family_indices.len() - start).min(t_max);
        result.push(family_indices[start..start + take].to_vec());
        start += take;
    }
}

/// Canonical order of `labels` shared by prover and verifier, *without*
/// chunking: combinable polynomials first, sorted by label, then singletons in
/// input order. `PolynomialLabel`'s derived `Ord` clusters equal variants
/// together and orders within a variant by index, which is exactly the
/// per-family canonical key both sides must agree on. This ordering is
/// independent of the bundling factor; only the chunk boundaries drawn over it
/// depend on `t_max`.
pub(super) fn canonical_order(labels: &[PolynomialLabel]) -> Vec<usize> {
    let mut combinable: Vec<usize> = Vec::new();
    let mut singletons: Vec<usize> = Vec::new();
    for (idx, label) in labels.iter().enumerate() {
        if poly_is_combinable(label) {
            combinable.push(idx);
        } else {
            singletons.push(idx);
        }
    }
    combinable.sort_by(|&a, &b| labels[a].cmp(&labels[b]));
    combinable.extend(singletons);
    combinable
}

/// Bundle partition of `labels`. Returns a list of index-vecs into `labels`;
/// each inner vec is one bundle, with indices in the canonical order shared
/// between prover and verifier.
///
/// Output order: combinable polynomials first, grouped by label variant and
/// sorted within each group by label, then singletons in input order.
///
/// # Soundness for linearised polynomials
/// Any polynomial whose *individual* commitment is used downstream must be
/// committed as a singleton, typically the quotient pieces and simple-selector
/// fixed columns, because of their use in linearisation. A multi-poly bundle
/// exposes only the combined group element, from which the individual
/// commitments cannot be recovered.
pub(super) fn partition(t_max: usize, labels: &[PolynomialLabel]) -> Vec<Vec<usize>> {
    let order = canonical_order(labels);

    let mut result: Vec<Vec<usize>> = Vec::new();
    // Walk the canonical order: chunk each maximal run of one combinable variant
    // (hence a single basis) into bundles of at most `t_max`, and emit each
    // singleton as its own bundle.
    let mut start = 0;
    while start < order.len() {
        if !poly_is_combinable(&labels[order[start]]) {
            result.push(vec![order[start]]);
            start += 1;
            continue;
        }
        let mut end = start + 1;
        while end < order.len()
            && poly_is_combinable(&labels[order[end]])
            && mem::discriminant(&labels[order[end]]) == mem::discriminant(&labels[order[start]])
        {
            end += 1;
        }
        chunk_family(&mut result, &order[start..end], t_max);
        start = end;
    }
    result
}

/// Logical bundle size for a bundle holding `real_count` real polynomials at
/// ceiling `t_max`. fflonk requires bundle sizes to be a power of two, so
/// bundles are padded with null polynomials up to the next power.
pub(super) fn bundle_t(real_count: usize, t_max: usize) -> usize {
    real_count.next_power_of_two().min(t_max)
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
    fn committed_instances_stay_singletons() {
        let labels = vec![
            PolynomialLabel::CommittedInstance(0),
            PolynomialLabel::Advice(0),
            PolynomialLabel::CommittedInstance(1),
        ];
        let p = partition(4, &labels);
        // Advice bundles; each committed instance is its own bundle, in input order.
        assert_eq!(p, vec![vec![1], vec![0], vec![2]]);
    }

    #[test]
    fn trash_in_own_bundle() {
        let labels = vec![
            PolynomialLabel::Trash(1),
            PolynomialLabel::Advice(0),
            PolynomialLabel::Trash(0),
        ];
        let p = partition(4, &labels);
        // Advice first, then Trash sorted by argument index.
        assert_eq!(p, vec![vec![1], vec![2, 0]]);
    }

    #[test]
    fn logup_multiplicities_sorted_by_index() {
        let labels = vec![
            PolynomialLabel::LogupMultiplicities(2),
            PolynomialLabel::LogupMultiplicities(0),
            PolynomialLabel::LogupMultiplicities(1),
        ];
        let p = partition(4, &labels);
        // Sorted by argument index: 0 (pos 1), 1 (pos 2), 2 (pos 0)
        assert_eq!(p, vec![vec![1, 2, 0]]);
    }

    #[test]
    fn families_emit_in_label_variant_order() {
        // Advice + PermAcc + Logup* + singleton: each variant gets its own bundle,
        // emitted in label variant order, then singletons in input order.
        let labels = vec![
            PolynomialLabel::LogupAggregator(0),
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
