//! Bundling policy for fflonk: how the polynomials in a `commit` call are
//! partitioned into sub-bundles of size `t ≤ T_MAX` each.
//!
//! `T_MAX = 2^FFLONK_T_MAX_LOG` is the scheme-wide const generic of
//! [`FflonkScheme`](super::FflonkScheme), so both sides agree on `t_max`
//! without consulting the SRS. Any change to the partition strategy is a
//! protocol-level change (commitments produced differ).
//!
//! ## Bundling policy
//!
//! - Bundlable families (`Advice`, `CommittedInstance`,
//!   `PermutationAccumulator`, `LogupHelper`, `LogupMultiplicities`,
//!   `LogupAggregator`) are grouped per-family, sorted by their family's
//!   canonical key (`usize` index for the numeric variants, lexicographic
//!   `String` for the named `Logup*` variants), and chunked into sub-bundles of
//!   size `≤ t_max`.
//! - Non-bundlable labels are committed as their own singleton sub-bundles (`t
//!   = 1`).
//!
//! Families involved in linearisation (`QuotientPiece` and simple-selector
//! `Fixed`) must stay singletons for the current protocol.

use std::collections::BTreeMap;

use crate::poly::query::PolynomialLabel;

/// Which bundlable family a label belongs to, for partition's purposes.
/// `Ord` drives BTreeMap iteration order in `partition`; that order is
/// deterministic but not relied upon (see module docs).
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

/// Sort a bin of label-indices by the family's canonical key. Mixing variants
/// within one bin is impossible by construction (each bin is one family).
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
        BundleFamily::LogupAggregator => indices.sort_by(|&a, &b| match (&labels[a], &labels[b]) {
            (PolynomialLabel::LogupAggregator(na), PolynomialLabel::LogupAggregator(nb)) => {
                na.cmp(nb)
            }
            _ => unreachable!(),
        }),
    }
}

/// Chunk one family's indices into sub-bundles of size `<= t_max`, appending
/// each chunk to `result`. Trailing chunks may have fewer than `t_max` entries;
/// their logical bundle size is the next power of two.
fn chunk_family(result: &mut Vec<Vec<usize>>, family_indices: &[usize], t_max: usize) {
    // Always true in practice, but adding this assert just in case, since the
    // property is required for termination.
    assert!(t_max > 0);

    let mut start = 0usize;
    while start < family_indices.len() {
        let take = (family_indices.len() - start).min(t_max);
        result.push(family_indices[start..start + take].to_vec());
        start += take;
    }
}

/// Sub-bundle partition of `labels`. Returns a list of index-vecs into
/// `labels`; each inner vec is one sub-bundle, with indices in canonical
/// order shared between prover and verifier.
///
/// Output order: bundlable families first (each sorted by its canonical
/// key, with families themselves ordered by [`BundleFamily`]'s `Ord`),
/// then singletons in input order.
///
/// # Soundness for linearised polynomials
/// Any polynomial whose *individual* commitment is used downstream must be
/// committed as a singleton. Typically, the quotient pieces and simple-selector
/// fixed columns, due to their use in linearisation. A multi-poly bundle
/// exposes only the combined group element, from which the individual
/// commitments cannot be recovered.
pub(super) fn partition(t_max: usize, labels: &[PolynomialLabel]) -> Vec<Vec<usize>> {
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
/// at scheme cap `t_max`. This is because fflonk requires bundle's sizes to be
/// a power of two, which makes it necessary to pad bundles with null
/// polynomials until the next power.
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
    fn families_emit_in_bundlefamily_ord() {
        // Advice + PermAcc + Logup* + singleton: each family gets its own bundle,
        // emitted in BundleFamily Ord order, then singletons in input order.
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
