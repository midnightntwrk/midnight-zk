use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    hash::Hash,
};

use ff::Field;

use crate::poly::{query::PolynomialLabel, Error};

#[derive(Clone, Debug)]
pub(super) struct CommitmentData<F> {
    pub(super) label: PolynomialLabel,
    pub(super) set_index: usize,
    pub(super) point_indices: Vec<usize>,
    pub(super) evals: Vec<F>,
}

impl<F> CommitmentData<F> {
    fn new(label: PolynomialLabel) -> Self {
        CommitmentData {
            label,
            set_index: 0,
            point_indices: vec![],
            evals: vec![],
        }
    }
}

type IntermediateSets<F> = (Vec<CommitmentData<F>>, Vec<Vec<F>>);

/// Groups `(label, point, eval)` triples by label and computes the
/// intermediate data structures needed by the Halo2 multi-opening argument.
///
/// Returns:
/// - A vector of `CommitmentData`, one per unique label, each recording which
///   point-set index it belongs to and the evaluation at each point.
/// - A vector of point sets, where each set is a `Vec<F>` of the distinct
///   evaluation points for all labels assigned to that set.
pub(super) fn construct_intermediate_sets<F: Field + Hash + Ord>(
    queries: &[(PolynomialLabel, F, F)],
) -> Result<IntermediateSets<F>, Error> {
    let mut commitment_map: Vec<CommitmentData<F>> = vec![];

    // Maps each unique point to a compact integer index.
    let mut point_index_map = HashMap::new();

    for (label, point, _eval) in queries {
        let num_points = point_index_map.len();
        let point_idx = point_index_map.entry(*point).or_insert(num_points);

        if let Some(pos) = commitment_map.iter().position(|c| &c.label == label) {
            if commitment_map[pos].point_indices.contains(point_idx) {
                return Err(Error::DuplicatedQuery);
            }
            commitment_map[pos].point_indices.push(*point_idx);
        } else {
            let mut tmp = CommitmentData::new(label.clone());
            tmp.point_indices.push(*point_idx);
            commitment_map.push(tmp);
        }
    }

    // Inverse map: point_index → point.
    let inverse_point_index_map: HashMap<_, _> =
        point_index_map.iter().map(|(&p, &i)| (i, p)).collect();

    // Map from ordered point-index-sets to their set index.
    let mut point_idx_sets: BTreeMap<BTreeSet<usize>, usize> = BTreeMap::new();
    // Per-commitment snapshot of its point_index_set (used in the second pass).
    let mut commitment_set_map: Vec<(PolynomialLabel, BTreeSet<usize>)> =
        Vec::with_capacity(commitment_map.len());

    for commitment_data in commitment_map.iter() {
        let point_index_set: BTreeSet<_> = commitment_data.point_indices.iter().cloned().collect();
        commitment_set_map.push((commitment_data.label.clone(), point_index_set.clone()));

        let num_sets = point_idx_sets.len();
        point_idx_sets.entry(point_index_set).or_insert(num_sets);
    }

    // Initialise empty evals vec for each unique commitment.
    for commitment_data in commitment_map.iter_mut() {
        let len = commitment_data.point_indices.len();
        commitment_data.evals = vec![F::ZERO; len];
    }

    // Populate set_index and evals for each commitment.
    for (label, point, eval) in queries {
        let point_index = point_index_map.get(point).unwrap();

        let point_index_set =
            commitment_set_map.iter().find(|(l, _)| l == label).map(|(_, s)| s).unwrap();
        assert!(!point_index_set.is_empty());

        let set_index = point_idx_sets.get(point_index_set).unwrap();

        let point_index_set_vec: Vec<usize> = point_index_set.iter().cloned().collect();
        let point_index_in_set = point_index_set_vec.iter().position(|i| i == point_index).unwrap();

        for commitment_data in commitment_map.iter_mut() {
            if &commitment_data.label == label {
                commitment_data.set_index = *set_index;
                commitment_data.evals[point_index_in_set] = *eval;
            }
        }
    }

    // Build the actual point sets from the index sets.
    let mut point_sets: Vec<Vec<F>> = vec![Vec::new(); point_idx_sets.len()];
    for (point_idx_set, &set_idx) in point_idx_sets.iter() {
        for &point_idx in point_idx_set {
            let point = inverse_point_index_map.get(&point_idx).unwrap();
            point_sets[set_idx].push(*point);
        }
    }

    Ok((commitment_map, point_sets))
}

/// Computes the dummy openings needed to reduce the number of distinct
/// multi-open point sets. Each input `(key, point)` pair represents a query
/// (e.g., a commitment opened at a given point). The function groups queries
/// by key (by commitment) computes the union of all point sets that contain
/// more than one point, and returns the missing `(index, point)` pairs that,
/// once added, make every such point set identical. Keys with a single point
/// are left untouched (we do this because there are many commitments opened
/// at a single point, e.g. most selectors; we could also pad those, but the
/// impact on the proof size would be more significant).
///
/// Each returned `index` refers to the position of the key's first occurrence
/// in the input, so callers can index back into the original query slice.
///
/// The output order is deterministic (insertion order), so prover and verifier
/// stay in sync.
#[cfg(feature = "fewer-point-sets")]
pub fn compute_dummy_queries<K: PartialEq, P: PartialEq + Clone>(
    pairs: &[(K, P)],
) -> Vec<(usize, P)> {
    // Group by key, tracking each key's first occurrence index.
    let mut groups: Vec<(usize, Vec<P>)> = vec![];
    for (i, (key, point)) in pairs.iter().enumerate() {
        match groups.iter_mut().find(|(idx, _)| pairs[*idx].0 == *key) {
            Some((_, points)) if !points.contains(point) => points.push(point.clone()),
            Some(_) => panic!("duplicate (key, point) pair in compute_dummy_queries input"),
            None => groups.push((i, vec![point.clone()])),
        }
    }

    // Union of all non-singleton point sets (insertion order).
    let mut union = vec![];
    for (_, points) in &groups {
        assert!(!points.is_empty(), "unexpected empty point set");
        if points.len() == 1 {
            continue;
        }
        for p in points {
            if !union.contains(p) {
                union.push(p.clone());
            }
        }
    }

    // Collect missing (first_index, point) dummy queries.
    let mut dummy_queries = vec![];
    for (idx, existing) in &groups {
        for p in &union {
            if !existing.contains(p) {
                dummy_queries.push((*idx, p.clone()));
            }
        }
    }
    dummy_queries
}
