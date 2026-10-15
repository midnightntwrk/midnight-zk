use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Debug,
    hash::Hash,
};

use ff::Field;

use crate::poly::{Error, query::PolynomialLabel};

#[derive(Clone, Debug)]
pub(super) struct CommitmentData {
    pub(super) label: PolynomialLabel,
    pub(super) set_index: usize,
    point_indices: Vec<usize>,
}

pub(super) type IntermediateSets<F> = (Vec<CommitmentData>, Vec<Vec<F>>);

/// Groups a list of `(label, point)` queries into per-polynomial data and
/// point sets for multi-open batching.
///
/// Queries are grouped by their [`PolynomialLabel`] (each label identifies a
/// unique polynomial) and by point set.
///
/// Returns [`Error::DuplicatedQuery`] if the same `(label, point)` pair appears
/// more than once.
pub fn construct_intermediate_sets<F: Field + Hash + Ord>(
    queries: &[(PolynomialLabel, F)],
) -> Result<IntermediateSets<F>, Error> {
    // Construct sets of unique commitments and corresponding information about
    // their queries.
    let mut commitment_map: Vec<CommitmentData> = vec![];

    // Also construct mapping from a unique point to a point_index. This defines
    // an ordering on the points.
    let mut point_index_map = HashMap::new();

    // Iterate over all of the queries, computing the ordering of the points
    // while also creating new commitment data.
    for (query_label, query_point) in queries {
        let num_points = point_index_map.len();
        let point_idx = point_index_map.entry(*query_point).or_insert(num_points);

        if let Some(pos) = commitment_map.iter().position(|comm| &comm.label == query_label) {
            if commitment_map[pos].point_indices.contains(point_idx) {
                return Err(Error::DuplicatedQuery);
            }
            commitment_map[pos].point_indices.push(*point_idx);
        } else {
            commitment_map.push(CommitmentData {
                label: query_label.clone(),
                set_index: 0,
                point_indices: vec![*point_idx],
            });
        }
    }

    // Also construct inverse mapping from point_index to the point
    let inverse_point_index_map: HashMap<_, _> =
        point_index_map.iter().map(|(&p, &i)| (i, p)).collect();

    // Map each unique ordered point_idx_set to its set_idx, and each commitment
    // to the set_idx of its point_idx_set.
    let mut point_idx_sets: BTreeMap<BTreeSet<usize>, usize> = BTreeMap::new();
    for commitment_data in commitment_map.iter_mut() {
        let point_index_set: BTreeSet<_> = commitment_data.point_indices.iter().cloned().collect();
        let num_sets = point_idx_sets.len();
        commitment_data.set_index = *point_idx_sets.entry(point_index_set).or_insert(num_sets);
    }

    // Get actual points in each point set
    let mut point_sets: Vec<Vec<F>> = vec![Vec::new(); point_idx_sets.len()];
    for (point_idx_set, &set_idx) in point_idx_sets.iter() {
        for &point_idx in point_idx_set {
            let point = inverse_point_index_map.get(&point_idx).unwrap();
            point_sets[set_idx].push(*point);
        }
    }

    Ok((commitment_map, point_sets))
}
