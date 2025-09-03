use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Debug,
    hash::Hash,
};

use ff::Field;

use crate::poly::{query::Query, Error};

#[derive(Clone, Debug)]
pub(super) struct CommitmentData<F, T: PartialEq> {
    pub(super) commitment: T,
    pub(super) set_index: usize,
    pub(super) point_indices: Vec<usize>,
    pub(super) evals: Vec<F>,
}

impl<F, T: PartialEq> CommitmentData<F, T> {
    fn new(commitment: T) -> Self {
        CommitmentData {
            commitment,
            set_index: 0,
            point_indices: vec![],
            evals: vec![],
        }
    }
}

pub(super) type IntermediateSets<F, Q> = (
    Vec<CommitmentData<<Q as Query<F>>::Eval, <Q as Query<F>>::Commitment>>,
    Vec<Vec<F>>,
);

pub fn construct_intermediate_sets<F: Field + Hash + Ord, Q: Query<F>>(
    queries: &[Q],
) -> Result<IntermediateSets<F, Q>, Error> {
    // Construct sets of unique commitments and corresponding information about
    // their queries.
    let mut commitment_map: Vec<CommitmentData<Q::Eval, Q::Commitment>> = vec![];

    // Also construct mapping from a unique point to a point_index. This defines
    // an ordering on the points.
    let mut point_index_map = HashMap::new();

    // Iterate over all of the queries, computing the ordering of the points
    // while also creating new commitment data.
    for query in queries {
        let num_points = point_index_map.len();
        let point_idx = point_index_map
            .entry(query.get_point())
            .or_insert(num_points);

        if let Some(pos) = commitment_map
            .iter()
            .position(|comm| comm.commitment == query.get_commitment())
        {
            if commitment_map[pos].point_indices.contains(point_idx) {
                return Err(Error::DuplicatedQuery);
            }
            commitment_map[pos].point_indices.push(*point_idx);
        } else {
            let mut tmp = CommitmentData::new(query.get_commitment());
            tmp.point_indices.push(*point_idx);
            commitment_map.push(tmp);
        }
    }

    // Also construct inverse mapping from point_index to the point
    let inverse_point_index_map: HashMap<_, _> =
        point_index_map.iter().map(|(&p, &i)| (i, p)).collect();

    // Construct map of unique ordered point_idx_sets to their set_idx
    let mut point_idx_sets: BTreeMap<BTreeSet<usize>, usize> = BTreeMap::new();
    // Also construct mapping from commitment to point_idx_set
    let mut commitment_set_map = Vec::with_capacity(commitment_map.len());

    for commitment_data in commitment_map.iter() {
        let point_index_set: BTreeSet<_> = commitment_data.point_indices.iter().cloned().collect();

        // Push point_index_set to CommitmentData for the relevant commitment
        commitment_set_map.push((commitment_data.commitment.clone(), point_index_set.clone()));

        let num_sets = point_idx_sets.len();
        point_idx_sets.entry(point_index_set).or_insert(num_sets);
    }

    // Initialise empty evals vec for each unique commitment
    for commitment_data in commitment_map.iter_mut() {
        let len = commitment_data.point_indices.len();
        commitment_data.evals = vec![Q::Eval::default(); len];
    }

    // Populate set_index, evals and points for each commitment using point_idx_sets
    for query in queries {
        // The index of the point at which the commitment is queried
        let point_index = point_index_map.get(&query.get_point()).unwrap();

        // The point_index_set at which the commitment was queried
        let point_index_set = commitment_set_map
            .iter()
            .find(|(c, _)| *c == query.get_commitment())
            .map(|(_, s)| s)
            .unwrap();
        assert!(!point_index_set.is_empty());

        // The set_index of the point_index_set
        let set_index = point_idx_sets.get(point_index_set).unwrap();

        let point_index_set: Vec<usize> = point_index_set.iter().cloned().collect();

        // The offset of the point_index in the point_index_set
        let point_index_in_set = point_index_set
            .iter()
            .position(|i| i == point_index)
            .unwrap();

        for commitment_data in commitment_map.iter_mut() {
            if query.get_commitment() == commitment_data.commitment {
                commitment_data.set_index = *set_index;
                // Insert the eval using the ordering of the point_index_set
                commitment_data.evals[point_index_in_set] = query.get_eval();
            }
        }
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
