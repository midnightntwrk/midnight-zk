use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Debug,
    hash::Hash,
};

use ff::{Field, PrimeField};

use crate::poly::{query::PolynomialLabel, Error};

// -------------------------------------------------------------------------
// Curve-free fflonk math. Naming follows the paper
// (https://eprint.iacr.org/2021/1167.pdf).
// -------------------------------------------------------------------------

/// Paper's `combine_t`: interleaves up to `t` coefficient slots of equal
/// length `n` into `g` of length `t·n`, where `g[j·t + i] = slots[i][j]` —
/// encoding `g(X) = Σ_i X^i · f_i(X^t)`. Passing fewer than `t` slots leaves
/// the trailing (pad) slots zero, so a padded bundle can pass its real slots
/// only.
///
/// # Panics
/// If `slots.len() > t`, or the slots have unequal lengths.
pub(super) fn combine<F: Field>(slots: &[&[F]], t: usize) -> Vec<F> {
    let n = slots.first().map_or(0, |s| s.len());
    assert!(
        slots.len() <= t,
        "combine: {} slots exceeds t = {t}",
        slots.len()
    );
    assert!(
        slots.iter().all(|s| s.len() == n),
        "combine: all slots must have equal length"
    );
    let mut values = vec![F::ZERO; t * n];
    for (i, slot) in slots.iter().enumerate() {
        for (j, &c) in slot.iter().enumerate() {
            values[j * t + i] = c;
        }
    }
    values
}

/// Returns a primitive `t`-th root of unity in `F`, where `t` is a power of
/// two not exceeding the field's 2-adicity `F::S`. Computed as
/// `F::ROOT_OF_UNITY^(2^(S − log2 t))`.
///
/// # Panics
/// If `t` is not a power of two, or `log2 t > F::S`.
pub(super) fn primitive_root_of_unity<F: PrimeField>(t: usize) -> F {
    assert!(t.is_power_of_two(), "t must be a power of two");
    let log_t = t.trailing_zeros();
    assert!(log_t <= F::S, "t exceeds field 2-adicity (F::S)");
    let exp: u64 = 1u64 << (F::S - log_t);
    F::ROOT_OF_UNITY.pow_vartime([exp])
}

/// Paper's `roots_t(x)`: returns `[z, z ω_t, z ω_t², ..., z ω_t^{t−1}]`, the
/// `t` t-th roots of `x = z^t`, given any `t`-th root `z` of `x` and a
/// primitive `t`-th root of unity `omega_t`.
pub(super) fn roots<F: Field>(z: F, omega_t: F, t: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(t);
    let mut acc = z;
    for _ in 0..t {
        out.push(acc);
        acc *= omega_t;
    }
    out
}

/// Paper's `S̄(root)`: evaluates the vector of claimed evaluations `claimed` as
/// a polynomial at `root`: `Σ_i root^i · claimed[i]`.
///
/// When `root` is a `t`-th root of `x` and `claimed = (f_0(x), …, f_{t-1}(x))`,
/// this equals `g(root)` by Lemma 5.1 of the paper.
pub(super) fn eval_claims_as_poly<F: Field>(claimed: &[F], root: F) -> F {
    let mut acc = F::ZERO;
    let mut root_pow = F::ONE;
    for &c in claimed {
        acc += root_pow * c;
        root_pow *= root;
    }
    acc
}

/// Returns one specific `t`-th root of `x`, computed by `log2(t)` applications
/// of `Field::sqrt`. Deterministic as prover and verifier compute the same root
/// (the `t` roots of `x` are then `{z, z ω_t, ..., z ω_t^{t-1}}`).
///
/// # Panics
/// If `t` is not a power of two, or if `x` is not a `t`-th power in `F`
/// (intermediate `sqrt()` returns `None`). For fflonk, the caller guarantees
/// `x` is a `t`-th power by construction (logical points are `s^t · ω_n^r`).
pub(super) fn t_th_root<F: PrimeField>(x: F, t: usize) -> F {
    assert!(t.is_power_of_two(), "t must be a power of two");
    let log_t = t.trailing_zeros();
    let mut r = x;
    for _ in 0..log_t {
        r = Option::<F>::from(r.sqrt())
            .expect("t_th_root: input is not a square — protocol-level error");
    }
    r
}

#[derive(Clone, Debug)]
pub(crate) struct CommitmentData<F> {
    pub(crate) label: PolynomialLabel,
    pub(crate) set_index: usize,
    pub(crate) point_indices: Vec<usize>,
    pub(crate) evals: Vec<F>,
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

pub(super) type IntermediateSets<F> = (Vec<CommitmentData<F>>, Vec<Vec<F>>);

/// Groups a list of `(label, point, eval)` queries into per-polynomial data and
/// point sets for multi-open batching.
///
/// Queries are grouped by their [`PolynomialLabel`] (each label identifies a
/// unique polynomial) and by point set.
///
/// Returns [`Error::DuplicatedQuery`] if the same `(label, point)` pair appears
/// more than once.
///
/// Returns:
/// - A vector of `CommitmentData`, one per unique label, each recording which
///   point-set index it belongs to and the evaluation at each point.
/// - A vector of point sets, where each set is a `Vec<F>` of the distinct
///   evaluation points for all labels assigned to that set.
pub(crate) fn construct_intermediate_sets<F: Field + Hash + Ord>(
    queries: &[(PolynomialLabel, F, F)],
) -> Result<IntermediateSets<F>, Error> {
    // Construct sets of unique commitments and corresponding information about
    // their queries.
    let mut commitment_map: Vec<CommitmentData<F>> = vec![];

    // Also construct mapping from a unique point to a point_index. This defines
    // an ordering on the points.
    let mut point_index_map = HashMap::new();

    // Iterate over all of the queries, computing the ordering of the points
    // while also creating new commitment data.
    for (query_label, query_point, _query_eval) in queries {
        let num_points = point_index_map.len();
        let point_idx = point_index_map.entry(*query_point).or_insert(num_points);

        if let Some(pos) = commitment_map.iter().position(|comm| &comm.label == query_label) {
            if commitment_map[pos].point_indices.contains(point_idx) {
                return Err(Error::DuplicatedQuery);
            }
            commitment_map[pos].point_indices.push(*point_idx);
        } else {
            let mut tmp = CommitmentData::new(query_label.clone());
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
        commitment_set_map.push((commitment_data.label.clone(), point_index_set.clone()));

        let num_sets = point_idx_sets.len();
        point_idx_sets.entry(point_index_set).or_insert(num_sets);
    }

    // Initialise empty evals vec for each unique commitment
    for commitment_data in commitment_map.iter_mut() {
        let len = commitment_data.point_indices.len();
        commitment_data.evals = vec![F::default(); len];
    }

    // Populate set_index, evals and points for each commitment using point_idx_sets
    for (query_label, query_point, query_eval) in queries {
        // The index of the point at which the commitment is queried
        let point_index = point_index_map.get(query_point).unwrap();

        // The point_index_set at which the commitment was queried
        let point_index_set = commitment_set_map
            .iter()
            .find(|(l, _)| l == query_label)
            .map(|(_, s)| s)
            .unwrap();
        assert!(!point_index_set.is_empty());

        // The set_index of the point_index_set
        let set_index = point_idx_sets.get(point_index_set).unwrap();

        let point_index_set: Vec<usize> = point_index_set.iter().cloned().collect();

        // The offset of the point_index in the point_index_set
        let point_index_in_set = point_index_set.iter().position(|i| i == point_index).unwrap();

        for commitment_data in commitment_map.iter_mut() {
            if *query_label == commitment_data.label {
                commitment_data.set_index = *set_index;
                // Insert the eval using the ordering of the point_index_set
                commitment_data.evals[point_index_in_set] = *query_eval;
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

/// Computes the dummy openings needed to reduce the number of distinct
/// multi-open point sets. Each input `(key, point)` pair represents a query
/// (e.g., a commitment opened at a given point). The function groups queries
/// by key, computes the union of all non-singleton groups' points, and returns
/// the missing `(index, point)` pairs that, once added, make every group's
/// point set equal to the union.
///
/// Note: singleton groups are then padded against the union (even though they
/// don't contribute to it).
///
/// Each returned `index` refers to the position of the key's first occurrence
/// in the input, so callers can index back into the original query slice.
///
/// The output order is deterministic (insertion order), so prover and verifier
/// stay in sync.
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
