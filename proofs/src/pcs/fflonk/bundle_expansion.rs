//! Bundle pre-expansion data structures and pure helpers.
//!
//! `FflonkScheme::multi_open` and `FflonkScheme::multi_prepare` each run a
//! fflonk-specific phase before the standard multi-open argument:
//!
//! - Prover (`multi_open`): classify queries into bundles, materialise the
//!   combined polynomial `g` for each `t > 1` bundle, compute the opening
//!   point-set unions, expand into synthetic queries on `g` at the `t`-th roots
//!   of each logical opening point.
//! - Verifier (`multi_prepare`): classify queries into bundles, collect the
//!   per-(slot, logical) evaluations the prover wrote, reconstruct `g(root)`
//!   for each `t`-th root via Lemma 5.1 of the fflonk paper.
//!
//! The two sides must produce identical enumerations of (bundle, slot, point)
//! so the transcript I/O matches.

use std::{collections::HashMap, hash::Hash};

use ff::{Field, WithSmallOrderMulGroup};
use midnight_curves::pairing::MultiMillerLoop;
use rustc_hash::FxHashMap;

use super::{
    FflonkScheme,
    commitment::FflonkCommitment,
    math::{eval_claims_as_poly, primitive_root_of_unity, roots as t_th_roots, t_th_root},
    partition,
};
use crate::{
    pcs::msm::MSMKZG,
    poly::{
        Error, ProverQuery,
        query::{PolynomialLabel, VerifierQuery},
    },
    utils::{
        arithmetic::{CurveAffine, CurveExt, MSM},
        helpers::ProcessedSerdeObject,
    },
};

/// Per-bundle prover-side preparation. Holds everything `multi_open` needs to
/// (a) write over-opening evals to the transcript and (b) emit the synthetic
/// queries on `g`.
pub(super) struct MultiOpenPrepData<F> {
    /// Index into the prover's `bundle_indices` vec, used to look up `g_poly`
    /// and the canonical labels.
    pub(super) bundle_idx: usize,
    /// Synthetic label shared with the verifier (`fflonk_bundle[advice_0]`).
    pub(super) synth_label: PolynomialLabel,
    /// The bundle's logical packing factor `t = bundle_t(real_count, t_max)`.
    /// It exceeds the number of real polynomials in the bundle when the
    /// trailing bundle has padded zero slots.
    pub(super) t: usize,
    /// Distinct logical points seen for this bundle, sorted. The synthetic
    /// queries on `g` are emitted at the `t` t-th roots of each.
    pub(super) union_logicals: Vec<F>,
    /// `(slot, logical_point)` pairs the prover must over-open and write to the
    /// transcript, in [`missing_openings`] order (so the verifier reads them in
    /// the same order). Slots are always real slot indices (in `[0,
    /// real_count)`); pad slots are never over-opened, their eval being known
    /// to be zero.
    pub(super) missing: Vec<(usize, F)>,
}

/// Per-bundle verifier-side accumulator. Holds the bundle's G1 commitment, the
/// canonical labels (so slot indices are well-defined), the `(slot, point)`
/// pairs the verifier saw in queries order, and the eval lookup populated both
/// from the original queries and from the over-opening reads.
pub(super) struct BundleAcc<E: MultiMillerLoop> {
    pub(super) bundle_g1: E::G1,
    /// Real labels of the bundle's polynomials, in canonical order. Length
    /// equals `real_count`, which is less than `t` for a padded trailing
    /// bundle.
    pub(super) canonical_labels: Vec<PolynomialLabel>,
    /// Logical bundle size, `bundle_t(real_count, t_max)`. Slots
    /// `[canonical_labels.len(), t)` are pad slots whose evals are implicitly
    /// zero (never written / read on the transcript).
    pub(super) t: usize,
    pub(super) pairs: Vec<(usize, E::Fr)>,
    pub(super) evals: FxHashMap<(usize, E::Fr), E::Fr>,
}

/// The `(index, point)` openings missing for every key of `pairs` to be opened
/// at the union of all points, where `index` is the position of the key's first
/// occurrence. Output order is deterministic (insertion order), so prover and
/// verifier agree on the transcript order.
///
/// Every slot of a bundle must be opened at every logical point the bundle is
/// opened at, since the verifier reconstructs `g` at a root from the
/// evaluations of *all* slots. This is why the union is over all points, unlike
/// `fewer-point-sets`'s
/// `compute_dummy_queries`,
/// which pads towards multi-point keys only.
pub fn missing_openings<K: PartialEq, P: PartialEq + Clone>(pairs: &[(K, P)]) -> Vec<(usize, P)> {
    // Group by key, tracking each key's first occurrence index.
    let mut groups: Vec<(usize, Vec<P>)> = vec![];
    for (i, (key, point)) in pairs.iter().enumerate() {
        match groups.iter_mut().find(|(idx, _)| pairs[*idx].0 == *key) {
            Some((_, points)) if !points.contains(point) => points.push(point.clone()),
            Some(_) => panic!("duplicate (key, point) pair in missing_openings input"),
            None => groups.push((i, vec![point.clone()])),
        }
    }

    let mut union: Vec<P> = vec![];
    for (_, points) in &groups {
        for p in points {
            if !union.contains(p) {
                union.push(p.clone());
            }
        }
    }

    let mut missing = vec![];
    for (idx, existing) in &groups {
        for p in &union {
            if !existing.contains(p) {
                missing.push((*idx, p.clone()));
            }
        }
    }
    missing
}

/// Checks that the bundle layout a commitment carries is the one
/// `partition::partition` derives from its labels at `t_max`.
///
/// The per-bundle sizes travel on the wire but are *not* absorbed into the
/// transcript (only the committed points are), so on their own they are not
/// bound by Fiat-Shamir. They are bound here instead: `t_max` comes from the
/// `t_max_log` the prover wrote to the transcript, which *is* hashed, and the
/// labels come from the verifier itself. The sizes are therefore only a parsing
/// aid, telling the reader how many points to consume, and any deviation from
/// the partition they must encode is rejected.
pub(super) fn check_bundle_layout<E: MultiMillerLoop>(
    pairs: &[(E::G1, Vec<PolynomialLabel>)],
    t_max: usize,
) -> Result<(), Error> {
    let labels: Vec<PolynomialLabel> =
        pairs.iter().flat_map(|(_, labels)| labels.iter().cloned()).collect();
    let expected = partition::partition(t_max, &labels);
    let matches = expected.len() == pairs.len()
        && expected
            .iter()
            .zip(pairs)
            .all(|(bundle, (_, labels))| bundle.len() == labels.len());
    matches.then_some(()).ok_or(Error::OpeningError)
}

/// Build the prover-side per-bundle preparation list, sorted by `synth_label`
/// so prover and verifier visit bundles in the same order. Pure function, no
/// transcript I/O.
pub(super) fn build_prover_multi_pre<E: MultiMillerLoop>(
    bundle_indices: &[Vec<usize>],
    all_labels: &[PolynomialLabel],
    t_max: usize,
    queries: &[ProverQuery<E::Fr>],
) -> Vec<MultiOpenPrepData<E::Fr>>
where
    E::Fr: Ord,
{
    let mut multi_pre: Vec<MultiOpenPrepData<E::Fr>> = Vec::with_capacity(bundle_indices.len());
    for (bundle_idx, indices) in bundle_indices.iter().enumerate() {
        let t = partition::bundle_t(indices.len(), t_max);
        if t <= 1 {
            continue;
        }
        let bundle_labels: Vec<PolynomialLabel> =
            indices.iter().map(|&i| all_labels[i].clone()).collect();
        let synth_label = FflonkCommitment::<E>::synthetic_bundle_label(&bundle_labels);

        // `(slot, point)` pairs in queries order.
        let pairs: Vec<(usize, E::Fr)> = queries
            .iter()
            .filter_map(|q| {
                let slot = bundle_labels.iter().position(|l| l == &q.label)?;
                Some((slot, q.point))
            })
            .collect();
        let missing: Vec<(usize, E::Fr)> = missing_openings(&pairs)
            .into_iter()
            .map(|(idx, point)| (pairs[idx].0, point))
            .collect();

        let mut union_logicals: Vec<E::Fr> = vec![];
        for &(_, p) in &pairs {
            if !union_logicals.contains(&p) {
                union_logicals.push(p);
            }
        }
        union_logicals.sort();

        multi_pre.push(MultiOpenPrepData {
            bundle_idx,
            synth_label,
            t,
            union_logicals,
            missing,
        });
    }
    multi_pre.sort_by(|a, b| a.synth_label.to_string().cmp(&b.synth_label.to_string()));
    multi_pre
}

/// Classify the verifier's queries into:
/// - `multi_bundles_sorted`: `(synth_label, BundleAcc)` pairs, sorted by
///   `synth_label` so the over-opening read order matches the prover's write
///   order.
/// - `label_to_msm`: per-label MSM source, populated for singletons and
///   `Linear` bundles (the `t > 1` bundle MSMs are added by the caller, after
///   the over-opening reads).
/// - `singleton_triples`: `(label, point, eval)` triples for `t = 1`
///   commitments and `Linear`.
///
/// Pure function, no transcript I/O. Mirror of [`build_prover_multi_pre`].
#[allow(clippy::type_complexity)]
pub(super) fn classify_verifier_queries<'com, E>(
    queries: &[VerifierQuery<'com, E::Fr, FflonkScheme<E>>],
    // Bundling ceiling for this proof (`2^t_max_log`), read from the transcript
    // by `multi_prepare`. Must equal the `t_max` the prover used in
    // `commit`/`multi_open`, or the reconstructed `bundle_t` (and thus the whole
    // opening) diverges.
    t_max: usize,
) -> (
    Vec<(PolynomialLabel, BundleAcc<E>)>,
    HashMap<PolynomialLabel, MSMKZG<E>>,
    Vec<(PolynomialLabel, E::Fr, E::Fr)>,
)
where
    E: MultiMillerLoop,
    E::Fr: WithSmallOrderMulGroup<3> + Hash,
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
    FflonkCommitment<E>: 'com,
{
    let mut multi_bundles: FxHashMap<PolynomialLabel, BundleAcc<E>> = FxHashMap::default();
    let mut label_to_msm: HashMap<PolynomialLabel, MSMKZG<E>> = HashMap::new();
    let mut singleton_triples: Vec<(PolynomialLabel, E::Fr, E::Fr)> = Vec::new();

    for q in queries.iter() {
        match q.commitment {
            FflonkCommitment::Linear(points, scalars, labels) => {
                // Linearization commitment: pass-through, expanded MSM with all
                // (point, scalar, label) terms.
                singleton_triples.push((q.label.clone(), q.point, q.eval));
                let mut msm = MSMKZG::init();
                for ((p, s), label) in points.iter().zip(scalars).zip(labels) {
                    msm.append_term(*s, *p, label.clone());
                }
                label_to_msm.insert(q.label.clone(), msm);
            }
            FflonkCommitment::Regular(pairs) => {
                let (p, labels) = FflonkCommitment::<E>::find_bundle(pairs, &q.label);
                if labels.len() == 1 {
                    // Singleton (t=1): pass-through, single-term MSM.
                    singleton_triples.push((q.label.clone(), q.point, q.eval));
                    let mut msm = MSMKZG::init();
                    msm.append_term(E::Fr::ONE, *p, q.label.clone());
                    label_to_msm.insert(q.label.clone(), msm);
                } else {
                    // `t > 1` bundle: accumulate per (synthetic label, logical point).
                    // `labels` holds only the real labels; the logical bundle size `t`
                    // is derived from their count, so a trailing bundle has pad slots
                    // `[labels.len(), t)` whose evals are implicitly zero.
                    let t = partition::bundle_t(labels.len(), t_max);
                    let synth = FflonkCommitment::<E>::synthetic_bundle_label(labels);
                    let acc = multi_bundles.entry(synth).or_insert_with(|| BundleAcc::<E> {
                        bundle_g1: *p,
                        canonical_labels: labels.clone(),
                        t,
                        pairs: Vec::new(),
                        evals: FxHashMap::default(),
                    });
                    let slot = acc
                        .canonical_labels
                        .iter()
                        .position(|l| l == &q.label)
                        .expect("fflonk multi_prepare: query label missing from its bundle");
                    acc.pairs.push((slot, q.point));
                    acc.evals.insert((slot, q.point), q.eval);
                }
            }
        }
    }

    let mut multi_bundles_sorted: Vec<(PolynomialLabel, BundleAcc<E>)> =
        multi_bundles.into_iter().collect();
    multi_bundles_sorted.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));

    (multi_bundles_sorted, label_to_msm, singleton_triples)
}

/// Reconstruct the synthetic `(synth_label, root, g(root))` triples for one
/// multi-poly bundle, using Lemma 5.1's forward Vandermonde
/// ([`eval_claims_as_poly`]) to compute `g(root)` from the per-slot evaluations
/// at each distinct logical point.
///
/// Caller must have filled `acc.evals` with every `(slot, logical)` pair for
/// real slots (slots `< acc.canonical_labels.len()`) before calling this. Pad
/// slots are zero by construction and not present in `acc.evals`; this function
/// fills them with `E::Fr::ZERO`.
pub(super) fn synth_triples_for_bundle<E: MultiMillerLoop>(
    synth_label: &PolynomialLabel,
    acc: &BundleAcc<E>,
    t_th_root_cache: &mut FxHashMap<(E::Fr, usize), E::Fr>,
) -> Vec<(PolynomialLabel, E::Fr, E::Fr)>
where
    E::Fr: Hash + Ord,
{
    let omega_t = primitive_root_of_unity::<E::Fr>(acc.t);
    let real_count = acc.canonical_labels.len();

    // Sorted, like the prover's `union_logicals`, so both sides emit the
    // synthetic queries in the same order.
    let mut union_logicals: Vec<E::Fr> = vec![];
    for &(_, p) in &acc.pairs {
        if !union_logicals.contains(&p) {
            union_logicals.push(p);
        }
    }
    union_logicals.sort();

    let mut triples: Vec<(PolynomialLabel, E::Fr, E::Fr)> = Vec::new();
    for logical in union_logicals {
        // `t_th_root(logical, t)` only depends on the pair, but the function is called
        // per (bundle, logical) and bundles typically share logical points (a point
        // and its rotations), so the cache cuts redundant `log2(t)` sqrt chains.
        let z = *t_th_root_cache
            .entry((logical, acc.t))
            .or_insert_with(|| t_th_root(logical, acc.t));
        let slot_evals: Vec<E::Fr> = (0..acc.t)
            .map(|slot| {
                if slot < real_count {
                    *acc.evals.get(&(slot, logical)).expect(
                        "fflonk multi_prepare: over-opening should have filled every real slot",
                    )
                } else {
                    E::Fr::ZERO
                }
            })
            .collect();
        for r in t_th_roots(z, omega_t, acc.t) {
            triples.push((synth_label.clone(), r, eval_claims_as_poly(&slot_evals, r)));
        }
    }
    triples
}
