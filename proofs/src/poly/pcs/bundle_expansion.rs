//! Bundle pre-expansion data structures and pure helpers.
//!
//! `FflonkScheme::multi_open` and `FflonkScheme::multi_prepare` each have a
//! "fflonk-specific" phase that runs before the standard Halo2:
//!
//! - Prover (`multi_open`): classify queries into bundles, materialise the
//!   combined polynomial `g` for each `t > 1` bundle, compute the over-opening
//!   point-set unions, expand into synthetic queries on `g` at the `t`-th roots
//!   of each logical opening point.
//! - Verifier (`multi_prepare`): classify queries into bundles, collect the
//!   per-(slot, logical) evaluations the prover wrote, reconstruct `g(root)`
//!   for each `t`-th root via Lemma 5.1 of the fflonk paper.
//!
//! The two sides must produce *identical* enumerations of (bundle, slot,
//! point) so the transcript I/O matches.

use std::hash::Hash;

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use midnight_curves::pairing::MultiMillerLoop;
use rustc_hash::{FxHashMap, FxHashSet};

use super::commitment::{find_bundle, synthetic_bundle_label, FflonkBundle, FflonkCommitment};
use crate::{
    poly::{
        pcs::{compute_dummy_queries, msm::MSMKZG, FflonkScheme},
        query::{PolynomialLabel, VerifierQuery},
        ProverQuery,
    },
    utils::{
        arithmetic::{CurveAffine, CurveExt, MSM},
        helpers::ProcessedSerdeObject,
    },
};

/// Per-bundle prover-side preparation. Holds everything `multi_open` needs
/// to (a) write over-opening evals to the transcript and (b) emit the synthetic
/// queries on `g`.
pub(super) struct MultiPreData<F> {
    /// Index into the prover's `sub_bundles` vec. Used to look up `g_poly`
    /// and the canonical labels.
    pub(super) bundle_idx: usize,
    /// Synthetic label shared with the verifier (`fflonk_g[Advice_X]`).
    pub(super) synth_label: PolynomialLabel,
    /// The bundle's logical packing factor `t = bundle_t(real_count, t_max)`.
    /// May exceed the number of real polynomials in the bundle when the
    /// trailing bundle has padded zero slots.
    pub(super) t: usize,
    /// Distinct logical points seen for this bundle, sorted. The synthetic
    /// queries on `g` are emitted at the `t` t-th roots of each.
    pub(super) union_logicals: Vec<F>,
    /// `(slot, logical_point)` pairs the prover needs to over-open and
    /// write to the transcript, in `compute_dummy_queries` insertion order
    /// (so the verifier sees them in the same order). Slots are always
    /// real slot indices (in `[0, real_count)`); pad slots are never
    /// over-opened because their eval is known to be zero.
    pub(super) missing: Vec<(usize, F)>,
}

/// Per-bundle verifier-side accumulator. Holds the bundle's G1 commitment,
/// the canonical labels (so slot indices are well-defined), the
/// `(slot, point)` pairs the verifier saw in queries-iter order (input to
/// `compute_dummy_queries`), and the eval lookup populated both from the
/// original queries and from the over-opening reads.
pub(super) struct BundleAcc<E: MultiMillerLoop> {
    pub(super) bundle_g1: E::G1,
    /// Real labels of the bundle's polynomials, in canonical order. Length
    /// equals `real_count`, which may be less than `t` for the trailing
    /// padded bundle.
    pub(super) canonical_labels: Vec<PolynomialLabel>,
    /// Logical bundle size, `bundle_t(real_count, t_max)`. Slots
    /// `[canonical_labels.len(), t)` are pad slots whose evals are
    /// implicitly zero (never written / read on the transcript).
    pub(super) t: usize,
    pub(super) pairs: Vec<(usize, E::Fr)>,
    pub(super) evals: FxHashMap<(usize, E::Fr), E::Fr>,
}

/// Build the prover-side per-bundle preparation list, sorted by
/// `synth_label.to_string()` so prover and verifier visit bundles in the
/// same order. Pure function, no transcript I/O.
pub(super) fn build_prover_multi_pre<F: PrimeField + Ord + std::hash::Hash>(
    sub_bundles: &[Vec<usize>],
    all_labels: &[PolynomialLabel],
    t_max: usize,
    queries: &[ProverQuery<F>],
) -> Vec<MultiPreData<F>> {
    let mut multi_pre: Vec<MultiPreData<F>> = Vec::with_capacity(sub_bundles.len());
    for (bundle_idx, indices) in sub_bundles.iter().enumerate() {
        let real_count = indices.len();
        let t = super::partition::bundle_t(real_count, t_max);
        if t <= 1 {
            continue;
        }
        let bundle_labels: Vec<PolynomialLabel> =
            indices.iter().map(|&i| all_labels[i].clone()).collect();
        let bundle_label_set: FxHashSet<&PolynomialLabel> = bundle_labels.iter().collect();
        let synth_label = synthetic_bundle_label(&bundle_labels);

        // `(slot, point)` pairs in queries-iter order.
        let pairs: Vec<(usize, F)> = queries
            .iter()
            .filter(|q| bundle_label_set.contains(&q.label))
            .map(|q| {
                let slot = bundle_labels.iter().position(|l| l == &q.label).unwrap();
                (slot, q.point)
            })
            .collect();
        let missing: Vec<(usize, F)> = compute_dummy_queries(&pairs)
            .into_iter()
            .map(|(idx, point)| (pairs[idx].0, point))
            .collect();

        let mut union_set: FxHashSet<F> = FxHashSet::default();
        for &(_, p) in &pairs {
            union_set.insert(p);
        }
        let mut union_logicals: Vec<F> = union_set.into_iter().collect();
        union_logicals.sort();

        multi_pre.push(MultiPreData {
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
/// - `multi_bundles_sorted`: a `Vec` of `(synth_label, BundleAcc)`, sorted by
///   `synth_label.to_string()` so the over-opening read order matches the
///   prover's write order.
/// - `label_to_msm`: per-label MSM source, populated for singletons and
///   `Linear` bundles (the t>1 bundle MSMs are added later, after the
///   over-opening reads, by the caller).
/// - `singleton_triples`: `(label, point, eval)` triples for `t=1` commitments
///   and `Linear`.
///
/// Pure function, no transcript I/O. Mirror of `build_prover_multi_pre`
/// for the verifier side.
#[allow(clippy::type_complexity)]
pub(super) fn classify_verifier_queries<'com, E>(
    queries: &[VerifierQuery<'com, E::Fr, FflonkScheme<E>>],
    // SRS-aware bundling ceiling for this proof (`2^effective_t_log`), read
    // from the transcript by `multi_prepare`. Must equal the `t_max` the
    // prover used in `commit`/`multi_open`, or the reconstructed `bundle_t`
    // (and thus the whole opening) diverges.
    t_max: usize,
) -> (
    Vec<(PolynomialLabel, BundleAcc<E>)>,
    FxHashMap<PolynomialLabel, MSMKZG<E>>,
    Vec<(PolynomialLabel, E::Fr, E::Fr)>,
)
where
    E: MultiMillerLoop,
    E::Fr: WithSmallOrderMulGroup<3> + Hash + Ord,
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
    FflonkCommitment<E>: 'com,
{
    let mut multi_bundles: FxHashMap<PolynomialLabel, BundleAcc<E>> = FxHashMap::default();
    let mut label_to_msm: FxHashMap<PolynomialLabel, MSMKZG<E>> = FxHashMap::default();
    let mut singleton_triples: Vec<(PolynomialLabel, E::Fr, E::Fr)> = Vec::new();

    for q in queries.iter() {
        let bundle = find_bundle(q.commitment, &q.label);
        match bundle {
            FflonkBundle::Bundle(p, labels) if labels.len() == 1 => {
                // Singleton (t=1): pass-through, single-term MSM.
                singleton_triples.push((q.label.clone(), q.point, q.eval));
                let mut msm = MSMKZG::init();
                msm.append_term(E::Fr::ONE, *p, q.label.clone());
                label_to_msm.insert(q.label.clone(), msm);
            }
            FflonkBundle::Bundle(p, labels) => {
                // t>1 bundle: accumulate per (synthetic label, logical point).
                // `labels` holds only the real labels (length = real_count);
                // the logical bundle size `t` is derived from real_count and
                // the scheme's `FFLONK_T_MAX_LOG`. The trailing bundle may have
                // `t > real_count`, with pad slots [real_count, t) whose
                // evals are implicitly zero (never appear in `pairs`).
                let real_count = labels.len();
                let t = super::partition::bundle_t(real_count, t_max);
                let synth = synthetic_bundle_label(labels);
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
            FflonkBundle::Linear(points, scalars, labels) => {
                // Linearization commitment: pass-through, expanded MSM with
                // all (point, scalar, label) terms.
                singleton_triples.push((q.label.clone(), q.point, q.eval));
                let mut msm = MSMKZG::init();
                for ((p, s), label) in points.iter().zip(scalars).zip(labels) {
                    msm.append_term(*s, *p, label.clone());
                }
                label_to_msm.insert(q.label.clone(), msm);
            }
        }
    }

    let mut multi_bundles_sorted: Vec<(PolynomialLabel, BundleAcc<E>)> =
        multi_bundles.into_iter().collect();
    multi_bundles_sorted.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));

    (multi_bundles_sorted, label_to_msm, singleton_triples)
}

/// Reconstruct the synthetic `(synth_label, root, g(root))` triples for one
/// `t > 1` bundle. Uses Lemma 5.1's forward Vandermonde
/// (`eval_claims_as_poly`) to compute `g(root)` from the per-slot
/// evaluations at each distinct logical point.
///
/// Caller must have filled `acc.evals` with every `(slot, logical)` pair
/// for real slots (slots `< acc.canonical_labels.len()`) before calling
/// this. Pad slots (`slot ≥ acc.canonical_labels.len()`) are zero by
/// construction and not present in `acc.evals`: this function fills
/// them with `E::Fr::ZERO`.
pub(super) fn synth_triples_for_bundle<E: MultiMillerLoop>(
    synth_label: &PolynomialLabel,
    acc: &BundleAcc<E>,
    t_th_root_cache: &mut FxHashMap<(E::Fr, usize), E::Fr>,
) -> Vec<(PolynomialLabel, E::Fr, E::Fr)>
where
    E::Fr: std::hash::Hash + Eq,
{
    use ff::Field;

    use super::utils::{
        eval_claims_as_poly, primitive_root_of_unity, roots as t_th_roots, t_th_root,
    };

    let omega_t = primitive_root_of_unity::<E::Fr>(acc.t);
    let real_count = acc.canonical_labels.len();
    let mut union_set: FxHashSet<E::Fr> = FxHashSet::default();
    for &(_, p) in &acc.pairs {
        union_set.insert(p);
    }
    let mut triples: Vec<(PolynomialLabel, E::Fr, E::Fr)> = Vec::new();
    for logical in union_set {
        // Cache across bundles: `t_th_root(logical, t)` only depends on the pair, but
        // the function is called per (bundle, logical). Multiple bundles typically
        // share the same logical points (point + rotations), so caching by `(logical,
        // t)` cuts those redundant `log2(t)` sqrts.
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
                    // Pad slot.
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
