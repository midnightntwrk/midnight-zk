//! fflonk-style polynomial commitment scheme ([reference](https://eprint.iacr.org/2021/1167.pdf)).
//!
//! Packs groups of `t` polynomials of degree `< n` into a single polynomial `g`
//! of degree `< t·n` via `g(X) = Σ_i X^i · f_i(X^t)`, commits once to `g`, and
//! opens at the `t` t-th roots of each logical query point.
//!
//! # Layout
//! - `math`: the curve-free fflonk paper math (`combine`, roots, ...).
//! - `partition`: the deterministic bundling policy.
//! - `commitment`: the `FflonkCommitment` type and its wire format.
//! - `bundle_expansion`: multi-open bundle pre-expansion.
//!
//! # Implementation
//! `commit_many` bundles via `partition::partition`. For each bundle of size
//! `t > 1` it builds `g(X) = Σ_i X^i · f_i(X^t)` from the `f_i` converted to
//! coefficient form; singleton bundles are committed in whichever basis they
//! were given.
//!
//! `multi_open` / `multi_prepare` pre-expand bundled queries into synthetic
//! queries on `g` at the `t`-th roots of each distinct logical opening point,
//! which is the characterisation of Lemma 5.1 of the paper (see
//! `eval_claims_as_poly`). The expansion is the only fflonk-specific phase;
//! everything downstream is the standard Halo2 multi-open argument, shared with
//! KZG through `multi_open_core`.
//!
//! # Protocol invariant
//! All polynomials of one bundlable family must be committed in a single
//! `commit_many` call: `multi_open` re-derives the bundles by partitioning the
//! labels it is queried on, and that partition has to reproduce the one used at
//! commit time. A prover violating this opens polynomials the commitments do
//! not contain, which the final pairing check rejects.
//!
//! TODO: for now, computing `g` is only possible if each `f_i` is in
//! coefficient form; `commit_many` converts otherwise. Native support for the
//! other bases will be implemented in the future.

use std::{borrow::Borrow, collections::BTreeMap, fmt::Debug, hash::Hash, marker::PhantomData};

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use midnight_curves::pairing::{Engine, MultiMillerLoop};
use rand_core::OsRng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};

pub mod commitment;

mod bundle_expansion;
mod math;
mod partition;

pub use commitment::FflonkCommitment;
// Re-exported for the in-circuit fflonk verifier, which re-derives the same
// bundle layout and the same `t`-th roots the off-circuit verifier does.
pub use math::{primitive_root_of_unity, t_th_root};
pub use partition::{bundle_t, partition};

pub use self::bundle_expansion::missing_openings;
use self::math::{combine, roots as t_th_roots};
#[cfg(feature = "fewer-point-sets")]
use crate::pcs::utils::compute_dummy_queries;
use crate::{
    pcs::{
        msm::{DualMSM, MSMKZG, msm_specific},
        multi_open::{multi_open_core, multi_prepare_core},
        params::{ParamsKZG, ParamsVerifierKZG},
        scheme::{Guard, Params, PolynomialCommitmentScheme},
    },
    poly::{
        Coeff, Error, EvaluationDomain, LagrangeCoeff, LagrangeDeltaCoeff,
        LagrangeDoubleDeltaCoeff, Polynomial, PolynomialBasis, PolynomialRepresentation,
        ProverQuery,
        query::{PolynomialLabel, VerifierQuery},
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{
        arithmetic::{CurveAffine, CurveExt, MSM, eval_polynomial},
        helpers::{ProcessedSerdeObject, SerdeFormat},
    },
};

/// The scheme-wide bundling exponent: fflonk packs up to `1 <<
/// FFLONK_T_MAX_LOG` polynomials into a single commitment. `0` means no
/// bundling (algebraically identical to classic KZG).
pub const FFLONK_T_MAX_LOG: u32 = 0;

/// Bundling ceiling actually usable for a circuit over a domain of size `n`.
/// The maximal bundle size is `1 << t_max_log`, capped by three independent
/// limits:
///
///   * the scheme-wide exponent [`FFLONK_T_MAX_LOG`],
///   * SRS room: `t_max_log ≤ log2(g_monomial_size) − log2(n)`,
///   * field 2-adicity: `t_max_log ≤ F::S − log2(n)`, so that the `t`-th roots
///     of the evaluation points exist.
///
/// The prover writes the resulting `t_max_log` to the transcript; the verifier
/// reads it back and range-checks it against `[0, FFLONK_T_MAX_LOG]` only. The
/// two other caps are not re-enforced verifier-side: a mismatched value yields
/// a partition that disagrees with the committed one, which the final pairing
/// check rejects.
// The caps are vacuous while `FFLONK_T_MAX_LOG` is 0, which clippy reports as a
// pointless `min`; they are load-bearing as soon as it is raised.
#[allow(clippy::unnecessary_min_or_max)]
fn effective_t_max_log<E: Engine>(params: &ParamsKZG<E>, n: usize) -> u32
where
    E::G1Affine: CurveAffine,
{
    let log_n = n.ilog2();
    let srs_room = params.g_monomial_size().ilog2().saturating_sub(log_n);
    let field_room = <E::Fr as PrimeField>::S.saturating_sub(log_n);
    FFLONK_T_MAX_LOG.min(srs_room).min(field_room)
}

/// The fflonk polynomial commitment scheme over a pairing-friendly curve `E`.
#[derive(Clone, Debug)]
pub struct FflonkScheme<E: Engine> {
    _marker: PhantomData<E>,
}

/// Verification guard for [`FflonkScheme`], a transparent wrapper around the
/// [`DualMSM`] KZG guard: fflonk's final check is the same pairing check.
///
/// It is a distinct type rather than `DualMSM` itself because a second
/// `Guard` impl on `DualMSM` would make `guard.verify(params)` ambiguous for
/// callers that do not name the scheme.
#[derive(Clone, Debug)]
pub struct FflonkVerificationGuard<E: MultiMillerLoop>(DualMSM<E>);

impl<E: MultiMillerLoop + Debug> FflonkVerificationGuard<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    /// Extracts the underlying [`DualMSM`], for callers that batch guards
    /// across proofs before a joint pairing check.
    pub fn into_dual_msm(self) -> DualMSM<E> {
        self.0
    }

    /// Scales both sides of the accumulated pairing check.
    pub fn scale(&mut self, factor: E::Fr) {
        self.0.scale(factor)
    }

    /// Folds another guard into this one, for batch verification.
    pub fn add_msm(&mut self, other: Self) {
        self.0.add_msm(other.0)
    }

    /// Whether the accumulated pairing check holds.
    pub fn check(self, params: &ParamsVerifierKZG<E>) -> bool {
        self.0.check(params)
    }
}

impl<E: MultiMillerLoop> PolynomialCommitmentScheme<E::Fr> for FflonkScheme<E>
where
    E::Fr: WithSmallOrderMulGroup<3>,
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    type Parameters = ParamsKZG<E>;
    type VerifierParameters = ParamsVerifierKZG<E>;
    type Commitment = FflonkCommitment<E>;
    type VerificationGuard = FflonkVerificationGuard<E>;

    fn gen_params(k: u32) -> Self::Parameters {
        ParamsKZG::unsafe_setup(k, OsRng)
    }

    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters {
        params.verifier_params()
    }

    /// A bundle of `t` polynomials over the circuit domain is a single
    /// polynomial of degree `t·2^k − 1`, so the scheme commits up to
    /// `T_MAX·2^k − 1` unless a larger polynomial is committed as a singleton
    /// (the quotient under `single-h-commitment`).
    fn internal_degree(k: u32, max_poly_degree: usize) -> usize {
        let bundle_degree = (1usize << (k + FFLONK_T_MAX_LOG)) - 1;
        bundle_degree.max(max_poly_degree)
    }

    /// fflonk requires the evaluation point to be a `T_MAX`-th power, so that
    /// the verifier can compute `t`-th roots for each bundle (each `t` divides
    /// `T_MAX = 2^FFLONK_T_MAX_LOG`, so any `T_MAX`-th power is also a `t`-th
    /// power). We squeeze `s` and return `s^T_MAX`.
    ///
    /// Soundness / ZK: `x = s^T_MAX` is uniformly distributed in the
    /// `T_MAX`-th-power subgroup of `F*` (order `(p-1)/T_MAX`), which is
    /// essentially full-sized for the BLS12 scalar field (`p-1 ≈ 2^254`).
    /// Schwartz-Zippel arguments and protocol blinding are unaffected.
    fn squeeze_evaluation_point<T: Transcript>(transcript: &mut T) -> E::Fr
    where
        E::Fr: Sampleable<T::Hash>,
    {
        // `FFLONK_T_MAX_LOG` must not exceed the field's 2-adicity: otherwise
        // `s^(2^FFLONK_T_MAX_LOG)` collapses into the odd-order subgroup and the
        // shift below overflows. Both operands are compile-time constants, so
        // this is a static check evaluated once per curve.
        #[allow(clippy::absurd_extreme_comparisons)]
        const {
            assert!(FFLONK_T_MAX_LOG <= <E::Fr as PrimeField>::S)
        };
        let s: E::Fr = transcript.squeeze_challenge();
        s.pow_vartime([1u64 << FFLONK_T_MAX_LOG])
    }

    fn commitment_byte_length(n: usize) -> usize {
        // A commitment is a bundle count followed by, per bundle, a polynomial
        // count and a group element. The `n` polynomials are assumed unbundled,
        // which is what the shipped `FFLONK_T_MAX_LOG = 0` produces; the cost
        // model does not track bundling.
        let single = Self::Commitment::default().byte_length(SerdeFormat::Processed);
        1 + n * (single - 1)
    }

    fn commit_many<B: PolynomialRepresentation, P: Borrow<Polynomial<E::Fr, B>> + Sync>(
        params: &Self::Parameters,
        polynomials: &BTreeMap<PolynomialLabel, P>,
    ) -> Self::Commitment {
        assert!(!polynomials.is_empty(), "cannot commit to zero polynomials");

        // The map fixes the bundling order to the labels' `Ord` order, which is the
        // order `read_commitment` tags the bundles it reads in.
        let labels: Vec<PolynomialLabel> = polynomials.keys().cloned().collect();
        let polynomials: Vec<&Polynomial<E::Fr, B>> =
            polynomials.values().map(Borrow::borrow).collect();

        // All polys of one call must share their length, so that the bundle's `n`
        // is well-defined and `combine` produces a length-`t·n` g.
        let n = polynomials[0].values.len();
        assert!(
            polynomials.iter().all(|p| p.values.len() == n),
            "fflonk commit: all polys in one call must have equal length"
        );

        // Shrink the bundling exponent to whatever the loaded SRS can afford for
        // this `n`. `multi_open` writes the same exponent to the transcript, and
        // the per-bundle sizes travel with the commitment, so the verifier
        // reconstructs the same partition.
        let t_max = 1usize << effective_t_max_log(params, n);
        let bundle_indices = partition::partition(t_max, &labels);

        let bases_b = params.bases::<B>();
        let mono_bases = &params.g;

        let bundles: Vec<(E::G1, Vec<PolynomialLabel>)> = bundle_indices
            .into_par_iter()
            .map(|indices| {
                let t = partition::bundle_t(indices.len(), t_max);
                if t == 1 {
                    // Singleton: MSM over the polynomial's own basis, as in KZG.
                    let idx = indices[0];
                    let p = polynomials[idx];
                    let size = p.values.len();
                    assert!(bases_b.len() >= size);
                    let g1 = msm_specific::<E::G1Affine>(&p.values, &bases_b[..size]);
                    (g1, vec![labels[idx].clone()])
                } else {
                    // Multi-poly bundle: convert to coefficient form (if needed), combine
                    // into `g` over `t` slots (padding with null polys), and MSM over the
                    // monomial bases.
                    let coeff_values_per_slot =
                        to_coeff_slots::<E, B>(&polynomials, &indices, n.trailing_zeros());
                    let slot_refs: Vec<&[E::Fr]> =
                        coeff_values_per_slot.iter().map(Vec::as_slice).collect();
                    let g_values = combine(&slot_refs, t);
                    let g1 = msm_specific::<E::G1Affine>(&g_values, &mono_bases[..t * n]);
                    let bundle_labels: Vec<PolynomialLabel> =
                        indices.iter().map(|&i| labels[i].clone()).collect();
                    (g1, bundle_labels)
                }
            })
            .collect();

        FflonkCommitment::Regular(bundles)
    }

    fn read_commitment<T: Transcript>(
        transcript: &mut T,
        labels: &[PolynomialLabel],
    ) -> std::io::Result<Self::Commitment>
    where
        Self::Commitment: Hashable<T::Hash>,
    {
        // The bundle sizes are on the wire, so the read yields the grouping with
        // placeholder labels; `with_labels` fills in the real ones.
        let commitment: FflonkCommitment<E> = transcript.read()?;
        Ok(commitment.with_labels(labels))
    }

    fn deserialize_commitment<R: std::io::Read>(
        reader: &mut R,
        format: SerdeFormat,
        labels: &[PolynomialLabel],
    ) -> std::io::Result<Self::Commitment> {
        FflonkCommitment::<E>::read_labeled(reader, format, labels)
    }

    fn write_commitment<T: Transcript>(
        transcript: &mut T,
        commitment: &Self::Commitment,
    ) -> std::io::Result<()>
    where
        Self::Commitment: Hashable<T::Hash>,
    {
        // All bundles of one commitment go out as a single transcript object.
        transcript.write(commitment)
    }

    fn multi_open<T: Transcript>(
        params: &Self::Parameters,
        queries: &[ProverQuery<E::Fr>],
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        E::Fr: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        FflonkCommitment<E>: Hashable<T::Hash>,
    {
        // === Bundle pre-expansion (fflonk-specific) ===
        //
        // Replace the queries targeting a `t > 1` bundle with synthetic queries on
        // the bundle's combined polynomial `g`, at the `t`-th roots of each distinct
        // logical opening point.

        // Distinct query labels, in first-appearance order, and the polynomial each
        // one identifies.
        let mut poly_lookup: FxHashMap<PolynomialLabel, &Polynomial<E::Fr, Coeff>> =
            FxHashMap::default();
        let mut all_labels: Vec<PolynomialLabel> = Vec::new();
        for q in queries.iter() {
            if poly_lookup.insert(q.label.clone(), q.poly).is_none() {
                all_labels.push(q.label.clone());
            }
        }

        // Bundling ceiling, mirroring the one `commit_many` derived from the SRS.
        let t_max_log = all_labels
            .iter()
            .find(|l| partition::poly_is_combinable(l))
            .map(|l| poly_lookup[l].values.len())
            .map_or(0, |n| effective_t_max_log(params, n));
        transcript
            .write(&E::Fr::from(t_max_log as u64))
            .map_err(|_| Error::OpeningError)?;
        let t_max = 1usize << t_max_log;

        // Theoretically unreachable, but the code below would panic on it.
        if all_labels.is_empty() {
            return Ok(());
        }
        let bundle_indices = partition::partition(t_max, &all_labels);

        // Materialise `g` for each `t > 1` bundle, indexed by bundle position.
        let g_polys: Vec<Option<Polynomial<E::Fr, Coeff>>> = bundle_indices
            .iter()
            .map(|indices| {
                let t = partition::bundle_t(indices.len(), t_max);
                if t <= 1 {
                    return None;
                }
                let n_bundle = poly_lookup[&all_labels[indices[0]]].values.len();
                assert!(
                    indices.iter().all(|&i| poly_lookup[&all_labels[i]].values.len() == n_bundle),
                    "fflonk multi_open: polys within a `t > 1` bundle must have equal length"
                );
                let slot_refs: Vec<&[E::Fr]> = indices
                    .iter()
                    .map(|&i| poly_lookup[&all_labels[i]].values.as_slice())
                    .collect();
                Some(Polynomial {
                    values: combine(&slot_refs, t),
                    _marker: PhantomData,
                })
            })
            .collect();

        // Per-bundle preparation: union of logical points, the (slot, point) pairs to
        // over-open, and the synthetic label.
        let multi_pre = bundle_expansion::build_prover_multi_pre::<E>(
            &bundle_indices,
            &all_labels,
            t_max,
            queries,
        );

        // Over-opening writes: a `t > 1` bundle needs every slot opened at every
        // point of the bundle's logical union.
        for pre in &multi_pre {
            for &(slot, logical) in &pre.missing {
                let poly = poly_lookup[&all_labels[bundle_indices[pre.bundle_idx][slot]]];
                let eval = eval_polynomial(&poly[..], logical);
                transcript.write(&eval).map_err(|_| Error::OpeningError)?;
            }
        }

        // Queries on singleton bundles are opened as they are.
        let bundled: FxHashSet<PolynomialLabel> = bundle_indices
            .iter()
            .filter(|indices| indices.len() > 1)
            .flat_map(|indices| indices.iter().map(|&i| all_labels[i].clone()))
            .collect();
        // Only extended under `fewer-point-sets`.
        #[allow(unused_mut)]
        let mut singleton_queries: Vec<ProverQuery<E::Fr>> =
            queries.iter().filter(|q| !bundled.contains(&q.label)).cloned().collect();

        // `fewer-point-sets` applies to the singleton slice only: the bundled
        // queries have been replaced by synthetic ones on `g`, whose point sets are
        // the `t`-th roots.
        #[cfg(feature = "fewer-point-sets")]
        {
            let pairs: Vec<(PolynomialLabel, E::Fr)> =
                singleton_queries.iter().map(|q| (q.label.clone(), q.point)).collect();
            for (idx, point) in compute_dummy_queries(&pairs) {
                let poly = singleton_queries[idx].poly;
                let label = singleton_queries[idx].label.clone();
                transcript
                    .write(&eval_polynomial(&poly[..], point))
                    .map_err(|_| Error::OpeningError)?;
                singleton_queries.push(ProverQuery::new(point, poly, label));
            }
        }

        // Bundle-synth slice: `t` queries on `g` at the t-th roots of each logical
        // point of the union (uniform across slots after over-opening). The
        // `t_th_root(logical, t)` cache is shared across bundles, which typically
        // open at the same logical points (ζ, ζ·ω, ...).
        let mut t_th_root_cache: FxHashMap<(E::Fr, usize), E::Fr> = FxHashMap::default();
        let mut expanded_queries = singleton_queries;
        for pre in &multi_pre {
            let g_poly =
                g_polys[pre.bundle_idx].as_ref().expect("g_poly must be Some for a t>1 bundle");
            let omega_t = primitive_root_of_unity::<E::Fr>(pre.t);
            for &logical in &pre.union_logicals {
                let z = *t_th_root_cache
                    .entry((logical, pre.t))
                    .or_insert_with(|| t_th_root(logical, pre.t));
                for r in t_th_roots(z, omega_t, pre.t) {
                    expanded_queries.push(ProverQuery::new(r, g_poly, pre.synth_label.clone()));
                }
            }
        }

        multi_open_core::<E::Fr, Self, T>(params, &expanded_queries, transcript)
    }

    fn multi_prepare<'com, T: Transcript>(
        queries: &[VerifierQuery<'com, E::Fr, FflonkScheme<E>>],
        transcript: &mut T,
    ) -> Result<FflonkVerificationGuard<E>, Error>
    where
        E::Fr: Sampleable<T::Hash> + Ord + Hash + Hashable<T::Hash>,
        E::G1: CurveExt<ScalarExt = E::Fr>,
        FflonkCommitment<E>: Hashable<T::Hash> + 'com,
    {
        // The prover's bundling ceiling, sent as a field element. Recover the
        // integer by matching against the field encoding of each value in the valid
        // band `[0, FFLONK_T_MAX_LOG]`. The SRS-room and 2-adicity caps are not
        // re-enforced here: an out-of-band claim just yields a partition that
        // mismatches the committed one, which the pairing check rejects.
        let claimed: E::Fr = transcript.read().map_err(|_| Error::SamplingError)?;
        let t_max_log = (0..=FFLONK_T_MAX_LOG)
            .find(|&i| claimed == E::Fr::from(i as u64))
            .ok_or(Error::OpeningError)?;
        let t_max = 1usize << t_max_log;

        // Bind the bundle sizes read off the wire to the transcript, see
        // `check_bundle_layout`. Commitments are deduplicated by address, since the
        // same one backs one query per polynomial it holds.
        let mut checked: Vec<*const FflonkCommitment<E>> = Vec::new();
        for q in queries.iter() {
            if let FflonkCommitment::Regular(pairs) = q.commitment {
                let addr = q.commitment as *const _;
                if !checked.contains(&addr) {
                    bundle_expansion::check_bundle_layout::<E>(pairs, t_max)?;
                    checked.push(addr);
                }
            }
        }

        // === Bundle pre-expansion (fflonk-specific) ===
        //
        // Singletons and `Linear` commitments pass through with their own (label,
        // point, eval) triple. Queries on a `t > 1` bundle are gathered per logical
        // point and expanded into synthetic triples on the bundle's `g`, whose
        // evaluations at the `t`-th roots are reconstructed through Lemma 5.1.

        // `singleton_triples` is only extended under `fewer-point-sets`.
        #[allow(unused_mut)]
        let (mut multi_bundles_sorted, mut label_to_msm, mut singleton_triples) =
            bundle_expansion::classify_verifier_queries::<E>(queries, t_max);

        // Over-opening reads, paired with the writes in `multi_open`.
        for (_synth, acc) in multi_bundles_sorted.iter_mut() {
            for (pair_idx, point) in bundle_expansion::missing_openings(&acc.pairs) {
                let slot = acc.pairs[pair_idx].0;
                let eval: E::Fr = transcript.read().map_err(|_| Error::SamplingError)?;
                acc.evals.insert((slot, point), eval);
            }
        }

        #[cfg(feature = "fewer-point-sets")]
        {
            let pairs: Vec<(PolynomialLabel, E::Fr)> = singleton_triples
                .iter()
                .map(|(label, point, _)| (label.clone(), *point))
                .collect();
            for (idx, point) in compute_dummy_queries(&pairs) {
                let label = singleton_triples[idx].0.clone();
                let eval: E::Fr = transcript.read().map_err(|_| Error::SamplingError)?;
                // `label_to_msm` already maps `label`, so no new entry is needed.
                singleton_triples.push((label, point, eval));
            }
        }

        let mut triples = singleton_triples;
        let mut t_th_root_cache: FxHashMap<(E::Fr, usize), E::Fr> = FxHashMap::default();
        for (synth_label, acc) in multi_bundles_sorted.into_iter() {
            triples.extend(bundle_expansion::synth_triples_for_bundle::<E>(
                &synth_label,
                &acc,
                &mut t_th_root_cache,
            ));
            let mut msm = MSMKZG::init();
            msm.append_term(E::Fr::ONE, acc.bundle_g1, synth_label.clone());
            label_to_msm.insert(synth_label, msm);
        }

        let msm_accumulator = multi_prepare_core::<E, MSMKZG<E>, T>(
            &triples,
            &label_to_msm,
            transcript,
            |transcript| {
                // `f` and `π` commit to a single polynomial, so anything else on the
                // wire is a malformed proof and must be rejected, not panicked on.
                let commitment: FflonkCommitment<E> =
                    transcript.read().map_err(|_| Error::SamplingError)?;
                commitment.single_point().copied().ok_or(Error::OpeningError)
            },
        )?;
        Ok(FflonkVerificationGuard(msm_accumulator))
    }
}

/// The polynomials of a bundle, in coefficient form, in bundle-slot order.
/// Lagrange-family bases are reinterpreted in their concrete basis, folded back
/// to `LagrangeCoeff` and interpolated; only that fold-back differs per basis.
fn to_coeff_slots<E: MultiMillerLoop, B: PolynomialRepresentation>(
    polynomials: &[&Polynomial<E::Fr, B>],
    indices: &[usize],
    log_n: u32,
) -> Vec<Vec<E::Fr>>
where
    E::Fr: WithSmallOrderMulGroup<3>,
{
    if let PolynomialBasis::Coeff = B::BASIS {
        return indices.iter().map(|&i| polynomials[i].values.clone()).collect();
    }

    let domain = EvaluationDomain::<E::Fr>::new(1, log_n);
    let to_lagrange = |values: Vec<E::Fr>| -> Polynomial<E::Fr, LagrangeCoeff> {
        match B::BASIS {
            PolynomialBasis::Lagrange => Polynomial {
                values,
                _marker: PhantomData,
            },
            PolynomialBasis::LagrangeDelta => Polynomial::<E::Fr, LagrangeDeltaCoeff> {
                values,
                _marker: PhantomData,
            }
            .into_lagrange(),
            PolynomialBasis::LagrangeDoubleDelta => Polynomial::<E::Fr, LagrangeDoubleDeltaCoeff> {
                values,
                _marker: PhantomData,
            }
            .into_lagrange(),
            other => panic!(
                "fflonk t>1 bundling not supported for basis {other:?} (Coeff, Lagrange, \
                 LagrangeDelta, LagrangeDoubleDelta only)"
            ),
        }
    };
    indices
        .iter()
        .map(|&i| {
            let lagrange = to_lagrange(polynomials[i].values.clone());
            domain.lagrange_to_coeff(lagrange).values
        })
        .collect()
}

/// The final pairing check is identical to KZG's; we delegate to the inner
/// [`DualMSM`].
impl<E: MultiMillerLoop> Guard<E::Fr, FflonkScheme<E>> for FflonkVerificationGuard<E>
where
    E::Fr: WithSmallOrderMulGroup<3>,
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn verify(self, params: &ParamsVerifierKZG<E>) -> Result<(), Error> {
        self.0.check(params).then_some(()).ok_or(Error::OpeningError)
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, hash::Hash};

    use blake2b_simd::State as Blake2bState;
    use ff::WithSmallOrderMulGroup;
    use midnight_curves::{CurveAffine, CurveExt, pairing::MultiMillerLoop, serde::SerdeObject};
    use rand_core::OsRng;

    use super::{FFLONK_T_MAX_LOG, FflonkCommitment, FflonkScheme, effective_t_max_log};
    use crate::{
        pcs::{
            Guard, PolynomialCommitmentScheme,
            params::{ParamsKZG, ParamsVerifierKZG},
        },
        poly::{
            EvaluationDomain, PolynomialLabel,
            query::{ProverQuery, VerifierQuery},
        },
        transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
        utils::{
            arithmetic::eval_polynomial,
            helpers::{ProcessedSerdeObject, SerdeFormat},
        },
    };

    /// Round-trip mirroring `kzg::tests::test_roundtrip_gwc`: commits three
    /// polynomials, runs `multi_open` + `multi_prepare` end-to-end, and asserts
    /// the pairing check passes (and fails when one eval is tampered with).
    #[test]
    fn test_roundtrip_gwc() {
        use midnight_curves::Bls12;

        const K: u32 = 4;

        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);

        let proof = create_proof::<_, CircuitTranscript<Blake2bState>>(&params);

        let verifier_params = params.verifier_params();
        verify::<Bls12, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], false);
        verify::<Bls12, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], true);
    }

    /// `deserialize_commitment` groups the labels it is given by the per-bundle
    /// sizes read off the wire, and re-sorts deliberately shuffled labels into
    /// canonical order. This is what lets the verifier follow the prover's
    /// effective bundling factor instead of re-deriving it.
    #[test]
    fn read_groups_by_bundle_sizes_and_reorders() {
        use group::Group;
        use midnight_curves::{Bls12, G1Projective};

        // Three bundles packing 2, 2 and 1 polynomials.
        let g = G1Projective::generator();
        let com = FflonkCommitment::<Bls12>::Regular(vec![
            (g, vec![PolynomialLabel::NoLabel; 2]),
            (g + g, vec![PolynomialLabel::NoLabel; 2]),
            (g + g + g, vec![PolynomialLabel::NoLabel; 1]),
        ]);
        let mut bytes = vec![];
        com.write(&mut bytes, SerdeFormat::Processed).unwrap();

        // Labels supplied out of order: the read sorts them canonically, then
        // chunks them by the bundle sizes.
        let labels: Vec<_> = [4usize, 1, 3, 0, 2].map(PolynomialLabel::Advice).to_vec();
        let read = FflonkScheme::<Bls12>::deserialize_commitment(
            &mut &bytes[..],
            SerdeFormat::Processed,
            &labels,
        )
        .unwrap();

        let FflonkCommitment::Regular(pairs) = read else {
            panic!("expected Regular");
        };
        let groups: Vec<Vec<_>> = pairs.into_iter().map(|(_, l)| l).collect();
        assert_eq!(
            groups,
            vec![
                vec![PolynomialLabel::Advice(0), PolynomialLabel::Advice(1)],
                vec![PolynomialLabel::Advice(2), PolynomialLabel::Advice(3)],
                vec![PolynomialLabel::Advice(4)],
            ]
        );
    }

    /// A commitment whose wire sizes do not encode `partition(t_max, labels)`
    /// is rejected: the sizes are not hashed, so they are bound to the
    /// transcript-carried `t_max` by this check. Const-independent.
    #[test]
    fn forged_bundle_layout_is_rejected() {
        use group::Group;
        use midnight_curves::{Bls12, G1Projective};

        use super::bundle_expansion::check_bundle_layout;

        let g = G1Projective::generator();
        let labels = [PolynomialLabel::Advice(0), PolynomialLabel::Advice(1)];
        let as_bundle = vec![(g, labels.to_vec())];
        let as_singletons = vec![(g, vec![labels[0].clone()]), (g, vec![labels[1].clone()])];

        // Without bundling the only legal layout is one bundle per polynomial.
        assert!(check_bundle_layout::<Bls12>(&as_singletons, 1).is_ok());
        assert!(check_bundle_layout::<Bls12>(&as_bundle, 1).is_err());

        // At `t_max = 2` both advice polys must be packed together.
        assert!(check_bundle_layout::<Bls12>(&as_bundle, 2).is_ok());
        assert!(check_bundle_layout::<Bls12>(&as_singletons, 2).is_err());
    }

    /// End-to-end round-trip through a real `t > 1` bundle (provisioned SRS, so
    /// the effective bundling factor equals the const). Commits `t` combinable
    /// polynomials in one `commit_many`, opens them, and checks the pairing.
    /// No-op at the shipped `FFLONK_T_MAX_LOG = 0`; bump the const to activate
    /// it in a test round.
    #[test]
    fn bundled_roundtrip_with_provisioned_srs() {
        use midnight_curves::{Bls12, Fq};

        if FFLONK_T_MAX_LOG == 0 {
            return;
        }
        const K: u32 = 4;
        let n = 1usize << K;
        let t = 1usize << FFLONK_T_MAX_LOG;

        // Extended monomial basis 2^(K + FFLONK_T_MAX_LOG) => effective == const.
        let mut params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K + FFLONK_T_MAX_LOG, OsRng);
        params.downsize_lagrange(K);
        assert_eq!(effective_t_max_log(&params, n), FFLONK_T_MAX_LOG);

        let domain = EvaluationDomain::new(1, K);
        let polys: Vec<_> = (0..t)
            .map(|j| {
                let mut p = domain.empty_coeff();
                for (i, c) in p.iter_mut().enumerate() {
                    *c = Fq::from((j * n + i + 1) as u64);
                }
                p
            })
            .collect();
        let labels: Vec<_> = (0..t).map(PolynomialLabel::Advice).collect();

        // Prover.
        let mut transcript = CircuitTranscript::<Blake2bState>::init();
        let polys_map: BTreeMap<_, _> = labels.iter().cloned().zip(polys.iter()).collect();
        let com = FflonkScheme::<Bls12>::commit_many(&params, &polys_map);
        match &com {
            FflonkCommitment::Regular(p) => assert_eq!(p.len(), 1, "expected one t>1 bundle"),
            _ => panic!("expected Regular"),
        }
        FflonkScheme::<Bls12>::write_commitment(&mut transcript, &com).unwrap();
        let x = FflonkScheme::<Bls12>::squeeze_evaluation_point(&mut transcript);
        for p in &polys {
            transcript.write(&eval_polynomial(p, x)).unwrap();
        }
        let queries: Vec<_> = polys
            .iter()
            .zip(&labels)
            .map(|(p, l)| ProverQuery::new(x, p, l.clone()))
            .collect();
        FflonkScheme::<Bls12>::multi_open(&params, &queries, &mut transcript).unwrap();
        let proof = transcript.finalize();

        // Verifier.
        let vp = params.verifier_params();
        let mut vt = CircuitTranscript::<Blake2bState>::init_from_bytes(&proof);
        let read_com = FflonkScheme::<Bls12>::read_commitment(&mut vt, &labels).unwrap();
        match &read_com {
            FflonkCommitment::Regular(p) => {
                assert_eq!(p.len(), 1);
                assert_eq!(p[0].1.len(), t, "bundle must carry all t labels");
            }
            _ => panic!("expected Regular"),
        }
        let vx = FflonkScheme::<Bls12>::squeeze_evaluation_point(&mut vt);
        let vevals: Vec<Fq> = (0..t).map(|_| vt.read().unwrap()).collect();
        let vqueries: Vec<_> = labels
            .iter()
            .zip(&vevals)
            .map(|(l, e)| VerifierQuery::new(vx, &read_com, l.clone(), *e))
            .collect();
        let guard = FflonkScheme::<Bls12>::multi_prepare(&vqueries, &mut vt).unwrap();
        assert!(
            Guard::<Fq, FflonkScheme<Bls12>>::verify(guard, &vp).is_ok(),
            "bundled proof must verify"
        );
    }

    /// Round-trip over several bundles whose slots are opened at *different*
    /// points, which is what forces the over-opening writes/reads, plus a
    /// padded trailing bundle and a non-combinable singleton. No-op at the
    /// shipped `FFLONK_T_MAX_LOG = 0`.
    #[test]
    fn bundled_roundtrip_with_rotations_and_singleton() {
        use midnight_curves::{Bls12, Fq};

        if FFLONK_T_MAX_LOG == 0 {
            return;
        }
        const K: u32 = 4;
        let n = 1usize << K;
        let t = 1usize << FFLONK_T_MAX_LOG;

        let mut params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K + FFLONK_T_MAX_LOG, OsRng);
        params.downsize_lagrange(K);

        let domain = EvaluationDomain::new(1, K);
        let omega = domain.get_omega();

        // `t + 3` advice polys: one full bundle plus a trailing one, padded when
        // `t > 4`. The `Fixed` poly is not combinable, so it stays a singleton.
        let nb_advice = t + 3;
        let polys: Vec<_> = (0..nb_advice + 1)
            .map(|j| {
                let mut p = domain.empty_coeff();
                for (i, c) in p.iter_mut().enumerate() {
                    *c = Fq::from((j * n + i + 1) as u64);
                }
                p
            })
            .collect();
        let labels: Vec<_> = (0..nb_advice)
            .map(PolynomialLabel::Advice)
            .chain([PolynomialLabel::Fixed(0)])
            .collect();

        // Prover.
        let mut transcript = CircuitTranscript::<Blake2bState>::init();
        let polys_map: BTreeMap<_, _> = labels.iter().cloned().zip(polys.iter()).collect();
        let com = FflonkScheme::<Bls12>::commit_many(&params, &polys_map);
        FflonkScheme::<Bls12>::write_commitment(&mut transcript, &com).unwrap();

        let x = FflonkScheme::<Bls12>::squeeze_evaluation_point(&mut transcript);
        // Every other polynomial is opened at the rotated point, so the slots of a
        // bundle disagree on their opening points.
        let point_of = |i: usize| if i.is_multiple_of(2) { x } else { x * omega };
        let evals: Vec<Fq> =
            polys.iter().enumerate().map(|(i, p)| eval_polynomial(p, point_of(i))).collect();
        for e in &evals {
            transcript.write(e).unwrap();
        }
        let queries: Vec<_> = polys
            .iter()
            .zip(&labels)
            .enumerate()
            .map(|(i, (p, l))| ProverQuery::new(point_of(i), p, l.clone()))
            .collect();
        FflonkScheme::<Bls12>::multi_open(&params, &queries, &mut transcript).unwrap();
        let proof = transcript.finalize();

        // Verifier.
        let vp = params.verifier_params();
        let mut vt = CircuitTranscript::<Blake2bState>::init_from_bytes(&proof);
        let read_com = FflonkScheme::<Bls12>::read_commitment(&mut vt, &labels).unwrap();
        let vx = FflonkScheme::<Bls12>::squeeze_evaluation_point(&mut vt);
        let vevals: Vec<Fq> = (0..labels.len()).map(|_| vt.read().unwrap()).collect();
        assert_eq!(vevals, evals);
        let vqueries: Vec<_> = labels
            .iter()
            .zip(&vevals)
            .enumerate()
            .map(|(i, (l, e))| {
                let point = if i % 2 == 0 { vx } else { vx * omega };
                VerifierQuery::new(point, &read_com, l.clone(), *e)
            })
            .collect();
        let guard = FflonkScheme::<Bls12>::multi_prepare(&vqueries, &mut vt).unwrap();
        assert!(
            Guard::<Fq, FflonkScheme<Bls12>>::verify(guard, &vp).is_ok(),
            "bundled proof with rotations must verify"
        );
    }

    /// Two `t > 1` bundles with identical layout add homomorphically:
    /// `commit(P) + commit(Q)` equals `commit(P + Q)` slot-wise, a single
    /// point. No-op at the shipped `FFLONK_T_MAX_LOG = 0`.
    #[test]
    fn add_same_layout_bundles_is_homomorphic() {
        use midnight_curves::{Bls12, Fq};

        if FFLONK_T_MAX_LOG == 0 {
            return;
        }
        const K: u32 = 4;
        let n = 1usize << K;
        let t = 1usize << FFLONK_T_MAX_LOG;

        let mut params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K + FFLONK_T_MAX_LOG, OsRng);
        params.downsize_lagrange(K);

        let domain = EvaluationDomain::new(1, K);
        let labels: Vec<_> = (0..t).map(PolynomialLabel::Advice).collect();

        let bundle = |seed: u64| -> Vec<_> {
            (0..t)
                .map(|j| {
                    let mut p = domain.empty_coeff();
                    for (i, c) in p.iter_mut().enumerate() {
                        *c = Fq::from(seed * 1000 + (j * n + i + 1) as u64);
                    }
                    p
                })
                .collect()
        };
        let polys_a = bundle(1);
        let polys_b = bundle(2);
        let polys_sum: Vec<_> = polys_a.iter().zip(&polys_b).map(|(a, b)| a.clone() + b).collect();

        let map_a: BTreeMap<_, _> = labels.iter().cloned().zip(polys_a.iter()).collect();
        let map_b: BTreeMap<_, _> = labels.iter().cloned().zip(polys_b.iter()).collect();
        let map_sum: BTreeMap<_, _> = labels.iter().cloned().zip(polys_sum.iter()).collect();
        let com_a = FflonkScheme::<Bls12>::commit_many(&params, &map_a);
        let com_b = FflonkScheme::<Bls12>::commit_many(&params, &map_b);
        let com_sum = FflonkScheme::<Bls12>::commit_many(&params, &map_sum);

        match (com_a + com_b, com_sum) {
            (FflonkCommitment::Regular(added), FflonkCommitment::Regular(expected)) => {
                assert_eq!(added.len(), 1);
                assert_eq!(expected.len(), 1);
                assert_eq!(added[0].0, expected[0].0, "homomorphic point sum mismatch");
                assert_eq!(added[0].1, expected[0].1, "labels must be preserved");
            }
            _ => panic!("expected Regular commitments"),
        }
    }

    fn verify<E, T>(verifier_params: &ParamsVerifierKZG<E>, proof: &[u8], should_fail: bool)
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
        FflonkCommitment<E>: Hashable<T::Hash>,
    {
        let mut transcript = T::init_from_bytes(proof);

        let label = |name: &str| PolynomialLabel::Custom(name.into());
        let a = FflonkScheme::<E>::read_commitment(&mut transcript, &[label("a")]).unwrap();
        let b = FflonkScheme::<E>::read_commitment(&mut transcript, &[label("b")]).unwrap();
        let c = FflonkScheme::<E>::read_commitment(&mut transcript, &[label("c")]).unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y: E::Fr = transcript.squeeze_challenge();

        let avx: E::Fr = transcript.read().unwrap();
        let bvx: E::Fr = transcript.read().unwrap();
        let cvy: E::Fr = transcript.read().unwrap();

        // When tampering, `b`'s eval is swapped for `a`'s to force the pairing
        // check to fail.
        let queries = vec![
            VerifierQuery::new(x, &a, label("a"), avx),
            VerifierQuery::new(x, &b, label("b"), if should_fail { avx } else { bvx }),
            VerifierQuery::new(y, &c, label("c"), cvy),
        ];

        let guard = FflonkScheme::<E>::multi_prepare(&queries, &mut transcript).unwrap();
        let result = Guard::<E::Fr, FflonkScheme<E>>::verify(guard, verifier_params);

        if should_fail {
            assert!(result.is_err());
        } else {
            assert!(result.is_ok());
        }
    }

    fn create_proof<E, T>(params: &ParamsKZG<E>) -> Vec<u8>
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
    {
        let k = (params.g.len() - 1).ilog2() + 1;
        let domain = EvaluationDomain::new(1, k);

        let poly = |offset: u64| {
            let mut p = domain.empty_coeff();
            for (i, a) in p.iter_mut().enumerate() {
                *a = <E::Fr>::from(offset + i as u64);
            }
            p
        };
        let (ax, bx, cx) = (poly(10), poly(100), poly(100));

        let mut transcript = T::init();

        let label = |name: &str| PolynomialLabel::Custom(name.into());
        for (p, name) in [(&ax, "a"), (&bx, "b"), (&cx, "c")] {
            let com = FflonkScheme::<E>::commit(params, p, label(name));
            FflonkScheme::<E>::write_commitment(&mut transcript, &com).unwrap();
        }

        let x: E::Fr = transcript.squeeze_challenge();
        let y: E::Fr = transcript.squeeze_challenge();

        transcript.write(&eval_polynomial(&ax, x)).unwrap();
        transcript.write(&eval_polynomial(&bx, x)).unwrap();
        transcript.write(&eval_polynomial(&cx, y)).unwrap();

        let queries = [
            ProverQuery::new(x, &ax, label("a")),
            ProverQuery::new(x, &bx, label("b")),
            ProverQuery::new(y, &cx, label("c")),
        ];

        FflonkScheme::<E>::multi_open(params, &queries, &mut transcript).unwrap();

        transcript.finalize()
    }
}
