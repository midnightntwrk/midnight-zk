//! fflonk-style polynomial commitment scheme ([reference](https://eprint.iacr.org/2021/1167.pdf)).
//!
//! Packs groups of `t` polynomials of degree `< n` into a single polynomial
//! `g` of degree `< t·n` via `g(X) = Σ_i X^i · f_i(X^t)`, commits once to `g`,
//! and opens at the `t` t-th roots of each logical query point.
//!
//! TODO: for now, the computation of `g` is only possible if each `f_i` is in
//! coefficient form. The current commit function performs a conversion
//! otherwise. Native support will be implemented in the future.

// ## Layout
// - `utils`: grouping helpers and the curve-free math.
// - `partition`: the deterministic sub-bundling policy.
// - `commitment`: implementation of the `PolynomialCommitmentScheme` trait.
// - `params`: `ParamsFflonk` (alias for `ParamsKZG`).
//
// ## Implementation
// `commit_many` bundles via `partition::partition`. For each sub-bundle of size
// `t > 1`, it builds `g(X) = Σ_i X^i · f_i(X^t)` from the `f_i` converted to
// coefficient form. Singleton sub-bundles are kept in whichever base they were
// initially.
//
// `multi_open` / `multi_prepare` pre-expand bundled queries into synthetic
// queries on `g` at `t`-th roots of each distinct logical opening point. This
// corresponds to the characterisation of the [paper](https://eprint.iacr.org/2021/1167.pdf)
// Lemma 5.1 (see `eval_claims_as_poly`). The expansion is the only
// fflonk-specific phase; everything downstream is the standard Halo2 multi-open
// argument (shared with KZG).

use std::{fmt::Debug, hash::Hash, marker::PhantomData};

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use group::Group;
use midnight_curves::pairing::{Engine, MultiMillerLoop};
use rand_core::OsRng;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::poly::{
    pcs::utils::{combine, primitive_root_of_unity, roots as t_th_roots, t_th_root},
    EvaluationDomain, LagrangeCoeff, LagrangeDeltaCoeff, LagrangeDoubleDeltaCoeff, PolynomialBasis,
};

pub mod commitment;
/// Multi-scalar-multiplication accumulators shared by the scheme and its
/// verifier ([`MSMKZG`], [`DualMSM`]).
pub mod msm;
/// Public parameters / SRS for the scheme (`ParamsKZG`,
/// `ParamsVerifierKZG`).
pub mod params;

mod bundle_expansion;
mod partition;
pub(crate) mod utils;

pub use commitment::{FflonkBundle, FflonkCommitment};
pub use params::{ParamsFflonk, ParamsVerifierFflonk};
pub use utils::compute_dummy_queries;

#[cfg(feature = "truncated-challenges")]
use crate::utils::arithmetic::{truncate, truncated_powers};
use crate::{
    poly::{
        commitment::{Guard, Params, PolynomialCommitmentScheme},
        pcs::{
            msm::{msm_specific, DualMSM, MSMKZG},
            params::ParamsKZG,
            utils::construct_intermediate_sets,
        },
        query::{PolynomialLabel, VerifierQuery},
        Coeff, Error, Polynomial, PolynomialRepresentation, ProverQuery,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{
        arithmetic::{
            eval_polynomial, evals_inner_product, inner_product, kate_division,
            lagrange_interpolate, msm_inner_product, poly_inner_product, powers, CurveAffine,
            CurveExt, MSM,
        },
        helpers::ProcessedSerdeObject,
    },
};

/// The scheme-wide bundling exponent: fflonk packs up to `1 <<
/// FFLONK_T_MAX_LOG` polynomials into a single commitment. `0` means no
/// bundling (algebraically identical to classic KZG).
pub const FFLONK_T_MAX_LOG: u32 = 0;

/// # Bundling ceiling for fflonk
///
/// The maximal fflonk bundling size is `1 << t_max_log`, where `t_max_log` is
/// computed by this function. It is capped by three independent limits, for a
/// circuit over domain of size `n`.
///
///   * the max exponent `FFLONK_T_MAX_LOG` chosen in the library
///   * SRS room: t_max_log ≤ log2(g_monomial_size) − log2(n)
///   * Field 2-adicity: t_max_log ≤ F::S − log2(n) (so that roots of unity can
///     be a t-th power)
///
/// The verifier applies the same `F::S − k` cap when decoding the exponent
/// from the transcript, so both sides agree by construction.
fn effective_t_max_log<E: Engine>(params: &ParamsKZG<E>, t_max_log: u32, n: usize) -> u32
where
    E::G1Affine: CurveAffine,
    E::Fr: PrimeField,
{
    let log_n = n.ilog2();
    let srs_room = params.g_monomial_size().ilog2().saturating_sub(log_n);
    let field_room = <E::Fr as PrimeField>::S.saturating_sub(log_n);
    t_max_log.min(srs_room).min(field_room)
}

/// The fflonk polynomial-commitment scheme over a pairing-friendly curve `E`.
///
/// `FFLONK_T_MAX_LOG` is the log of the maximum bundle size the scheme will
/// produce: any `t > 1` sub-bundle packs up to `T_MAX = 1 << FFLONK_T_MAX_LOG`
/// polynomials into one G1 point.
#[derive(Clone, Debug)]
pub struct FflonkScheme<E: Engine> {
    _marker: PhantomData<E>,
}

/// Verification guard for `FflonkScheme`, wrapping `DualMSM<E>`
#[derive(Clone, Debug)]
pub struct FflonkVerificationGuard<E: MultiMillerLoop>(DualMSM<E>);

impl<E: MultiMillerLoop + Debug> FflonkVerificationGuard<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    /// Scale every scalar in the inner [`DualMSM`] by `e`. Used to batch
    /// guards from independent proofs before a joint pairing check.
    pub fn scale(&mut self, e: E::Fr) {
        self.0.scale(e);
    }

    /// Fold `other`'s inner [`DualMSM`] into `self` (component-wise MSM
    /// concatenation). Used together with [`scale`](Self::scale) for batch
    /// verification.
    pub fn add_msm(&mut self, other: Self) {
        self.0.add_msm(other.0);
    }

    /// Run the pairing check directly on the inner [`DualMSM`]. Same
    /// semantics as [`Guard::verify`] but returns `bool` instead of
    /// `Result`, matching `DualMSM::check`'s shape (`self` consumed).
    pub fn check(self, params: &crate::poly::pcs::params::ParamsVerifierKZG<E>) -> bool {
        self.0.check(params)
    }

    /// Extract the underlying [`DualMSM`]. fflonk's verification guard is a
    /// transparent newtype; callers that need the raw `DualMSM`
    /// (`Accumulator::from_dual_msm`, batch infrastructure) consume it
    /// through this accessor.
    pub fn into_dual_msm(self) -> DualMSM<E> {
        self.0
    }

    /// Borrow the underlying [`DualMSM`].
    pub fn dual_msm(&self) -> &DualMSM<E> {
        &self.0
    }
}

impl<E: MultiMillerLoop> PolynomialCommitmentScheme<E::Fr> for FflonkScheme<E>
where
    E::Fr: WithSmallOrderMulGroup<3>,
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    type Parameters = ParamsFflonk<E>;
    type VerifierParameters = ParamsVerifierFflonk<E>;
    type Commitment = FflonkCommitment<E>;
    type VerificationGuard = FflonkVerificationGuard<E>;

    fn gen_params(k: u32) -> Self::Parameters {
        ParamsKZG::unsafe_setup(k, OsRng)
    }

    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters {
        params.verifier_params()
    }

    /// fflonk's bundles need `params.g.len() ≥ T_MAX * n`, on top of any
    /// blow-up `single-h-commitment` would already require. The blow-up is
    /// the larger of the two.
    fn srs_monomial_blowup(cs_degree: usize) -> usize {
        let bundle = 1usize << FFLONK_T_MAX_LOG;
        if cfg!(feature = "single-h-commitment") {
            bundle.max((cs_degree - 1).next_power_of_two())
        } else {
            bundle
        }
    }

    /// fflonk requires the evaluation point to be a `T_MAX`-th power so the
    /// verifier can compute `t`-th roots for each sub-bundle (each `t`
    /// divides `T_MAX = 2^FFLONK_T_MAX_LOG`, so any `T_MAX`-th power is also a
    /// `t`-th power). We squeeze `s` and return `s^T_MAX`.
    ///
    /// Soundness / ZK: `x = s^T_MAX` is uniformly distributed in the
    /// `T_MAX`-th-power subgroup of `F*` (order `(p-1)/T_MAX`), which is
    /// essentially full-sized for BLS12 scalar (`p-1 ≈ 2^254`). Schwartz-
    /// Zippel arguments and protocol blinding are unaffected.
    fn squeeze_evaluation_point<T: Transcript>(transcript: &mut T) -> E::Fr
    where
        E::Fr: Sampleable<T::Hash>,
    {
        // `FFLONK_T_MAX_LOG` must not exceed the field's 2-adicity: otherwise
        // `s^(2^FFLONK_T_MAX_LOG)` collapses into the odd-order subgroup and
        // the shift below overflows. Both operands are compile-time constants,
        // so this is a static check evaluated once per curve.
        #[allow(clippy::absurd_extreme_comparisons)]
        const {
            assert!(FFLONK_T_MAX_LOG <= <E::Fr as PrimeField>::S)
        };
        let s: E::Fr = transcript.squeeze_challenge();
        let t_max = 1u64 << FFLONK_T_MAX_LOG;
        s.pow_vartime([t_max])
    }

    fn commitment_byte_length(n: usize) -> usize {
        // `commit_many` folds `n` polynomials into a single length-prefixed
        // commitment: one `u8` prefix (1 byte) followed by the group elements.
        // !! The computation below assuming no fflonk bundling, i.e., `FFLONK_T_MAX_LOG
        // = 0`, changing this value will not be reflected in the cost model !!
        let single = <Self::Commitment as crate::utils::helpers::ProcessedSerdeObject>::byte_length(
            &Self::Commitment::default(),
            crate::utils::helpers::SerdeFormat::Processed,
        );
        1 + n * (single - 1)
    }

    fn commit_many<B: PolynomialRepresentation>(
        params: &Self::Parameters,
        polynomials: &[&Polynomial<E::Fr, B>],
        labels: &[PolynomialLabel],
    ) -> Self::Commitment {
        assert_eq!(
            polynomials.len(),
            labels.len(),
            "polynomials and labels must have the same length"
        );
        assert!(
            !polynomials.is_empty(),
            "cannot commit to an empty slice of polynomials"
        );

        // All polys in one call must share length (so partition's `n` is
        // well-defined, and combine produces a length-`t·n` g).
        let n = polynomials[0].values.len();
        assert!(
            polynomials.iter().all(|p| p.values.len() == n),
            "fflonk commit: all polys in one call must have equal length"
        );

        // SRS-aware ceiling: shrink the bundling exponent to whatever the
        // loaded SRS can afford for this `n` (see `effective_t_max_log`). For
        // a tight/insufficient SRS this is `< FFLONK_T_MAX_LOG`; `multi_open` writes
        // it to the transcript so the verifier reconstructs the same partition.
        let t_max_log = effective_t_max_log(params, FFLONK_T_MAX_LOG, n);
        let t_max = 1usize << t_max_log;
        let sub_bundles = partition::partition(t_max, labels);

        let bases_b = params.bases::<B>();
        let mono_bases = &params.g;

        let bundles: Vec<FflonkBundle<E>> = sub_bundles
            .into_par_iter()
            .map(|indices| {
                // Effective size of the bundle, including padding.
                let t = partition::bundle_t(indices.len(), t_max);
                if t == 1 {
                    // Singleton: MSM over the appropriate basis, as in KZG.
                    let idx = indices[0];
                    let p = polynomials[idx];
                    let size = p.values.len();
                    assert!(bases_b.len() >= size);
                    let g1 = msm_specific::<E::G1Affine>(&p.values, &bases_b[..size]);
                    FflonkBundle::Bundle(g1, vec![labels[idx].clone()])
                } else {
                    // Multi-poly bundle: convert to Coeff form (if needed), combine into `g` over
                    // `t` slots (by padding with null polys), and MSM over monomial bases.

                    // Note: `log_n` assumes `n` is a power of two, which may only be violated for
                    // the h-poly. It should therefore never be fflonk-bundled (enforced in
                    // `partition::partition`).
                    let log_n = n.trailing_zeros();

                    // Conversion to coefficient form.
                    // TODO: multibase support to avoid having to do this.
                    let coeff_values_per_slot: Vec<Vec<E::Fr>> = match B::BASIS {
                        PolynomialBasis::Coeff => {
                            indices.iter().map(|&i| polynomials[i].values.clone()).collect()
                        }
                        PolynomialBasis::Lagrange => {
                            let domain = EvaluationDomain::<E::Fr>::new(1, log_n);
                            indices
                                .iter()
                                .map(|&i| {
                                    let lagrange_poly: Polynomial<E::Fr, LagrangeCoeff> =
                                        Polynomial {
                                            values: polynomials[i].values.clone(),
                                            _marker: PhantomData,
                                        };
                                    domain.lagrange_to_coeff(lagrange_poly).values
                                })
                                .collect()
                        }
                        PolynomialBasis::LagrangeDelta => {
                            let domain = EvaluationDomain::<E::Fr>::new(1, log_n);
                            indices
                                .iter()
                                .map(|&i| {
                                    let delta_poly: Polynomial<E::Fr, LagrangeDeltaCoeff> =
                                        Polynomial {
                                            values: polynomials[i].values.clone(),
                                            _marker: PhantomData,
                                        };
                                    let lagrange = delta_poly.into_lagrange();
                                    domain.lagrange_to_coeff(lagrange).values
                                })
                                .collect()
                        }
                        PolynomialBasis::LagrangeDoubleDelta => {
                            let domain = EvaluationDomain::<E::Fr>::new(1, log_n);
                            indices
                                .iter()
                                .map(|&i| {
                                    let dd_poly: Polynomial<E::Fr, LagrangeDoubleDeltaCoeff> =
                                        Polynomial {
                                            values: polynomials[i].values.clone(),
                                            _marker: PhantomData,
                                        };
                                    let lagrange = dd_poly.into_lagrange();
                                    domain.lagrange_to_coeff(lagrange).values
                                })
                                .collect()
                        }
                        other => panic!(
                            "fflonk t>1 bundling not supported for basis {other:?} \
                             (Coeff, Lagrange, LagrangeDelta, LagrangeDoubleDelta only)"
                        ),
                    };

                    // Interleave the (possibly padded) slots into `g` of length
                    // `t·n` and commit via MSM over the monomial bases.
                    let slot_refs: Vec<&[E::Fr]> =
                        coeff_values_per_slot.iter().map(Vec::as_slice).collect();
                    let g_values = combine(&slot_refs, t);
                    let g1 = msm_specific::<E::G1Affine>(&g_values, &mono_bases[..t * n]);
                    let bundle_labels: Vec<PolynomialLabel> =
                        indices.iter().map(|&i| labels[i].clone()).collect();
                    FflonkBundle::Bundle(g1, bundle_labels)
                }
            })
            .collect();

        FflonkCommitment(bundles)
    }

    // TODO: at FFLONK_T_MAX_LOG = 0 the transcript is kept byte-identical to
    // KZG (conditional t_max_log write, singletons routed through the plain
    // multi_open path). This can be simplified once T > 0 is the norm.
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
        // Replace queries that target a `t > 1` bundle with synthetic queries on
        // the bundle's combined polynomial `g` at the `t`-th roots of each
        // distinct logical opening point.

        // Label -> polynomial map.
        let poly_lookup: FxHashMap<PolynomialLabel, &Polynomial<E::Fr, Coeff>> =
            queries.iter().map(|q| (q.label.clone(), q.poly)).collect();
        let all_labels: Vec<PolynomialLabel> = poly_lookup.keys().cloned().collect();

        // SRS-aware bundling ceiling.
        let t_max_log = all_labels
            .iter()
            .find(|l| partition::bundle_family(l).is_some())
            .map(|l| poly_lookup[l].values.len())
            .map_or(0, |n| effective_t_max_log(params, FFLONK_T_MAX_LOG, n));
        // Writing the ceiling to the transcript in case we are not in the trivial case.
        // Note: The `FFLONK_T_MAX_LOG != 0` is necessary to keep byte equivalence with
        // KZG, but has minor impact and could be removed once fflonk is
        // implemented for the verifier gagdet.
        if FFLONK_T_MAX_LOG != 0 {
            transcript
                .write(&E::Fr::from(t_max_log as u64))
                .map_err(|_| Error::OpeningError)?;
        }
        let t_max = 1usize << t_max_log;

        // Early return in a theoretically unreachable case (currently), where the code
        // would panic later.
        if all_labels.is_empty() {
            return Ok(());
        }
        let sub_bundles = partition::partition(t_max, &all_labels);

        // Materialise `g` for each `t > 1` sub-bundle. Indexed by sub-bundle position.
        let g_polys: Vec<Option<Polynomial<E::Fr, Coeff>>> = sub_bundles
            .iter()
            .map(|indices| {
                let real_count = indices.len();
                let t = partition::bundle_t(real_count, t_max);
                if t <= 1 {
                    return None;
                }
                let n_bundle = poly_lookup[&all_labels[indices[0]]].values.len();
                assert!(
                    indices.iter().all(|&i| poly_lookup[&all_labels[i]].values.len() == n_bundle),
                    "fflonk multi_open: polys within a `t > 1` sub-bundle must have equal length"
                );
                let slot_refs: Vec<&[E::Fr]> = indices
                    .iter()
                    .map(|&lbl_idx| poly_lookup[&all_labels[lbl_idx]].values.as_slice())
                    .collect();
                Some(Polynomial {
                    values: combine(&slot_refs, t),
                    _marker: PhantomData,
                })
            })
            .collect();

        // Per-bundle prover-side preparation: union of logical points, the (slot,
        // point) pairs to over-open, and the synthetic label. Sorted by synth-label so
        // prover and verifier visit bundles identically.
        let multi_pre =
            bundle_expansion::build_prover_multi_pre(&sub_bundles, &all_labels, t_max, queries);

        // Over-opening writes, mandatory for `t > 1` bundles whenever any slot is
        // missing an eval at a point in the bundle's logical union.
        for pre in &multi_pre {
            for &(slot, logical) in &pre.missing {
                let poly_for_slot = poly_lookup[&all_labels[sub_bundles[pre.bundle_idx][slot]]];
                let eval = eval_polynomial(&poly_for_slot[..], logical);
                transcript.write(&eval).map_err(|_| Error::OpeningError)?;
            }
        }

        // Build the singleton slice and the bundle-synth slice separately
        let bundled_labels: FxHashSet<PolynomialLabel> = sub_bundles
            .iter()
            .filter(|indices| indices.len() > 1)
            .flat_map(|indices| indices.iter().map(|&i| all_labels[i].clone()))
            .collect();
        let mut singleton_queries: Vec<ProverQuery<E::Fr>> = Vec::new();
        for q in queries.iter() {
            if !bundled_labels.contains(&q.label) {
                singleton_queries.push(ProverQuery::new(q.point, q.poly, q.label.clone()));
            }
        }

        // `fewer-point-sets` writes on the singleton slice. The same primitive as
        // over-opening, called with commitment-label keys instead of slot-index keys,
        // on the post-classification list.
        #[cfg(feature = "fewer-point-sets")]
        {
            let pairs: Vec<(PolynomialLabel, E::Fr)> =
                singleton_queries.iter().map(|q| (q.label.clone(), q.point)).collect();
            let dummies = compute_dummy_queries(&pairs);
            for (idx, point) in dummies {
                let poly = singleton_queries[idx].poly;
                let label = singleton_queries[idx].label.clone();
                transcript
                    .write(&eval_polynomial(poly, point))
                    .map_err(|_| Error::OpeningError)?;
                singleton_queries.push(ProverQuery::new(point, poly, label));
            }
        }

        // Bundle-synth slice: `t` queries on `g` at the t-th roots of each
        // logical in the union (uniform across slots after over-opening).
        // Share a `t_th_root(logical, t)` cache across bundles — bundles
        // typically open at the same logical points (ζ, ζ·ω, …); the sqrt
        // chain is identical per (logical, t) and should not be recomputed.
        let mut t_th_root_cache: FxHashMap<(E::Fr, usize), E::Fr> = FxHashMap::default();
        let mut bundle_synth_queries: Vec<ProverQuery<E::Fr>> = Vec::new();
        for pre in &multi_pre {
            let g_poly =
                g_polys[pre.bundle_idx].as_ref().expect("g_poly must be Some for t>1 bundle");
            let omega_t = primitive_root_of_unity::<E::Fr>(pre.t);
            for &logical in &pre.union_logicals {
                let z = *t_th_root_cache
                    .entry((logical, pre.t))
                    .or_insert_with(|| t_th_root(logical, pre.t));
                for r in t_th_roots(z, omega_t, pre.t) {
                    bundle_synth_queries.push(ProverQuery::new(r, g_poly, pre.synth_label.clone()));
                }
            }
        }

        let expanded_queries: Vec<ProverQuery<E::Fr>> =
            singleton_queries.into_iter().chain(bundle_synth_queries).collect();
        let queries = &expanded_queries[..];

        // Halo2 multi-opening argument (the standard batch-opening flow).
        let x1: E::Fr = transcript.squeeze_challenge();
        let x2: E::Fr = transcript.squeeze_challenge();

        let mut poly_lookup: FxHashMap<PolynomialLabel, &Polynomial<E::Fr, Coeff>> =
            FxHashMap::default();
        let triples: Vec<(PolynomialLabel, E::Fr, E::Fr)> = queries
            .iter()
            .map(|q| {
                let eval = eval_polynomial(&q.poly[..], q.point);
                poly_lookup.entry(q.label.clone()).or_insert(q.poly);
                (q.label.clone(), q.point, eval)
            })
            .collect();

        let (poly_map, point_sets) = construct_intermediate_sets(&triples)?;

        let mut q_polys = vec![vec![]; point_sets.len()];
        for com_data in poly_map.iter() {
            q_polys[com_data.set_index].push((*poly_lookup[&com_data.label]).clone());
        }

        let q_polys: Vec<_> = q_polys
            .par_iter()
            .map(|polys| {
                #[cfg(feature = "truncated-challenges")]
                let x1 = truncated_powers(x1);

                #[cfg(not(feature = "truncated-challenges"))]
                let x1 = powers(x1);

                poly_inner_product(polys, x1)
            })
            .collect();

        // Sort point sets by ascending cardinality so the in-circuit verifier
        // sees the single-point set first (enabling a collapse).
        let (q_polys, point_sets) = {
            let mut order: Vec<usize> = (0..point_sets.len()).collect();
            order.sort_by_key(|&i| (point_sets[i].len(), i));
            let q_polys: Vec<_> = order.iter().map(|&i| q_polys[i].clone()).collect();
            let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
            (q_polys, point_sets)
        };

        let f_poly = {
            let f_polys: Vec<_> = point_sets
                .into_par_iter()
                .zip(q_polys.clone().into_par_iter())
                .map(|(points, q_poly)| {
                    let poly = points
                        .iter()
                        .fold(q_poly.values, |poly, point| kate_division(&poly, *point));
                    Polynomial {
                        values: poly,
                        _marker: PhantomData,
                    }
                })
                .collect();
            poly_inner_product(&f_polys, powers(x2))
        };

        let f_com = Self::commit_many(
            params,
            &[&f_poly],
            &[PolynomialLabel::Custom("fflonk_batch".into())],
        );
        transcript.write(&f_com).map_err(|_| Error::OpeningError)?;

        let x3: E::Fr = transcript.squeeze_challenge();
        #[cfg(feature = "truncated-challenges")]
        let x3 = truncate(x3);

        let q_evals: Vec<E::Fr> =
            q_polys.par_iter().map(|q_poly| eval_polynomial(&q_poly.values, x3)).collect();
        for eval in &q_evals {
            transcript.write(eval).map_err(|_| Error::OpeningError)?;
        }

        let x4: E::Fr = transcript.squeeze_challenge();

        let final_poly = {
            let mut polys = q_polys;
            polys.push(f_poly);
            #[cfg(feature = "truncated-challenges")]
            let powers = truncated_powers(x4);

            #[cfg(not(feature = "truncated-challenges"))]
            let powers = powers(x4);

            poly_inner_product(&polys, powers)
        };
        let v = eval_polynomial(&final_poly, x3);

        let pi = {
            let pi_poly = Polynomial::<_, Coeff> {
                values: kate_division(&(&final_poly - v).values, x3),
                _marker: PhantomData,
            };
            Self::commit_many(
                params,
                &[&pi_poly],
                &[PolynomialLabel::Custom("fflonk_proof".into())],
            )
        };

        transcript.write(&pi).map_err(|_| Error::OpeningError)
    }

