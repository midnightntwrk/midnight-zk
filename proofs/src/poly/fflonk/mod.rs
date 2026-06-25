//! fflonk-style polynomial commitment scheme (Gabizon–Williamson 2021,
//! `resources/fflonk.pdf`).
//!
//! Packs groups of `t` polynomials of degree `< n` into a single polynomial
//! `g` of degree `< t·n` via `g(X) = Σ_i X^i · f_i(X^t)` (the paper's
//! `combine_t`), commits once to `g`, and opens at the `t` t-th roots of
//! each logical query point.
//!
//! ## Layout
//! - [`primitives`]: curve-free math (`combine`, `primitive_root_of_unity`,
//!   `roots`, `eval_claims_as_poly`, `t_th_root`, …).
//! - [`partition`]: the deterministic sub-bundling policy. Variant-aware:
//!   `Advice(_)` labels share a bundle group; everything else is a singleton.
//! - [`commitment`]: [`FflonkCommitment`] and [`FflonkBundle`].
//! - [`params`]: [`ParamsFflonk`] (alias for `ParamsKZG`).
//!
//! ## Real-bundling scope (v1)
//! `commit` bundles via [`partition::partition`]. For each `t > 1`
//! sub-bundle it builds `g(X) = Σ_i X^i · f_i(X^t)` (Coeff-only — panics
//! on other reps for `t > 1`) and commits via MSM over `params.g[..t·n]`
//! (monomial bases). Singleton sub-bundles take the same MSM-over-bases
//! path as the trait's default (no `g`).
//!
//! `multi_open` / `multi_prepare` pre-expand bundled queries into synthetic
//! queries on `g` at `t`-th roots of each distinct logical opening point,
//! using [`primitives::t_th_root`] (one canonical `t`-th root via repeated
//! `sqrt`) and Lemma 5.1 (`eval_claims_as_poly`). The expansion is the
//! ONLY fflonk-specific phase; everything downstream is the standard
//! Halo2 GWC multi-open argument (shared with KZG).
//!
//! ## Caller obligation
//! **All query points on a `t > 1` bundle must be `t`-th powers in the
//! field.** Tests achieve this by squeezing `s` and using `s^t · ω_n^r` as
//! query points; the real protocol must arrange the same when fflonk is
//! the active PCS. `t_th_root` panics otherwise (intermediate `sqrt` fails).
//!
//! [`PolynomialCommitmentScheme`]: crate::poly::commitment::PolynomialCommitmentScheme

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
};

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use group::Group;
use midnight_curves::pairing::{Engine, MultiMillerLoop};
use rand_core::OsRng;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::poly::{
    fflonk::primitives::{primitive_root_of_unity, roots as t_th_roots, t_th_root},
    EvaluationDomain, LagrangeCoeff, LagrangeDeltaCoeff, LagrangeDoubleDeltaCoeff, PolynomialBasis,
};

pub mod commitment;
pub mod params;

mod bundle_expansion;
mod partition;
mod primitives;


pub use commitment::{FflonkBundle, FflonkCommitment};
pub use params::{ParamsFflonk, ParamsVerifierFflonk};

#[cfg(feature = "truncated-challenges")]
use crate::utils::arithmetic::{truncate, truncated_powers};
use crate::{
    poly::{
        commitment::{Guard, Params, PolynomialCommitmentScheme},
        kzg::{
            compute_dummy_queries,
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

/// SRS-aware bundling ceiling.
///
/// fflonk packs up to `2^T_MAX_LOG` polynomials of length `n` into a single
/// polynomial of degree `< t·n`, so committing to it needs a monomial SRS of
/// at least `t·n` bases. The largest bundling exponent the *loaded* SRS can
/// afford for this `n` is `log2(g_monomial_size) - log2(n)`, so we cap the
/// configured `T_MAX_LOG` by it.
///
/// This lets a circuit whose domain leaves less than `T_MAX_LOG` of headroom
/// under the SRS still prove (with smaller bundles) instead of panicking. The
/// returned exponent is what the prover writes to the transcript so the
/// verifier reconstructs the identical partition; see [`FflonkScheme::commit`],
/// [`FflonkScheme::multi_open`] and [`FflonkScheme::multi_prepare`].
///
/// We derive the domain exponent from the polynomial length `n` rather than
/// `params.max_k()`: the latter reports the SRS's *Lagrange* size, which is
/// only the circuit domain when the SRS was built tight to it (it isn't, e.g.,
/// for an extended SRS or the unit tests). `log2(n)` is always the bundle's
/// true domain and matches the verifier's `vk.domain.k()`.
fn effective_t_max_log<E: Engine>(params: &ParamsKZG<E>, t_max_log: u32, n: usize) -> u32
where
    E::G1Affine: CurveAffine,
{
    let room = params.g_monomial_size().ilog2().saturating_sub(n.ilog2());
    t_max_log.min(room)
}

/// The fflonk polynomial-commitment scheme over a pairing-friendly curve `E`.
///
/// `T_MAX_LOG` is the log₂ of the maximum bundle size the scheme will produce:
/// any `t > 1` sub-bundle packs up to `T_MAX = 2^T_MAX_LOG` polynomials into
/// one G1 point. `T_MAX_LOG = 0` (the default) degenerates to KZG-equivalent
/// behavior (`t = 1` everywhere). Benchmarks can sweep `T_MAX_LOG` to find
/// the verifier sweet spot.
///
/// # Deployment constraint (SRS sizing)
///
/// fflonk does **not** extend the SRS — the library only ever uses what was
/// already downloaded. Picking `T_MAX_LOG = p` consumes a larger portion of
/// the fixed SRS per circuit row. Concretely, if the loaded SRS exposes
/// `G = params.g.len()` monomial bases (this is what `Params::g_monomial_size`
/// returns), then circuits of domain size `n = 2^k` are supported iff
/// ```text
///     T_MAX · n  ≤  G        ⇔        p + k  ≤  log2(G)
/// ```
/// In other words, adopting `T_MAX_LOG = p` shrinks the maximum supportable
/// `k` from `log2(G)` to `log2(G) − p`. This is the well-known fflonk
/// trade-off (paper Table 1: SRS size `t · n · G₁`). `commit` enforces it
/// as a runtime assert (`mono_bases.len() ≥ t · n`); pick `T_MAX_LOG` with
/// the largest expected circuit `k` in mind.
///
/// A second, field-level constraint must also hold for every commit with
/// `t > 1`:
/// ```text
///     T_MAX_LOG + log_n  ≤  F::S
/// ```
/// where `F::S` is the 2-adicity of `F` (32 for BLS12-381 scalar). This is
/// needed so that `ω_n` is a `T_MAX`-th power — i.e., so that rotated
/// logical points `x · ω_n^r` remain `T_MAX`-th powers and `t_th_root` can
/// terminate at open time. Also asserted in `commit`.
///
/// # Single-h-commitment interaction
///
/// The existing `single-h-commitment` Cargo feature already provisions a
/// monomial basis larger than the circuit Lagrange domain (so the quotient
/// `h(X)` can be committed in one G1). It is the natural switch to enable
/// for fflonk: with it on, the ratio `g.len() / g_lagrange.len()` is what
/// budgets `T_MAX_LOG` on top of the circuit's `k`.
#[derive(Clone, Debug)]
pub struct FflonkScheme<E: Engine, const T_MAX_LOG: u32 = 0> {
    _marker: PhantomData<E>,
}

/// Verification guard for [`FflonkScheme`]. A newtype around [`DualMSM`] so
/// the `Guard<_, FflonkScheme<_, _>>` impl doesn't conflict with KZG's
/// `Guard<_, KZGCommitmentScheme<E>>` on the same `DualMSM` type (which
/// would cause method-resolution ambiguity at generic call sites since
/// [`ParamsVerifierFflonk`] aliases `ParamsVerifierKZG`).
#[derive(Clone, Debug)]
pub struct FflonkVerificationGuard<E: MultiMillerLoop, const T_MAX_LOG: u32 = 0>(DualMSM<E>);

impl<E: MultiMillerLoop + Debug, const T_MAX_LOG: u32> FflonkVerificationGuard<E, T_MAX_LOG>
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
    /// `Result`, matching `DualMSM::check`'s shape (`self` consumed) so
    /// callers that used to hold a raw `DualMSM` need no plumbing change
    /// beyond the type swap.
    pub fn check(self, params: &crate::poly::kzg::params::ParamsVerifierKZG<E>) -> bool {
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

impl<E: MultiMillerLoop, const T_MAX_LOG: u32> PolynomialCommitmentScheme<E::Fr>
    for FflonkScheme<E, T_MAX_LOG>
where
    E::Fr: WithSmallOrderMulGroup<3>,
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    type Parameters = ParamsFflonk<E>;
    type VerifierParameters = ParamsVerifierFflonk<E>;
    type Commitment = FflonkCommitment<E, T_MAX_LOG>;
    type VerificationGuard = FflonkVerificationGuard<E, T_MAX_LOG>;

    fn gen_params(k: u32) -> Self::Parameters {
        ParamsKZG::unsafe_setup(k, OsRng)
    }

    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters {
        params.verifier_params()
    }

    /// fflonk requires the evaluation point to be a `T_MAX`-th power so the
    /// verifier can compute `t`-th roots for each sub-bundle (each `t`
    /// divides `T_MAX = 2^T_MAX_LOG`, so any `T_MAX`-th power is also a
    /// `t`-th power). We squeeze `s` and return `s^T_MAX`.
    ///
    /// Soundness / ZK: `x = s^T_MAX` is uniformly distributed in the
    /// `T_MAX`-th-power subgroup of `F*` (order `(p-1)/T_MAX`), which is
    /// essentially full-sized for BLS12 scalar (`p-1 ≈ 2^254`). Schwartz-
    /// Zippel arguments and protocol blinding are unaffected.
    ///
    /// # Panics
    /// If `T_MAX_LOG > F::S`. The full domain-fit check
    /// `T_MAX_LOG + log_n ≤ F::S` is enforced at `commit` time (where `log_n`
    /// is known); this assert is just the cheap upper bound that doesn't
    /// require a domain size.
    /// fflonk additionally requires `k + T_MAX_LOG ≤ F::S` so that `ω_n`
    /// (a primitive `2^k`-th root of unity) is itself a `T_MAX`-th power
    /// — equivalently, so that every rotated query point `ω_n^r · x`
    /// remains a `T_MAX`-th power and the verifier's `t_th_root` chain
    /// succeeds. Surface this at SRS-load time rather than at proof time.
    fn max_supported_k() -> u32 {
        let field_s = <E::Fr as PrimeField>::S;
        field_s.saturating_sub(T_MAX_LOG)
    }

    /// fflonk's bundles need `params.g.len() ≥ T_MAX * n`, on top of any
    /// blow-up `single-h-commitment` would already require. The blow-up is
    /// the larger of the two.
    fn srs_monomial_blowup(cs_degree: usize) -> usize {
        let bundle = 1usize << T_MAX_LOG;
        #[cfg(feature = "single-h-commitment")]
        {
            bundle.max((cs_degree - 1).next_power_of_two())
        }
        #[cfg(not(feature = "single-h-commitment"))]
        {
            let _ = cs_degree;
            bundle
        }
    }

    fn squeeze_evaluation_point<T: Transcript>(transcript: &mut T) -> E::Fr
    where
        E::Fr: Sampleable<T::Hash>,
    {
        // u64 cast avoids any theoretical u32 overflow; both quantities are
        // tiny in practice (`T_MAX_LOG ≤ 6` or so, `F::S = 32` for BLS12).
        assert!(
            (T_MAX_LOG as u64) <= (<E::Fr as PrimeField>::S as u64),
            "fflonk: T_MAX_LOG ({}) exceeds field 2-adicity F::S ({})",
            T_MAX_LOG,
            <E::Fr as PrimeField>::S,
        );
        let s: E::Fr = transcript.squeeze_challenge();
        let t_max = 1u64 << T_MAX_LOG;
        s.pow_vartime([t_max])
    }

    fn commit<B: PolynomialRepresentation>(
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
        // a tight/insufficient SRS this is `< T_MAX_LOG`; `multi_open` writes
        // it to the transcript so the verifier reconstructs the same partition.
        let t_max_log = effective_t_max_log(params, T_MAX_LOG, n);
        let t_max = 1usize << t_max_log;
        let sub_bundles = partition::partition(t_max, labels);

        let bases_b = params.bases::<B>();
        let mono_bases = &params.g;

        let bundles: Vec<FflonkBundle<E>> = sub_bundles
            .into_par_iter()
            .map(|indices| {
                // `indices` carries the REAL polynomial indices for this
                // sub-bundle (`real_count = indices.len()`). The bundle's
                // logical size `t` is the next power of two ≥ real_count,
                // capped at `t_max`. Slots `[real_count, t)` are padded
                // zeros.
                let real_count = indices.len();
                let t = partition::bundle_t(real_count, t_max);
                if t == 1 {
                    // Singleton: MSM over the `B`-appropriate basis.
                    let idx = indices[0];
                    let p = polynomials[idx];
                    let size = p.values.len();
                    assert!(bases_b.len() >= size);
                    let g1 = msm_specific::<E::G1Affine>(&p.values, &bases_b[..size]);
                    FflonkBundle::Bundle(g1, vec![labels[idx].clone()])
                } else {
                    // Multi-poly bundle: convert to Coeff form (if needed),
                    // combine into `g` over `t` slots (with `t - real_count`
                    // pad slots left at zero), and MSM over monomial bases.
                    // `msm_specific` filters zero coefficients, so the
                    // pad slots cost only the `O(t·n)` allocation here,
                    // not extra group ops at MSM time.
                    let tn = t * n;
                    assert!(
                        mono_bases.len() >= tn,
                        "fflonk commit: SRS too small for t={t}, n={n} (need {tn} monomial bases)"
                    );
                    // Field-2-adicity check: for rotated logical points
                    // `x · ω_n^r` to be `t`-th powers (so `t_th_root`
                    // succeeds at open time), `ω_n` must itself be a `t`-th
                    // power. Since `ω_n` has order `n = 2^log_n` and the
                    // subgroup of `t`-th powers in `F*` has order
                    // `(p-1)/t = 2^{S-t_max_log} · m` (m odd), this needs
                    // `log_n + t_max_log ≤ F::S`. We use the *effective*
                    // `t_max_log` (not `T_MAX_LOG`): with SRS-aware capping
                    // `log_n + t_max_log ≤ log2(g_monomial_size) ≤ F::S`, so
                    // this never fires for a validly-loaded SRS. u64 cast for
                    // overflow safety (all values tiny in practice).
                    assert!(
                        n.is_power_of_two(),
                        "fflonk commit: t>1 bundle requires n={n} to be a power of two"
                    );
                    let log_n = n.trailing_zeros();
                    assert!(
                        (log_n as u64) + (t_max_log as u64) <= (<E::Fr as PrimeField>::S as u64),
                        "fflonk commit: log_n ({}) + t_max_log ({}) > F::S ({}); \
                         field lacks 2-adicity for this (t_max, n)",
                        log_n,
                        t_max_log,
                        <E::Fr as PrimeField>::S,
                    );

                    // Per-slot coefficient-form values. For `B = Coeff`, pass
                    // through. For the Lagrange family (`Lagrange`,
                    // `LagrangeDelta`, `LagrangeDoubleDelta`), reduce to
                    // `LagrangeCoeff` (O(n) prefix-sum for the delta variants)
                    // and then IFFT to `Coeff`.
                    //
                    // TODO(multibase): once the basis-aware fflonk SRS lands
                    // (see resources/fflonk-multibase paper §2.1 / §2.3),
                    // the iFFT and the delta-undoing become unnecessary —
                    // each bundle commits against a basis-adapted extended
                    // SRS that preserves the input basis's sparsity. The
                    // expected wall-clock win per bundle is documented in
                    // memory/fflonk-bench-findings (~30 ms recovered at
                    // T=2, K=13 on the Advice bundle's MSM slot alone, plus
                    // the David-#379 LagrangeDelta sparsity that would
                    // otherwise be destroyed here for permutation and
                    // logup phases).
                    let coeff_values_per_slot: Vec<Vec<E::Fr>> = match B::BASIS {
                        PolynomialBasis::Coeff => {
                            indices.iter().map(|&i| polynomials[i].values.clone()).collect()
                        }
                        PolynomialBasis::Lagrange => {
                            assert!(
                                n.is_power_of_two(),
                                "fflonk commit (Lagrange): n={n} must be a power of two"
                            );
                            let log_n = n.trailing_zeros();
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
                            assert!(
                                n.is_power_of_two(),
                                "fflonk commit (LagrangeDelta): n={n} must be a power of two"
                            );
                            let log_n = n.trailing_zeros();
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
                            assert!(
                                n.is_power_of_two(),
                                "fflonk commit (LagrangeDoubleDelta): n={n} must be a power of two"
                            );
                            let log_n = n.trailing_zeros();
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

                    // out[j*t + i] = coeff_values_per_slot[i][j] — paper's combine_t.
                    let mut g_values = vec![E::Fr::ZERO; tn];
                    for (i, coeffs) in coeff_values_per_slot.iter().enumerate() {
                        for (j, &c) in coeffs.iter().enumerate() {
                            g_values[j * t + i] = c;
                        }
                    }
                    let g1 = msm_specific::<E::G1Affine>(&g_values, &mono_bases[..tn]);
                    let bundle_labels: Vec<PolynomialLabel> =
                        indices.iter().map(|&i| labels[i].clone()).collect();
                    FflonkBundle::Bundle(g1, bundle_labels)
                }
            })
            .collect();

        FflonkCommitment(bundles)
    }

    fn multi_open<T: Transcript>(
        params: &Self::Parameters,
        queries: &[ProverQuery<E::Fr>],
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        E::Fr: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        FflonkCommitment<E, T_MAX_LOG>: Hashable<T::Hash>,
    {
        // === Bundle pre-expansion (fflonk-specific) ===
        //
        // Replace queries that target a `t > 1` bundle with synthetic queries on
        // the bundle's combined polynomial `g` at the `t`-th roots of each
        // distinct logical opening point. Singleton (`t = 1`) queries pass
        // through unchanged. Downstream GWC machinery is unchanged and operates
        // on the expanded query list.

        // Build label → poly map plus an *insertion-order* `all_labels` vec
        // (HashMap iteration order is non-deterministic and would make the
        // sub-bundle order, and downstream GWC commitment_map order, differ
        // from what the verifier sees).
        let mut poly_lookup: HashMap<PolynomialLabel, &Polynomial<E::Fr, Coeff>> = HashMap::new();
        let mut all_labels: Vec<PolynomialLabel> = Vec::new();
        for q in queries {
            if !poly_lookup.contains_key(&q.label) {
                all_labels.push(q.label.clone());
                poly_lookup.insert(q.label.clone(), q.poly);
            }
        }
        // SRS-aware bundling ceiling, keyed on the bundlable polynomial
        // domain. Written to the transcript as a field element (our
        // `Hashable` bound is on `E::Fr`) so the verifier reconstructs the
        // same partition; at `T_MAX_LOG == 0` (no bundling, KZG-equivalent)
        // nothing is written, preserving byte-for-byte KZG transcripts.
        // Written before the empty-query early-return so it always pairs
        // with the read at the top of `multi_prepare`.
        //
        // We need the polynomial length for *some* bundlable label to size
        // the bundle. All bundlable families share the constraint system's
        // Lagrange domain `n`, so any one of them works. Picking the first
        // bundlable label in encounter order gives a result invariant to
        // family — matches the verifier's expectation regardless of which
        // family (Advice, PermutationAccumulator, …) drives the bundle.
        let bundle_n = all_labels
            .iter()
            .find(|l| partition::bundle_family(l).is_some())
            .map(|l| poly_lookup[l].values.len());
        let t_max_log = bundle_n.map_or(0, |n| effective_t_max_log(params, T_MAX_LOG, n));
        if T_MAX_LOG > 0 {
            transcript
                .write(&E::Fr::from(t_max_log as u64))
                .map_err(|_| Error::OpeningError)?;
        }
        let t_max = 1usize << t_max_log;

        if all_labels.is_empty() {
            return Ok(());
        }
        let sub_bundles = partition::partition(t_max, &all_labels);

        // Materialise `g` for each `t > 1` sub-bundle. Indexed by sub-bundle
        // position; `None` for singletons. The bundle's logical size `t` is
        // `bundle_t(real_count, t_max)`, with pad slots [real_count, t)
        // left at zero in `g_values`.
        //
        // Length-uniformity is required PER BUNDLE (so the interleave produces
        // a coherent length-`t·n_bundle` g), not globally — singletons can be
        // of any length. This matters under `single-h-commitment`, where `h`
        // is a singleton polynomial whose length differs from the other polys'.
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
                    indices
                        .iter()
                        .all(|&i| poly_lookup[&all_labels[i]].values.len() == n_bundle),
                    "fflonk multi_open: polys within a `t > 1` sub-bundle must have equal length"
                );
                let mut g_values = vec![E::Fr::ZERO; t * n_bundle];
                for (i, &lbl_idx) in indices.iter().enumerate() {
                    let p = poly_lookup[&all_labels[lbl_idx]];
                    for (j, &c) in p.values.iter().enumerate() {
                        g_values[j * t + i] = c;
                    }
                }
                Some(Polynomial {
                    values: g_values,
                    _marker: PhantomData,
                })
            })
            .collect();

        // Per-bundle prover-side preparation: union of logical points, the
        // (slot, point) pairs to over-open, and the synthetic label. Sorted
        // by synth-label so prover and verifier visit bundles identically.
        let multi_pre =
            bundle_expansion::build_prover_multi_pre(&sub_bundles, &all_labels, t_max, queries);

        // Coset metadata for the GWC kate_division fold. Each bundle's
        // synthetic queries land at the t-th roots of the bundle's logical
        // points — a union of cosets in the same point set. Recording the
        // `(anchor, t)` list per bundle's synth_label lets us, after
        // `construct_intermediate_sets`, recover per-set coset structure and
        // feed it to `kate_division`'s `t > 1` branch instead of doing `|set|`
        // sequential single-point divisions. The win on this slot is small
        // in absolute terms at our T values (~ms), but the change is local
        // and correctness-preserving so we keep it.
        let bundle_coset_metadata: HashMap<PolynomialLabel, Vec<(E::Fr, usize)>> = multi_pre
            .iter()
            .map(|pre| {
                let cosets: Vec<(E::Fr, usize)> = pre
                    .union_logicals
                    .iter()
                    .map(|&l| (l, pre.t))
                    .collect();
                (pre.synth_label.clone(), cosets)
            })
            .collect();

        // Over-opening writes — mandatory for `t > 1` bundles whenever any
        // slot is missing an eval at a point in the bundle's logical union.
        for pre in &multi_pre {
            for &(slot, logical) in &pre.missing {
                let poly_for_slot = poly_lookup[&all_labels[sub_bundles[pre.bundle_idx][slot]]];
                let eval = eval_polynomial(&poly_for_slot[..], logical);
                transcript.write(&eval).map_err(|_| Error::OpeningError)?;
            }
        }

        // Build the singleton slice and the bundle-synth slice separately —
        // `fewer-point-sets` operates only on the singleton slice (bundles
        // already share a canonical t-th-root point set per logical-union
        // member; padding them up to a wider union would *increase* the set
        // count, the opposite of what the heuristic wants).
        //
        // **Iteration-order invariant**: we walk `queries` in their natural
        // emission order (the chain order from `compute_queries`), filtering
        // out labels that live in a `t > 1` bundle (those flow through the
        // bundle-synth slice below). This mirrors the verifier-side
        // [`bundle_expansion::classify_verifier_queries`], which also walks
        // queries in their natural order. Both sides hand the same triples,
        // in the same order, to [`construct_intermediate_sets`], so the
        // resulting `commitment_map` and `point_index_map` agree at every
        // `set_index`. The previous implementation iterated `sub_bundles` to
        // build this slice, which made the prover's order depend on
        // `partition`'s family-emission order — sound for the Advice-only
        // case but breaks the prover/verifier `set_index` agreement the
        // moment `partition` introduces a second bundle family. Walking
        // queries directly here decouples the singleton order from
        // `partition`'s family layout (`partition` only needs to identify
        // *which* labels belong to t>1 bundles, not order them).
        let bundled_labels: HashSet<PolynomialLabel> = sub_bundles
            .iter()
            .filter(|indices| indices.len() > 1)
            .flat_map(|indices| indices.iter().map(|&i| all_labels[i].clone()))
            .collect();
        let mut singleton_queries: Vec<ProverQuery<E::Fr>> = Vec::new();
        for q in queries.iter() {
            if bundled_labels.contains(&q.label) {
                continue;
            }
            singleton_queries.push(ProverQuery::new(q.point, q.poly, q.label.clone()));
        }

        // `fewer-point-sets` writes on the singleton slice. The same primitive
        // as over-opening, called with commitment-label keys instead of
        // slot-index keys, on the post-classification list.
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
        let mut t_th_root_cache: HashMap<(E::Fr, usize), E::Fr> = HashMap::new();
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

        // Halo2 multi-opening argument (see KZG mod.rs for the same flow).
        let x1: E::Fr = transcript.squeeze_challenge();
        let x2: E::Fr = transcript.squeeze_challenge();

        let mut poly_lookup: HashMap<PolynomialLabel, &Polynomial<E::Fr, Coeff>> = HashMap::new();
        let triples: Vec<(PolynomialLabel, E::Fr, E::Fr)> = queries
            .iter()
            .map(|q| {
                let eval = eval_polynomial(&q.poly[..], q.point);
                poly_lookup.entry(q.label.clone()).or_insert(q.poly);
                (q.label.clone(), q.point, eval)
            })
            .collect();

        let (poly_map, point_sets) = construct_intermediate_sets(&triples)?;

        // Per-set coset structure: `None` for non-bundle sets (singleton fold),
        // `Some(cosets)` for bundle-derived sets (use `kate_division`'s
        // `t > 1` branch per coset).
        let mut set_cosets: Vec<Option<Vec<(E::Fr, usize)>>> = vec![None; point_sets.len()];
        for com_data in poly_map.iter() {
            if let Some(cosets) = bundle_coset_metadata.get(&com_data.label) {
                // Multiple bundle labels could land in the same set_index;
                // the cosets are identical by construction, just take the first.
                if set_cosets[com_data.set_index].is_none() {
                    set_cosets[com_data.set_index] = Some(cosets.clone());
                }
            }
        }

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

        // Sort point sets by ascending cardinality (see KZG: in-circuit
        // verifier wants the single-x set first to enable a collapse).
        let (q_polys, point_sets, set_cosets) = {
            let mut order: Vec<usize> = (0..point_sets.len()).collect();
            order.sort_by_key(|&i| (point_sets[i].len(), i));
            let q_polys: Vec<_> = order.iter().map(|&i| q_polys[i].clone()).collect();
            let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
            let set_cosets: Vec<_> = order.iter().map(|&i| set_cosets[i].clone()).collect();
            (q_polys, point_sets, set_cosets)
        };

        let f_poly = {
            let f_polys: Vec<_> = point_sets
                .into_par_iter()
                .zip(q_polys.clone().into_par_iter())
                .zip(set_cosets.into_par_iter())
                .map(|((points, q_poly), cosets)| {
                    let poly = match cosets {
                        // Coset path: one `kate_division(_, anchor, t)` per
                        // coset in the union — `K` calls vs `K·t` singleton
                        // calls on the same point set.
                        Some(cosets) => cosets
                            .iter()
                            .fold(q_poly.values, |poly, &(anchor, t)| {
                                kate_division(&poly, anchor, t)
                            }),
                        // Singleton / generic path: one `kate_division` per
                        // point with `t = 1`, matching the pre-coset behavior.
                        None => points.iter().fold(q_poly.values, |poly, point| {
                            kate_division(&poly, *point, 1)
                        }),
                    };
                    Polynomial {
                        values: poly,
                        _marker: PhantomData,
                    }
                })
                .collect();
            poly_inner_product(&f_polys, powers(x2))
        };

        let f_com = Self::commit(
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
                values: kate_division(&(&final_poly - v).values, x3, 1),
                _marker: PhantomData,
            };
            let pi_com = Self::commit(
                params,
                &[&pi_poly],
                &[PolynomialLabel::Custom("fflonk_proof".into())],
            );
            pi_com
        };

        transcript.write(&pi).map_err(|_| Error::OpeningError)
    }

    fn multi_prepare<'com, T: Transcript>(
        queries: &[VerifierQuery<'com, E::Fr, FflonkScheme<E, T_MAX_LOG>>],
        k: u32,
        transcript: &mut T,
    ) -> Result<FflonkVerificationGuard<E, T_MAX_LOG>, Error>
    where
        E::Fr: Sampleable<T::Hash> + Ord + Hash + Hashable<T::Hash>,
        E::G1: CurveExt<ScalarExt = E::Fr>,
        FflonkCommitment<E, T_MAX_LOG>: Hashable<T::Hash> + 'com,
    {
        // SRS-aware bundling ceiling: read the prover's effective exponent
        // (paired with the write at the top of `multi_open`) and sanity-check
        // it. At `T_MAX_LOG == 0` nothing was written and there is no bundling.
        // Two checks: `≤ T_MAX_LOG` (can't exceed the configured cap) and
        // `≤ F::S − k` (so `ω_n` is a valid `2^t`-th power and `t_th_root`
        // terminates). Decoding by search over the (tiny) valid range both
        // recovers the integer and enforces the range in one step — any value
        // outside it (or a non-small field element) is rejected.
        let t_max_log: u32 = if T_MAX_LOG > 0 {
            // `effective_t_log` is the prover's chosen bundling exponent, sent
            // as a field element (so the encoding works for *any* transcript
            // hash — the byte-oriented Blake2b one and the field-absorbing
            // Poseidon one used in-circuit alike; `u32` would only work for the
            // former). We recover the integer and range-check it in one step by
            // matching against the field encoding of each value in the valid
            // band `[0, min(T_MAX_LOG, F::S − k)]`. This comparison is
            // endianness-agnostic (no `to_repr` byte poking), and the band is
            // tiny (≤ F::S). The two bounds are what the protocol needs:
            // `≤ T_MAX_LOG` so the eval point is a valid `2^t`-th power, and
            // `≤ F::S − k` so `ω_n` is, hence `t_th_root` terminates. An
            // out-of-range value is rejected here; an in-range value
            // inconsistent with the committed bundles fails the KZG opening
            // downstream.
            let claimed: E::Fr = transcript.read().map_err(|_| Error::SamplingError)?;
            let upper = T_MAX_LOG.min(<E::Fr as PrimeField>::S.saturating_sub(k));
            (0..=upper)
                .find(|&i| claimed == E::Fr::from(i as u64))
                .ok_or(Error::OpeningError)?
        } else {
            0
        };
        let t_max = 1usize << t_max_log;

        // === Bundle pre-expansion (fflonk-specific) ===
        //
        // Classify each query by its bundle (singleton vs t>1 vs Linear). For
        // singletons and Linear, emit the original (label, point, eval) triple
        // and register the MSM source. For t>1 bundles, defer: gather queries
        // by logical point, then expand into synthetic triples on the bundle's
        // `g` at the `t`-th roots of each logical, reconstructing g(root) via
        // Lemma 5.1 (`eval_claims_as_poly`). Downstream GWC sees a flat
        // (synth_label or original_label) → MSM mapping.

        // `singleton_triples` is only mutated under `fewer-point-sets`;
        // accept the unused-mut warning otherwise.
        #[allow(unused_mut)]
        let (mut multi_bundles_sorted, mut label_to_msm, mut singleton_triples) =
            bundle_expansion::classify_verifier_queries::<E, T_MAX_LOG>(queries, t_max);

        // Per-bundle over-opening reads. Same primitive as the prover side,
        // same input pairs ⇒ same dummy enumeration ⇒ matching transcript I/O.
        for (_synth, acc) in multi_bundles_sorted.iter_mut() {
            let missing = compute_dummy_queries(&acc.pairs);
            for (pair_idx, point) in missing {
                let slot = acc.pairs[pair_idx].0;
                let eval: E::Fr = transcript.read().map_err(|_| Error::SamplingError)?;
                acc.evals.insert((slot, point), eval);
            }
        }

        // `fewer-point-sets` reads on the singleton + Linear slice.
        // Bundle-derived triples are added *after* this — they live in a
        // separate point-set space (t-th roots), so the heuristic doesn't
        // (and shouldn't) touch them.
        #[cfg(feature = "fewer-point-sets")]
        {
            let pairs: Vec<(PolynomialLabel, E::Fr)> = singleton_triples
                .iter()
                .map(|(label, point, _)| (label.clone(), *point))
                .collect();
            let dummies = compute_dummy_queries(&pairs);
            for (idx, point) in dummies {
                let label = singleton_triples[idx].0.clone();
                let eval: E::Fr = transcript.read().map_err(|_| Error::SamplingError)?;
                singleton_triples.push((label, point, eval));
                // `label_to_msm` already maps `label`, so no new entry needed.
            }
        }

        // Now stitch the final triples list: singletons + Linear first
        // (their MSMs/labels are already in `label_to_msm`), then the
        // bundle-derived synthetic triples reconstructed via Lemma 5.1.
        let mut triples = singleton_triples;

        // Shared cache: `t_th_root(logical, t)` is identical across bundles
        // sharing the same (logical point, t), so amortize the sqrt chain.
        let mut t_th_root_cache: HashMap<(E::Fr, usize), E::Fr> = HashMap::new();
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
        // === GWC machinery ===

        let x1: E::Fr = transcript.squeeze_challenge();
        let x2: E::Fr = transcript.squeeze_challenge();

        let (commitment_map, point_sets) = construct_intermediate_sets(&triples)?;

        let mut q_coms: Vec<_> = vec![vec![]; point_sets.len()];
        let mut q_eval_sets = vec![vec![]; point_sets.len()];

        for com_data in commitment_map.into_iter() {
            let msm = label_to_msm
                .get(&com_data.label)
                .cloned()
                .expect("fflonk multi_prepare: no MSM registered for label");
            q_coms[com_data.set_index].push(msm);
            q_eval_sets[com_data.set_index].push(com_data.evals);
        }

        let nb_x1_powers = q_coms.iter().map(Vec::len).max().unwrap_or(0);
        assert!(nb_x1_powers >= q_eval_sets.iter().map(Vec::len).max().unwrap_or(0));

        #[cfg(feature = "truncated-challenges")]
        let powers_x1 = truncated_powers(x1).take(nb_x1_powers).collect::<Vec<_>>();

        #[cfg(not(feature = "truncated-challenges"))]
        let powers_x1 = powers(x1).take(nb_x1_powers).collect::<Vec<_>>();

        let q_coms = q_coms
            .into_iter()
            .map(|msms| msm_inner_product(msms, &powers_x1))
            .collect::<Vec<_>>();

        let q_eval_sets = q_eval_sets
            .iter()
            .map(|evals| evals_inner_product(evals, &powers_x1))
            .collect::<Vec<_>>();

        let (q_coms, q_eval_sets, point_sets) = {
            let mut order: Vec<usize> = (0..point_sets.len()).collect();
            order.sort_by_key(|&i| (point_sets[i].len(), i));
            let q_coms: Vec<_> = order.iter().map(|&i| q_coms[i].clone()).collect();
            let q_eval_sets: Vec<_> = order.iter().map(|&i| q_eval_sets[i].clone()).collect();
            let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
            (q_coms, q_eval_sets, point_sets)
        };

        let f_com: E::G1 = transcript
            .read::<FflonkCommitment<E, T_MAX_LOG>>()
            .map_err(|_| Error::SamplingError)?
            .0
            .into_iter()
            .next()
            .unwrap()
            .into_point();

        let x3: E::Fr = transcript.squeeze_challenge();
        #[cfg(feature = "truncated-challenges")]
        let x3 = truncate(x3);

        let mut q_evals_on_x3 = Vec::<E::Fr>::with_capacity(q_eval_sets.len());
        for _ in 0..q_eval_sets.len() {
            q_evals_on_x3.push(transcript.read().map_err(|_| Error::SamplingError)?);
        }

        let f_eval =
            point_sets.iter().zip(q_eval_sets.iter()).zip(q_evals_on_x3.iter()).rev().fold(
                E::Fr::ZERO,
                |acc_eval, ((points, evals), proof_eval)| {
                    let r_poly = lagrange_interpolate(points, evals);
                    let r_eval = eval_polynomial(&r_poly, x3);
                    let den = points.iter().fold(E::Fr::ONE, |acc, point| acc * &(x3 - point));
                    let eval = (*proof_eval - &r_eval) * den.invert().unwrap();
                    acc_eval * &(x2) + &eval
                },
            );

        let x4: E::Fr = transcript.squeeze_challenge();

        let final_com = {
            let size = q_coms.len() + 1;
            let mut coms = q_coms;
            let mut f_com_as_msm = MSMKZG::init();

            f_com_as_msm.append_term(
                E::Fr::ONE,
                f_com,
                PolynomialLabel::Custom("fflonk_batch".into()),
            );

            #[cfg(feature = "truncated-challenges")]
            coms.iter_mut().skip(1).for_each(MSMKZG::collapse);
            coms.push(f_com_as_msm);

            #[cfg(feature = "truncated-challenges")]
            let powers = truncated_powers(x4);

            #[cfg(not(feature = "truncated-challenges"))]
            let powers = powers(x4);

            msm_inner_product(coms, &powers.take(size).collect::<Vec<_>>())
        };

        let v = {
            let mut evals = q_evals_on_x3;
            evals.push(f_eval);

            #[cfg(feature = "truncated-challenges")]
            let powers = truncated_powers(x4);

            #[cfg(not(feature = "truncated-challenges"))]
            let powers = powers(x4);

            inner_product(&evals, powers)
        };

        let pi: E::G1 = transcript
            .read::<FflonkCommitment<E, T_MAX_LOG>>()
            .map_err(|_| Error::SamplingError)?
            .0
            .into_iter()
            .next()
            .unwrap()
            .into_point();

        let mut pi_msm = MSMKZG::<E>::init();
        pi_msm.append_term(E::Fr::ONE, pi, PolynomialLabel::Custom("π".into()));

        let scaled_pi = MSMKZG {
            scalars: vec![x3, v],
            bases: vec![pi, -E::G1::generator()],
            labels: vec![
                PolynomialLabel::Custom("π".into()),
                PolynomialLabel::Custom("-G".into()),
            ],
        };

        let mut msm_accumulator = DualMSM {
            left: pi_msm,
            right: final_com,
        };
        msm_accumulator.right.add_msm(&scaled_pi);

        Ok(FflonkVerificationGuard(msm_accumulator))
    }
}

/// The final pairing check is identical to KZG's (one G1 left, one G1
/// right, then pairing). We delegate to the inner [`DualMSM::check`].
impl<E: MultiMillerLoop, const T_MAX_LOG: u32> Guard<E::Fr, FflonkScheme<E, T_MAX_LOG>>
    for FflonkVerificationGuard<E, T_MAX_LOG>
where
    E::Fr: WithSmallOrderMulGroup<3>,
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn verify(
        self,
        params: &<FflonkScheme<E, T_MAX_LOG> as PolynomialCommitmentScheme<E::Fr>>::VerifierParameters,
    ) -> Result<(), Error> {
        self.0.check(params).then_some(()).ok_or(Error::OpeningError)
    }
}

#[cfg(test)]
mod tests;
