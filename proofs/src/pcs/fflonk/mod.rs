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

use self::math::{combine, primitive_root_of_unity, roots as t_th_roots, t_th_root};
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
