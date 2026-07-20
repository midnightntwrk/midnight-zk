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

