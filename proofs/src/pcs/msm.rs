use std::{any::TypeId, fmt::Debug};

use ff::Field;
use group::{prime::PrimeCurveAffine, Curve, Group};
use itertools::izip;
use midnight_curves::{
    msm::msm_best,
    pairing::{Engine, MillerLoopResult, MultiMillerLoop},
    CurveAffine, Fq, G1Affine,
};
use rayon::iter::{IntoParallelRefMutIterator, ParallelIterator};

use super::params::ParamsVerifierKZG;
use crate::{poly::PolynomialLabel, utils::arithmetic::MSM};

/// A multi-scalar multiplication in the polynomial commitment scheme.
/// For every i, term (bases_i, scalars_i) may be have an optional
/// label_i for debugging or other purposes.
#[derive(Clone, Default, Debug)]
pub struct MSMKZG<E: Engine> {
    pub(crate) scalars: Vec<E::Fr>,
    pub(crate) bases: Vec<E::G1>,
    pub(crate) labels: Vec<PolynomialLabel>,
}

impl<E: Engine> MSMKZG<E> {
    /// Create an empty MSM instance
    pub fn init() -> Self {
        MSMKZG {
            scalars: vec![],
            bases: vec![],
            labels: vec![],
        }
    }

    /// Creates an MSM instance from parallel slices of scalars, bases, and
    /// labels.
    pub fn new(scalars: &[E::Fr], bases: &[E::G1], labels: &[PolynomialLabel]) -> Self {
        Self {
            scalars: scalars.to_vec(),
            bases: bases.to_vec(),
            labels: labels.to_vec(),
        }
    }

    /// Create an MSM from various MSMs
    pub fn from_many(msms: Vec<Self>) -> Self {
        let len = msms.iter().map(|m| m.scalars.len()).sum();

        let mut scalars = Vec::with_capacity(len);
        let mut bases = Vec::with_capacity(len);
        let mut labels = Vec::with_capacity(len);

        for mut msm in msms {
            scalars.append(&mut msm.scalars);
            bases.append(&mut msm.bases);
            labels.append(&mut msm.labels);
        }

        Self {
            scalars,
            bases,
            labels,
        }
    }

    /// Create a new MSM from a given base (with scalar of 1).
    pub fn from_base(base: &E::G1) -> Self {
        MSMKZG {
            scalars: vec![E::Fr::ONE],
            bases: vec![*base],
            labels: vec![PolynomialLabel::NoLabel],
        }
    }
}

impl<E: Engine + Debug> MSMKZG<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    /// Evaluates the MSM to a single point and replaces all terms with that
    /// single point (scalar = 1), labeling the result with `label`.
    ///
    /// This mirrors `AssignedMsm::collapse` in the circuits crate.
    ///
    /// # Panics (in debug mode)
    ///
    /// If a term carries a `Fixed` or `PermutationFixed` label.
    //  This is because these "fixed" labels carry information that we do not want
    //  to lose when collapsing, since it is relevant for the `verifier_gadget`.
    pub fn collapse(&mut self, label: PolynomialLabel) {
        debug_assert!(
            !self.labels.iter().any(|l| matches!(
                l,
                PolynomialLabel::Fixed(_) | PolynomialLabel::PermutationFixed(_)
            )),
            "collapse: no label may be Fixed or PermutationFixed, found: {:?}",
            self.labels,
        );
        let point = self.eval();
        self.scalars = vec![E::Fr::ONE];
        self.bases = vec![point];
        self.labels = vec![label];
    }
}

impl<E: Engine + Debug> MSM<E::G1Affine> for MSMKZG<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn append_term(&mut self, scalar: E::Fr, point: E::G1, label: PolynomialLabel) {
        self.scalars.push(scalar);
        self.bases.push(point);
        self.labels.push(label);
    }

    fn add_msm(&mut self, other: &Self) {
        self.scalars.reserve(other.scalars().len());
        self.scalars.extend_from_slice(&other.scalars());

        self.bases.reserve(other.bases().len());
        self.bases.extend_from_slice(&other.bases());

        self.labels.reserve(other.labels().len());
        self.labels.extend_from_slice(&other.labels());
    }

    fn scale(&mut self, factor: E::Fr) {
        self.scalars.par_iter_mut().for_each(|s| {
            *s *= &factor;
        })
    }

    fn check(&self) -> bool {
        bool::from(self.eval().is_identity())
    }

    fn eval(&self) -> E::G1 {
        if self.scalars == vec![E::Fr::ONE] {
            self.bases[0]
        } else {
            let mut affine = vec![E::G1Affine::identity(); self.bases.len()];
            E::G1::batch_normalize(&self.bases, &mut affine);
            msm_specific::<E::G1Affine>(&self.scalars, &affine)
        }
    }

    fn bases(&self) -> Vec<E::G1> {
        self.bases.clone()
    }

    fn scalars(&self) -> Vec<E::Fr> {
        self.scalars.clone()
    }

    fn labels(&self) -> Vec<PolynomialLabel> {
        self.labels.clone()
    }
}

#[allow(unsafe_code)]
/// Wrapper over the MSM function to use the blstrs underlying function.
/// Bases are passed as affine points.
pub fn msm_specific<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    // We remove zeros (keep only non-zero coefficients).
    let (coeffs, bases): (Vec<C::Scalar>, Vec<C>) = coeffs
        .iter()
        .zip(bases)
        .filter(|(s, _)| !s.is_zero_vartime())
        .map(|(s, b)| (*s, *b))
        .unzip();

    if coeffs.is_empty() {
        return C::Curve::identity();
    }

    // NOTE: Empirically checked that for MSMs larger than 2**18, the blstrs
    // implementation regresses.
    // TODO: Review this threshold after optimizations.
    if coeffs.len() <= (2 << 18) && TypeId::of::<C>() == TypeId::of::<G1Affine>() {
        // Safe: we just checked the type.
        let coeffs = unsafe { &*(coeffs.as_slice() as *const _ as *const [Fq]) };
        let bases = unsafe { &*(bases.as_slice() as *const _ as *const [G1Affine]) };
        // TODO: 255 is fine because type is checked. Another option is propagating
        // nbits as an input of msm_specific.
        let res = G1Affine::multi_exp_affine(bases, coeffs);
        unsafe { std::mem::transmute_copy(&res) }
    } else {
        msm_best(&coeffs, &bases)
    }
}

/// Two channel MSM accumulator
#[derive(Debug, Clone)]
pub struct DualMSM<E: Engine> {
    pub(crate) left: MSMKZG<E>,
    pub(crate) right: MSMKZG<E>,
}

/// A [DualMSM] split into left and right vectors of `(Scalar, Point)` tuples
pub type SplitDualMSM<'a, E> = (
    Vec<(
        &'a PolynomialLabel,
        &'a <E as Engine>::Fr,
        &'a <E as Engine>::G1,
    )>,
    Vec<(
        &'a PolynomialLabel,
        &'a <E as Engine>::Fr,
        &'a <E as Engine>::G1,
    )>,
);

impl<E: MultiMillerLoop + Debug> Default for DualMSM<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn default() -> Self {
        Self::init()
    }
}

impl<E: MultiMillerLoop + Debug> DualMSM<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    /// Create an empty two channel MSM accumulator instance
    pub fn init() -> Self {
        Self {
            left: MSMKZG::init(),
            right: MSMKZG::init(),
        }
    }

    /// Create a new two channel MSM accumulator instance
    pub fn new(left: MSMKZG<E>, right: MSMKZG<E>) -> Self {
        Self { left, right }
    }

    /// Split the [DualMSM] into `left` and `right`
    pub fn split(&self) -> SplitDualMSM<'_, E> {
        let left = izip!(
            self.left.labels.iter(),
            self.left.scalars.iter(),
            self.left.bases.iter()
        )
        .collect();
        let right = izip!(
            self.right.labels.iter(),
            self.right.scalars.iter(),
            self.right.bases.iter(),
        )
        .collect();
        (left, right)
    }

    /// Scale all scalars in the MSM by some scaling factor
    pub fn scale(&mut self, e: E::Fr) {
        self.left.scale(e);
        self.right.scale(e);
    }

    /// Add another multiexp into this one
    pub fn add_msm(&mut self, other: Self) {
        self.left.add_msm(&other.left);
        self.right.add_msm(&other.right);
    }

    /// Performs final pairing check with given verifier params and two channel
    /// linear combination
    pub fn check(self, params: &ParamsVerifierKZG<E>) -> bool {
        let left = if self.left.scalars.len() == 1 && self.left.scalars[0] == E::Fr::ONE {
            self.left.bases[0]
        } else {
            self.left.eval()
        };

        let right = self.right.eval();

        let (term_1, term_2) = (
            (&left.into(), &params.s_g2_prepared),
            (&right.into(), &params.n_g2_prepared),
        );
        let terms = &[term_1, term_2];

        bool::from(E::multi_miller_loop(&terms[..]).final_exponentiation().is_identity())
    }
}
