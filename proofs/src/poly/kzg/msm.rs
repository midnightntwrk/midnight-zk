use std::fmt::Debug;

use group::{prime::PrimeCurveAffine, Curve, Group};
use halo2curves::{
    msm::msm_best,
    pairing::{Engine, MillerLoopResult, MultiMillerLoop},
    CurveAffine,
};

use super::params::ParamsVerifierKZG;
use crate::{
    poly::{
        commitment::{Guard, PolynomialCommitmentScheme},
        kzg::KZGCommitmentScheme,
        Error,
    },
    utils::{
        arithmetic::{parallelize, CurveExt, MSM},
        helpers::ProcessedSerdeObject,
    },
};

/// A multiscalar multiplication in the polynomial commitment scheme
#[derive(Clone, Default, Debug)]
pub struct MSMKZG<E: Engine> {
    pub(crate) scalars: Vec<E::Fr>,
    pub(crate) bases: Vec<E::G1>,
}

impl<E: Engine> MSMKZG<E> {
    /// Create an empty MSM instance
    pub fn new() -> Self {
        MSMKZG {
            scalars: vec![],
            bases: vec![],
        }
    }

    /// Prepares all scalars in the MSM to linear combination
    pub fn combine_with_base(&mut self, base: E::Fr) {
        use ff::Field;
        let mut acc = E::Fr::ONE;
        if !self.scalars.is_empty() {
            for scalar in self.scalars.iter_mut().rev() {
                *scalar *= &acc;
                acc *= base;
            }
        }
    }
}

impl<E: Engine + Debug> MSM<E::G1Affine> for MSMKZG<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn append_term(&mut self, scalar: E::Fr, point: E::G1) {
        self.scalars.push(scalar);
        self.bases.push(point);
    }

    fn add_msm(&mut self, other: &Self) {
        self.scalars.extend(other.scalars().iter());
        self.bases.extend(other.bases().iter());
    }

    fn scale(&mut self, factor: E::Fr) {
        if !self.scalars.is_empty() {
            parallelize(&mut self.scalars, |scalars, _| {
                for other_scalar in scalars {
                    *other_scalar *= &factor;
                }
            })
        }
    }

    fn check(&self) -> bool {
        bool::from(self.eval().is_identity())
    }

    fn eval(&self) -> E::G1 {
        let mut bases = vec![E::G1Affine::identity(); self.scalars.len()];
        E::G1::batch_normalize(&self.bases, &mut bases);
        msm_best(&self.scalars, &bases)
    }

    fn bases(&self) -> Vec<E::G1> {
        self.bases.clone()
    }

    fn scalars(&self) -> Vec<E::Fr> {
        self.scalars.clone()
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
    Vec<(&'a <E as Engine>::Fr, &'a <E as Engine>::G1)>,
    Vec<(&'a <E as Engine>::Fr, &'a <E as Engine>::G1)>,
);

impl<E: MultiMillerLoop + Debug> Default for DualMSM<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E: MultiMillerLoop> Guard<E::Fr, KZGCommitmentScheme<E>> for DualMSM<E>
where
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn verify(
        self,
        params: &<KZGCommitmentScheme<E> as PolynomialCommitmentScheme<E::Fr>>::VerifierParameters,
    ) -> Result<(), Error> {
        self.check(params).then_some(()).ok_or(Error::OpeningError)
    }
}

impl<E: MultiMillerLoop + Debug> DualMSM<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    /// Create a new two channel MSM accumulator instance
    pub fn new() -> Self {
        Self {
            left: MSMKZG::new(),
            right: MSMKZG::new(),
        }
    }

    /// Split the [DualMSM] into `left` and `right`.
    pub fn split(&self) -> SplitDualMSM<E> {
        let left = self
            .left
            .scalars
            .iter()
            .zip(self.left.bases.iter())
            .collect();
        let right = self
            .right
            .scalars
            .iter()
            .zip(self.right.bases.iter())
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
        let s_g2_prepared = E::G2Prepared::from(params.s_g2.into());
        let n_g2_prepared = E::G2Prepared::from(-E::G2Affine::generator());

        let left = self.left.eval();
        let right = self.right.eval();

        let (term_1, term_2) = (
            (&left.into(), &s_g2_prepared),
            (&right.into(), &n_g2_prepared),
        );
        let terms = &[term_1, term_2];

        bool::from(
            E::multi_miller_loop(&terms[..])
                .final_exponentiation()
                .is_identity(),
        )
    }
}
