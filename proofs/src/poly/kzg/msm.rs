use std::{any::TypeId, collections::BTreeMap, fmt::Debug, iter};

use ff::Field;
use group::{Curve, Group, prime::PrimeCurveAffine};
use itertools::izip;
use midnight_curves::{
    CurveAffine, Fq, G1Affine,
    msm::msm_best,
    pairing::{Engine, MillerLoopResult, MultiMillerLoop},
};
use rayon::iter::{IntoParallelRefMutIterator, ParallelIterator};

use super::params::ParamsVerifierKZG;
use crate::{
    poly::{Error, PolynomialLabel, commitment::Guard},
    utils::{
        arithmetic::{CurveExt, MSM},
        helpers::ProcessedSerdeObject,
    },
};

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
    /// Evaluates the terms whose label is not
    /// [fixed](PolynomialLabel::is_fixed) to a single point (scalar = 1),
    /// labeled with `label`. Fixed terms are kept, those sharing a label
    /// have their scalars summed.
    ///
    /// This mirrors `AssignedMsm::collapse` in the circuits crate, which keeps
    /// the fixed bases apart for the `verifier_gadget`.
    pub fn collapse(&mut self, label: PolynomialLabel) {
        let mut fixed = BTreeMap::<PolynomialLabel, (E::Fr, E::G1)>::new();
        let mut variable = MSMKZG::<E>::init();
        for ((scalar, base), l) in self.scalars.iter().zip(&self.bases).zip(&self.labels) {
            if l.is_fixed() {
                fixed.entry(l.clone()).or_insert((E::Fr::ZERO, *base)).0 += scalar;
            } else {
                variable.append_term(*scalar, *base, l.clone());
            }
        }
        let point = variable.eval();
        self.labels = fixed.keys().cloned().chain(iter::once(label)).collect();
        (self.scalars, self.bases) =
            fixed.into_values().chain(iter::once((E::Fr::ONE, point))).unzip();
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
        // A collapse leaves no term to evaluate when all of them are fixed.
        if self.scalars.is_empty() {
            E::G1::identity()
        } else if self.scalars == vec![E::Fr::ONE] {
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
/// Wrapper over the MSM function:
/// Bls12-381 uses blstrs [`G1Affine::multi_exp_affine`], other curves use
/// `msm_best`.
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

    if TypeId::of::<C>() == TypeId::of::<G1Affine>() {
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

impl<E: MultiMillerLoop> Guard<ParamsVerifierKZG<E>> for DualMSM<E>
where
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn verify(self, params: &ParamsVerifierKZG<E>) -> Result<(), Error> {
        self.check(params).then_some(()).ok_or(Error::OpeningError)
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

#[cfg(test)]
mod tests {
    use ff::Field;
    use group::Group;
    use midnight_curves::{Bls12, Fq, G1Projective};
    use rand_core::OsRng;

    use super::MSMKZG;
    use crate::{
        poly::{
            PolynomialLabel::{self, Advice, Collection, Fixed, NoLabel, PermutationFixed},
            kzg::commitment::KZGCommitment,
        },
        utils::arithmetic::MSM,
    };

    #[test]
    fn test_collapse_keeps_fixed_terms() {
        let fixed_chunk = Collection(vec![Fixed(1), PermutationFixed(0)]);
        let labels = [
            Fixed(0),
            Advice(0),
            fixed_chunk.clone(),
            Collection(vec![Fixed(2), Advice(1)]),
            Fixed(0),
        ];
        let scalars: Vec<_> = labels.iter().map(|_| Fq::random(OsRng)).collect();
        let mut bases: Vec<_> = labels.iter().map(|_| G1Projective::random(OsRng)).collect();
        bases[4] = bases[0];

        let mut msm = MSMKZG::<Bls12>::new(&scalars, &bases, &labels);
        let expected = msm.eval();
        msm.collapse(PolynomialLabel::NoLabel);

        assert_eq!(msm.eval(), expected);
        assert_eq!(
            msm.labels,
            [Fixed(0), fixed_chunk, PolynomialLabel::NoLabel]
        );
        assert_eq!(msm.bases[..2], [bases[0], bases[2]]);
        assert_eq!(msm.scalars[..2], [scalars[0] + scalars[4], scalars[2]]);
        assert_eq!(msm.scalars[2], Fq::ONE);

        // Only fixed terms: the collapsed point is the identity.
        let mut msm = MSMKZG::<Bls12>::new(&scalars[..1], &bases[..1], &labels[..1]);
        msm.collapse(PolynomialLabel::NoLabel);
        assert_eq!(msm.bases, [bases[0], G1Projective::identity()]);
    }

    /// A fixed column queried at two rotations lands in a collapsed point set:
    /// its term must survive the collapse, as it does in-circuit.
    #[test]
    fn test_commitment_collapse_keeps_fixed_terms() {
        let points: Vec<_> = (0..2).map(|_| G1Projective::random(OsRng)).collect();
        let scalars: Vec<_> = (0..2).map(|_| Fq::random(OsRng)).collect();
        let expected = points[0] * scalars[0] + points[1] * scalars[1];

        let mut com = KZGCommitment::<Bls12>::Linear(
            points.clone(),
            scalars.clone(),
            vec![Fixed(0), Advice(0)],
        );
        com.collapse(NoLabel);
        let KZGCommitment::Linear(bases, coeffs, labels) = com else {
            panic!("the fixed term was folded")
        };
        assert_eq!(labels, [Fixed(0), NoLabel]);
        assert_eq!(bases[0], points[0]);
        assert_eq!(coeffs[0], scalars[0]);
        assert_eq!(
            MSMKZG::<Bls12>::new(&coeffs, &bases, &labels).eval(),
            expected
        );

        let mut com = KZGCommitment::<Bls12>::Linear(points, scalars, vec![Advice(0), Advice(1)]);
        com.collapse(NoLabel);
        assert_eq!(com, KZGCommitment::Simple(expected, NoLabel));
    }
}
