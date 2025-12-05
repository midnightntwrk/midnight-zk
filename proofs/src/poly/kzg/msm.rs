use std::{any::TypeId, fmt::Debug};

use ff::Field;
use group::Group;
use halo2curves::{
    pairing::{Engine, MillerLoopResult, MultiMillerLoop},
    CurveAffine,
};
use midnight_curves::{Fq, G1Projective};
use rayon::iter::{IntoParallelRefMutIterator, ParallelIterator};

#[cfg(feature = "gpu")]
use midnight_curves::G1Affine;
#[cfg(feature = "gpu")]
use crate::gpu::MsmExecutor;

use super::params::ParamsVerifierKZG;
use crate::{
    poly::{
        commitment::{Guard, PolynomialCommitmentScheme},
        kzg::KZGCommitmentScheme,
        Error,
    },
    utils::{
        arithmetic::{CurveExt, MSM},
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
    pub fn init() -> Self {
        MSMKZG {
            scalars: vec![],
            bases: vec![],
        }
    }

    /// Create an MSM from various MSMs
    pub fn from_many(msms: Vec<Self>) -> Self {
        let len = msms.iter().map(|m| m.scalars.len()).sum();

        let mut scalars = Vec::with_capacity(len);
        let mut bases = Vec::with_capacity(len);

        for mut msm in msms {
            scalars.append(&mut msm.scalars);
            bases.append(&mut msm.bases);
        }

        Self { scalars, bases }
    }

    /// Create a new MSM from a given base (with scalar of 1).
    pub fn from_base(base: &E::G1) -> Self {
        MSMKZG {
            scalars: vec![E::Fr::ONE],
            bases: vec![*base],
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
        self.scalars.reserve(other.scalars().len());
        self.scalars.extend_from_slice(&other.scalars());

        self.bases.reserve(other.bases().len());
        self.bases.extend_from_slice(&other.bases());
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
            msm_specific::<E::G1Affine>(&self.scalars, &self.bases)
        }
    }

    fn bases(&self) -> Vec<E::G1> {
        self.bases.clone()
    }

    fn scalars(&self) -> Vec<E::Fr> {
        self.scalars.clone()
    }
}

/// Check if BLST optimization is available for the given curve type
/// 
/// This should always return true for midnight_curves::G1Affine (BLS12-381).
/// If this returns false, the code will panic in msm_specific().
#[inline]
pub fn is_blst_available<C: CurveAffine>() -> bool {
    TypeId::of::<C>() == TypeId::of::<midnight_curves::G1Affine>()
}

#[cfg(feature = "gpu")]
/// MSM using pre-uploaded GPU bases (zero-copy optimization)
/// 
/// Uses bases cached in GPU memory, eliminating per-call conversion and upload overhead.
/// This is the primary optimization that provides GPU acceleration for K≥14.
/// 
/// # Arguments
/// * `coeffs` - Scalars for MSM computation
/// * `device_bases` - Pre-uploaded GPU bases (from ParamsKZG::get_or_upload_gpu_bases)
/// 
/// # Panics
/// Panics if type is not midnight_curves::G1Affine
pub fn msm_with_cached_bases<C: CurveAffine>(
    coeffs: &[C::Scalar],
    device_bases: &icicle_runtime::memory::DeviceVec<icicle_bls12_381::curve::G1Affine>,
) -> C::Curve {
    #[cfg(feature = "trace-msm")]
    let start = std::time::Instant::now();
    #[cfg(feature = "trace-msm")]
    eprintln!("[MSM-CACHED] Starting with {} points (using pre-uploaded GPU bases)", coeffs.len());
    
    // Verify we're using midnight_curves (BLS12-381)
    assert!(
        is_blst_available::<C>(),
        "MSM must use midnight_curves::G1Affine. Found: {}",
        std::any::type_name::<C>()
    );
    
    // Safe: we just verified the type
    let coeffs = unsafe { &*(coeffs as *const _ as *const [Fq]) };
    
    // Use GPU-cached bases via MsmExecutor
    use once_cell::sync::Lazy;
    static MSM_EXECUTOR: Lazy<MsmExecutor> = Lazy::new(MsmExecutor::default);
    
    #[cfg(feature = "trace-msm")]
    eprintln!("   [MSM-CACHED] Executing zero-copy GPU MSM");
    
    let res = MSM_EXECUTOR.execute_with_device_bases(coeffs, device_bases)
        .expect("Cached MSM execution failed");
    let result = unsafe { std::mem::transmute_copy(&res) };
    
    #[cfg(feature = "trace-msm")]
    {
        let elapsed = start.elapsed();
        eprintln!("✓  [MSM-CACHED] Completed in {:?} (no conversion overhead!)", elapsed);
    }
    
    result
}

#[allow(unsafe_code)]
/// MSM using BLST multi_exp with optional GPU acceleration
/// 
/// This function REQUIRES midnight_curves::G1Affine and will panic if used with other curves.
/// 
/// # GPU Acceleration
/// When compiled with `gpu` feature and size >= 16384 (K≥14):
/// - Uses ICICLE CUDA backend via GPU executor
/// - Automatically selects GPU for K≥14, CPU for smaller circuits
/// - GPU provides approximately 2x speedup for large circuits on capable hardware
pub fn msm_specific<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C::Curve]) -> C::Curve {
    #[cfg(feature = "trace-msm")]
    let start = std::time::Instant::now();
    #[cfg(feature = "trace-msm")]
    eprintln!("[MSM] Starting multi-scalar multiplication with {} points", coeffs.len());
    
    // Verify we're using midnight_curves (BLS12-381 with BLST)
    assert!(
        is_blst_available::<C>(),
        "MSM must use midnight_curves::G1Affine with BLST optimization. Found: {}",
        std::any::type_name::<C>()
    );
    
    // Safe: we just verified the type
    let coeffs = unsafe { &*(coeffs as *const _ as *const [Fq]) };
    let bases = unsafe { &*(bases as *const _ as *const [G1Projective]) };
    
    #[cfg(feature = "gpu")]
    {
        // Convert projective bases to affine for GPU MSM
        let bases_affine: Vec<G1Affine> = bases.iter().map(|p| G1Affine::from(*p)).collect();
        
        // Use GPU accelerated MSM via MsmExecutor
        // Will automatically use GPU for K>=14, CPU for smaller sizes
        use once_cell::sync::Lazy;
        static MSM_EXECUTOR: Lazy<MsmExecutor> = Lazy::new(MsmExecutor::default);
        
        #[cfg(feature = "trace-msm")]
        let backend = if bases.len() >= 16384 { "GPU" } else { "CPU" };
        #[cfg(feature = "trace-msm")]
        eprintln!("   [MSM] Using {} backend ({} points)", backend, bases.len());
        
        let res = MSM_EXECUTOR.execute(coeffs, &bases_affine)
            .expect("MSM execution failed");
        let result = unsafe { std::mem::transmute_copy(&res) };
        
        #[cfg(feature = "trace-msm")]
        {
            let elapsed = start.elapsed();
            eprintln!("✓  [MSM] Completed in {:?}", elapsed);
        }
        
        result
    }
    
    #[cfg(not(feature = "gpu"))]
    {
        // CPU-only path using BLST multi_exp
        #[cfg(feature = "trace-msm")]
        eprintln!("   [MSM] Using BLST multi_exp (BLS12-381 optimized)");
        
        let res = G1Projective::multi_exp(bases, coeffs);
        let result = unsafe { std::mem::transmute_copy(&res) };
        
        #[cfg(feature = "trace-msm")]
        {
            let elapsed = start.elapsed();
            eprintln!("✓  [MSM] Completed in {:?}", elapsed);
        }
        
        result
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
        Self::init()
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
    pub fn split(&self) -> SplitDualMSM<E> {
        let left = self.left.scalars.iter().zip(self.left.bases.iter()).collect();
        let right = self.right.scalars.iter().zip(self.right.bases.iter()).collect();
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
