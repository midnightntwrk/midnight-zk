use std::{fmt::Debug, io, sync::OnceLock};

use ff::{Field, PrimeField};
use group::{Curve, Group, GroupEncoding, prime::PrimeCurveAffine};
use midnight_curves::{
    pairing::{Engine, MultiMillerLoop},
    serde::SerdeObject,
};
use rand_core::RngCore;

use crate::{
    poly::{PolynomialBasis, PolynomialRepresentation},
    utils::{
        SerdeFormat,
        arithmetic::{CurveAffine, g_to_lagrange, parallelize},
        helpers::ProcessedSerdeObject,
    },
};

/// These are the public parameters for the polynomial commitment scheme.
///
/// The bases of the `LagrangeDelta` and `LagrangeDoubleDelta` representations
/// only depend on the Lagrange SRS, and are not part of the parameters written
/// by [`Self::write`]. They are built by the first commitment in one of these
/// representations, or ahead of it by [`Self::precompute_delta_bases`]. To
/// skip building them on every run, store them with
/// [`Self::write_delta_bases`] and load them with [`Self::read_delta_bases`].
#[derive(Debug, Clone)]
pub struct ParamsKZG<E: Engine> {
    pub(crate) g: Vec<E::G1Affine>,
    pub(crate) g_lagrange: Vec<E::G1Affine>,
    /// The bases of the `LagrangeDelta` and `LagrangeDoubleDelta`
    /// representations, derived from `g_lagrange`. Empty until they are built
    /// or read.
    pub(crate) delta_bases: OnceLock<DeltaBases<E::G1Affine>>,
    pub(crate) g2: E::G2,
    pub(crate) s_g2: E::G2,
}

/// The bases of the commit-only delta representations of a Lagrange SRS.
#[derive(Debug, Clone)]
pub(crate) struct DeltaBases<C> {
    /// Suffix-sum of the Lagrange SRS:
    /// `delta[i] = sum_{j=i}^{n-1} g_lagrange[j]`.
    delta: Vec<C>,
    /// Suffix-sum of `delta`:
    /// `double_delta[i] = sum_{j=i}^{n-1} delta[j]`.
    /// Used as the SRS for the `LagrangeDoubleDelta` basis. Same derivation
    /// as `delta`, applied a second time:
    /// `sum_j a_j · L_j = sum_i c_i · double_delta[i]`,
    /// where `c_i = b_i - b_{i-1}` and `b_i = a_i - a_{i-1}`.
    double_delta: Vec<C>,
}

impl<C: CurveAffine> DeltaBases<C> {
    /// Builds the delta bases of the Lagrange SRS `g_lagrange`.
    fn new(g_lagrange: &[C]) -> Self {
        let delta = suffix_sum(g_lagrange);
        let double_delta = suffix_sum(&delta);
        Self {
            delta,
            double_delta,
        }
    }

    /// Whether the bases have the size of `g_lagrange` and satisfy the suffix
    /// sum relations with it at the last position and at a few others.
    ///
    /// The bases of another SRS fail at every position, so this tells apart
    /// the bases of `g_lagrange` from those of another SRS or of another
    /// size. It does not validate every point.
    fn matches(&self, g_lagrange: &[C]) -> bool {
        let n = g_lagrange.len();
        if n == 0 || self.delta.len() != n || self.double_delta.len() != n {
            return false;
        }
        let is_sum = |sum: &C, a: &C, b: &C| (a.to_curve() + *b).to_affine() == *sum;
        self.delta[n - 1] == g_lagrange[n - 1]
            && self.double_delta[n - 1] == self.delta[n - 1]
            && [0, n / 2, n.saturating_sub(2)].into_iter().filter(|i| i + 1 < n).all(|i| {
                is_sum(&self.delta[i], &self.delta[i + 1], &g_lagrange[i])
                    && is_sum(
                        &self.double_delta[i],
                        &self.double_delta[i + 1],
                        &self.delta[i],
                    )
            })
    }
}

/// Builds the suffix-sum of an affine SRS: `out[i] = sum_{j=i}^{n-1} input[j]`.
///
/// Accumulate in projective coordinates (one curve add per step) and
/// batch-normalise to affine at the end. n-1 projective adds + one O(n)
/// batch_normalise.
///
/// # Panics
/// If input is empty
pub(crate) fn suffix_sum<C: CurveAffine>(input: &[C]) -> Vec<C> {
    let n = input.len();
    let mut acc_proj: Vec<C::Curve> = vec![C::Curve::identity(); n];
    acc_proj[n - 1] = input[n - 1].into();
    for i in (0..n - 1).rev() {
        acc_proj[i] = acc_proj[i + 1] + input[i];
    }
    let mut acc_affine = vec![C::identity(); n];
    C::Curve::batch_normalize(&acc_proj, &mut acc_affine);
    acc_affine
}

/// Writes `points`: compressed if `format` is `Processed`, raw otherwise.
pub(crate) fn write_points<C, W>(
    points: &[C],
    writer: &mut W,
    format: SerdeFormat,
) -> io::Result<()>
where
    C: GroupEncoding + SerdeObject,
    W: io::Write,
{
    for el in points {
        match format {
            SerdeFormat::Processed => writer.write_all(el.to_bytes().as_ref())?,
            _ => el.write_raw(writer)?,
        }
    }
    Ok(())
}

/// Reads `n` points written by [`write_points`] in `format`. Compressed points
/// are decompressed in parallel.
pub(crate) fn read_points<C, R>(reader: &mut R, format: SerdeFormat, n: usize) -> io::Result<Vec<C>>
where
    C: GroupEncoding + SerdeObject + Clone + Send,
    R: io::Read,
{
    match format {
        SerdeFormat::Processed => {
            let mut points_compressed = vec![C::Repr::default(); n];
            for points_compressed in points_compressed.iter_mut() {
                reader.read_exact((*points_compressed).as_mut())?;
            }
            let mut points = vec![Option::<C>::None; n];
            parallelize(&mut points, |points, chunks| {
                for (i, point) in points.iter_mut().enumerate() {
                    *point = Option::from(C::from_bytes(&points_compressed[chunks + i]));
                }
            });
            points
                .into_iter()
                .map(|p| p.ok_or_else(|| io::Error::other("invalid point encoding")))
                .collect()
        }
        SerdeFormat::RawBytes => (0..n).map(|_| C::read_raw(reader)).collect(),
        SerdeFormat::RawBytesUnchecked => {
            Ok((0..n).map(|_| C::read_raw_unchecked(reader)).collect())
        }
    }
}

impl<E> ParamsKZG<E>
where
    E: Engine + Debug,
    E::G1Affine: CurveAffine,
{
    /// Return the SRS bases corresponding to the polynomial representation `B`.
    ///
    /// The `LagrangeDelta` and `LagrangeDoubleDelta` bases are built here if
    /// they are missing: see [`ParamsKZG`].
    pub fn bases<B: PolynomialRepresentation>(&self) -> &[E::G1Affine] {
        match B::BASIS {
            PolynomialBasis::Coeff => &self.g,
            PolynomialBasis::Lagrange => &self.g_lagrange,
            PolynomialBasis::LagrangeDelta => &self.delta_bases().delta,
            PolynomialBasis::LagrangeDoubleDelta => &self.delta_bases().double_delta,
            PolynomialBasis::ExtendedLagrange => {
                unimplemented!("KZG does not support extended Lagrange bases")
            }
        }
    }

    /// The delta bases. If they are missing, they are built on the fly, with a
    /// warning on how to avoid it.
    fn delta_bases(&self) -> &DeltaBases<E::G1Affine> {
        self.delta_bases.get_or_init(|| {
            tracing::warn!(
                k = self.max_k(),
                "Building the delta bases of the KZG parameters on the fly. Store them once \
                 with `ParamsKZG::write_delta_bases` and load them with \
                 `ParamsKZG::read_delta_bases` to make later runs faster."
            );
            DeltaBases::new(&self.g_lagrange)
        })
    }

    /// Builds the `LagrangeDelta` and `LagrangeDoubleDelta` bases, unless they
    /// are there already. Otherwise, the first commitment in one of these
    /// representations builds them.
    pub fn precompute_delta_bases(&self) {
        self.delta_bases.get_or_init(|| DeltaBases::new(&self.g_lagrange));
    }

    /// Whether the `LagrangeDelta` and `LagrangeDoubleDelta` bases have been
    /// built or read already.
    pub fn has_delta_bases(&self) -> bool {
        self.delta_bases.get().is_some()
    }

    /// Returns the size of the SRS, expressed as the exponent `k` such that it
    /// has `2^k` elements.
    pub fn max_k(&self) -> u32 {
        assert_eq!(self.g.len(), self.g_lagrange.len());
        self.g_lagrange.len().ilog2()
    }

    /// Downsize the current parameters to match a smaller `k`. The delta bases
    /// depend on the size, so they are dropped, to be built again on first use.
    pub fn downsize(&mut self, new_k: u32) {
        if self.max_k() == new_k {
            return;
        }

        let n = 1 << new_k;
        assert!(n < self.g_lagrange.len());
        self.g.truncate(n);
        self.g_lagrange = g_to_lagrange(&self.g, new_k);
        self.delta_bases = OnceLock::new();
    }

    /// Initializes parameters for the curve, draws toxic secret from given rng.
    /// MUST NOT be used in production.
    pub fn unsafe_setup<R: RngCore>(k: u32, rng: R) -> Self {
        // Largest root of unity exponent of the Engine is `2^E::Fr::S`, so we can
        // only support FFTs of polynomials below degree `2^E::Fr::S`.
        assert!(k <= E::Fr::S);
        let n: u64 = 1 << k;

        // Calculate g = [G1, [s] G1, [s^2] G1, ..., [s^(n-1)] G1] in parallel.
        let g1 = E::G1::generator();
        let s = <E::Fr>::random(rng);

        let mut g = vec![E::G1::identity(); n as usize];
        parallelize(&mut g, |g, start| {
            let mut current_g: E::G1 = g1;
            current_g *= s.pow_vartime([start as u64]);
            for g in g.iter_mut() {
                *g = current_g;
                current_g *= s;
            }
        });

        let mut g_lagrange = vec![E::G1::identity(); n as usize];
        let mut root = E::Fr::ROOT_OF_UNITY;
        for _ in k..E::Fr::S {
            root = root.square();
        }
        let n_inv = E::Fr::from(n).invert().expect("inversion should be ok for n = 1<<k");
        let multiplier = (s.pow_vartime([n]) - E::Fr::ONE) * n_inv;
        parallelize(&mut g_lagrange, |g, start| {
            for (idx, g) in g.iter_mut().enumerate() {
                let offset = start + idx;
                let root_pow = root.pow_vartime([offset as u64]);
                let scalar = multiplier * root_pow * (s - root_pow).invert().unwrap();
                *g = g1 * scalar;
            }
        });

        let mut g_affine = vec![E::G1Affine::identity(); n as usize];
        E::G1::batch_normalize(&g, &mut g_affine);

        let mut g_lagrange_affine = vec![E::G1Affine::identity(); n as usize];
        E::G1::batch_normalize(&g_lagrange, &mut g_lagrange_affine);

        let g2 = E::G2::generator();
        let s_g2 = g2 * s;

        Self {
            g: g_affine,
            g_lagrange: g_lagrange_affine,
            delta_bases: OnceLock::new(),
            g2,
            s_g2,
        }
    }

    /// Initializes parameters for the curve through existing parameters
    /// k, g, g_lagrange (optional), g2, s_g2
    pub fn from_parts(
        k: u32,
        g: Vec<E::G1>,
        g_lagrange: Option<Vec<E::G1>>,
        g2: E::G2,
        s_g2: E::G2,
    ) -> Self {
        let n = g.len();
        let mut g_affine = vec![E::G1Affine::identity(); n];
        E::G1::batch_normalize(&g, &mut g_affine);
        let g_lagrange_affine = match g_lagrange {
            Some(g_l) => {
                let mut aff = vec![E::G1Affine::identity(); g_l.len()];
                E::G1::batch_normalize(&g_l, &mut aff);
                aff
            }
            None => g_to_lagrange(&g_affine, k),
        };
        Self {
            g: g_affine,
            g_lagrange: g_lagrange_affine,
            delta_bases: OnceLock::new(),
            g2,
            s_g2,
        }
    }

    /// Returns the committed lagrange polynomials of these KZG params.
    pub fn g_lagrange(&self) -> &[E::G1Affine] {
        &self.g_lagrange
    }

    /// Returns generator on G2
    pub fn g2(&self) -> E::G2 {
        self.g2
    }

    /// Returns \[τ\]₂, a commitment to τ in G2.
    pub fn s_g2(&self) -> E::G2 {
        self.s_g2
    }

    /// Writes parameters to buffer
    pub fn write<W>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        E::G1Affine: SerdeObject,
        E::G2: ProcessedSerdeObject,
        W: io::Write,
    {
        writer.write_all(&self.g.len().ilog2().to_le_bytes())?;
        write_points(&self.g, writer, format)?;
        write_points(&self.g_lagrange, writer, format)?;
        self.g2.write(writer, format)?;
        self.s_g2.write(writer, format)?;
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read<R>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>
    where
        E::G1Affine: SerdeObject,
        E::G2: ProcessedSerdeObject,
        R: io::Read,
    {
        Self::read_with_max_k(reader, format, None)
    }

    /// Like [`Self::read`], but fails if `k` exceeds `max_k`, before
    /// allocating anything of that size.
    pub fn read_with_max_k<R>(
        reader: &mut R,
        format: SerdeFormat,
        max_k: Option<u32>,
    ) -> io::Result<Self>
    where
        E::G1Affine: SerdeObject,
        E::G2: ProcessedSerdeObject,
        R: io::Read,
    {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);
        let max_k = max_k.map_or(E::Fr::S, |max_k| max_k.min(E::Fr::S));
        if k > max_k {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("k = {k} exceeds the maximum supported value {max_k}"),
            ));
        }
        let n = 1 << k;

        let g = read_points(reader, format, n)?;
        let g_lagrange = read_points(reader, format, n)?;

        let g2 = E::G2::read(reader, format)?;
        let s_g2 = E::G2::read(reader, format)?;

        Ok(Self {
            g,
            g_lagrange,
            delta_bases: OnceLock::new(),
            g2,
            s_g2,
        })
    }

    /// Writes the `LagrangeDelta` and `LagrangeDoubleDelta` bases, building
    /// them if they are missing: `k`, then the points of both bases, written
    /// as [`Self::write`] writes those of the SRS.
    ///
    /// Only with `SerdeFormat::RawBytesUnchecked` is reading them back faster
    /// than building them: validating the points costs more than building the
    /// bases.
    pub fn write_delta_bases<W>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        E::G1Affine: SerdeObject,
        W: io::Write,
    {
        let bases = self.delta_bases.get_or_init(|| DeltaBases::new(&self.g_lagrange));
        writer.write_all(&self.max_k().to_le_bytes())?;
        write_points(&bases.delta, writer, format)?;
        write_points(&bases.double_delta, writer, format)
    }

    /// Reads the `LagrangeDelta` and `LagrangeDoubleDelta` bases written by
    /// [`Self::write_delta_bases`], in place of building them.
    ///
    /// The bases must be those of these parameters: it fails, leaving the
    /// parameters unchanged, if they are for another `k`, or if they do not
    /// match the Lagrange SRS at the few positions that are checked. This
    /// catches the bases of another SRS, but it does not validate every point:
    /// the bases must be as trusted as the SRS itself.
    ///
    /// With `SerdeFormat::RawBytesUnchecked`, it may panic on truncated or
    /// malformed input.
    pub fn read_delta_bases<R>(&mut self, reader: &mut R, format: SerdeFormat) -> io::Result<()>
    where
        E::G1Affine: SerdeObject,
        R: io::Read,
    {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);
        if k != self.max_k() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("delta bases for k = {k}, expected k = {}", self.max_k()),
            ));
        }
        let n = self.g_lagrange.len();

        let bases = DeltaBases {
            delta: read_points(reader, format, n)?,
            double_delta: read_points(reader, format, n)?,
        };
        if !bases.matches(&self.g_lagrange) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "the delta bases are not those of this SRS",
            ));
        }
        self.delta_bases = OnceLock::from(bases);
        Ok(())
    }
}

// TODO: see the issue at https://github.com/appliedzkp/halo2/issues/45
// So we probably need much smaller verifier key. However for new bases in g1
// should be in verifier keys.
/// KZG multi-open verification parameters
#[derive(Clone, Debug)]
pub struct ParamsVerifierKZG<E: MultiMillerLoop> {
    pub(crate) s_g2: E::G2,
    pub(crate) n_g2_prepared: E::G2Prepared,
    pub(crate) s_g2_prepared: E::G2Prepared,
}

impl<E> ParamsVerifierKZG<E>
where
    E: MultiMillerLoop + Debug,
    E::G2: Curve + ProcessedSerdeObject,
{
    /// Returns \[τ\]₂, a commitment to τ in G2.
    pub fn s_g2(&self) -> E::G2 {
        self.s_g2
    }

    /// Writes parameters to buffer
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        self.s_g2.write(writer, format)?;
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let s_g2 = E::G2::read(reader, format)?;
        let s_g2_prepared = E::G2Prepared::from(s_g2.into());
        let n_g2_prepared = E::G2Prepared::from(-E::G2Affine::generator());

        Ok(Self {
            s_g2,
            n_g2_prepared,
            s_g2_prepared,
        })
    }
}

impl<E: MultiMillerLoop + Debug> ParamsKZG<E> {
    /// Consume the prover parameters into verifier parameters. Need to specify
    /// the size of public inputs.
    pub fn verifier_params(&self) -> ParamsVerifierKZG<E> {
        let n_g2_prepared = E::G2Prepared::from((-self.g2).into());
        let s_g2_prepared = E::G2Prepared::from(self.s_g2.into());
        ParamsVerifierKZG {
            s_g2: self.s_g2,
            n_g2_prepared,
            s_g2_prepared,
        }
    }
}

#[cfg(test)]
mod test {
    use rand_core::OsRng;

    use crate::{
        poly::{
            PolynomialLabel,
            commitment::PolynomialCommitmentScheme,
            kzg::{KZGCommitmentScheme, params::ParamsKZG},
        },
        utils::SerdeFormat,
    };

    #[test]
    fn test_commit_lagrange() {
        const K: u32 = 6;

        use midnight_curves::{Bls12, Fq};

        use crate::poly::{EvaluationDomain, FftDomain};

        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);
        let domain = EvaluationDomain::new(1, K);

        let mut a = domain.empty_lagrange();

        for (i, a) in a.iter_mut().enumerate() {
            *a = Fq::from(i as u64);
        }

        let b = FftDomain::new(&domain).lagrange_to_coeff(a.clone());

        let tmp = KZGCommitmentScheme::commit(&params, &a, PolynomialLabel::NoLabel);
        let com = KZGCommitmentScheme::commit(&params, &b, PolynomialLabel::NoLabel);

        assert_eq!(tmp, com);
    }

    #[test]
    fn test_commit_in_delta_basis_matches_lagrange() {
        const K: u32 = 6;

        use ff::Field;
        use midnight_curves::{Bls12, Fq};

        use crate::poly::EvaluationDomain;

        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);
        let domain = EvaluationDomain::new(1, K);

        // A polynomial with long constant runs and a few isolated transitions —
        // exercises the structure the optimization is designed for.
        let mut a = domain.empty_lagrange();
        for (i, slot) in a.iter_mut().enumerate() {
            *slot = match i {
                0..16 => Fq::ZERO,
                16..40 => Fq::from(7),
                40..50 => Fq::from(7) + Fq::from(i as u64),
                _ => Fq::from(42),
            };
        }

        let c_lagrange = KZGCommitmentScheme::commit(&params, &a, PolynomialLabel::NoLabel);
        let c_delta = KZGCommitmentScheme::commit(&params, &a.to_delta(), PolynomialLabel::NoLabel);
        assert_eq!(c_lagrange, c_delta);

        // Round-trip identity: to_delta then into_lagrange recovers the original.
        let restored = a.to_delta().into_lagrange();
        assert_eq!(restored.values, a.values);
    }

    #[test]
    fn test_commit_in_double_delta_basis_matches_lagrange() {
        const K: u32 = 6;

        use midnight_curves::{Bls12, Fq};

        use crate::poly::EvaluationDomain;

        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);
        let domain = EvaluationDomain::new(1, K);

        // A polynomial with linear runs (constant first differences) and a
        // few transitions — exercises the structure the double-delta basis
        // is designed for: linear segments collapse to zeros after two
        // delta applications.
        let mut a = domain.empty_lagrange();
        for (i, slot) in a.iter_mut().enumerate() {
            *slot = match i {
                0..16 => Fq::from(i as u64),
                16..40 => Fq::from(16) + Fq::from(2u64) * Fq::from((i - 16) as u64),
                40..50 => Fq::from(99),
                _ => Fq::from(i as u64) - Fq::from(50),
            };
        }

        let c_lagrange = KZGCommitmentScheme::commit(&params, &a, PolynomialLabel::NoLabel);

        // Fused single-pass conversion matches the two-step path.
        let c_double_delta_fused =
            KZGCommitmentScheme::commit(&params, &a.to_double_delta(), PolynomialLabel::NoLabel);
        let c_double_delta_two_step = KZGCommitmentScheme::commit(
            &params,
            &a.to_delta().into_double_delta(),
            PolynomialLabel::NoLabel,
        );
        assert_eq!(c_lagrange, c_double_delta_fused);
        assert_eq!(c_lagrange, c_double_delta_two_step);

        // Both fused and two-step transforms produce the same scalar vector.
        let fused = a.to_double_delta();
        let two_step = a.to_delta().into_double_delta();
        assert_eq!(fused.values, two_step.values);

        // Round-trip identity, both inverse paths.
        let restored_fused = a.to_double_delta().into_lagrange();
        let restored_stepwise = a.to_double_delta().into_lagrange_delta().into_lagrange();
        assert_eq!(restored_fused.values, a.values);
        assert_eq!(restored_stepwise.values, a.values);
    }

    #[test]
    fn test_parameter_serialisation_roundtrip() {
        const K: u32 = 4;

        use midnight_curves::Bls12;

        let params0: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);
        let mut data = vec![];
        ParamsKZG::write(&params0, &mut data, SerdeFormat::RawBytesUnchecked).unwrap();
        let params1 =
            ParamsKZG::<Bls12>::read::<_>(&mut &data[..], SerdeFormat::RawBytesUnchecked).unwrap();

        assert_eq!(params0.g.len(), params1.g.len());
        assert_eq!(params0.g_lagrange.len(), params1.g_lagrange.len());

        assert_eq!(params0.g, params1.g);
        assert_eq!(params0.g_lagrange, params1.g_lagrange);
        assert_eq!(params0.g2, params1.g2);
        assert_eq!(params0.s_g2, params1.s_g2);
    }

    #[test]
    fn test_delta_bases_are_built_on_first_use() {
        const K: u32 = 6;

        use midnight_curves::{Bls12, Fq};

        use crate::poly::EvaluationDomain;

        let commit_in_all_bases = |params: &ParamsKZG<Bls12>, k: u32| {
            let mut a = EvaluationDomain::new(1, k).empty_lagrange();
            for (i, a) in a.iter_mut().enumerate() {
                *a = Fq::from((i * i) as u64);
            }
            let label = PolynomialLabel::NoLabel;
            let lagrange = KZGCommitmentScheme::commit(params, &a, label.clone());
            assert!(!params.has_delta_bases());
            let delta = KZGCommitmentScheme::commit(params, &a.to_delta(), label.clone());
            assert!(params.has_delta_bases());
            let double_delta = KZGCommitmentScheme::commit(params, &a.to_double_delta(), label);
            assert_eq!(lagrange, delta);
            assert_eq!(lagrange, double_delta);
        };

        // Neither the setup nor a commitment in the Lagrange basis builds the
        // delta bases: the first commitment in a delta basis does.
        let mut params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);
        assert!(!params.has_delta_bases());
        commit_in_all_bases(&params, K);

        // Downsizing drops them, and those of the smaller SRS are built next.
        params.downsize(K - 1);
        assert!(!params.has_delta_bases());
        commit_in_all_bases(&params, K - 1);

        // Downsizing to the same size keeps them.
        params.downsize(K - 1);
        assert!(params.has_delta_bases());

        // They can be built ahead of the first commitment.
        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);
        params.precompute_delta_bases();
        assert!(params.has_delta_bases());
    }

    #[test]
    fn test_delta_bases_serialisation_roundtrip() {
        use midnight_curves::Bls12;

        for k in [0, 1, 4] {
            let params0: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(k, OsRng);
            params0.precompute_delta_bases();
            let bases0 = params0.delta_bases.get().unwrap();

            for format in [
                SerdeFormat::Processed,
                SerdeFormat::RawBytes,
                SerdeFormat::RawBytesUnchecked,
            ] {
                // Reading the SRS does not build the delta bases.
                let mut srs = vec![];
                params0.write(&mut srs, format).unwrap();
                let mut params1 = ParamsKZG::<Bls12>::read(&mut &srs[..], format).unwrap();
                assert!(!params1.has_delta_bases());

                let mut data = vec![];
                params0.write_delta_bases(&mut data, format).unwrap();
                params1.read_delta_bases(&mut &data[..], format).unwrap();
                let bases1 = params1.delta_bases.get().unwrap();
                assert_eq!(bases0.delta, bases1.delta);
                assert_eq!(bases0.double_delta, bases1.double_delta);

                // Writing the delta bases builds them if they are missing.
                let params2 = ParamsKZG::<Bls12>::read(&mut &srs[..], format).unwrap();
                let mut data2 = vec![];
                params2.write_delta_bases(&mut data2, format).unwrap();
                assert!(params2.has_delta_bases());
                assert_eq!(data, data2);
            }
        }
    }

    #[test]
    fn test_read_delta_bases_rejects_other_parameters() {
        const K: u32 = 4;

        use std::io::ErrorKind::InvalidData;

        use midnight_curves::Bls12;

        let format = SerdeFormat::RawBytesUnchecked;
        let mut params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);

        // The delta bases of another SRS of the same size.
        let other: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);
        let mut other_srs = vec![];
        other.write_delta_bases(&mut other_srs, format).unwrap();

        // The delta bases of the same SRS, downsized.
        let mut smaller = params.clone();
        smaller.downsize(K - 1);
        let mut other_size = vec![];
        smaller.write_delta_bases(&mut other_size, format).unwrap();

        // The SRS itself, in place of its delta bases.
        let mut srs = vec![];
        params.write(&mut srs, format).unwrap();

        // The delta bases with one point of the first one replaced.
        let mut one_point_off = vec![];
        params.clone().write_delta_bases(&mut one_point_off, format).unwrap();
        let point_len = (one_point_off.len() - 4) / (2 << K);
        one_point_off.copy_within(4 + point_len..4 + 2 * point_len, 4);

        // They are all rejected, with the delta bases left as they were.
        let check_rejected = |params: &mut ParamsKZG<Bls12>| {
            let before = params.delta_bases.get().map(|bases| bases.delta.clone());
            for data in [&other_srs, &other_size, &srs, &one_point_off] {
                let err = params.read_delta_bases(&mut &data[..], format).unwrap_err();
                assert_eq!(err.kind(), InvalidData);
                let after = params.delta_bases.get().map(|bases| bases.delta.clone());
                assert_eq!(before, after);
            }
        };
        check_rejected(&mut params);
        assert!(!params.has_delta_bases());
        params.precompute_delta_bases();
        check_rejected(&mut params);
        assert!(params.has_delta_bases());
    }

    #[test]
    fn test_read_rejects_oversized_k() {
        use ff::PrimeField;
        use midnight_curves::{Bls12, Fq};

        let data = (Fq::S + 1).to_le_bytes();
        for format in [
            SerdeFormat::Processed,
            SerdeFormat::RawBytes,
            SerdeFormat::RawBytesUnchecked,
        ] {
            let err = ParamsKZG::<Bls12>::read::<_>(&mut &data[..], format).err().unwrap();
            assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
            assert!(err.to_string().contains("exceeds the maximum supported value"));
        }
    }
}
