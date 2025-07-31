//! Contains utilities for performing arithmetic over univariate polynomials in
//! various forms, including computing commitments to them and provably opening
//! the committed polynomials at arbitrary points.

use std::{
    fmt::Debug,
    io,
    marker::PhantomData,
    ops::{
        Add, AddAssign, Deref, DerefMut, Index, IndexMut, Mul, MulAssign, RangeFrom, RangeFull, Sub,
    },
};

use ff::{BatchInvert, PrimeField, WithSmallOrderMulGroup};
use group::ff::Field;
use halo2curves::serde::SerdeObject;

use crate::utils::{arithmetic::parallelize, SerdeFormat};

mod domain;
mod query;

/// KZG commitment scheme
pub mod kzg;

pub mod commitment;

pub use domain::*;
pub use query::{ProverQuery, VerifierQuery};

use crate::utils::{helpers::read_f, rational::Rational};

/// This is an error that could occur during proving or circuit synthesis.
// TODO: these errors need to be cleaned up
#[derive(Debug)]
pub enum Error {
    /// OpeningProof is not well-formed
    OpeningError,
    /// Caller needs to re-sample a point
    SamplingError,
    /// Multiopen argument only supports a single query to the same (commitment,
    /// opening) pair.
    DuplicatedQuery,
}

/// The representation with which a polynomial is encoded.
pub trait PolynomialRepresentation: Copy + Debug + Send + Sync {
    /// Computes the number of field elements needed to encode a polynomial
    /// in this representation for a given evaluation domain.
    fn len<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> usize;

    /// Constructs an empty (zero) polynomial in this representation,
    /// appropriate for the given domain.
    fn empty<F: WithSmallOrderMulGroup<3>>(
        evaluation_domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, Self> {
        Polynomial {
            values: vec![F::ZERO; Self::len(evaluation_domain)],
            _marker: Default::default(),
        }
    }

    /// Returns the generator `ω` associated with the evaluation domain.
    fn omega<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> F;

    /// Returns the logarithmic size parameter `k` of the evaluation domain,
    /// where the domain size is `2^k`.
    fn k<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> u32;

    /// Converts a polynomial from coefficient form into this representation
    /// over the given evaluation domain.
    fn coeff_to_self<F: WithSmallOrderMulGroup<3>>(
        evaluation_domain: &EvaluationDomain<F>,
        poly: Polynomial<F, Coeff>,
    ) -> Polynomial<F, Self>;

    /// Returns the multiplicative coset generator `g_coset` if this
    /// representation uses an extended domain.
    fn g_coset<F: WithSmallOrderMulGroup<3>>(_evaluation_domain: &EvaluationDomain<F>) -> F;
}

/// The polynomial is defined as coefficients
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Coeff;
impl PolynomialRepresentation for Coeff {
    fn len<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> usize {
        evaluation_domain.n as usize
    }

    fn omega<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> F {
        evaluation_domain.get_omega()
    }

    fn k<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> u32 {
        evaluation_domain.k()
    }

    fn coeff_to_self<F: WithSmallOrderMulGroup<3>>(
        _evaluation_domain: &EvaluationDomain<F>,
        poly: Polynomial<F, Coeff>,
    ) -> Polynomial<F, Self> {
        poly
    }

    fn g_coset<F: WithSmallOrderMulGroup<3>>(_evaluation_domain: &EvaluationDomain<F>) -> F {
        F::ONE
    }
}

/// The polynomial is defined as coefficients of Lagrange basis polynomials
#[derive(Clone, Copy, Debug)]
pub struct LagrangeCoeff;
impl PolynomialRepresentation for LagrangeCoeff {
    fn len<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> usize {
        evaluation_domain.n as usize
    }

    fn omega<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> F {
        evaluation_domain.get_omega()
    }

    fn k<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> u32 {
        evaluation_domain.k()
    }

    fn coeff_to_self<F: WithSmallOrderMulGroup<3>>(
        evaluation_domain: &EvaluationDomain<F>,
        poly: Polynomial<F, Coeff>,
    ) -> Polynomial<F, Self> {
        evaluation_domain.coeff_to_lagrange(poly)
    }

    fn g_coset<F: WithSmallOrderMulGroup<3>>(_evaluation_domain: &EvaluationDomain<F>) -> F {
        F::ONE
    }
}

/// The polynomial is defined as coefficients of Lagrange basis polynomials in
/// an extended size domain which supports multiplication
#[derive(Clone, Copy, Debug)]
pub struct ExtendedLagrangeCoeff;
impl PolynomialRepresentation for ExtendedLagrangeCoeff {
    fn len<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> usize {
        evaluation_domain.extended_len()
    }

    fn omega<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> F {
        evaluation_domain.get_extended_omega()
    }

    fn k<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> u32 {
        evaluation_domain.extended_k()
    }

    fn coeff_to_self<F: WithSmallOrderMulGroup<3>>(
        evaluation_domain: &EvaluationDomain<F>,
        poly: Polynomial<F, Coeff>,
    ) -> Polynomial<F, Self> {
        evaluation_domain.coeff_to_extended(poly)
    }

    fn g_coset<F: WithSmallOrderMulGroup<3>>(evaluation_domain: &EvaluationDomain<F>) -> F {
        evaluation_domain.g_coset
    }
}

/// Represents a univariate polynomial defined over a field and a particular
/// representation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Polynomial<F, B> {
    pub(crate) values: Vec<F>,
    pub(crate) _marker: PhantomData<B>,
}

impl<F: PrimeField, B> Polynomial<F, B> {
    /// Creates a zero polynomial of the given size.
    pub fn init(num_coeffs: usize) -> Self {
        Polynomial {
            values: vec![F::ZERO; num_coeffs],
            _marker: PhantomData,
        }
    }
}

impl<F, B> Index<usize> for Polynomial<F, B> {
    type Output = F;

    fn index(&self, index: usize) -> &F {
        self.values.index(index)
    }
}

impl<F, B> IndexMut<usize> for Polynomial<F, B> {
    fn index_mut(&mut self, index: usize) -> &mut F {
        self.values.index_mut(index)
    }
}

impl<F, B> Index<RangeFrom<usize>> for Polynomial<F, B> {
    type Output = [F];

    fn index(&self, index: RangeFrom<usize>) -> &[F] {
        self.values.index(index)
    }
}

impl<F, B> IndexMut<RangeFrom<usize>> for Polynomial<F, B> {
    fn index_mut(&mut self, index: RangeFrom<usize>) -> &mut [F] {
        self.values.index_mut(index)
    }
}

impl<F, B> Index<RangeFull> for Polynomial<F, B> {
    type Output = [F];

    fn index(&self, index: RangeFull) -> &[F] {
        self.values.index(index)
    }
}

impl<F, B> IndexMut<RangeFull> for Polynomial<F, B> {
    fn index_mut(&mut self, index: RangeFull) -> &mut [F] {
        self.values.index_mut(index)
    }
}

impl<F, B> Deref for Polynomial<F, B> {
    type Target = [F];

    fn deref(&self) -> &[F] {
        &self.values[..]
    }
}

impl<F, B> DerefMut for Polynomial<F, B> {
    fn deref_mut(&mut self) -> &mut [F] {
        &mut self.values[..]
    }
}

impl<F, B> Polynomial<F, B> {
    /// Iterate over the values, which are either in coefficient or evaluation
    /// form depending on the representation `B`.
    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.values.iter()
    }

    /// Iterate over the values mutably, which are either in coefficient or
    /// evaluation form depending on the representation `B`.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut F> {
        self.values.iter_mut()
    }

    /// Gets the size of this polynomial in terms of the number of
    /// coefficients used to describe it.
    pub fn num_coeffs(&self) -> usize {
        self.values.len()
    }
}

impl<F: PrimeField + SerdeObject, B> Polynomial<F, B> {
    /// Reads polynomial from buffer using `SerdePrimeField::read`.
    pub(crate) fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let mut poly_len = [0u8; 4];
        reader.read_exact(&mut poly_len)?;
        let poly_len = u32::from_be_bytes(poly_len);

        (0..poly_len)
            .map(|_| read_f(reader, format))
            .collect::<io::Result<Vec<_>>>()
            .map(|values| Self {
                values,
                _marker: PhantomData,
            })
    }

    /// Writes polynomial to buffer using `SerdePrimeField::write`.
    pub(crate) fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&(self.values.len() as u32).to_be_bytes())?;
        for value in self.values.iter() {
            value.write_raw(writer)?;
        }
        Ok(())
    }
}

pub(crate) fn batch_invert_rational<F: Field>(
    assigned: Vec<Polynomial<Rational<F>, LagrangeCoeff>>,
) -> Vec<Polynomial<F, LagrangeCoeff>> {
    let mut assigned_denominators: Vec<_> = assigned
        .iter()
        .map(|f| {
            f.iter()
                .map(|value| value.denominator())
                .collect::<Vec<_>>()
        })
        .collect();

    assigned_denominators
        .iter_mut()
        .flat_map(|f| {
            f.iter_mut()
                // If the denominator is trivial, we can skip it, reducing the
                // size of the batch inversion.
                .filter_map(|d| d.as_mut())
        })
        .batch_invert();

    assigned
        .iter()
        .zip(assigned_denominators)
        .map(|(poly, inv_denoms)| poly.invert(inv_denoms.into_iter().map(|d| d.unwrap_or(F::ONE))))
        .collect()
}

impl<F: Field> Polynomial<Rational<F>, LagrangeCoeff> {
    pub(crate) fn invert(
        &self,
        inv_denoms: impl ExactSizeIterator<Item = F>,
    ) -> Polynomial<F, LagrangeCoeff> {
        assert_eq!(inv_denoms.len(), self.values.len());
        Polynomial {
            values: self
                .values
                .iter()
                .zip(inv_denoms)
                .map(|(a, inv_den)| a.numerator() * inv_den)
                .collect(),
            _marker: self._marker,
        }
    }
}

impl<'a, F: Field, B: PolynomialRepresentation> Add<&'a Polynomial<F, B>> for Polynomial<F, B> {
    type Output = Polynomial<F, B>;

    fn add(mut self, rhs: &'a Polynomial<F, B>) -> Polynomial<F, B> {
        self.add_assign(rhs);
        self
    }
}

impl<'a, F: Field, B: PolynomialRepresentation> AddAssign<&'a Polynomial<F, B>>
    for Polynomial<F, B>
{
    fn add_assign(&mut self, rhs: &'a Polynomial<F, B>) {
        parallelize(&mut self.values, |lhs, start| {
            for (lhs, rhs) in lhs.iter_mut().zip(rhs.values[start..].iter()) {
                *lhs += *rhs;
            }
        });
    }
}

impl<F: Field, B: PolynomialRepresentation> Add<Polynomial<F, B>> for Polynomial<F, B> {
    type Output = Polynomial<F, B>;

    fn add(mut self, rhs: Polynomial<F, B>) -> Polynomial<F, B> {
        parallelize(&mut self.values, |lhs, start| {
            for (lhs, rhs) in lhs.iter_mut().zip(rhs.values[start..].iter()) {
                *lhs += *rhs;
            }
        });

        self
    }
}

impl<'a, F: Field, B: PolynomialRepresentation> Sub<&'a Polynomial<F, B>> for Polynomial<F, B> {
    type Output = Polynomial<F, B>;

    fn sub(mut self, rhs: &'a Polynomial<F, B>) -> Polynomial<F, B> {
        parallelize(&mut self.values, |lhs, start| {
            for (lhs, rhs) in lhs.iter_mut().zip(rhs.values[start..].iter()) {
                *lhs -= *rhs;
            }
        });

        self
    }
}

impl<F: Field> Polynomial<F, LagrangeCoeff> {
    /// Rotates the values in a `LagrangeCoeff` polynomial by `Rotation`
    pub fn rotate(&self, rotation: Rotation) -> Polynomial<F, LagrangeCoeff> {
        let mut values = self.values.clone();
        if rotation.0 < 0 {
            values.rotate_right((-rotation.0) as usize);
        } else {
            values.rotate_left(rotation.0 as usize);
        }
        Polynomial {
            values,
            _marker: PhantomData,
        }
    }
}

impl<F: Field, B: PolynomialRepresentation> Mul<F> for Polynomial<F, B> {
    type Output = Polynomial<F, B>;

    fn mul(mut self, rhs: F) -> Polynomial<F, B> {
        self.mul_assign(rhs);
        self
    }
}

impl<F: Field, B: PolynomialRepresentation> MulAssign<F> for Polynomial<F, B> {
    fn mul_assign(&mut self, rhs: F) {
        if rhs == F::ZERO {
            parallelize(&mut self.values, |lhs, _| {
                for lhs in lhs.iter_mut() {
                    *lhs = F::ZERO;
                }
            });
        } else if rhs != F::ONE {
            parallelize(&mut self.values, |lhs, _| {
                for lhs in lhs.iter_mut() {
                    *lhs *= rhs;
                }
            });
        }
    }
}

impl<F: Field, B: PolynomialRepresentation> Sub<F> for &Polynomial<F, B> {
    type Output = Polynomial<F, B>;

    fn sub(self, rhs: F) -> Polynomial<F, B> {
        let mut res = self.clone();
        res.values[0] -= rhs;
        res
    }
}

/// Describes the relative rotation of a vector. Negative numbers represent
/// reverse (leftmost) rotations and positive numbers represent forward
/// (rightmost) rotations. Zero represents no rotation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Rotation(pub i32);

impl Rotation {
    /// The current location in the evaluation domain
    pub fn cur() -> Rotation {
        Rotation(0)
    }

    /// The previous location in the evaluation domain
    pub fn prev() -> Rotation {
        Rotation(-1)
    }

    /// The next location in the evaluation domain
    pub fn next() -> Rotation {
        Rotation(1)
    }
}
