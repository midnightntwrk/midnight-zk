use std::{cell::RefCell, rc::Rc};

use midnight_circuits::{
    ecc::curves::CircuitCurve,
    field::NativeChip,
    hash::poseidon::{constants::PoseidonField, PoseidonChip},
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{AssignedNative, InnerValue, Instantiable},
    verifier::SelfEmulation,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    transcript::Hashable,
};

use crate::light_fiat_shamir::LightPoseidonFS;

/// An assigned point of curve C. It is "fake" in the sense that it cannot be
/// operated with it, only assigned as public input or fixed.
/// It is represented by an opaque vector of scalars, derive from hashing
/// the point off-circuit. Since this hashing is done off-circuit, we require
/// that the point be public for the sake of soundness.
///
/// The field `public` indicates whether the point has already been constrained
/// as public input. All points of this type are required to eventually be
/// constrained as public (if they are not fixed).
/// We can make sure of this by calling the [FakeCurveChip::finalize] at the end
/// of the circuit `synthesize` function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakePoint<C: CircuitCurve> {
    pieces: Vec<AssignedNative<C::Scalar>>,
    public: Rc<RefCell<bool>>,
}

impl<C> Instantiable<C::Scalar> for FakePoint<C>
where
    C: CircuitCurve + Hashable<LightPoseidonFS<C::Scalar>>,
    C::Scalar: PoseidonField,
{
    fn as_public_input(p: &C) -> Vec<C::Scalar> {
        <C as Hashable<LightPoseidonFS<C::Scalar>>>::to_input(p)
    }
}

impl<C: CircuitCurve> InnerValue for FakePoint<C> {
    type Element = C;

    fn value(&self) -> Value<Self::Element> {
        unimplemented!("The value of a FakePoint cannot be recovered")
    }
}

/// A "fake" curve chip that can only be used for assigning points and declaring
/// them as public inputs.
///
/// All assigned points that are not assigned as fixed are stored in the
/// `public_points` field and must be eventually constrained as public inputs.
/// We can make sure of this by calling the [FakeCurveChip::finalize] at the
/// end of the circuit `synthesize` function.
///
/// We wrap the vector of points `Rc<RefCell<...>>` so that we can clone the
/// chip with the guarantee that all clones will reference the same points.
#[derive(Clone, Debug)]
pub struct FakeCurveChip<C: CircuitCurve> {
    scalar_chip: NativeChip<C::Scalar>,
    public_points: Rc<RefCell<Vec<FakePoint<C>>>>,
}

impl<C: CircuitCurve> FakeCurveChip<C> {
    /// Initializes a new `FakeCurveChip` from a native chip.
    pub fn new(scalar_chip: &NativeChip<C::Scalar>) -> Self {
        Self {
            scalar_chip: scalar_chip.clone(),
            public_points: Rc::new(RefCell::new(Vec::new())),
        }
    }

    /// Make sure all assigned points were eventually made public.
    /// It is very important to call this function at the very end of the
    /// circuit `synthesize`.
    pub fn finalize(&self) -> Result<(), Error> {
        // Let's panic instead of returning an error, which gives a more descriptive
        // message of this subtle issue.
        if self
            .public_points
            .borrow()
            .iter()
            .any(|p| !*p.public.borrow())
        {
            panic!("Not all assigned `FakePoint`s were made public")
        }
        Ok(())
    }
}

impl<C> AssignmentInstructions<C::Scalar, FakePoint<C>> for FakeCurveChip<C>
where
    C: CircuitCurve + Hashable<LightPoseidonFS<C::Scalar>>,
    C::Scalar: PoseidonField,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        value: Value<C>,
    ) -> Result<FakePoint<C>, Error> {
        // Figure out how many pieces a point needs, all points need the same  number of
        // pieces, so we can take an arbitrary off-circuit point here.
        let l = <C as Hashable<LightPoseidonFS<C::Scalar>>>::to_input(&C::generator()).len();
        let pieces_val = value
            .map(|p| <C as Hashable<LightPoseidonFS<C::Scalar>>>::to_input(&p))
            .transpose_vec(l);
        let assigned_point = FakePoint::<C> {
            pieces: self.scalar_chip.assign_many(layouter, &pieces_val)?,
            public: Rc::new(RefCell::new(false)),
        };

        self.public_points.borrow_mut().push(assigned_point.clone());

        Ok(assigned_point)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        constant: <FakePoint<C> as InnerValue>::Element,
    ) -> Result<FakePoint<C>, Error> {
        let pieces_val = <C as Hashable<LightPoseidonFS<C::Scalar>>>::to_input(&constant);
        let assigned_point = FakePoint::<C> {
            pieces: self.scalar_chip.assign_many_fixed(layouter, &pieces_val)?,
            public: Rc::new(RefCell::new(true)),
        };

        self.public_points.borrow_mut().push(assigned_point.clone());

        Ok(assigned_point)
    }
}

impl<C> PublicInputInstructions<C::Scalar, FakePoint<C>> for FakeCurveChip<C>
where
    C: CircuitCurve + Hashable<LightPoseidonFS<C::Scalar>>,
    C::Scalar: PoseidonField,
{
    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<C::Scalar>,
        point: &FakePoint<C>,
    ) -> Result<Vec<AssignedNative<C::Scalar>>, Error> {
        Ok(point.pieces.clone())
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        point: &FakePoint<C>,
    ) -> Result<(), Error> {
        *point.public.borrow_mut() = true;
        point
            .pieces
            .iter()
            .try_for_each(|x| self.scalar_chip.constrain_as_public_input(layouter, x))
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        value: Value<C>,
    ) -> Result<FakePoint<C>, Error> {
        let assigned_point = self.assign(layouter, value)?;
        self.constrain_as_public_input(layouter, &assigned_point)?;
        Ok(assigned_point)
    }
}

/// Implementation of a light version of the SelfEmulation trait for blstrs.
#[derive(Clone, Debug)]
pub struct LightBlstrsEmulation {}

impl SelfEmulation for LightBlstrsEmulation {
    type F = midnight_curves::Fq;
    type C = midnight_curves::G1Projective;
    type AssignedPoint = FakePoint<Self::C>;
    type Hash = LightPoseidonFS<Self::F>;

    type ScalarChip = NativeChip<Self::F>;
    type CurveChip = FakeCurveChip<Self::C>;
    type SpongeChip = PoseidonChip<Self::F>;

    type G1Affine = midnight_curves::G1Affine;
    type G2Affine = midnight_curves::G2Affine;
    type Engine = midnight_curves::Bls12;

    fn msm(
        _layouter: &mut impl Layouter<Self::F>,
        _curve_chip: &Self::CurveChip,
        _scalars: &[(AssignedNative<Self::F>, usize)],
        _bases: &[Self::AssignedPoint],
    ) -> Result<Self::AssignedPoint, Error> {
        unimplemented!("msm is not allowed with light blstrs emulation")
    }

    fn constrain_scalar_as_committed_public_input(
        layouter: &mut impl Layouter<Self::F>,
        scalar_chip: &Self::ScalarChip,
        assigned_scalar: &AssignedNative<Self::F>,
    ) -> Result<(), Error> {
        scalar_chip.constrain_as_committed_public_input(layouter, assigned_scalar)
    }
}
