//! Module that contains type and generic bounds.
//! Its purpose is to minimize complexity in the rest of the verifier chip.

use blstrs;
use ff::{PrimeField, WithSmallOrderMulGroup};
use group::{prime::PrimeCurveAffine, Curve, Group};
use halo2curves::{
    pairing::{Engine, MultiMillerLoop},
    serde::SerdeObject,
    CurveExt,
};
use midnight_proofs::transcript::Hashable;
use pasta_curves::arithmetic::CurveAffine;

use crate::{
    ecc::{
        curves::{CircuitCurve, WeierstrassCurve},
        foreign::{AssignedForeignPoint, ForeignEccChip},
    },
    field::{
        decomposition::chip::P2RDecompositionChip, foreign::params::FieldEmulationParams,
        NativeChip, NativeGadget,
    },
    hash::poseidon::{constants::PoseidonField, PoseidonChip, PoseidonState},
    instructions::SpongeInstructions,
    types::AssignedNative,
};

/// A curve amenable for self emulation.
/// It must have a pairing and implement its own emulation parameters.
pub trait SelfEmulationCurve:
    WeierstrassCurve<CryptographicGroup = Self, Base = <Self as CurveExt>::Base>
    + FieldEmulationParams<Self::ScalarField, <Self as CircuitCurve>::Base>
    + CurveExt<ScalarExt = Self::ScalarField, AffineExt = Self::G1Affine>
    + Group<Scalar = <Self as CurveExt>::ScalarExt>
    + From<<Self as CurveExt>::AffineExt>
    + Hashable<PoseidonState<Self::ScalarField>>
{
    /// The Scalar field of the underlying curve.
    /// This is the SNARK native field.
    type ScalarField: PrimeField
        + WithSmallOrderMulGroup<3>
        + PoseidonField
        + Hashable<PoseidonState<Self::ScalarField>>
        + SerdeObject;

    /// The first source group (type of KZG commitments).
    type G1Affine: CurveAffine<
            ScalarExt = Self::ScalarField,
            CurveExt = Self,
            Base = <Self as CircuitCurve>::Base,
        > + Into<Self>
        + From<Self>
        + SerdeObject
        + Hashable<PoseidonState<Self::ScalarField>>;

    /// The second source group.
    type G2Affine: SerdeObject + PrimeCurveAffine + From<<Self::Engine as Engine>::G2>;

    /// Wrapper type for the pairing engine.
    type Engine: Engine
        + MultiMillerLoop<
            Fr = Self::ScalarField,
            G1 = Self,
            G1Affine = <Self as Curve>::AffineRepr,
            G2Affine = Self::G2Affine,
        >;
}

/// Alias on the self-emulated ECC chip, parametrized by a [SelfEmulationCurve].
pub type CurveChip<C> =
    ForeignEccChip<<C as SelfEmulationCurve>::ScalarField, C, C, ScalarChip<C>, ScalarChip<C>>;

/// Alias on the self-emulation scalar field chip, parametrized by a
/// [SelfEmulationCurve].
pub type ScalarChip<C> = NativeGadget<
    <C as SelfEmulationCurve>::ScalarField,
    P2RDecompositionChip<<C as SelfEmulationCurve>::ScalarField>,
    NativeChip<<C as SelfEmulationCurve>::ScalarField>,
>;

/// Alias on the self-emulation base field chip, parametrized by a
/// [SelfEmulationCurve].
#[cfg(any(test, feature = "testing"))]
pub type BaseChip<C> = crate::field::foreign::FieldChip<
    <C as SelfEmulationCurve>::ScalarField,
    <C as CircuitCurve>::Base,
    C,
    ScalarChip<C>,
>;

/// Alias on an assigned native scalar, parametrized by a [SelfEmulationCurve].
pub type AssignedScalar<C> = AssignedNative<<C as SelfEmulationCurve>::ScalarField>;

/// Alias on an assigned self-emulated point, parametrized by a
/// [SelfEmulationCurve].
pub type AssignedPoint<C> = AssignedForeignPoint<<C as SelfEmulationCurve>::ScalarField, C, C>;

/// Alias on the Poseidon chip, native over the [SelfEmulationCurve].
pub type SpongeChip<C> = PoseidonChip<<C as SelfEmulationCurve>::ScalarField>;

/// Alias on the Poseidon state, native over the [SelfEmulationCurve].
pub type SpongeState<C> = <SpongeChip<C> as SpongeInstructions<
    <C as SelfEmulationCurve>::ScalarField,
    AssignedScalar<C>,
    AssignedScalar<C>,
>>::State;

// Implementations

impl SelfEmulationCurve for blstrs::G1Projective {
    type ScalarField = blstrs::Fq;
    type G1Affine = blstrs::G1Affine;
    type G2Affine = blstrs::G2Affine;
    type Engine = blstrs::Bls12;
}
