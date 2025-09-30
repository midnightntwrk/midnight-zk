use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    field::AssignedNative,
    hash::sha512::utils::{spread, u64_in_be_limbs},
    instructions::FieldInstructions,
    utils::util::u128_to_fe,
};

/// An assigned value in plain (non-spreaded) form, guaranteed to be in the
/// range [0, 2^L).
#[derive(Clone, Debug)]
pub(super) struct AssignedPlain<F: PrimeField, const L: usize>(pub AssignedNative<F>);

/// An assigned value in spreaded form, it is guaranteed to be the spreaded form
/// of a value in the range [0, 2^L).
#[derive(Clone, Debug)]
pub(super) struct AssignedSpreaded<F: PrimeField, const L: usize>(pub AssignedNative<F>);

/// A pair of assigned plain-spreaded values guaranteed to be consistent.
/// The plain value is also guaranteed to be in the range [0, 2^L).
#[derive(Clone, Debug)]
pub(super) struct AssignedPlainSpreaded<F: PrimeField, const L: usize> {
    pub(super) plain: AssignedPlain<F, L>,
    pub(super) spreaded: AssignedSpreaded<F, L>,
}

/// The assigned spreaded values of 13-12-5-6-13-13-2 limbs (in big-endian) for
/// the register A of 64 bits. Input type of Σ₀(A).
/// The limb sizes are chosen to make the rotations required for Σ₀ efficient.
#[derive(Clone, Debug)]
pub(super) struct LimbsOfA<F: PrimeField> {
    pub(super) combined: AssignedPlainSpreaded<F, 64>,
    pub(super) spreaded_limb_13a: AssignedSpreaded<F, 13>,
    pub(super) spreaded_limb_12: AssignedSpreaded<F, 12>,
    pub(super) spreaded_limb_05: AssignedSpreaded<F, 5>,
    pub(super) spreaded_limb_06: AssignedSpreaded<F, 6>,
    pub(super) spreaded_limb_13b: AssignedSpreaded<F, 13>,
    pub(super) spreaded_limb_13c: AssignedSpreaded<F, 13>,
    pub(super) spreaded_limb_02: AssignedSpreaded<F, 2>,
}

/// The assigned spreaded values of 13-10-13-10-4-13-1 limbs (in big-endian) for
/// the register E of 64 bits. Input type of Σ₁(E).
/// The limb sizes are chosen to make the rotations required for Σ₁ efficient.
#[derive(Clone, Debug)]
pub(super) struct LimbsOfE<F: PrimeField> {
    pub(super) combined: AssignedPlainSpreaded<F, 64>,
    pub(super) spreaded_limb_13a: AssignedSpreaded<F, 13>,
    pub(super) spreaded_limb_10a: AssignedSpreaded<F, 10>,
    pub(super) spreaded_limb_13b: AssignedSpreaded<F, 13>,
    pub(super) spreaded_limb_10b: AssignedSpreaded<F, 10>,
    pub(super) spreaded_limb_04: AssignedSpreaded<F, 4>,
    pub(super) spreaded_limb_13c: AssignedSpreaded<F, 13>,
    pub(super) spreaded_limb_01: AssignedSpreaded<F, 1>,
}

/// The assigned values of 3-13-13-13-3-11-1-1-5-1 limbs (in big-endian) for the
/// word W of 64 bits. Input type of σ₀(W) and σ₁(W).
/// The limb sizes are chosen to make the rotations required for σ₀ and σ₁
/// efficient.
#[derive(Clone, Debug)]
pub(super) struct AssignedMessageWord<F: PrimeField> {
    pub(super) combined_plain: AssignedPlain<F, 64>,
    pub(super) spreaded_w_03a: AssignedSpreaded<F, 3>,
    pub(super) spreaded_w_13a: AssignedSpreaded<F, 13>,
    pub(super) spreaded_w_13b: AssignedSpreaded<F, 13>,
    pub(super) spreaded_w_13c: AssignedSpreaded<F, 13>,
    pub(super) spreaded_w_03b: AssignedSpreaded<F, 3>,
    pub(super) spreaded_w_11: AssignedSpreaded<F, 11>,
    pub(super) spreaded_w_01a: AssignedSpreaded<F, 1>,
    pub(super) spreaded_w_01b: AssignedSpreaded<F, 1>,
    pub(super) spreaded_w_05: AssignedSpreaded<F, 5>,
    pub(super) spreaded_w_01c: AssignedSpreaded<F, 1>,
}

/// The assigned values of the state vector (A, B, C, D, E, F, G, H).
/// They are provided and updated in each compression round.
#[derive(Clone, Debug)]
pub(super) struct CompressionState<F: PrimeField> {
    pub(super) a: LimbsOfA<F>,
    pub(super) b: AssignedPlainSpreaded<F, 64>,
    pub(super) c: AssignedPlainSpreaded<F, 64>,
    pub(super) d: AssignedPlain<F, 64>,
    pub(super) e: LimbsOfE<F>,
    pub(super) f: AssignedPlainSpreaded<F, 64>,
    pub(super) g: AssignedPlainSpreaded<F, 64>,
    pub(super) h: AssignedPlain<F, 64>,
}

impl<F: PrimeField, const N: usize> AssignedPlain<F, N> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        c: u64,
    ) -> Result<Self, Error> {
        assert!((c as u128) < (1 << N));
        Ok(Self(field_chip.assign_fixed(layouter, F::from(c))?))
    }
}

impl<F: PrimeField, const N: usize> AssignedSpreaded<F, N> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        c: u64,
    ) -> Result<Self, Error> {
        assert!((c as u128) < (1 << N));
        Ok(Self(
            field_chip.assign_fixed(layouter, u128_to_fe(spread(c)))?,
        ))
    }
}

impl<F: PrimeField, const N: usize> AssignedPlainSpreaded<F, N> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        c: u64,
    ) -> Result<Self, Error> {
        Ok(Self {
            plain: AssignedPlain::<F, N>::fixed(layouter, field_chip, c)?,
            spreaded: AssignedSpreaded::<F, N>::fixed(layouter, field_chip, c)?,
        })
    }
}

impl<F: PrimeField> LimbsOfA<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        constant: u64,
    ) -> Result<Self, Error> {
        let [c13a, c12, c05, c06, c13b, c13c, c02] =
            u64_in_be_limbs(constant, [13, 12, 5, 6, 13, 13, 2]);
        Ok(Self {
            combined: AssignedPlainSpreaded::<F, 64>::fixed(layouter, field_chip, constant)?,
            spreaded_limb_13a: AssignedSpreaded::<F, 13>::fixed(layouter, field_chip, c13a)?,
            spreaded_limb_12: AssignedSpreaded::<F, 12>::fixed(layouter, field_chip, c12)?,
            spreaded_limb_05: AssignedSpreaded::<F, 5>::fixed(layouter, field_chip, c05)?,
            spreaded_limb_06: AssignedSpreaded::<F, 6>::fixed(layouter, field_chip, c06)?,
            spreaded_limb_13b: AssignedSpreaded::<F, 13>::fixed(layouter, field_chip, c13b)?,
            spreaded_limb_13c: AssignedSpreaded::<F, 13>::fixed(layouter, field_chip, c13c)?,
            spreaded_limb_02: AssignedSpreaded::<F, 2>::fixed(layouter, field_chip, c02)?,
        })
    }

    pub(super) fn plain(&self) -> AssignedPlain<F, 64> {
        self.combined.plain.clone()
    }
}

impl<F: PrimeField> LimbsOfE<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        constant: u64,
    ) -> Result<Self, Error> {
        let [c13a, c10a, c13b, c10b, c04, c13c, c01] =
            u64_in_be_limbs(constant, [13, 10, 13, 10, 4, 13, 1]);
        Ok(Self {
            combined: AssignedPlainSpreaded::<F, 64>::fixed(layouter, field_chip, constant)?,
            spreaded_limb_13a: AssignedSpreaded::<F, 13>::fixed(layouter, field_chip, c13a)?,
            spreaded_limb_10a: AssignedSpreaded::<F, 10>::fixed(layouter, field_chip, c10a)?,
            spreaded_limb_13b: AssignedSpreaded::<F, 13>::fixed(layouter, field_chip, c13b)?,
            spreaded_limb_10b: AssignedSpreaded::<F, 10>::fixed(layouter, field_chip, c10b)?,
            spreaded_limb_04: AssignedSpreaded::<F, 4>::fixed(layouter, field_chip, c04)?,
            spreaded_limb_13c: AssignedSpreaded::<F, 13>::fixed(layouter, field_chip, c13c)?,
            spreaded_limb_01: AssignedSpreaded::<F, 1>::fixed(layouter, field_chip, c01)?,
        })
    }

    pub(super) fn plain(&self) -> AssignedPlain<F, 64> {
        self.combined.plain.clone()
    }
}

impl<F: PrimeField> CompressionState<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        [a, b, c, d, e, f, g, h]: [u64; 8],
    ) -> Result<Self, Error> {
        Ok(Self {
            a: LimbsOfA::<F>::fixed(layouter, field_chip, a)?,
            b: AssignedPlainSpreaded::<F, 64>::fixed(layouter, field_chip, b)?,
            c: AssignedPlainSpreaded::<F, 64>::fixed(layouter, field_chip, c)?,
            d: AssignedPlain::<F, 64>::fixed(layouter, field_chip, d)?,
            e: LimbsOfE::<F>::fixed(layouter, field_chip, e)?,
            f: AssignedPlainSpreaded::<F, 64>::fixed(layouter, field_chip, f)?,
            g: AssignedPlainSpreaded::<F, 64>::fixed(layouter, field_chip, g)?,
            h: AssignedPlain::<F, 64>::fixed(layouter, field_chip, h)?,
        })
    }

    pub(super) fn plain(self) -> [AssignedPlain<F, 64>; 8] {
        [
            self.a.combined.plain,
            self.b.plain,
            self.c.plain,
            self.d,
            self.e.combined.plain,
            self.f.plain,
            self.g.plain,
            self.h,
        ]
    }
}
