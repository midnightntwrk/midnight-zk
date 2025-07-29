use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    field::{AssignedNative, NativeChip},
    hash::new_sha256::utils::{spread, u32_in_be_limbs},
    instructions::AssignmentInstructions,
};

/// Assigned plain value of given number of bits L.
#[derive(Clone, Debug)]
pub struct AssignedPlain<F: PrimeField, const L: usize>(pub AssignedNative<F>);

/// Assigned spreaded value of given number of bits L.
#[derive(Clone, Debug)]
pub(super) struct AssignedSpreaded<F: PrimeField, const L: usize>(pub AssignedNative<F>);

/// A pair of assigned plain-spreaded values guaranteed to be consistent.
/// The plain value is also guaranteed to be in the range [0, 2^L).
#[derive(Clone, Debug)]
pub(super) struct AssignedPlainSpreaded<F: PrimeField, const L: usize> {
    pub plain: AssignedPlain<F, L>,
    pub spreaded: AssignedSpreaded<F, L>,
}

/// The assigned spreaded values of 10-9-11-2 limbs (in big-endian) for the
/// register A of 32 bits. Input type of Σ₀(A).
#[derive(Clone, Debug)]
pub(super) struct LimbsOfA<F: PrimeField> {
    pub combined: AssignedPlainSpreaded<F, 32>,
    pub spreaded_limb_10: AssignedSpreaded<F, 10>,
    pub spreaded_limb_09: AssignedSpreaded<F, 9>,
    pub spreaded_limb_11: AssignedSpreaded<F, 11>,
    pub spreaded_limb_02: AssignedSpreaded<F, 2>,
}

/// The assigned spreaded values of 7-12-2-5-6 limbs (in big-endian) for the
/// register E of 32 bits. Input type of Σ₁(E).
#[derive(Clone, Debug)]
pub(super) struct LimbsOfE<F: PrimeField> {
    pub combined: AssignedPlainSpreaded<F, 32>,
    pub spreaded_limb_07: AssignedSpreaded<F, 7>,
    pub spreaded_limb_12: AssignedSpreaded<F, 12>,
    pub spreaded_limb_02: AssignedSpreaded<F, 2>,
    pub spreaded_limb_05: AssignedSpreaded<F, 5>,
    pub spreaded_limb_06: AssignedSpreaded<F, 6>,
}

#[derive(Clone, Debug)]
pub(super) struct CompressionState<F: PrimeField> {
    pub(super) a: LimbsOfA<F>,
    pub(super) b: AssignedPlainSpreaded<F, 32>,
    pub(super) c: AssignedPlainSpreaded<F, 32>,
    pub(super) d: AssignedPlain<F, 32>,
    pub(super) e: LimbsOfE<F>,
    pub(super) f: AssignedPlainSpreaded<F, 32>,
    pub(super) g: AssignedPlainSpreaded<F, 32>,
    pub(super) h: AssignedPlain<F, 32>,
}

impl<F: PrimeField, const N: usize> AssignedPlain<F, N> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        native_chip: &NativeChip<F>,
        c: u32,
    ) -> Result<Self, Error> {
        assert!(c < (1 << N));
        Ok(Self(native_chip.assign_fixed(layouter, F::from(c as u64))?))
    }
}

impl<F: PrimeField, const N: usize> AssignedSpreaded<F, N> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        native_chip: &NativeChip<F>,
        c: u32,
    ) -> Result<Self, Error> {
        assert!(c < (1 << N));
        Ok(Self(
            native_chip.assign_fixed(layouter, F::from(spread(c)))?,
        ))
    }
}

impl<F: PrimeField, const N: usize> AssignedPlainSpreaded<F, N> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        native_chip: &NativeChip<F>,
        c: u32,
    ) -> Result<Self, Error> {
        assert!(c < (1 << N));
        Ok(Self {
            plain: AssignedPlain::<F, N>::fixed(layouter, native_chip, c)?,
            spreaded: AssignedSpreaded::<F, N>::fixed(layouter, native_chip, c)?,
        })
    }
}

impl<F: PrimeField> LimbsOfA<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        native_chip: &NativeChip<F>,
        constant: u32,
    ) -> Result<Self, Error> {
        let [c10, c09, c11, c02] = u32_in_be_limbs(constant, [10, 9, 11, 2]);
        Ok(Self {
            combined: AssignedPlainSpreaded::<F, 32>::fixed(layouter, native_chip, constant)?,
            spreaded_limb_10: AssignedSpreaded::<F, 10>::fixed(layouter, native_chip, c10)?,
            spreaded_limb_09: AssignedSpreaded::<F, 9>::fixed(layouter, native_chip, c09)?,
            spreaded_limb_11: AssignedSpreaded::<F, 11>::fixed(layouter, native_chip, c11)?,
            spreaded_limb_02: AssignedSpreaded::<F, 2>::fixed(layouter, native_chip, c02)?,
        })
    }

    pub(super) fn plain(&self) -> AssignedPlain<F, 32> {
        self.combined.plain.clone()
    }
}

impl<F: PrimeField> LimbsOfE<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        native_chip: &NativeChip<F>,
        constant: u32,
    ) -> Result<Self, Error> {
        let [c07, c12, c02, c05, c06] = u32_in_be_limbs(constant, [7, 12, 2, 5, 6]);
        Ok(Self {
            combined: AssignedPlainSpreaded::<F, 32>::fixed(layouter, native_chip, constant)?,
            spreaded_limb_07: AssignedSpreaded::<F, 7>::fixed(layouter, native_chip, c07)?,
            spreaded_limb_12: AssignedSpreaded::<F, 12>::fixed(layouter, native_chip, c12)?,
            spreaded_limb_02: AssignedSpreaded::<F, 2>::fixed(layouter, native_chip, c02)?,
            spreaded_limb_05: AssignedSpreaded::<F, 5>::fixed(layouter, native_chip, c05)?,
            spreaded_limb_06: AssignedSpreaded::<F, 6>::fixed(layouter, native_chip, c06)?,
        })
    }

    pub(super) fn plain(&self) -> AssignedPlain<F, 32> {
        self.combined.plain.clone()
    }
}

impl<F: PrimeField> CompressionState<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        native_chip: &NativeChip<F>,
        v: &[u32; 8],
    ) -> Result<Self, Error> {
        Ok(Self {
            a: LimbsOfA::<F>::fixed(layouter, native_chip, v[0])?,
            b: AssignedPlainSpreaded::<F, 32>::fixed(layouter, native_chip, v[1])?,
            c: AssignedPlainSpreaded::<F, 32>::fixed(layouter, native_chip, v[2])?,
            d: AssignedPlain::<F, 32>::fixed(layouter, native_chip, v[3])?,
            e: LimbsOfE::<F>::fixed(layouter, native_chip, v[4])?,
            f: AssignedPlainSpreaded::<F, 32>::fixed(layouter, native_chip, v[5])?,
            g: AssignedPlainSpreaded::<F, 32>::fixed(layouter, native_chip, v[6])?,
            h: AssignedPlain::<F, 32>::fixed(layouter, native_chip, v[7])?,
        })
    }

    pub(super) fn plain(self) -> [AssignedPlain<F, 32>; 8] {
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
