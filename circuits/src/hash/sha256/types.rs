use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    field::AssignedNative,
    hash::sha256::utils::{spread, u32_in_be_limbs},
    instructions::{ControlFlowInstructions, FieldInstructions},
    types::AssignedBit,
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

/// The assigned spreaded values of 10-9-11-2 limbs (in big-endian) for the
/// register A of 32 bits. Input type of Σ₀(A).
/// The limb sizes are chosen to make the rotations required for Σ₀ efficient.
#[derive(Clone, Debug)]
pub(super) struct LimbsOfA<F: PrimeField> {
    pub(super) combined: AssignedPlainSpreaded<F, 32>,
    pub(super) spreaded_limb_10: AssignedSpreaded<F, 10>,
    pub(super) spreaded_limb_09: AssignedSpreaded<F, 9>,
    pub(super) spreaded_limb_11: AssignedSpreaded<F, 11>,
    pub(super) spreaded_limb_02: AssignedSpreaded<F, 2>,
}

/// The assigned spreaded values of 7-12-2-5-6 limbs (in big-endian) for the
/// register E of 32 bits. Input type of Σ₁(E).
/// The limb sizes are chosen to make the rotations required for Σ₁ efficient.
#[derive(Clone, Debug)]
pub(super) struct LimbsOfE<F: PrimeField> {
    pub(super) combined: AssignedPlainSpreaded<F, 32>,
    pub(super) spreaded_limb_07: AssignedSpreaded<F, 7>,
    pub(super) spreaded_limb_12: AssignedSpreaded<F, 12>,
    pub(super) spreaded_limb_02: AssignedSpreaded<F, 2>,
    pub(super) spreaded_limb_05: AssignedSpreaded<F, 5>,
    pub(super) spreaded_limb_06: AssignedSpreaded<F, 6>,
}

/// The assigned values of 12-1x3-7-3-4-3 limbs (in big-endian) for the
/// word W of 32 bits. Input type of σ₀(W) and σ₁(W).
/// The limb sizes are chosen to make the rotations required for σ₀ and σ₁
/// efficient.
#[derive(Clone, Debug)]
pub(super) struct AssignedMessageWord<F: PrimeField> {
    pub(super) combined_plain: AssignedPlain<F, 32>,
    pub(super) spreaded_w_12: AssignedSpreaded<F, 12>,
    pub(super) spreaded_w_1a: AssignedSpreaded<F, 1>,
    pub(super) spreaded_w_1b: AssignedSpreaded<F, 1>,
    pub(super) spreaded_w_1c: AssignedSpreaded<F, 1>,
    pub(super) spreaded_w_07: AssignedSpreaded<F, 7>,
    pub(super) spreaded_w_3a: AssignedSpreaded<F, 3>,
    pub(super) spreaded_w_04: AssignedSpreaded<F, 4>,
    pub(super) spreaded_w_3b: AssignedSpreaded<F, 3>,
}

/// The assigned values of the state vector (A, B, C, D, E, F, G, H).
/// They are provided and updated in each compression round.
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
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        c: u32,
    ) -> Result<Self, Error> {
        assert!((c as u64) < (1 << N));
        Ok(Self(field_chip.assign_fixed(layouter, F::from(c as u64))?))
    }
}

impl<F: PrimeField, const N: usize> AssignedSpreaded<F, N> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        c: u32,
    ) -> Result<Self, Error> {
        assert!((c as u64) < (1 << N));
        Ok(Self(field_chip.assign_fixed(layouter, F::from(spread(c)))?))
    }
}

impl<F: PrimeField, const N: usize> AssignedPlainSpreaded<F, N> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        c: u32,
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
        constant: u32,
    ) -> Result<Self, Error> {
        let [c10, c09, c11, c02] = u32_in_be_limbs(constant, [10, 9, 11, 2]);
        Ok(Self {
            combined: AssignedPlainSpreaded::<F, 32>::fixed(layouter, field_chip, constant)?,
            spreaded_limb_10: AssignedSpreaded::<F, 10>::fixed(layouter, field_chip, c10)?,
            spreaded_limb_09: AssignedSpreaded::<F, 9>::fixed(layouter, field_chip, c09)?,
            spreaded_limb_11: AssignedSpreaded::<F, 11>::fixed(layouter, field_chip, c11)?,
            spreaded_limb_02: AssignedSpreaded::<F, 2>::fixed(layouter, field_chip, c02)?,
        })
    }

    pub(super) fn plain(&self) -> AssignedPlain<F, 32> {
        self.combined.plain.clone()
    }
}

impl<F: PrimeField> LimbsOfE<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        constant: u32,
    ) -> Result<Self, Error> {
        let [c07, c12, c02, c05, c06] = u32_in_be_limbs(constant, [7, 12, 2, 5, 6]);
        Ok(Self {
            combined: AssignedPlainSpreaded::<F, 32>::fixed(layouter, field_chip, constant)?,
            spreaded_limb_07: AssignedSpreaded::<F, 7>::fixed(layouter, field_chip, c07)?,
            spreaded_limb_12: AssignedSpreaded::<F, 12>::fixed(layouter, field_chip, c12)?,
            spreaded_limb_02: AssignedSpreaded::<F, 2>::fixed(layouter, field_chip, c02)?,
            spreaded_limb_05: AssignedSpreaded::<F, 5>::fixed(layouter, field_chip, c05)?,
            spreaded_limb_06: AssignedSpreaded::<F, 6>::fixed(layouter, field_chip, c06)?,
        })
    }

    pub(super) fn plain(&self) -> AssignedPlain<F, 32> {
        self.combined.plain.clone()
    }
}

impl<F: PrimeField> CompressionState<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        [a, b, c, d, e, f, g, h]: [u32; 8],
    ) -> Result<Self, Error> {
        Ok(Self {
            a: LimbsOfA::<F>::fixed(layouter, field_chip, a)?,
            b: AssignedPlainSpreaded::<F, 32>::fixed(layouter, field_chip, b)?,
            c: AssignedPlainSpreaded::<F, 32>::fixed(layouter, field_chip, c)?,
            d: AssignedPlain::<F, 32>::fixed(layouter, field_chip, d)?,
            e: LimbsOfE::<F>::fixed(layouter, field_chip, e)?,
            f: AssignedPlainSpreaded::<F, 32>::fixed(layouter, field_chip, f)?,
            g: AssignedPlainSpreaded::<F, 32>::fixed(layouter, field_chip, g)?,
            h: AssignedPlain::<F, 32>::fixed(layouter, field_chip, h)?,
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

impl<F: PrimeField, const N: usize> AssignedPlain<F, N> {
    pub(super) fn select(
        layouter: &mut impl Layouter<F>,
        cf_chip: &impl ControlFlowInstructions<F, AssignedNative<F>>,
        bit: &AssignedBit<F>,
        x: &Self,
        y: &Self,
    ) -> Result<Self, Error> {
        Ok(Self(cf_chip.select(layouter, bit, &x.0, &y.0)?))
    }
}

impl<F: PrimeField, const N: usize> AssignedSpreaded<F, N> {
    pub(super) fn select(
        layouter: &mut impl Layouter<F>,
        cf_chip: &impl ControlFlowInstructions<F, AssignedNative<F>>,
        bit: &AssignedBit<F>,
        x: &Self,
        y: &Self,
    ) -> Result<Self, Error> {
        Ok(Self(cf_chip.select(layouter, bit, &x.0, &y.0)?))
    }
}

impl<F: PrimeField, const N: usize> AssignedPlainSpreaded<F, N> {
    pub(super) fn select(
        layouter: &mut impl Layouter<F>,
        cf_chip: &impl ControlFlowInstructions<F, AssignedNative<F>>,
        bit: &AssignedBit<F>,
        x: &Self,
        y: &Self,
    ) -> Result<Self, Error> {
        let plain = AssignedPlain::select(layouter, cf_chip, bit, &x.plain, &y.plain)?;
        let spreaded = AssignedSpreaded::select(layouter, cf_chip, bit, &x.spreaded, &y.spreaded)?;
        Ok(Self { plain, spreaded })
    }
}

impl<F: PrimeField> LimbsOfA<F> {
    pub(super) fn select(
        layouter: &mut impl Layouter<F>,
        cf_chip: &impl ControlFlowInstructions<F, AssignedNative<F>>,
        bit: &AssignedBit<F>,
        x: &Self,
        y: &Self,
    ) -> Result<Self, Error> {
        let combined =
            AssignedPlainSpreaded::select(layouter, cf_chip, bit, &x.combined, &y.combined)?;
        let spreaded_limb_10 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_10,
            &y.spreaded_limb_10,
        )?;

        let spreaded_limb_09 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_09,
            &y.spreaded_limb_09,
        )?;

        let spreaded_limb_11 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_11,
            &y.spreaded_limb_11,
        )?;

        let spreaded_limb_02 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_02,
            &y.spreaded_limb_02,
        )?;
        Ok(Self {
            combined,
            spreaded_limb_10,
            spreaded_limb_09,
            spreaded_limb_11,
            spreaded_limb_02,
        })
    }
}

impl<F: PrimeField> LimbsOfE<F> {
    pub(super) fn select(
        layouter: &mut impl Layouter<F>,
        cf_chip: &impl ControlFlowInstructions<F, AssignedNative<F>>,
        bit: &AssignedBit<F>,
        x: &Self,
        y: &Self,
    ) -> Result<Self, Error> {
        let combined =
            AssignedPlainSpreaded::select(layouter, cf_chip, bit, &x.combined, &y.combined)?;
        let spreaded_limb_07 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_07,
            &y.spreaded_limb_07,
        )?;

        let spreaded_limb_12 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_12,
            &y.spreaded_limb_12,
        )?;

        let spreaded_limb_02 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_02,
            &y.spreaded_limb_02,
        )?;

        let spreaded_limb_05 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_05,
            &y.spreaded_limb_05,
        )?;

        let spreaded_limb_06 = AssignedSpreaded::select(
            layouter,
            cf_chip,
            bit,
            &x.spreaded_limb_06,
            &y.spreaded_limb_06,
        )?;

        Ok(Self {
            combined,
            spreaded_limb_07,
            spreaded_limb_12,
            spreaded_limb_02,
            spreaded_limb_05,
            spreaded_limb_06,
        })
    }
}

impl<F: PrimeField> CompressionState<F> {
    pub(super) fn select(
        layouter: &mut impl Layouter<F>,
        cf_chip: &impl ControlFlowInstructions<F, AssignedNative<F>>,
        bit: &AssignedBit<F>,
        x: &Self,
        y: &Self,
    ) -> Result<Self, Error> {
        let a = LimbsOfA::select(layouter, cf_chip, bit, &x.a, &y.a)?;
        let b = AssignedPlainSpreaded::select(layouter, cf_chip, bit, &x.b, &y.b)?;
        let c = AssignedPlainSpreaded::select(layouter, cf_chip, bit, &x.c, &y.c)?;
        let d = AssignedPlain::select(layouter, cf_chip, bit, &x.d, &y.d)?;
        let e = LimbsOfE::select(layouter, cf_chip, bit, &x.e, &y.e)?;
        let f = AssignedPlainSpreaded::select(layouter, cf_chip, bit, &x.f, &y.f)?;
        let g = AssignedPlainSpreaded::select(layouter, cf_chip, bit, &x.g, &y.g)?;
        let h = AssignedPlain::select(layouter, cf_chip, bit, &x.h, &y.h)?;

        Ok(Self {
            a,
            b,
            c,
            d,
            e,
            f,
            g,
            h,
        })
    }
}
