use crate::{
    field::{decomposition::chip::P2RDecompositionChip, AssignedNative, NativeChip, NativeGadget},
    hash::sha256::types::{
        AssignedMessageWord, AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded,
        CompressionState, LimbsOfA, LimbsOfE,
    },
    instructions::AssertionInstructions,
    types::{AssignedBit, InnerValue},
};
use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::instructions::ControlFlowInstructions;

use super::Sha256Chip;

pub struct VarLenSha256Gadget<F: PrimeField> {
    pub(super) sha256chip: Sha256Chip<F>,
}

impl<F: PrimeField> VarLenSha256Gadget<F> {
    fn ng(&self) -> &NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>> {
        &self.sha256chip.native_gadget
    }
}

/// InnerValue impl for Sha internal types.

// TODO We are using:
// type Element = F
// but it would be more accurate to use some bounded type like
// uint guaranteed to be in [0, 2^L)
impl<F: PrimeField, const L: usize> InnerValue for AssignedPlain<F, L> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.0.value().cloned()
    }
}

impl<F: PrimeField, const L: usize> InnerValue for AssignedSpreaded<F, L> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.0.value().cloned()
    }
}

impl<F: PrimeField, const L: usize> InnerValue for AssignedPlainSpreaded<F, L> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.plain.value() // plain and spreaded values are consistent.
    }
}

impl<F: PrimeField> InnerValue for LimbsOfA<F> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.combined.value()
    }
}

impl<F: PrimeField> InnerValue for LimbsOfE<F> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.combined.value()
    }
}

// TODO: Uncomment if necessary, delete otherwise.
// impl<F: PrimeField> InnerValue for AssignedMessageWord<F> {
//     type Element = F;

//     fn value(&self) -> Value<Self::Element> {
//         self.combined_plain.value()
//     }
// }

impl<F: PrimeField> InnerValue for CompressionState<F> {
    type Element = [F; 8];

    fn value(&self) -> Value<Self::Element> {
        let vals: Value<Vec<F>> = Value::from_iter([
            self.a.value(),
            self.b.value(),
            self.c.value(),
            self.d.value(),
            self.e.value(),
            self.f.value(),
            self.g.value(),
            self.h.value(),
        ]);
        vals.map(|v| v.try_into().unwrap())
    }
}

// ----------------------------
// AssertionInstruction implementation for internal types.

impl<F: PrimeField, const L: usize> AssertionInstructions<F, AssignedPlain<F, L>>
    for VarLenSha256Gadget<F>
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlain<F, L>,
        y: &AssignedPlain<F, L>,
    ) -> Result<(), Error> {
        self.ng().assert_equal(layouter, &x.0, &y.0)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlain<F, L>,
        y: &AssignedPlain<F, L>,
    ) -> Result<(), Error> {
        self.ng().assert_not_equal(layouter, &x.0, &y.0)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlain<F, L>,
        constant: <AssignedPlain<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.ng().assert_equal_to_fixed(layouter, &x.0, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlain<F, L>,
        constant: <AssignedPlain<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.ng()
            .assert_not_equal_to_fixed(layouter, &x.0, constant)
    }
}

impl<F: PrimeField, const L: usize> AssertionInstructions<F, AssignedSpreaded<F, L>>
    for VarLenSha256Gadget<F>
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSpreaded<F, L>,
        y: &AssignedSpreaded<F, L>,
    ) -> Result<(), Error> {
        self.ng().assert_equal(layouter, &x.0, &y.0)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSpreaded<F, L>,
        y: &AssignedSpreaded<F, L>,
    ) -> Result<(), Error> {
        self.ng().assert_not_equal(layouter, &x.0, &y.0)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSpreaded<F, L>,
        constant: <AssignedSpreaded<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.ng().assert_equal_to_fixed(layouter, &x.0, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSpreaded<F, L>,
        constant: <AssignedSpreaded<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.ng()
            .assert_not_equal_to_fixed(layouter, &x.0, constant)
    }
}

impl<F: PrimeField, const L: usize> AssertionInstructions<F, AssignedPlainSpreaded<F, L>>
    for VarLenSha256Gadget<F>
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlainSpreaded<F, L>,
        y: &AssignedPlainSpreaded<F, L>,
    ) -> Result<(), Error> {
        self.assert_equal(layouter, &x.plain, &y.plain)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlainSpreaded<F, L>,
        y: &AssignedPlainSpreaded<F, L>,
    ) -> Result<(), Error> {
        self.assert_not_equal(layouter, &x.plain, &y.plain)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlainSpreaded<F, L>,
        constant: <AssignedPlainSpreaded<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, &x.plain, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlainSpreaded<F, L>,
        constant: <AssignedPlainSpreaded<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, &x.plain, constant)
    }
}

impl<F: PrimeField> AssertionInstructions<F, LimbsOfA<F>> for VarLenSha256Gadget<F> {
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfA<F>,
        y: &LimbsOfA<F>,
    ) -> Result<(), Error> {
        self.assert_equal(layouter, &x.combined, &y.combined)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfA<F>,
        y: &LimbsOfA<F>,
    ) -> Result<(), Error> {
        self.assert_not_equal(layouter, &x.combined, &y.combined)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfA<F>,
        constant: <LimbsOfA<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, &x.combined, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfA<F>,
        constant: <LimbsOfA<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, &x.combined, constant)
    }
}

impl<F: PrimeField> AssertionInstructions<F, LimbsOfE<F>> for VarLenSha256Gadget<F> {
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfE<F>,
        y: &LimbsOfE<F>,
    ) -> Result<(), Error> {
        self.assert_equal(layouter, &x.combined, &y.combined)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfE<F>,
        y: &LimbsOfE<F>,
    ) -> Result<(), Error> {
        self.assert_not_equal(layouter, &x.combined, &y.combined)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfE<F>,
        constant: <LimbsOfE<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, &x.combined, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfE<F>,
        constant: <LimbsOfE<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, &x.combined, constant)
    }
}

impl<F: PrimeField> AssertionInstructions<F, CompressionState<F>> for VarLenSha256Gadget<F> {
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &CompressionState<F>,
        y: &CompressionState<F>,
    ) -> Result<(), Error> {
        // self.assert_equal(layouter, &x.a.combined.plain.0, &y.a.combined.plain.0)?;
        self.assert_equal(layouter, &x.a, &y.a)?;
        self.assert_equal(layouter, &x.b, &y.b)?;
        self.assert_equal(layouter, &x.c, &y.c)?;
        self.assert_equal(layouter, &x.d, &y.d)?;
        self.assert_equal(layouter, &x.e, &y.e)?;
        self.assert_equal(layouter, &x.f, &y.f)?;
        self.assert_equal(layouter, &x.g, &y.g)?;
        self.assert_equal(layouter, &x.h, &y.h)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &CompressionState<F>,
        y: &CompressionState<F>,
    ) -> Result<(), Error> {
        self.assert_not_equal(layouter, &x.a, &y.a)?;
        self.assert_not_equal(layouter, &x.b, &y.b)?;
        self.assert_not_equal(layouter, &x.c, &y.c)?;
        self.assert_not_equal(layouter, &x.d, &y.d)?;
        self.assert_not_equal(layouter, &x.e, &y.e)?;
        self.assert_not_equal(layouter, &x.f, &y.f)?;
        self.assert_not_equal(layouter, &x.g, &y.g)?;
        self.assert_not_equal(layouter, &x.h, &y.h)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &CompressionState<F>,
        constant: <CompressionState<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, &x.a, constant[0])?;
        self.assert_equal_to_fixed(layouter, &x.b, constant[1])?;
        self.assert_equal_to_fixed(layouter, &x.c, constant[2])?;
        self.assert_equal_to_fixed(layouter, &x.d, constant[3])?;
        self.assert_equal_to_fixed(layouter, &x.e, constant[4])?;
        self.assert_equal_to_fixed(layouter, &x.f, constant[5])?;
        self.assert_equal_to_fixed(layouter, &x.g, constant[6])?;
        self.assert_equal_to_fixed(layouter, &x.h, constant[7])
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &CompressionState<F>,
        constant: <CompressionState<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, &x.a, constant[0])?;
        self.assert_not_equal_to_fixed(layouter, &x.b, constant[1])?;
        self.assert_not_equal_to_fixed(layouter, &x.c, constant[2])?;
        self.assert_not_equal_to_fixed(layouter, &x.d, constant[3])?;
        self.assert_not_equal_to_fixed(layouter, &x.e, constant[4])?;
        self.assert_not_equal_to_fixed(layouter, &x.f, constant[5])?;
        self.assert_not_equal_to_fixed(layouter, &x.g, constant[6])?;
        self.assert_not_equal_to_fixed(layouter, &x.h, constant[7])
    }
}

// Implementation of ControlFlowInstructions

impl<F: PrimeField, const L: usize> ControlFlowInstructions<F, AssignedPlain<F, L>>
    for VarLenSha256Gadget<F>
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedPlain<F, L>,
        y: &AssignedPlain<F, L>,
    ) -> Result<AssignedPlain<F, L>, Error> {
        Ok(AssignedPlain(self.ng().select(layouter, cond, &x.0, &y.0)?))
    }
}

impl<F: PrimeField, const L: usize> ControlFlowInstructions<F, AssignedSpreaded<F, L>>
    for VarLenSha256Gadget<F>
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedSpreaded<F, L>,
        y: &AssignedSpreaded<F, L>,
    ) -> Result<AssignedSpreaded<F, L>, Error> {
        Ok(AssignedSpreaded(
            self.ng().select(layouter, cond, &x.0, &y.0)?,
        ))
    }
}

impl<F: PrimeField, const L: usize> ControlFlowInstructions<F, AssignedPlainSpreaded<F, L>>
    for VarLenSha256Gadget<F>
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedPlainSpreaded<F, L>,
        y: &AssignedPlainSpreaded<F, L>,
    ) -> Result<AssignedPlainSpreaded<F, L>, Error> {
        let plain = self.select(layouter, cond, &x.plain, &y.plain)?;
        let spreaded = self.select(layouter, cond, &x.spreaded, &y.spreaded)?;
        Ok(AssignedPlainSpreaded { plain, spreaded })
    }
}

impl<F: PrimeField> ControlFlowInstructions<F, LimbsOfA<F>> for VarLenSha256Gadget<F> {
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &LimbsOfA<F>,
        y: &LimbsOfA<F>,
    ) -> Result<LimbsOfA<F>, Error> {
        let combined = self.select(layouter, cond, &x.combined, &y.combined)?;
        let spreaded_limb_10 =
            self.select(layouter, cond, &x.spreaded_limb_10, &y.spreaded_limb_10)?;
        let spreaded_limb_09 =
            self.select(layouter, cond, &x.spreaded_limb_09, &y.spreaded_limb_09)?;
        let spreaded_limb_11 =
            self.select(layouter, cond, &x.spreaded_limb_11, &y.spreaded_limb_11)?;
        let spreaded_limb_02 =
            self.select(layouter, cond, &x.spreaded_limb_02, &y.spreaded_limb_02)?;

        Ok(LimbsOfA {
            combined,
            spreaded_limb_10,
            spreaded_limb_09,
            spreaded_limb_11,
            spreaded_limb_02,
        })
    }
}

impl<F: PrimeField> ControlFlowInstructions<F, LimbsOfE<F>> for VarLenSha256Gadget<F> {
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &LimbsOfE<F>,
        y: &LimbsOfE<F>,
    ) -> Result<LimbsOfE<F>, Error> {
        let combined = self.select(layouter, cond, &x.combined, &y.combined)?;
        let spreaded_limb_07 =
            self.select(layouter, cond, &x.spreaded_limb_07, &y.spreaded_limb_07)?;
        let spreaded_limb_12 =
            self.select(layouter, cond, &x.spreaded_limb_12, &y.spreaded_limb_12)?;
        let spreaded_limb_02 =
            self.select(layouter, cond, &x.spreaded_limb_02, &y.spreaded_limb_02)?;
        let spreaded_limb_05 =
            self.select(layouter, cond, &x.spreaded_limb_05, &y.spreaded_limb_05)?;
        let spreaded_limb_06 =
            self.select(layouter, cond, &x.spreaded_limb_06, &y.spreaded_limb_06)?;

        Ok(LimbsOfE {
            combined,
            spreaded_limb_07,
            spreaded_limb_12,
            spreaded_limb_02,
            spreaded_limb_05,
            spreaded_limb_06,
        })
    }
}

impl<F: PrimeField> ControlFlowInstructions<F, CompressionState<F>> for VarLenSha256Gadget<F> {
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &CompressionState<F>,
        y: &CompressionState<F>,
    ) -> Result<CompressionState<F>, Error> {
        let a = self.select(layouter, cond, &x.a, &y.a)?;
        let b = self.select(layouter, cond, &x.b, &y.b)?;
        let c = self.select(layouter, cond, &x.c, &y.c)?;
        let d = self.select(layouter, cond, &x.d, &y.d)?;
        let e = self.select(layouter, cond, &x.e, &y.e)?;
        let f = self.select(layouter, cond, &x.f, &y.f)?;
        let g = self.select(layouter, cond, &x.g, &y.g)?;
        let h = self.select(layouter, cond, &x.h, &y.h)?;

        Ok(CompressionState {
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

// ----------------------------
