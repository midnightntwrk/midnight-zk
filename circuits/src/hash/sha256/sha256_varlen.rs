use crate::{
    field::AssignedNative,
    hash::sha256::types::{
        AssignedMessageWord, AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded,
        CompressionState, LimbsOfA, LimbsOfE,
    },
    types::InnerValue,
};
use ff::PrimeField;
use midnight_proofs::circuit::Value;

use crate::instructions::ControlFlowInstructions;

use super::Sha256Chip;

pub struct VarLenSha256Gadget<F: PrimeField> {
    pub(super) sha256chip: Sha256Chip<F>,
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

// // TODO Try blanket impl for this
// impl<F: PrimeField, const L: usize> ControlFlowInstructions<F, AssignedPlain<F, L>>
//     for VarLenSha256Gadget<F>
// {
//     fn select(
//         &self,
//         layouter: &mut impl midnight_proofs::circuit::Layouter<F>,
//         cond: &crate::types::AssignedBit<F>,
//         x: &AssignedPlain<F, L>,
//         y: &AssignedPlain<F, L>,
//     ) -> Result<AssignedPlain<F, L>, midnight_proofs::plonk::Error> {
//         todo!()
//     }
// }
