use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    field::AssignedNative, instructions::FieldInstructions, utils::util::u32_to_fe, CircuitField,
};

/// An assigned 32-bit word, represented by a field element. The 32 bits are
/// stored in 4 bytes in little-endian order, i.e., the least significant byte
/// is in the lowest 8 bits of the field element. It is guaranteed to be in the
/// range [0, 2^32).
#[derive(Clone, Debug)]
pub(super) struct AssignedWord<F: CircuitField>(pub AssignedNative<F>);

impl<F: CircuitField> AssignedWord<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        value: u32,
    ) -> Result<Self, Error> {
        let assigned_native = field_chip.assign_fixed(layouter, u32_to_fe(value))?;
        Ok(AssignedWord(assigned_native))
    }
}
/// An assigned value in spreaded form, it is guaranteed to be the spreaded form
/// of a value in the range [0, 2^L).
#[derive(Clone, Debug)]
pub(super) struct AssignedSpreaded<F: CircuitField, const L: usize>(pub AssignedNative<F>);

/// The assigned values of the state vector (h0, h1, h2, h3, h4).
/// They are provided and updated for each block.
#[derive(Clone, Debug)]
pub(super) struct State<F: CircuitField> {
    pub(super) h0: AssignedWord<F>,
    pub(super) h1: AssignedWord<F>,
    pub(super) h2: AssignedWord<F>,
    pub(super) h3: AssignedWord<F>,
    pub(super) h4: AssignedWord<F>,
}

impl<F: CircuitField> From<[AssignedWord<F>; 5]> for State<F> {
    fn from(words: [AssignedWord<F>; 5]) -> Self {
        let [h0, h1, h2, h3, h4] = words;
        Self { h0, h1, h2, h3, h4 }
    }
}

impl<F: CircuitField> TryFrom<Vec<AssignedWord<F>>> for State<F> {
    type Error = Vec<AssignedWord<F>>;

    fn try_from(words: Vec<AssignedWord<F>>) -> Result<Self, Self::Error> {
        let arr: [AssignedWord<F>; 5] = words.try_into()?;
        Ok(arr.into())
    }
}

impl<F: CircuitField> Into<[AssignedWord<F>; 5]> for State<F> {
    fn into(self) -> [AssignedWord<F>; 5] {
        [self.h0, self.h1, self.h2, self.h3, self.h4]
    }
}

impl<F: CircuitField> State<F> {
    pub(super) fn fixed(
        layouter: &mut impl Layouter<F>,
        field_chip: &impl FieldInstructions<F, AssignedNative<F>>,
        constants: [u32; 5],
    ) -> Result<Self, Error> {
        let assigned_words: [AssignedWord<F>; 5] = field_chip
            .assign_many_fixed(layouter, &constants.map(u32_to_fe))?
            .into_iter()
            .map(AssignedWord)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        Ok(assigned_words.into())
    }
}
