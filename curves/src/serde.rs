use std::{convert::TryInto, fmt::Debug};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Repr<const T: usize>(
    #[cfg_attr(feature = "serde", serde(with = "serde_arrays"))] [u8; T],
);

impl<const T: usize> Repr<T> {
    pub fn inner(&self) -> &[u8; T] {
        &self.0
    }
}

impl<const T: usize> From<[u8; T]> for Repr<T> {
    fn from(bytes: [u8; T]) -> Self {
        Self(bytes)
    }
}

impl<const T: usize> From<&[u8]> for Repr<T> {
    fn from(bytes: &[u8]) -> Self {
        Self(bytes.try_into().unwrap())
    }
}

impl<const T: usize> From<Repr<T>> for [u8; T] {
    fn from(repr: Repr<T>) -> Self {
        repr.0
    }
}

impl<const T: usize> Default for Repr<T> {
    fn default() -> Self {
        Self([0u8; T])
    }
}

impl<const T: usize> AsMut<[u8]> for Repr<T> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl<const T: usize> AsRef<[u8]> for Repr<T> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<const T: usize> std::ops::Index<std::ops::Range<usize>> for Repr<T> {
    type Output = [u8];

    fn index(&self, range: std::ops::Range<usize>) -> &Self::Output {
        &self.0[range]
    }
}

impl<const T: usize> std::ops::Index<usize> for Repr<T> {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<const T: usize> std::ops::Index<std::ops::RangeTo<usize>> for Repr<T> {
    type Output = [u8];

    fn index(&self, range: std::ops::RangeTo<usize>) -> &Self::Output {
        &self.0[range]
    }
}

impl<const T: usize> std::ops::Index<std::ops::RangeFrom<usize>> for Repr<T> {
    type Output = [u8];

    fn index(&self, range: std::ops::RangeFrom<usize>) -> &Self::Output {
        &self.0[range]
    }
}

impl<const T: usize> std::ops::IndexMut<std::ops::Range<usize>> for Repr<T> {
    fn index_mut(&mut self, range: std::ops::Range<usize>) -> &mut Self::Output {
        &mut self.0[range]
    }
}

// Re-export SerdeObject from serde_traits to avoid duplication
pub use crate::serde_traits::SerdeObject;

#[allow(dead_code)]
pub(crate) enum CompressedFlagConfig {
    // NOTE: if needed we can add fields for bit positions

    // Secp256k1, Secp256r1 curves should be encoded with
    Extra, // sign: 0 identity: 1

    // Pasta curves should be encoded with
    // SingleSpare, // sign: 0

    // BN254 curve should be encoded with
    TwoSpare, // sign: 0, identity: 1

    // BLS12-{381, 377} curves should be encoded with
    ThreeSpare, // is_compressed: 0, sign: 1, identity: 2
}

impl CompressedFlagConfig {
    pub(crate) const fn has_extra_byte(&self) -> bool {
        matches!(self, CompressedFlagConfig::Extra)
    }
}

pub(crate) struct Flag {}

impl Flag {
    fn flag(pos: u8) -> u8 {
        1 << 7u8.checked_sub(pos).unwrap()
    }

    fn set(pos: u8, value: bool, flag_byte: &mut u8) {
        value.then(|| *flag_byte |= Self::flag(pos));
    }

    fn get(pos: u8, flag_byte: &mut u8) -> subtle::Choice {
        let flag = Self::flag(pos);
        let value = (*flag_byte & flag) != 0;
        *flag_byte &= !flag; // clear flag
        subtle::Choice::from(value as u8)
    }
}

pub(crate) trait Compressed<C: crate::CurveAffine>:
    Debug + Copy + Default + AsRef<[u8]> + AsMut<[u8]> + Send + Sync + 'static
where
    C::Base: crate::FieldEncoding,
{
    const CONFIG: CompressedFlagConfig;

    fn flag_byte(&mut self) -> &mut u8 {
        use crate::field_encoding::Endian;
        match Self::CONFIG {
            // Most sig byte is always the flag byte when extra byte flag is used
            CompressedFlagConfig::Extra => self.as_mut().first_mut().unwrap(),
            _ => match C::Base::REPR_ENDIAN {
                // Least sig byte is the flag byte
                Endian::LE => self.as_mut().last_mut().unwrap(),
                // Most sig byte is the flag byte
                Endian::BE => self.as_mut().first_mut().unwrap(),
            },
        }
    }

    fn sign(y: &C) -> subtle::Choice;

    fn resolve(x: C::Base, sign: subtle::Choice) -> subtle::CtOption<C>;

    fn pos_sign() -> u8 {
        match Self::CONFIG {
            CompressedFlagConfig::Extra => 0,
            CompressedFlagConfig::TwoSpare => 0,
            CompressedFlagConfig::ThreeSpare => 2,
        }
    }

    fn pos_compressed() -> Option<u8> {
        match Self::CONFIG {
            CompressedFlagConfig::ThreeSpare => Some(0),
            _ => None,
        }
    }

    fn pos_idetity() -> Option<u8> {
        match Self::CONFIG {
            CompressedFlagConfig::Extra => Some(1),
            CompressedFlagConfig::TwoSpare => Some(1),
            CompressedFlagConfig::ThreeSpare => Some(1),
        }
    }

    fn set_sign(&mut self, c: &C) {
        let sign = bool::from(Self::sign(c));
        let pos = Self::pos_sign();
        Flag::set(pos, sign, self.flag_byte());
    }

    fn set_compressed(&mut self) {
        if let Some(pos) = Self::pos_compressed() {
            Flag::set(pos, true, self.flag_byte())
        }
    }

    fn set_identity(&mut self, c: &C) {
        if let Some(pos) = Self::pos_idetity() {
            Flag::set(pos, bool::from(c.is_identity()), self.flag_byte());
        };
    }

    fn get_sign(&mut self) -> subtle::Choice {
        Flag::get(Self::pos_sign(), self.flag_byte())
    }

    fn get_is_compressed(&mut self) -> Option<subtle::Choice> {
        Self::pos_compressed().map(|pos| Flag::get(pos, self.flag_byte()))
    }

    fn get_is_identity(&mut self) -> Option<subtle::Choice> {
        Self::pos_idetity().map(|pos| Flag::get(pos, self.flag_byte()))
    }

    #[allow(dead_code)]
    fn set_flags(&mut self, c: &C) {
        self.set_identity(c);
        self.set_sign(c);
        self.set_compressed();
    }

    fn encode(c: &C) -> Self {
        use crate::FieldEncoding;
        let mut this = Self::default();
        let coordinates = c.coordinates().unwrap();
        let x = coordinates.x();
        let x_bytes = x.to_le_bytes();
        match Self::CONFIG {
            CompressedFlagConfig::Extra => {
                // Most sig byte is always the flag byte when extra byte flag is used
                this.as_mut()[1..1 + x_bytes.as_ref().len()].copy_from_slice(x_bytes.as_ref())
            }
            _ => this.as_mut()[..x_bytes.as_ref().len()].copy_from_slice(x_bytes.as_ref()),
        };
        this.set_identity(c);
        this.set_sign(c);
        this.set_compressed();
        this
    }

    fn decode(mut self) -> subtle::CtOption<C> {
        let is_compressed = self.get_is_compressed();
        // if is compressed set then it should be set one
        let is_valid_0: subtle::Choice = is_compressed.unwrap_or(subtle::Choice::from(1u8));

        let is_identity = self.get_is_identity();

        let sign = self.get_sign();

        // with extra byte config expect it goes to zero after it is read
        // otherwise `from_byte` checks if flag or rest unused bytes are zero
        let is_valid_1 = match Self::CONFIG {
            CompressedFlagConfig::Extra => *self.flag_byte() == 0,
            _ => true,
        };
        let is_valid_1: subtle::Choice = (is_valid_1 as u8).into();

        use ff::Field;
        let x = match Self::CONFIG {
            CompressedFlagConfig::Extra => {
                // Most sig byte is always the flag byte when extra byte flag is used
                <C::Base as crate::FieldEncoding>::from_le_bytes(&self.as_ref()[1..])
            }
            _ => <C::Base as crate::FieldEncoding>::from_le_bytes(self.as_ref()),
        };
        // Convert Option to CtOption
        let x = match x {
            Some(v) => subtle::CtOption::new(v, subtle::Choice::from(1u8)),
            None => subtle::CtOption::new(C::Base::ZERO, subtle::Choice::from(0u8)),
        };

        x.and_then(|x| -> subtle::CtOption<C> {
            let is_zero = x.is_zero();

            let (is_valid_2, is_identity) = match is_identity {
                // identity flag active
                Some(is_identity) => {
                    // identity flag set:
                    // * x must be zero
                    // * sign must not be set

                    // identity flag not set:
                    // * x must not be zero

                    let is_valid = (is_identity & is_zero & !sign) ^ (!is_identity & !is_zero);

                    (is_valid, is_identity)
                }

                // identitity flag inactive
                None => (subtle::Choice::from(1u8), is_zero),
            };

            let is_valid = is_valid_0 & is_valid_1 & is_valid_2;

            subtle::CtOption::new(C::identity(), is_valid & is_identity)
                .or_else(|| Self::resolve(x, sign).and_then(|c| subtle::CtOption::new(c, is_valid)))
        })
    }
}
