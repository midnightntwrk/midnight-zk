//! Compressed point encoding for the bn256 curve.
//!
//! bn256 uses the "two spare bits" layout: the field modulus leaves two unused
//! high bits in the most/least significant byte, which carry the sign flag (bit
//! position 0) and the identity flag (bit position 1). No extra byte is needed.

use std::fmt::Debug;

use crate::{
    serde::endian::{Endian, EndianRepr},
    CurveAffine,
};

/// Flag bit helpers, operating on the flag byte of a compressed encoding.
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

/// A compressed representation of an affine point, using the two-spare-bits
/// flag layout (sign at bit 0, identity at bit 1).
pub(crate) trait Compressed<C: CurveAffine>:
    Debug + Copy + Default + AsRef<[u8]> + AsMut<[u8]> + Send + Sync + 'static
where
    C::Base: EndianRepr,
{
    /// The flag byte is the byte holding the spare bits: the least significant
    /// byte for little-endian fields, the most significant for big-endian.
    fn flag_byte(&mut self) -> &mut u8 {
        match C::Base::ENDIAN {
            Endian::LE => self.as_mut().last_mut().unwrap(),
            Endian::BE => self.as_mut().first_mut().unwrap(),
        }
    }

    fn sign(y: &C) -> subtle::Choice;

    fn resolve(x: C::Base, sign: subtle::Choice) -> subtle::CtOption<C>;

    fn set_sign(&mut self, c: &C) {
        let sign = bool::from(Self::sign(c));
        Flag::set(0, sign, self.flag_byte());
    }

    fn set_identity(&mut self, c: &C) {
        Flag::set(1, bool::from(c.is_identity()), self.flag_byte());
    }

    fn get_sign(&mut self) -> subtle::Choice {
        Flag::get(0, self.flag_byte())
    }

    fn get_is_identity(&mut self) -> subtle::Choice {
        Flag::get(1, self.flag_byte())
    }

    fn encode(c: &C) -> Self {
        let mut this = Self::default();
        let coordinates = c.coordinates().unwrap();
        let x_bytes = coordinates.x().to_bytes();
        this.as_mut()[..x_bytes.len()].copy_from_slice(&x_bytes);
        this.set_identity(c);
        this.set_sign(c);
        this
    }

    fn decode(mut self) -> subtle::CtOption<C> {
        let is_identity = self.get_is_identity();
        let sign = self.get_sign();

        let x = <C::Base as EndianRepr>::from_bytes(self.as_ref());

        x.and_then(|x| -> subtle::CtOption<C> {
            use ff::Field;
            let is_zero = x.is_zero();

            // identity flag set:   x must be zero and sign must not be set.
            // identity flag unset: x must not be zero.
            let is_valid = (is_identity & is_zero & !sign) ^ (!is_identity & !is_zero);

            subtle::CtOption::new(C::identity(), is_valid & is_identity)
                .or_else(|| Self::resolve(x, sign).and_then(|c| subtle::CtOption::new(c, is_valid)))
        })
    }
}
