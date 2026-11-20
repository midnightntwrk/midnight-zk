//! HELPER FUNCTIONS

use std::{
    io,
    io::{Read, Write},
};

use ff::PrimeField;
use group::{Curve, GroupEncoding};
use midnight_curves::serde::SerdeObject;

use crate::poly::Polynomial;

/// This enum specifies how curve elements are serialized and deserialized.
///
/// Field elements are serialized in their internal (Montgomery) representation
/// in every format, and read with [`SerdeObject::read_raw`], whose checks
/// depend on the field: BLS12-381 scalars are not checked to be reduced.
#[derive(Clone, Copy, Debug)]
pub enum SerdeFormat {
    /// Curve elements are serialized in compressed form. When deserializing,
    /// they are validated (on BLS12-381: on the curve and in the prime-order
    /// subgroup).
    Processed,
    /// Curve elements are serialized in uncompressed form, as given by their
    /// [`SerdeObject`] implementation. When deserializing, they are validated
    /// as in `Processed`.
    RawBytes,
    /// Same serialization as `RawBytes`. When deserializing, curve elements
    /// skip the checks that their [`SerdeObject`] implementation allows to skip
    /// (on BLS12-381, the subgroup check). Only use it on trusted data: it is
    /// rejected when reading keys.
    RawBytesUnchecked,
}

/// Interface for Serde objects that can be represented in compressed form.
pub trait ProcessedSerdeObject: Sized {
    /// Reads an element from the buffer and parses it according to the
    /// `format` (see [`SerdeFormat`]). In every format, bytes that cannot be
    /// decoded give an error.
    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>;

    /// Writes an element according to `format`:
    /// - `Processed`: Writes a compressed element
    /// - Otherwise: Writes an uncompressed element
    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>;

    /// Length in bytes of an element when serialized in the given `format`.
    fn byte_length(&self, format: SerdeFormat) -> usize;
}

/// Helper function to read a field element with a serde format. There is no way
/// to compress field elements, so `Processed` and `RawBytes` act equivalently.
pub(crate) fn read_f<F: PrimeField + SerdeObject, R: io::Read>(
    reader: &mut R,
    format: SerdeFormat,
) -> io::Result<F> {
    match format {
        SerdeFormat::Processed | SerdeFormat::RawBytes => F::read_raw(reader),
        SerdeFormat::RawBytesUnchecked => F::try_read_raw_unchecked(reader),
    }
}

/// Trait for serialising SerdeObjects
impl<C> ProcessedSerdeObject for C
where
    C: Curve + GroupEncoding + From<C::AffineRepr>,
    C::AffineRepr: SerdeObject,
{
    fn read<R: Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        {
            match format {
                SerdeFormat::Processed => {
                    let mut compressed = <Self as GroupEncoding>::Repr::default();
                    reader.read_exact(compressed.as_mut())?;
                    Option::from(Self::from_bytes(&compressed))
                        .ok_or_else(|| io::Error::other("Invalid point encoding in proof"))
                }
                SerdeFormat::RawBytes => {
                    <Self as Curve>::AffineRepr::read_raw(reader).map(|p| p.into())
                }
                SerdeFormat::RawBytesUnchecked => {
                    <Self as Curve>::AffineRepr::try_read_raw_unchecked(reader).map(|p| p.into())
                }
            }
        }
    }

    fn write<W: Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        match format {
            SerdeFormat::Processed => writer.write_all(self.to_bytes().as_ref()),
            _ => self.to_affine().write_raw(writer),
        }
    }

    fn byte_length(&self, format: SerdeFormat) -> usize {
        match format {
            SerdeFormat::Processed => C::Repr::default().as_ref().len(),
            _ => C::Repr::default().as_ref().len() * 2,
        }
    }
}

/// Convert a slice of `bool` into a `u8`.
///
/// Panics if the slice has length greater than 8.
pub fn pack(bits: &[bool]) -> u8 {
    let mut value = 0u8;
    assert!(bits.len() <= 8);
    for (bit_index, bit) in bits.iter().enumerate() {
        value |= (*bit as u8) << bit_index;
    }
    value
}

/// Writes the first `bits.len()` bits of a `u8` into `bits`.
pub fn unpack(byte: u8, bits: &mut [bool]) {
    for (bit_index, bit) in bits.iter_mut().enumerate() {
        *bit = (byte >> bit_index) & 1 == 1;
    }
}

/// Reads a vector of polynomials from buffer
pub(crate) fn read_polynomial_vec<R: io::Read, F: PrimeField + SerdeObject, B>(
    reader: &mut R,
    format: SerdeFormat,
) -> io::Result<Vec<Polynomial<F, B>>> {
    let mut len = [0u8; 4];
    reader.read_exact(&mut len)?;
    let len = u32::from_be_bytes(len);

    (0..len)
        .map(|_| Polynomial::<F, B>::read(reader, format))
        .collect::<io::Result<Vec<_>>>()
}

/// Writes a slice of polynomials to buffer
pub(crate) fn write_polynomial_slice<W: io::Write, F: PrimeField + SerdeObject, B>(
    slice: &[Polynomial<F, B>],
    writer: &mut W,
) -> io::Result<()> {
    writer.write_all(&(slice.len() as u32).to_be_bytes())?;
    for poly in slice.iter() {
        poly.write(writer)?;
    }
    Ok(())
}

/// Gets the total number of bytes of a slice of polynomials, assuming all
/// polynomials are the same length
pub(crate) fn polynomial_slice_byte_length<F: PrimeField, B>(slice: &[Polynomial<F, B>]) -> usize {
    let field_len = F::default().to_repr().as_ref().len();
    4 + slice.len() * (4 + field_len * slice.first().map(|poly| poly.len()).unwrap_or(0))
}
