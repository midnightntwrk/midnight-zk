//! Serialization traits for curve elements and field elements.

use std::io::{self, Read, Write};

/// Trait for converting raw bytes to/from the internal representation of a
/// type. For example, field elements are represented in Montgomery form and
/// serialized/deserialized without Montgomery reduction.
///
/// The checks made by each function depend on the type. On BLS12-381 points,
/// the checked functions verify the encoding, the curve equation and the
/// prime-order subgroup, and the unchecked ones only skip the subgroup check.
pub trait SerdeObject: Sized {
    /// Reads the internal memory representation from bytes as quickly as
    /// possible, skipping checks that [`from_raw_bytes`](Self::from_raw_bytes)
    /// makes. Only use it on trusted data.
    ///
    /// # Panics
    ///
    /// May panic if the bytes have the wrong length or cannot be decoded.
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self;

    /// Read the internal memory representation from bytes.
    /// Returns None if the bytes do not represent a valid object.
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self>;

    /// Convert the internal memory representation to bytes.
    fn to_raw_bytes(&self) -> Vec<u8>;

    /// Reads the internal memory representation from a reader as quickly as
    /// possible, skipping checks that [`read_raw`](Self::read_raw) makes. Only
    /// use it on trusted data.
    ///
    /// # Panics
    ///
    /// May panic if the reader fails or the bytes cannot be decoded.
    fn read_raw_unchecked<R: Read>(reader: &mut R) -> Self;

    /// Read the internal memory representation from a reader.
    fn read_raw<R: Read>(reader: &mut R) -> io::Result<Self>;

    /// Write the internal memory representation to a writer.
    fn write_raw<W: Write>(&self, writer: &mut W) -> io::Result<()>;
}
