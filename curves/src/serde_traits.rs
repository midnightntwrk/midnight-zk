//! Raw serialization of field elements.

use std::io::{self, Read, Write};

/// Trait for converting a field element to and from the bytes of its internal
/// representation (Montgomery form), without the Montgomery conversion that the
/// canonical encoding of [`ff::PrimeField`] needs.
///
/// It is meant for the scalar fields that circuits are defined over, and it is
/// implemented for BLS12-381 `Fq` and for the BN256 fields (under
/// `dev-curves`).
///
/// It is not meant for curve points, which are serialized with
/// [`group::GroupEncoding`] (compressed) and [`group::UncompressedEncoding`]
/// (uncompressed).
///
/// The checked functions verify the length of the input. Whether they also
/// reject a value that is not reduced modulo the field characteristic depends
/// on the field: the BN256 fields do, BLS12-381 `Fq` does not.
pub trait SerdeObject: Sized {
    /// Reads the internal memory representation from bytes as quickly as
    /// possible, skipping checks that [`from_raw_bytes`](Self::from_raw_bytes)
    /// makes. Only use it on trusted data.
    ///
    /// # Panics
    ///
    /// May panic if the bytes have the wrong length.
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
    /// May panic if the reader fails.
    fn read_raw_unchecked<R: Read>(reader: &mut R) -> Self;

    /// Read the internal memory representation from a reader.
    fn read_raw<R: Read>(reader: &mut R) -> io::Result<Self>;

    /// Write the internal memory representation to a writer.
    fn write_raw<W: Write>(&self, writer: &mut W) -> io::Result<()>;
}
