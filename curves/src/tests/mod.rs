pub mod curve;
pub mod engine;
pub mod field;
pub mod field_halo2curves;
pub mod pairing;

pub fn hex_to_bytes(hex: &str) -> Vec<u8> {
    hex::decode(hex).expect("Invalid hex string")
}

/// Helper function to convert a hex string to a field element.
/// Used by BN256 tests.
#[cfg(any(test, feature = "dev-curves"))]
pub(crate) fn hex_to_field<F: ff::PrimeField>(hex: &str) -> F {
    let mut bytes = hex_to_bytes(hex);
    bytes.reverse();
    let mut repr = F::Repr::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(&bytes);
    F::from_repr(repr).unwrap()
}

/// Helper function to create a G1 point from hex coordinates.
/// Used by BN256 hash-to-curve tests.
#[cfg(any(test, feature = "dev-curves"))]
pub fn point_from_hex<C>(x_hex: &str, y_hex: &str) -> C
where
    C: crate::CurveAffine,
    C::Base: ff::PrimeField,
{
    let x = hex_to_field(x_hex);
    let y = hex_to_field(y_hex);
    C::from_xy(x, y).expect("Invalid point coordinates")
}
