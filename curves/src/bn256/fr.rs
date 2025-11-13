use core::convert::TryInto;
use halo2derive::impl_field;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

impl_field!(
    bn256_scalar,
    Fr,
    modulus = "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
    mul_gen = "7",
    zeta = "30644e72e131a029048b6e193fd84104cc37a73fec2bc5e9b8ca0b2d36636f23",
    from_uniform = [64, 48],
    endian = "little",
);

crate::extend_field_legendre!(Fr);
crate::impl_binops_calls!(Fr);
crate::impl_binops_additive!(Fr, Fr);
crate::impl_binops_multiplicative!(Fr, Fr);
crate::field_bits!(Fr);
crate::serialize_deserialize_primefield!(Fr);

crate::impl_from_u64!(Fr);
crate::impl_from_bool!(Fr);

#[cfg(test)]
mod test {

    use super::*;
    crate::field_testing_suite!(Fr, "field_arithmetic");
    crate::field_testing_suite!(Fr, "conversion");
    crate::field_testing_suite!(Fr, "serdeobject");
    crate::field_testing_suite!(Fr, "quadratic_residue");
    crate::field_testing_suite!(Fr, "bits");
    crate::field_testing_suite!(Fr, "constants");
    crate::field_testing_suite!(Fr, "sqrt");
    crate::field_testing_suite!(Fr, "zeta");
    crate::field_testing_suite!(Fr, "from_uniform_bytes", 64);
}
