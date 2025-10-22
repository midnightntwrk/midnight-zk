//! This module defines how constant values must be parsed.
//!
//!  - A single character is parsed as an [IrType::Bool]: '0' is false, '1' is
//!    true and any other character results in an error.
//!
//!  - A hexadecimal string is parsed as [IrType::Bytes].
//!
//!  - A string prefixed by "Native:" is parsed as an [IrType::Native]. The
//!    payload that follows this prefix is expected to be a hexadecimal string
//!    (optionally prefixed by a negative sign '-'), representing a big-endian
//!    integer, which must be smaller (in absolute value) than the native prime
//!    field modulus.
//!
//!  - A string prefixed by "BigUint:" is parsed as an [IrType::BigUint]. The
//!    payload that follows this prefix is expected to be a hexadecimal string
//!    representing a big-endian (non-negative) integer.
//!
//!  - A string prefixed by "Jubjub:" is parsed as an [IrType::JubjubPoint]. The
//!    payload that follows this prefix is expected to be a hexadecimal string of
//!    exactly 32 bytes, following the repr_J encoding as defined in [Zcash specification
//!    5.4.9.3 - JubJub](https://zips.z.cash/protocol/protocol.pdf#jubjub).
//!    Additionally, the following strings are allowed:
//!      - "Jubjub:GENERATOR", for the official generator of the Jubjub subgroup
//!      - "Jubjub:IDENTITY", for the identity point of the Jubjub curve
//!
//!  - A string prefixed by "JubjubScalar:" is parsed as an
//!    [IrType::JubjubScalar]. The payload that follows this prefix is expected
//!    to be a hexadecimal string representing a big-endian (non-negative)
//!    integer, which must be smaller than the Jubjub scalar field order.

use group::{Group, GroupEncoding};
use midnight_circuits::{
    compact_std_lib::ZkStdLib, ecc::curves::CircuitCurve, instructions::AssignmentInstructions,
};
use midnight_curves::{Fr as JubjubScalar, JubjubExtended, JubjubSubgroup};
use midnight_proofs::circuit::Layouter;
use num_bigint::BigUint;
use num_traits::Num;

use crate::{
    types::{CircuitValue, IrType},
    utils::F,
    Error, IrValue,
};

impl TryFrom<&str> for IrValue {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        use IrValue::*;

        match value.split(':').collect::<Vec<_>>().as_slice() {
            [b] if b.len() == 1 => parse_bool(b).map(Bool),
            [hex] => parse_bytes(hex).map(Bytes),
            ["Native", payload] => parse_native(payload).map(Native),
            ["BigUint", payload] => parse_biguint(payload).map(BigUint),
            ["Jubjub", payload] => parse_jubjub_point(payload).map(JubjubPoint),
            ["JubjubScalar", payload] => parse_jubjub_scalar(payload).map(JubjubScalar),
            _ => Err(Error::Other(format!("invalid format: {}", value))),
        }
    }
}

pub fn assign_constant(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    constant: &str,
) -> Result<CircuitValue, Error> {
    match IrValue::try_from(constant)? {
        IrValue::Bool(b) => {
            let assigned = std_lib.assign_fixed(layouter, b)?;
            Ok(CircuitValue::Bool(assigned))
        }
        IrValue::Bytes(bytes) => {
            let assigned = std_lib.assign_many_fixed(layouter, &bytes)?;
            Ok(CircuitValue::Bytes(assigned))
        }
        IrValue::Native(x) => {
            let assigned = std_lib.assign_fixed(layouter, x)?;
            Ok(CircuitValue::Native(assigned))
        }
        IrValue::BigUint(big) => {
            let assigned = std_lib.biguint().assign_fixed_biguint(layouter, big)?;
            Ok(CircuitValue::BigUint(assigned))
        }
        IrValue::JubjubPoint(p) => {
            let assigned = std_lib.jubjub().assign_fixed(layouter, p)?;
            Ok(CircuitValue::JubjubPoint(assigned))
        }
        IrValue::JubjubScalar(s) => {
            let assigned = std_lib.jubjub().assign_fixed(layouter, s)?;
            Ok(CircuitValue::JubjubScalar(assigned))
        }
    }
}

fn parse_bool(str: &str) -> Result<bool, Error> {
    match str {
        "0" => Ok(false),
        "1" => Ok(true),
        _ => Err(Error::ParsingError(IrType::Bool, str.to_string())),
    }
}

fn parse_bytes(str: &str) -> Result<Vec<u8>, Error> {
    const_hex::decode(str).map_err(|e| Error::Other(format!("{e:?}")))
}

fn parse_native(str: &str) -> Result<F, Error> {
    let mut repr = str.as_bytes();
    let is_negative = !repr.is_empty() && repr[0] == b'-';
    if is_negative {
        repr = &repr[1..];
    };
    let mut bytes = const_hex::decode(repr)
        .map_err(|_| Error::ParsingError(IrType::Native, str.to_string()))?;
    if bytes.len() > 32 {
        return Err(Error::ParsingError(IrType::Native, str.to_string()));
    }

    bytes.reverse();
    bytes.resize(32, 0);

    let x = F::from_bytes_le(&bytes.try_into().unwrap())
        .into_option()
        .ok_or(Error::ParsingError(IrType::Native, str.to_string()))?;
    Ok(if is_negative { -x } else { x })
}

fn parse_biguint(str: &str) -> Result<BigUint, Error> {
    let str = str.strip_prefix("0x").unwrap_or(str);
    BigUint::from_str_radix(str, 16).map_err(|e| Error::Other(format!("{e:?}")))
}

fn parse_jubjub_point(str: &str) -> Result<JubjubSubgroup, Error> {
    match str {
        "GENERATOR" => Ok(JubjubSubgroup::generator()),
        "IDENTITY" => Ok(JubjubSubgroup::identity()),
        _ => {
            let bytes: [u8; 32] = const_hex::decode(str)
                .map_err(|e| Error::Other(format!("{e:?}")))?
                .try_into()
                .map_err(|_| Error::ParsingError(IrType::JubjubPoint, str.to_string()))?;
            JubjubExtended::from_bytes(&bytes)
                .into_option()
                .map(|p| p.into_subgroup())
                .ok_or(Error::ParsingError(IrType::JubjubPoint, str.to_string()))
        }
    }
}

fn parse_jubjub_scalar(str: &str) -> Result<JubjubScalar, Error> {
    let mut bytes = const_hex::decode(str)
        .map_err(|_| Error::ParsingError(IrType::JubjubScalar, str.to_string()))?;

    if bytes.len() > 32 {
        return Err(Error::ParsingError(IrType::JubjubScalar, str.to_string()));
    }

    bytes.reverse();
    bytes.resize(32, 0);
    JubjubScalar::from_bytes(&bytes.try_into().unwrap())
        .into_option()
        .ok_or(Error::ParsingError(IrType::Native, str.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constants() {
        assert_eq!(parse_bool("0"), Ok(false));
        assert_eq!(parse_bool("1"), Ok(true));

        assert_eq!(parse_bytes("0xDEADBEEF"), Ok(vec![222, 173, 190, 239]));
        assert_eq!(parse_bytes("0xAAA"), Err(Error::Other("OddLength".into())));

        assert_eq!(parse_native("0x10"), Ok(F::from(16)));
        assert_eq!(parse_native("-0x11"), Ok(-F::from(17)));
        assert_eq!(parse_native("FF00"), Ok(F::from(0xFF00u64)));

        assert_eq!(parse_biguint("1234"), Ok(BigUint::from(0x1234u64)));

        assert_eq!(
            parse_jubjub_point("GENERATOR"),
            Ok(JubjubSubgroup::generator())
        );
        assert_eq!(
            parse_jubjub_point("IDENTITY"),
            Ok(JubjubSubgroup::identity())
        );

        assert_eq!(parse_jubjub_scalar("0407"), Ok(JubjubScalar::from(1031)));

        [
            ("1", Ok(IrValue::Bool(true))),
            ("0xFF0A00", Ok(IrValue::Bytes(vec![255, 10, 0]))),
            ("Native:4321", Ok(IrValue::Native(F::from(17185)))),
            (
                "BigUint:0x1234",
                Ok(IrValue::BigUint(BigUint::from(0x1234u64))),
            ),
            (
                "Jubjub:GENERATOR",
                Ok(IrValue::JubjubPoint(JubjubSubgroup::generator())),
            ),
            (
                "Jubjub:0xcb550cd538ea0cc1138480408e6eaab9b36c613f0dd3f7784fdb6eea837b13d7",
                Ok(IrValue::JubjubPoint(JubjubSubgroup::generator())),
            ),
            (
                "JubjubScalar:FF",
                Ok(IrValue::JubjubScalar(JubjubScalar::from(255))),
            ),
        ]
        .into_iter()
        .for_each(|(str, res)| assert_eq!(IrValue::try_from(str), res));
    }
}
