use group::GroupEncoding;
use midnight_circuits::{
    compact_std_lib::ZkStdLib, instructions::DecompositionInstructions, types::InnerValue,
};
use midnight_curves::{Fr as JubjubFr, JubjubSubgroup};
use midnight_proofs::circuit::{Layouter, Value};

use crate::{
    instructions::operations::{assert_equal_incircuit, into_bytes_incircuit, load_incircuit},
    types::{CircuitValue, IrValue},
    utils::{big_to_fe, F},
    Error, IrType, Operation,
};

impl IrValue {
    /// Builds an IrValue of the given type from the given bytes.
    ///
    /// In the case of prime field values or big integers, the bytes are
    /// interpreted as an integer in little-endian order.
    ///
    /// In the case of Jubjub points, we expect exactly `32` bytes.
    /// We follow the `repr_J` encoding as defined in
    /// [Zcash specification 5.4.9.3 - JubJub](https://zips.z.cash/protocol/protocol.pdf#jubjub).
    ///
    /// # Errors
    ///
    /// If the conversion is not possible.
    pub fn from_bytes(t: IrType, bytes: &[u8]) -> Result<IrValue, Error> {
        use IrType::*;
        match t {
            Native => Ok(big_to_fe::<F>(num_bigint::BigUint::from_bytes_le(bytes)).into()),

            BigUint(n) if n >= 8 * bytes.len() as u32 => {
                Ok(num_bigint::BigUint::from_bytes_le(bytes).into())
            }

            JubjubPoint if bytes.len() == 32 => {
                JubjubSubgroup::from_bytes(&bytes.try_into().unwrap())
                    .into_option()
                    .map(|p| IrValue::JubjubPoint(p))
                    .ok_or(Error::Other(format!(
                        "cannot convert {bytes:?} to JubjubPoint"
                    )))
            }

            JubjubScalar => {
                Ok(big_to_fe::<JubjubFr>(num_bigint::BigUint::from_bytes_le(bytes)).into())
            }

            _ => Err(Error::Unsupported(
                Operation::FromBytes(t),
                vec![IrType::Bytes(bytes.len())],
            )),
        }
    }
}

/// Builds an IrValue of the given type from the given bytes.
///
/// In the case of prime field values or big integers, the bytes are
/// interpreted as an integer in little-endian order.
///
/// In the case of Jubjub points, we expect exactly `32` bytes.
/// We follow the `repr_J` encoding as defined in
/// [Zcash specification 5.4.9.3 - JubJub](https://zips.z.cash/protocol/protocol.pdf#jubjub).
///
/// # Errors
///
/// If the conversion is not possible.
pub fn from_bytes_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    t: IrType,
    input_bytes: &CircuitValue,
) -> Result<CircuitValue, Error> {
    let bytes = match input_bytes {
        CircuitValue::Bytes(v) => v,
        _ => {
            return Err(Error::Other(format!(
                "expecting Bytes(n), got {:?}",
                input_bytes.get_type()
            )))
        }
    };

    use IrType::*;
    match t {
        Native => Ok(std_lib.assigned_from_le_bytes(layouter, bytes)?.into()),

        BigUint(n) if n >= 8 * bytes.len() as u32 => {
            Ok(std_lib.biguint().from_le_bytes(layouter, bytes)?.into())
        }

        JubjubPoint if bytes.len() == 32 => {
            // We witness the point that these bytes represent, convert it to bytes
            // in-circuit and assert equality between such bytes and the received ones.
            // This may not be the most efficient, but it is straightforward and
            // maintainable.
            let bytes_val: Value<Vec<u8>> =
                Value::from_iter(bytes.clone().into_iter().map(|b| b.value()));
            let p_val = bytes_val.map_with_result(|bytes| IrValue::from_bytes(t, &bytes))?;
            let p = load_incircuit(std_lib, layouter, t, &[p_val])?[0].clone();
            let expected_bytes = into_bytes_incircuit(std_lib, layouter, &p, 32)?;
            assert_equal_incircuit(std_lib, layouter, &expected_bytes, input_bytes)?;
            Ok(p)
        }

        JubjubScalar => Ok(std_lib.jubjub().scalar_from_le_bytes(layouter, bytes)?.into()),

        _ => Err(Error::Unsupported(
            Operation::FromBytes(t),
            vec![input_bytes.get_type()],
        )),
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use group::Group;
    use midnight_curves::{Fr as JubjubFr, JubjubSubgroup};

    use super::*;
    use crate::IrType;

    #[test]
    fn test_from_bytes() {
        use IrValue::*;
        let big = |x: u64| -> IrValue { num_bigint::BigUint::from(x).into() };

        assert_eq!(
            IrValue::from_bytes(IrType::Native, &[0]),
            Ok(Native(F::ZERO))
        );
        assert_eq!(
            IrValue::from_bytes(IrType::Native, &[255, 0]),
            Ok(Native(F::from(255)))
        );
        assert_eq!(
            IrValue::from_bytes(IrType::Native, &[0, 1, 0, 0]),
            Ok(Native(F::from(256)))
        );

        assert_eq!(
            IrValue::from_bytes(IrType::BigUint(39), &[0, 1, 0, 0, 0]),
            Err(Error::Unsupported(
                Operation::FromBytes(IrType::BigUint(39)),
                vec![IrType::Bytes(5)]
            ))
        );
        assert_eq!(
            IrValue::from_bytes(IrType::BigUint(40), &[0xee, 0xff, 0xc0, 0, 0]),
            Ok(big(0xc0ffee))
        );

        assert_eq!(
            IrValue::from_bytes(IrType::JubjubPoint, &{
                let mut id_bytes = vec![0u8; 32];
                id_bytes[0] = 1;
                id_bytes
            }),
            Ok(JubjubSubgroup::identity().into())
        );
        assert_eq!(
            IrValue::from_bytes(
                IrType::JubjubPoint,
                &[
                    203, 85, 12, 213, 56, 234, 12, 193, 19, 132, 128, 64, 142, 110, 170, 185, 179,
                    108, 97, 63, 13, 211, 247, 120, 79, 219, 110, 234, 131, 123, 19, 215
                ]
            ),
            Ok(JubjubSubgroup::generator().into())
        );

        assert_eq!(
            IrValue::from_bytes(IrType::JubjubScalar, &[1, 2, 3, 4]),
            Ok(JubjubScalar(JubjubFr::from(0x04030201)))
        );

        assert_eq!(
            IrValue::from_bytes(IrType::Bool, &[1]),
            Err(Error::Unsupported(
                Operation::FromBytes(IrType::Bool),
                vec![IrType::Bytes(1)]
            ))
        );
    }
}
