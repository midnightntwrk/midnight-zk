use group::{
    ff::{Field, PrimeField},
    GroupEncoding,
};
use midnight_circuits::{
    compact_std_lib::ZkStdLib,
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ConversionInstructions,
        DecompositionInstructions, EccInstructions,
    },
};
use midnight_proofs::circuit::Layouter;

use crate::{
    types::{CircuitValue, IrValue},
    utils::{AssignedNative, F},
    Error, Operation,
};

impl IrValue {
    /// Converts the given value into n bytes.
    ///
    /// In the case of prime field values or big integers, the bytes represent
    /// the underlying integer in little-endian order.
    ///
    /// In the case of Jubjub points, the `n` must be exactly `32`. We follow
    /// the `repr_J` encoding as defined in
    /// [Zcash specification 5.4.9.3 - JubJub](https://zips.z.cash/protocol/protocol.pdf#jubjub).
    ///
    /// # Errors
    ///
    /// If the conversion is not possible.
    pub fn into_bytes(self, n: usize) -> Result<IrValue, Error> {
        use IrValue::*;
        match self {
            Native(x) => {
                let bytes = x.to_bytes_le();
                if n as u32 > F::NUM_BITS.div_ceil(8) || bytes[n..].iter().any(|&b| b != 0) {
                    Err(Error::Other(format!("cannot convert {x} to Bytes({n})")))
                } else {
                    Ok(bytes[..n].to_vec().into())
                }
            }

            BigUint(big) => {
                let bytes = big.to_bytes_le();
                if bytes.len() > n {
                    Err(Error::Other(format!("cannot convert {big} to Bytes({n})")))
                } else {
                    let mut result = bytes;
                    result.resize(n, 0);
                    Ok(result.into())
                }
            }

            JubjubPoint(p) if n == 32 => Ok(p.to_bytes().to_vec().into()),

            _ => Err(Error::Unsupported(
                Operation::IntoBytes(n),
                vec![self.get_type()],
            )),
        }
    }
}

/// Converts the given value into n bytes, in-circuit.
///
/// In the case of field values or big integers, the bytes are in little-endian
/// order.
///
/// In the case of Jubjub points, the `n` must be exactly `32`. We follow
/// the `repr_J` encoding as defined in
/// [Zcash specification 5.4.9.3 - JubJub](https://zips.z.cash/protocol/protocol.pdf#jubjub).
///
/// # Unsatisfiable
///
/// If the input value is of type (field or BigUint) and its actual value is
/// greater than or equal to 2^(8n), the circuit will become unsatisfiable.
///
/// # Errors
///
/// If the conversion is not possible.
pub fn into_bytes_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    input: &CircuitValue,
    n: usize,
) -> Result<CircuitValue, Error> {
    use CircuitValue::*;
    match input {
        Native(x) => {
            let bytes = std_lib.assigned_to_le_bytes(layouter, x, Some(n))?;
            Ok(bytes.to_vec().into())
        }

        BigUint(big) => {
            let mut bytes = std_lib.biguint().to_le_bytes(layouter, big)?;

            bytes[n..]
                .iter()
                .try_for_each(|b| std_lib.assert_equal_to_fixed(layouter, b, 0u8))?;

            let zero = std_lib.assign_fixed(layouter, 0u8)?;
            bytes.resize(n, zero);

            Ok(bytes.to_vec().into())
        }

        JubjubPoint(p) if n == 32 => {
            let u = std_lib.jubjub().x_coordinate(p);
            let v = std_lib.jubjub().y_coordinate(p);

            let mut bytes = std_lib.assigned_to_le_bytes(layouter, &v, Some(32))?;
            let u0: AssignedNative = std_lib.sgn0(layouter, &u)?.into();

            let byte_31: AssignedNative = bytes[31].clone().into();
            let updated_byte_31 = std_lib.linear_combination(
                layouter,
                &[(F::ONE, byte_31), (F::from(128), u0)],
                F::ZERO,
            )?;

            bytes[31] = std_lib.convert(layouter, &updated_byte_31)?;
            Ok(bytes.to_vec().into())
        }

        _ => Err(Error::Unsupported(
            Operation::IntoBytes(n),
            vec![input.get_type()],
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
    fn test_into_bytes() {
        use IrValue::*;
        let big = |x: u64| -> IrValue { num_bigint::BigUint::from(x).into() };

        assert_eq!(Native(F::ZERO).into_bytes(1), Ok(vec![0].into()));
        assert_eq!(Native(F::from(255)).into_bytes(2), Ok(vec![255, 0].into()));
        assert_eq!(Native(F::from(256)).into_bytes(3), Ok(vec![0, 1, 0].into()));
        assert_eq!(
            Native(F::from(256)).into_bytes(1),
            Err(Error::Other(format!(
                "cannot convert {} to Bytes(1)",
                F::from(256)
            )))
        );

        assert_eq!(big(256).into_bytes(5), Ok(vec![0, 1, 0, 0, 0].into()));
        assert_eq!(
            big(0xdeadbeef).into_bytes(5),
            Ok(vec![0xef, 0xbe, 0xad, 0xde, 0].into())
        );
        assert_eq!(
            big(0xdeadbeef).into_bytes(3),
            Err(Error::Other("cannot convert 3735928559 to Bytes(3)".into()))
        );

        assert_eq!(
            JubjubPoint(JubjubSubgroup::identity()).into_bytes(32),
            Ok({
                let mut id_bytes = vec![0u8; 32];
                id_bytes[0] = 1;
                id_bytes.into()
            })
        );
        assert_eq!(
            JubjubPoint(JubjubSubgroup::generator()).into_bytes(32),
            Ok(vec![
                203, 85, 12, 213, 56, 234, 12, 193, 19, 132, 128, 64, 142, 110, 170, 185, 179, 108,
                97, 63, 13, 211, 247, 120, 79, 219, 110, 234, 131, 123, 19, 215
            ]
            .into())
        );
        assert_eq!(
            JubjubPoint(JubjubSubgroup::identity()).into_bytes(33),
            Err(Error::Unsupported(
                Operation::IntoBytes(33),
                vec![IrType::JubjubPoint]
            ))
        );

        assert_eq!(
            JubjubScalar(JubjubFr::ONE).into_bytes(32),
            Err(Error::Unsupported(
                Operation::IntoBytes(32),
                vec![IrType::JubjubScalar]
            ))
        );
    }
}
