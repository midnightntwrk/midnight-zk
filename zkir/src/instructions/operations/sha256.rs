use midnight_circuits::compact_std_lib::ZkStdLib;
use midnight_proofs::circuit::Layouter;
use sha2::Digest;

use crate::{
    types::CircuitValue,
    utils::{AssignedByte, F},
    Error, IrValue,
};

/// Computes SHA-256 off-circuit on the given input (presumably of type
/// `Bytes(n)` for some `n`).
///
/// # Errors
///
/// If the inputs are not of type `Bytes`.
pub fn sha256_offcircuit(input: &IrValue) -> Result<IrValue, Error> {
    let bytes: Vec<u8> = input.clone().try_into()?;
    let h: [u8; 32] = sha2::Sha256::digest(bytes).into();
    Ok(IrValue::Bytes(h.to_vec()))
}

/// Computes SHA-256 in-circuit on the given input (presumably of type
/// `Bytes(n)` for some `n`).
///
/// # Errors
///
/// If the inputs are not of type `Bytes`.
pub fn sha256_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    input: &CircuitValue,
) -> Result<CircuitValue, Error> {
    let bytes: Vec<AssignedByte> = input.clone().try_into()?;
    let h = std_lib.sha2_256(layouter, &bytes)?;
    Ok(CircuitValue::Bytes(h.to_vec()))
}

#[cfg(test)]
mod tests {
    use ff::Field;

    use super::*;
    use crate::utils::constants::parse_bytes;

    fn bytes(s: &str) -> IrValue {
        parse_bytes(s).unwrap().into()
    }

    #[test]
    fn test_sha256_offcircuit() {
        use IrValue::*;

        assert_eq!(
            sha256_offcircuit(&Bytes(vec![])),
            Ok(bytes(
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            ))
        );

        assert_eq!(
            sha256_offcircuit(&Bytes(vec![0xde, 0xad, 0xbe, 0xef])),
            Ok(bytes(
                "5f78c33274e43fa9de5659265c1d917e25c03722dcb0b8d27db8d5feaa813953"
            ))
        );

        assert_eq!(
            sha256_offcircuit(&Native(F::ONE)),
            Err(Error::Other("cannot convert Native to \"Bytes\"".into()))
        );
    }
}
