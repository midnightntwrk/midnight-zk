use midnight_circuits::compact_std_lib::ZkStdLib;
use midnight_proofs::circuit::Layouter;
use sha2::Digest;

use crate::{
    types::CircuitValue,
    utils::{AssignedByte, F},
    Error, IrValue,
};

/// Computes SHA-512 off-circuit on the given input (presumably of type
/// `Bytes(n)` for some `n`).
///
/// # Errors
///
/// If the inputs are not of type `Bytes`.
pub fn sha512_offcircuit(input: &IrValue) -> Result<IrValue, Error> {
    let bytes: Vec<u8> = input.clone().try_into()?;
    let h: [u8; 64] = sha2::Sha512::digest(bytes).into();
    Ok(IrValue::Bytes(h.to_vec()))
}

/// Computes SHA-512 in-circuit on the given input (presumably of type
/// `Bytes(n)` for some `n`).
///
/// # Errors
///
/// If the inputs are not of type `Bytes`.
pub fn sha512_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    input: &CircuitValue,
) -> Result<CircuitValue, Error> {
    let bytes: Vec<AssignedByte> = input.clone().try_into()?;
    let h = std_lib.sha512(layouter, &bytes)?;
    Ok(CircuitValue::Bytes(h.to_vec()))
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::utils::constants::parse_bytes;

    fn bytes(s: &str) -> IrValue {
        parse_bytes(s).unwrap().into()
    }

    #[test]
    fn test_sha256_offcircuit() {
        use IrValue::*;

        assert_eq!(
            sha512_offcircuit(&Bytes(vec![])),
            Ok(bytes(
                "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
            ))
        );

        assert_eq!(
            sha512_offcircuit(&Bytes(vec![0xde, 0xad, 0xbe, 0xef])),
            Ok(bytes(
                "1284b2d521535196f22175d5f558104220a6ad7680e78b49fa6f20e57ea7b185d71ec1edb137e70eba528dedb141f5d2f8bb53149d262932b27cf41fed96aa7f"
            ))
        );

        assert_eq!(
            sha512_offcircuit(&BigUint(num_bigint::BigUint::from(42u64))),
            Err(Error::Other(
                "cannot convert BigUint(6) to \"Bytes\"".into()
            ))
        );
    }
}
