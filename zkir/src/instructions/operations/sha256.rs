// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use midnight_proofs::circuit::Layouter;
use midnight_zk_stdlib::ZkStdLib;
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
