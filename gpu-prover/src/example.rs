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

//! The example relation the shipped binaries serve: knowledge of a Poseidon
//! preimage of three field elements (the `poseidon` example of the ZK
//! standard library).
//!
//! Input format: 96 bytes, three scalars of BLS12-381 in canonical 32-byte
//! little-endian form. The public input is their Poseidon hash, which the
//! prover computes from the witness.
//!
//! A service for another circuit implements [`ServedRelation`] for its own
//! relation type and calls [`crate::daemon::main`] and
//! [`crate::client::main`] with it.

use ff::{Field, PrimeField};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{AssignmentInstructions, PublicInputInstructions, hash::HashCPU},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};

use crate::ServedRelation;

type F = midnight_curves::Fq;

/// Knowledge of a Poseidon preimage of three field elements.
#[derive(Clone, Copy, Debug, Default)]
pub struct PoseidonPreimage;

impl Relation for PoseidonPreimage {
    type Instance = F;
    type Witness = [F; 3];
    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonPreimage)
    }
}

impl ServedRelation for PoseidonPreimage {
    fn name(&self) -> String {
        "poseidon-preimage".into()
    }

    fn decode_input(&self, input: &[u8]) -> Result<(F, [F; 3]), String> {
        if input.len() != 96 {
            return Err(format!("the input has {} bytes, 96 expected", input.len()));
        }
        let mut w = [F::ZERO; 3];
        for (i, c) in input.chunks_exact(32).enumerate() {
            let mut repr = <F as PrimeField>::Repr::default();
            repr.as_mut().copy_from_slice(c);
            w[i] = Option::from(F::from_repr(repr))
                .ok_or_else(|| format!("scalar {i} of the input is not canonical"))?;
        }
        let h = <PoseidonChip<F> as HashCPU<F, F>>::hash(&w);
        Ok((h, w))
    }
}

/// A valid example input from a seed (test and demo data, not secret).
pub fn example_input(seed: u64) -> Vec<u8> {
    let mut v = Vec::with_capacity(96);
    for i in 0..3u64 {
        let x = F::from(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(i + 1));
        v.extend_from_slice(x.to_repr().as_ref());
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_checks_length_and_canonical_form() {
        let r = PoseidonPreimage;
        assert!(r.decode_input(&example_input(1)).is_ok());
        assert!(r.decode_input(&[0u8; 95]).is_err());
        let e = r.decode_input(&[0xffu8; 96]).unwrap_err();
        assert!(e.contains("not canonical"));
        assert!(!e.contains("ff"));
    }
}
