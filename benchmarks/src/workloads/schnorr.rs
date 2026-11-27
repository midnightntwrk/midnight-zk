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

//! The `schnorr` workload: verification of a Schnorr signature over Jubjub
//! with Poseidon as the hash function, both native to the proof system.

use ff::Field;
use group::Group;
use midnight_circuits::{
    ecc::native::AssignedScalarOfNativeCurve,
    hash::poseidon::PoseidonChip,
    instructions::{
        AssertionInstructions, AssignmentInstructions, DecompositionInstructions, EccInstructions,
        PublicInputInstructions, hash::HashCPU,
    },
    types::{AssignedNativePoint, Instantiable},
};
use midnight_curves::{Fr as JubjubScalar, JubjubAffine, JubjubExtended as Jubjub, JubjubSubgroup};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::workload::{RelationCase, Workload, relation_workload};

type F = midnight_curves::Fq;

/// A Schnorr signature `(s, e)`.
#[derive(Clone, Default)]
pub struct SchnorrSignature {
    s: JubjubScalar,
    e_bytes: [u8; 32],
}

type SchnorrPK = JubjubSubgroup;
type SchnorrSK = JubjubScalar;
type Message = F;

/// The scalar that the challenge bytes stand for.
fn challenge_scalar(e_bytes: &[u8; 32]) -> JubjubScalar {
    let mut buff = [0u8; 64];
    buff[..32].copy_from_slice(e_bytes);
    JubjubScalar::from_bytes_wide(&buff)
}

fn sign(message: Message, secret_key: &SchnorrSK, mut rng: impl RngCore) -> SchnorrSignature {
    let k = JubjubScalar::random(&mut rng);
    let r = JubjubSubgroup::generator() * k;

    let (rx, ry) = get_coords(&r);
    let (pkx, pky) = get_coords(&(JubjubSubgroup::generator() * secret_key));

    let e_bytes = PoseidonChip::hash(&[pkx, pky, rx, ry, message]).to_bytes_le();
    let s = k - challenge_scalar(&e_bytes) * secret_key;

    SchnorrSignature { s, e_bytes }
}

fn verify(sig: &SchnorrSignature, pk: &SchnorrPK, m: Message) -> bool {
    let rv = JubjubSubgroup::generator() * sig.s + pk * challenge_scalar(&sig.e_bytes);

    let (rx, ry) = get_coords(&rv);
    let (pkx, pky) = get_coords(pk);

    PoseidonChip::hash(&[pkx, pky, rx, ry, m]).to_bytes_le() == sig.e_bytes
}

/// The affine coordinates of a Jubjub point.
fn get_coords(point: &JubjubSubgroup) -> (F, F) {
    let point: &Jubjub = point.into();
    let point: JubjubAffine = point.into();
    (point.get_u(), point.get_v())
}

/// Knowledge of a Schnorr signature of a public message under a public key.
#[derive(Clone, Default)]
pub struct SchnorrExample;

impl Relation for SchnorrExample {
    type Instance = (SchnorrPK, Message);
    type Witness = SchnorrSignature;
    type Error = Error;

    fn format_instance((pk, msg): &Self::Instance) -> Result<Vec<F>, Error> {
        Ok([
            AssignedNativePoint::<Jubjub>::as_public_input(pk),
            vec![*msg],
        ]
        .concat())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let jubjub = std_lib.jubjub();

        let (pk_val, m_val) = instance.map(|(pk, m)| (pk, m)).unzip();
        let pk: AssignedNativePoint<Jubjub> = jubjub.assign(layouter, pk_val)?;
        let message = std_lib.assign(layouter, m_val)?;

        jubjub.constrain_as_public_input(layouter, &pk)?;
        std_lib.constrain_as_public_input(layouter, &message)?;

        let (sig_s_val, sig_e_bytes_val) = witness.map(|sig| (sig.s, sig.e_bytes)).unzip();
        let sig_s: AssignedScalarOfNativeCurve<Jubjub> = jubjub.assign(layouter, sig_s_val)?;
        let sig_e_bytes = std_lib.assign_many(layouter, &sig_e_bytes_val.transpose_array())?;

        let generator: AssignedNativePoint<Jubjub> =
            jubjub.assign_fixed(layouter, <JubjubSubgroup as Group>::generator())?;

        let sig_e = jubjub.scalar_from_le_bytes(layouter, &sig_e_bytes)?;

        // rv = s * G + e * pk
        let rv = jubjub.msm(layouter, &[sig_s, sig_e], &[generator, pk.clone()])?;

        let (pkx, pky) = (jubjub.x(layouter, &pk)?, jubjub.y(layouter, &pk)?);
        let (rx, ry) = (jubjub.x(layouter, &rv)?, jubjub.y(layouter, &rv)?);

        // ev = hash(pk.x || pk.y || rv.x || rv.y || m)
        let h = std_lib.poseidon(layouter, &[pkx, pky, rx, ry, message])?;
        let ev_bytes = std_lib.assigned_to_le_bytes(layouter, &h, None)?;

        assert_eq!(ev_bytes.len(), sig_e_bytes.len());
        (ev_bytes.iter().zip(sig_e_bytes.iter()))
            .try_for_each(|(ev, e)| std_lib.assert_equal(layouter, ev, e))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: true,
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(SchnorrExample)
    }
}

fn build() -> RelationCase<SchnorrExample> {
    let mut rng = ChaCha8Rng::seed_from_u64(0xf001ba11);

    let sk = JubjubScalar::random(&mut rng);
    let pk = JubjubSubgroup::generator() * sk;
    let message = F::random(&mut rng);
    let sig = sign(message, &sk, &mut rng);
    assert!(verify(&sig, &pk, message));

    RelationCase {
        relation: SchnorrExample,
        instance: (pk, message),
        witness: sig,
        k: None,
    }
}

/// The workloads defined in this module.
pub fn workloads() -> Vec<Box<dyn Workload>> {
    vec![relation_workload("schnorr", build)]
}

#[cfg(test)]
mod tests {
    use crate::workload::Pcs;

    /// Proves and verifies every workload under `pcs`, and checks that
    /// building it again gives the same circuit.
    fn check(pcs: Pcs) {
        for workload in super::workloads() {
            let name = workload.name();
            assert!(
                workload.supported_pcs().contains(&pcs),
                "{name} under {pcs}"
            );
            let mut prepared = workload.setup(pcs);
            let proof = prepared.prove();
            assert!(prepared.verify(&proof), "{name} under {pcs}");
            assert_eq!(
                prepared.vk_hash(),
                workload.setup(pcs).vk_hash(),
                "{name} under {pcs}"
            );
        }
    }

    #[test]
    fn kzg() {
        check(Pcs::Kzg);
    }

    #[test]
    fn fflonk() {
        check(Pcs::FflonkT4);
        check(Pcs::FflonkT16);
    }
}
