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

//! The `jwt` workload: validity of a 2.5 kB JWT credential signed with ECDSA
//! over secp256k1. It checks the signature of the issuer, decodes the
//! Base64 body, checks two attributes of the JSON and proves knowledge of the
//! secret key of the holder.

use midnight_circuits::{
    CircuitField,
    field::foreign::{AssignedField, params::MultiEmulationParams},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, Base64Instructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
        RangeCheckInstructions,
    },
    parsing::{DateFormat, Separator},
    testing_utils::ecdsa::{ECDSASig, Ecdsa, FromBase64, PublicKey},
    types::{AssignedByte, AssignedForeignPoint, AssignedNative, InnerValue, Instantiable},
};
use midnight_curves::k256::{Fq as K256Scalar, K256};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use sha2::Digest;

use crate::workload::{RelationCase, Workload, relation_workload};

type F = midnight_curves::Fq;

/// The credential, a JWT followed by a line feed.
const CREDENTIAL: &[u8] =
    include_bytes!("../../../zk_stdlib/examples/identity/jwt/credentials/2k-credential");

/// The public key of the issuer, who signed the credential.
const PUB_KEY: &[u8] =
    b"_bDXlQJ636HHOvXSe-flG0f-OkkRu8Jusm93PB2GBjoykg753nsOiW1vhEpCnxxybkMdarJLXIUJIYw1K2emQI";

/// The secret key of the holder of the credential, in big-endian.
const HOLDER_SK_BYTES: [u8; 32] = [
    0xc4, 0xe0, 0x5a, 0x8e, 0xc1, 0x68, 0x35, 0xce, 0x36, 0xf0, 0x9f, 0xcb, 0x94, 0x10, 0x08, 0x33,
    0xc8, 0x2d, 0xba, 0xe7, 0x85, 0xc0, 0x08, 0x36, 0x87, 0xc2, 0x51, 0xf4, 0x0a, 0xc6, 0xa5, 0x5e,
];

const HEADER_LEN: usize = 38;
const PAYLOAD_LEN: usize = 2463;

type PK = K256;
type Payload = [u8; PAYLOAD_LEN];
type SK = K256Scalar;

const VALID_NAME: &[u8] = b"Alice";
const NAME_LEN: usize = VALID_NAME.len();
const BIRTHDATE_LEN: usize = 10;
const COORD_LEN: usize = 43;

/// Birth dates must be before this one, written as `YYYYMMDD`.
const BIRTHDATE_LIMIT: u64 = 20_040_101;

/// Knowledge of a credential signed by the public issuer, whose holder is
/// called Alice, was born before 2004 and whose secret key is known.
#[derive(Clone, Default)]
pub struct FullCredential;

impl Relation for FullCredential {
    type Instance = PK;
    type Witness = (Payload, ECDSASig, SK);
    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(AssignedForeignPoint::<F, K256, MultiEmulationParams>::as_public_input(instance))
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1();
        let secp256k1_scalar = secp256k1_curve.scalar_field_chip();

        let b64_chip = std_lib.base64();

        let pk = secp256k1_curve.assign(layouter, instance)?;
        secp256k1_curve.constrain_as_public_input(layouter, &pk)?;

        let payload = witness.map(|(payload, _, _)| payload).transpose_array();
        let (sig, sk) = witness.map(|(_, sig, sk)| (sig, sk)).unzip();

        let payload = std_lib.assign_many(layouter, &payload)?;

        Self::verify_ecdsa(std_lib, layouter, pk, &payload, sig)?;

        let json =
            b64_chip.decode_base64(layouter, &payload[HEADER_LEN + 1..PAYLOAD_LEN], false)?;

        let name = Self::get_property(std_lib, layouter, &json, b"givenName", NAME_LEN)?;
        Self::assert_str_match(std_lib, layouter, &name, VALID_NAME)?;

        let birthdate = Self::get_property(std_lib, layouter, &json, b"birthDate", BIRTHDATE_LEN)?;
        Self::assert_date_before(std_lib, layouter, &birthdate, BIRTHDATE_LIMIT)?;

        // The public key of the holder.
        let x = Self::get_property(std_lib, layouter, &json, b"x", COORD_LEN)?;
        let y = Self::get_property(std_lib, layouter, &json, b"y", COORD_LEN)?;
        let x_val = b64_chip.decode_base64url(layouter, &x, false)?;
        let y_val = b64_chip.decode_base64url(layouter, &y, false)?;

        let x_coord = secp256k1_curve
            .base_field_chip()
            .assigned_from_be_bytes(layouter, &x_val[..32])?;
        let y_coord = secp256k1_curve
            .base_field_chip()
            .assigned_from_be_bytes(layouter, &y_val[..32])?;

        let holder_pk = secp256k1_curve.point_from_coordinates(layouter, &x_coord, &y_coord)?;
        let holder_sk: AssignedField<_, K256Scalar, MultiEmulationParams> =
            secp256k1_scalar.assign(layouter, sk)?;

        let generator: AssignedForeignPoint<_, K256, MultiEmulationParams> =
            secp256k1_curve.assign_fixed(layouter, K256::generator())?;
        let must_be_pk = secp256k1_curve.msm(layouter, &[holder_sk], &[generator])?;
        secp256k1_curve.assert_equal(layouter, &holder_pk, &must_be_pk)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            secp256k1: true,
            base64: true,
            automaton: true,
            nr_pow2range_cols: 3,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(FullCredential)
    }
}

impl FullCredential {
    /// Verifies the secp256k1 ECDSA signature of the given message.
    fn verify_ecdsa(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        pk: AssignedForeignPoint<F, K256, MultiEmulationParams>,
        message: &[AssignedByte<F>],
        sig: Value<ECDSASig>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1();
        let secp256k1_scalar = secp256k1_curve.scalar_field_chip();
        let secp256k1_base = secp256k1_curve.base_field_chip();

        let msg_hash: AssignedField<_, _, _> = {
            let hash_bytes = std_lib.sha2_256(layouter, message)?;
            secp256k1_scalar.assigned_from_be_bytes(layouter, &hash_bytes)?
        };

        let r_value = sig.map(|sig| sig.get_r());
        let r_le_bytes = std_lib.assign_many(layouter, &r_value.transpose_array())?;
        let s = secp256k1_scalar.assign(layouter, sig.map(|sig| sig.get_s()))?;

        let r_as_scalar = secp256k1_scalar.assigned_from_le_bytes(layouter, &r_le_bytes)?;
        let r_as_base = secp256k1_base.assigned_from_le_bytes(layouter, &r_le_bytes)?;

        // lhs.x = r, for lhs = (msg_hash * s^-1) * G + (r * s^-1) * PK.
        let r_over_s = secp256k1_scalar.div(layouter, &r_as_scalar, &s)?;
        let m_over_s = secp256k1_scalar.div(layouter, &msg_hash, &s)?;

        let generator = secp256k1_curve.assign_fixed(layouter, K256::generator())?;
        let lhs = secp256k1_curve.msm(layouter, &[m_over_s, r_over_s], &[generator, pk])?;
        let lhs_x = secp256k1_curve.x(layouter, &lhs)?;

        secp256k1_base.assert_equal(layouter, &lhs_x, &r_as_base)
    }

    /// Returns the value, of `value_len` bytes, of the string field
    /// `field_name` of the JSON `cred`, after checking that the snippet
    /// `"<field_name>":"<value>"` appears in it.
    fn get_property(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        cred: &[AssignedByte<F>],
        field_name: &[u8],
        value_len: usize,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let field_prefix: Vec<u8> = [b"\"".as_slice(), field_name, b"\":\""].concat();
        let snippet_len = field_prefix.len() + value_len + 1;

        // The position of the snippet is found off-circuit and given as a hint.
        let seq: Value<Vec<u8>> = Value::from_iter(cred.iter().map(|b| b.value()));
        let (value_raw, idx_val): (Value<Vec<u8>>, Value<F>) = seq
            .map(|d| {
                let pos = find_subsequence(&d, &field_prefix)
                    .expect("Field prefix should appear in credential");
                assert!(
                    pos + snippet_len <= d.len(),
                    "Snippet exceeds credential length"
                );
                let value =
                    d[pos + field_prefix.len()..pos + field_prefix.len() + value_len].to_vec();
                (value, F::from(pos as u64))
            })
            .unzip();

        let prefix_bytes: Vec<AssignedByte<F>> =
            std_lib.assign_many_fixed(layouter, &field_prefix)?;
        let value_bytes: Vec<AssignedByte<F>> =
            std_lib.assign_many(layouter, value_raw.transpose_vec(value_len).as_slice())?;
        let closing_quote: AssignedByte<F> = std_lib.assign_fixed(layouter, b'"')?;

        let snippet_bytes: Vec<AssignedByte<F>> = prefix_bytes
            .into_iter()
            .chain(value_bytes.iter().cloned())
            .chain(std::iter::once(closing_quote))
            .collect();
        assert_eq!(snippet_bytes.len(), snippet_len);

        let idx: AssignedNative<F> = std_lib.assign(layouter, idx_val)?;
        std_lib.scanner().check_bytes(layouter, cred, &idx, &snippet_bytes)?;

        Ok(value_bytes)
    }

    fn assert_str_match(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        str1: &[AssignedByte<F>],
        str2: &[u8],
    ) -> Result<(), Error> {
        assert_eq!(
            str1.len(),
            str2.len(),
            "Compared string lengths must match."
        );
        for (b1, b2) in str1.iter().zip(str2.iter()) {
            std_lib.assert_equal_to_fixed(layouter, b1, *b2)?
        }
        Ok(())
    }

    /// Asserts that `date`, formatted as `YYYY-MM-DD`, is before `limit`,
    /// given as the integer `YYYYMMDD`.
    fn assert_date_before(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        date: &[AssignedByte<F>],
        limit: u64,
    ) -> Result<(), Error> {
        let format = (DateFormat::YYYYMMDD, Separator::Sep('-'));
        let date = std_lib.parser().date_to_int(layouter, date, format, None)?;
        std_lib.assert_lower_than_fixed(layouter, &date, &limit.into())
    }
}

/// The index of the first occurrence of `subseq` in `seq`.
fn find_subsequence(seq: &[u8], subseq: &[u8]) -> Option<usize> {
    seq.windows(subseq.len()).position(|window| window == subseq)
}

/// Splits a JWT `header.body.signature` into the signed payload
/// `header.body` and the signature.
fn split_blob(blob: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let mut parts = blob.split(|c| *c == b'.');

    let header = parts.next().unwrap();
    let body = parts.next().unwrap();
    let signature = parts.next().unwrap();
    assert!(parts.next().is_none());

    ([header, b".", body].concat(), signature.to_vec())
}

fn build() -> RelationCase<FullCredential> {
    let issuer_pk = PublicKey::from_base64(PUB_KEY).expect("a Base64 public key");

    let jwt = CREDENTIAL.strip_suffix(b"\n").expect("a final line feed");
    let (payload, signature) = split_blob(jwt);
    let signature = ECDSASig::from_base64(&signature).expect("a Base64 signature");

    let payload_hash: [u8; 32] = sha2::Sha256::digest(&payload).into();
    let payload_hash = K256Scalar::from_bytes_be(&payload_hash).expect("a scalar of secp256k1");
    assert!(Ecdsa::verify(&issuer_pk, &payload_hash, &signature));

    let payload: Payload = payload.try_into().expect("a payload of PAYLOAD_LEN bytes");
    let holder_sk = K256Scalar::from_bytes_be(&HOLDER_SK_BYTES).expect("a scalar of secp256k1");

    RelationCase {
        relation: FullCredential,
        instance: issuer_pk,
        witness: (payload, signature, holder_sk),
        k: None,
    }
}

/// The workloads defined in this module.
pub fn workloads() -> Vec<Box<dyn Workload>> {
    vec![relation_workload("jwt", build)]
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
    fn fflonk_does_not_fit_the_srs() {
        for workload in super::workloads() {
            assert_eq!(workload.supported_pcs(), [Pcs::Kzg]);
        }
    }
}
