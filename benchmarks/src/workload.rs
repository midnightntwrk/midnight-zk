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

//! The interface between the workloads and the runner.

use std::fmt;

use ff::PrimeField;
use midnight_curves::Bls12;
use midnight_proofs::{poly::kzg::params::ParamsKZG, utils::SerdeFormat};
use midnight_zk_stdlib::{FflonkKZG, KZG, MidnightPCS, MidnightPK, MidnightVK, Relation};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use serde::{Deserialize, Serialize};
use sha2::Digest;

use crate::srs;

/// The hash function of the proof transcripts.
pub type TranscriptHash = blake2b_simd::State;

/// A polynomial commitment scheme to benchmark the prover under.
///
/// The fflonk schemes are named after `T_MAX`, the largest number of
/// polynomials they combine into one commitment: `fflonk-t4` is
/// `FflonkKZG<2>`. Plain KZG commits to each polynomial on its own, so it is
/// the baseline with `T_MAX = 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Pcs {
    /// Plain KZG.
    #[serde(rename = "kzg")]
    Kzg,
    /// Fflonk over KZG with up to 2 polynomials per commitment.
    #[serde(rename = "fflonk-t2")]
    FflonkT2,
    /// Fflonk over KZG with up to 4 polynomials per commitment.
    #[serde(rename = "fflonk-t4")]
    FflonkT4,
    /// Fflonk over KZG with up to 8 polynomials per commitment.
    #[serde(rename = "fflonk-t8")]
    FflonkT8,
    /// Fflonk over KZG with up to 16 polynomials per commitment.
    #[serde(rename = "fflonk-t16")]
    FflonkT16,
}

impl Pcs {
    /// All schemes, in reporting order.
    pub const ALL: [Pcs; 5] = [
        Pcs::Kzg,
        Pcs::FflonkT2,
        Pcs::FflonkT4,
        Pcs::FflonkT8,
        Pcs::FflonkT16,
    ];

    /// The name used on the command line and in results.
    pub fn name(self) -> &'static str {
        match self {
            Pcs::Kzg => "kzg",
            Pcs::FflonkT2 => "fflonk-t2",
            Pcs::FflonkT4 => "fflonk-t4",
            Pcs::FflonkT8 => "fflonk-t8",
            Pcs::FflonkT16 => "fflonk-t16",
        }
    }

    /// The logarithm of the number of polynomials per commitment.
    pub fn log2_t_max(self) -> u32 {
        match self {
            Pcs::Kzg => 0,
            Pcs::FflonkT2 => 1,
            Pcs::FflonkT4 => 2,
            Pcs::FflonkT8 => 3,
            Pcs::FflonkT16 => 4,
        }
    }

    /// The scheme that `PCS` implements.
    pub fn of<PCS: MidnightPCS>() -> Pcs {
        // The identifier of a stdlib scheme is its `LOG2_T_MAX`, 0 for KZG.
        Pcs::ALL[usize::from(PCS::ID)]
    }

    /// Whether circuits of size `2^k` fit in the available SRS under this
    /// scheme, which needs `T_MAX` times as many points as rows.
    pub fn fits(self, k: u32) -> bool {
        k + self.log2_t_max() <= srs::MAX_SRS_K
    }
}

impl fmt::Display for Pcs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A circuit of the standard set, together with a valid assignment.
pub trait Workload {
    /// A unique name in `snake_case`, used to select the workload.
    fn name(&self) -> &'static str;

    /// The schemes this workload can run under with the available SRS.
    fn supported_pcs(&self) -> Vec<Pcs>;

    /// Generates the keys and the witness. None of this is timed.
    fn setup(&self, pcs: Pcs) -> Box<dyn Prepared>;
}

/// A workload that is ready to prove.
pub trait Prepared: Send {
    /// The logarithm of the number of rows of the circuit.
    fn k(&self) -> u32;

    /// The SHA-256 digest of the serialized verifying key, in hexadecimal. It
    /// identifies the circuit across builds.
    fn vk_hash(&self) -> String;

    /// Generates a proof. This is the timed section, so it must do nothing
    /// but proving. It can be called repeatedly.
    fn prove(&mut self) -> Vec<u8>;

    /// Whether `proof` is a valid proof of the latest call to
    /// [`Prepared::prove`].
    fn verify(&self, proof: &[u8]) -> bool;
}

/// The hexadecimal SHA-256 digest of a verifying key.
///
/// The digest covers the serialized key and its transcript representation.
/// The latter commits to the constraint system, which the former omits.
pub fn vk_hash<PCS: MidnightPCS>(vk: &MidnightVK<PCS>) -> String {
    let mut bytes = Vec::new();
    vk.write(&mut bytes, SerdeFormat::RawBytes)
        .expect("writing to a Vec cannot fail");
    bytes.extend_from_slice(vk.vk().transcript_repr().to_repr().as_ref());
    sha2::Sha256::digest(&bytes).iter().map(|b| format!("{b:02x}")).collect()
}

/// A stdlib relation with a satisfying instance and witness.
#[derive(Clone, Debug)]
pub struct RelationCase<R: Relation> {
    /// The relation.
    pub relation: R,
    /// A public input of the relation.
    pub instance: R::Instance,
    /// A witness for `instance`.
    pub witness: R::Witness,
    /// The logarithm of the number of rows, or `None` for the smallest one
    /// that fits the circuit.
    pub k: Option<u32>,
}

/// Builds a workload out of a stdlib relation without committed instances.
///
/// `build` is called once per [`Workload::setup`] and must be deterministic.
pub fn relation_workload<R>(name: &'static str, build: fn() -> RelationCase<R>) -> Box<dyn Workload>
where
    R: Relation + Send + 'static,
    R::Instance: Send,
    R::Witness: Send,
{
    Box::new(RelationWorkload { name, build })
}

struct RelationWorkload<R: Relation> {
    name: &'static str,
    build: fn() -> RelationCase<R>,
}

impl<R> Workload for RelationWorkload<R>
where
    R: Relation + Send + 'static,
    R::Instance: Send,
    R::Witness: Send,
{
    fn name(&self) -> &'static str {
        self.name
    }

    fn supported_pcs(&self) -> Vec<Pcs> {
        let case = (self.build)();
        let k = case.k.unwrap_or_else(|| midnight_zk_stdlib::optimal_k(&case.relation));
        Pcs::ALL.into_iter().filter(|pcs| pcs.fits(k)).collect()
    }

    fn setup(&self, pcs: Pcs) -> Box<dyn Prepared> {
        let case = (self.build)();
        match pcs {
            Pcs::Kzg => primed(PreparedRelation::<R, KZG>::new(case)),
            Pcs::FflonkT2 => primed(PreparedRelation::<R, FflonkKZG<1>>::new(case)),
            Pcs::FflonkT4 => primed(PreparedRelation::<R, FflonkKZG<2>>::new(case)),
            Pcs::FflonkT8 => primed(PreparedRelation::<R, FflonkKZG<3>>::new(case)),
            Pcs::FflonkT16 => primed(PreparedRelation::<R, FflonkKZG<4>>::new(case)),
        }
    }
}

/// Proves once, untimed. The first proof fills the caches of the parameters,
/// such as the fflonk residue bases, which would otherwise be timed.
fn primed(mut prepared: impl Prepared + 'static) -> Box<dyn Prepared> {
    prepared.prove();
    Box::new(prepared)
}

struct PreparedRelation<R: Relation, PCS: MidnightPCS> {
    case: RelationCase<R>,
    params: ParamsKZG<Bls12>,
    vk: MidnightVK<PCS>,
    pk: MidnightPK<R, PCS>,
    rng: ChaCha8Rng,
}

impl<R: Relation, PCS: MidnightPCS> PreparedRelation<R, PCS> {
    fn new(case: RelationCase<R>) -> Self {
        let k = case.k.unwrap_or_else(|| midnight_zk_stdlib::optimal_k(&case.relation));
        let params = srs::load::<PCS>(k);
        let vk = midnight_zk_stdlib::setup_vk::<R, PCS>(&params, &case.relation);
        let pk = midnight_zk_stdlib::setup_pk(&case.relation, &vk);
        let rng = ChaCha8Rng::seed_from_u64(0);
        Self {
            case,
            params,
            vk,
            pk,
            rng,
        }
    }
}

impl<R, PCS> Prepared for PreparedRelation<R, PCS>
where
    R: Relation + Send,
    R::Instance: Send,
    R::Witness: Send,
    PCS: MidnightPCS,
{
    fn k(&self) -> u32 {
        self.vk.k() as u32
    }

    fn vk_hash(&self) -> String {
        vk_hash(&self.vk)
    }

    fn prove(&mut self) -> Vec<u8> {
        midnight_zk_stdlib::prove::<R, TranscriptHash, PCS>(
            &self.params,
            &self.pk,
            &self.case.relation,
            &self.case.instance,
            self.case.witness.clone(),
            &mut self.rng,
        )
        .expect("proving a satisfied relation cannot fail")
    }

    fn verify(&self, proof: &[u8]) -> bool {
        midnight_zk_stdlib::verify::<R, TranscriptHash, PCS>(
            &self.params.verifier_params(),
            &self.vk,
            &self.case.instance,
            None,
            proof,
        )
        .is_ok()
    }
}

#[cfg(test)]
mod tests {
    use midnight_circuits::{
        instructions::{AssignmentInstructions, PublicInputInstructions},
        types::AssignedNative,
    };
    use midnight_proofs::{
        circuit::{Layouter, Value},
        plonk::Error,
    };
    use midnight_zk_stdlib::{ZkStdLib, ZkStdLibArch};

    use super::*;

    type F = midnight_curves::Fq;

    /// Knowledge of a public value.
    #[derive(Clone, Default)]
    struct Identity;

    impl Relation for Identity {
        type Instance = F;
        type Witness = F;
        type Error = Error;

        fn format_instance(instance: &F) -> Result<Vec<F>, Error> {
            Ok(vec![*instance])
        }

        fn circuit(
            &self,
            std_lib: &ZkStdLib,
            layouter: &mut impl Layouter<F>,
            _instance: Value<F>,
            witness: Value<F>,
        ) -> Result<(), Error> {
            let x: AssignedNative<F> = std_lib.assign(layouter, witness)?;
            std_lib.constrain_as_public_input(layouter, &x)
        }

        fn used_chips(&self) -> ZkStdLibArch {
            ZkStdLibArch::default()
        }

        fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
            Ok(())
        }

        fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
            Ok(Identity)
        }
    }

    #[test]
    fn pcs_matches_the_stdlib_schemes() {
        assert_eq!(Pcs::of::<KZG>(), Pcs::Kzg);
        assert_eq!(Pcs::of::<FflonkKZG<1>>(), Pcs::FflonkT2);
        assert_eq!(Pcs::of::<FflonkKZG<2>>(), Pcs::FflonkT4);
        assert_eq!(Pcs::of::<FflonkKZG<3>>(), Pcs::FflonkT8);
        assert_eq!(Pcs::of::<FflonkKZG<4>>(), Pcs::FflonkT16);
        for pcs in Pcs::ALL {
            assert_eq!(pcs.name().strip_prefix("fflonk-t").map(|t| t.parse()), {
                (pcs != Pcs::Kzg).then(|| Ok(1u32 << pcs.log2_t_max()))
            });
            let json = serde_json::to_string(&pcs).unwrap();
            assert_eq!(json, format!("\"{pcs}\""));
            assert!(pcs.fits(srs::MAX_SRS_K - pcs.log2_t_max()));
            assert!(!pcs.fits(srs::MAX_SRS_K - pcs.log2_t_max() + 1));
        }
    }

    #[test]
    fn relation_workload_proves_under_every_pcs() {
        let workload = relation_workload("identity", || RelationCase {
            relation: Identity,
            instance: F::from(7),
            witness: F::from(7),
            k: None,
        });
        assert_eq!(workload.supported_pcs(), Pcs::ALL);
        for pcs in Pcs::ALL {
            let mut prepared = workload.setup(pcs);
            let proof = prepared.prove();
            assert!(prepared.verify(&proof), "{pcs}");
            assert!(!prepared.verify(&proof[1..]), "{pcs}");
            assert_eq!(prepared.vk_hash().len(), 64);
        }
    }
}
