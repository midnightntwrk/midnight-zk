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

//! A privately assigned verifying key, which must be bound to a trusted value
//! before it can be used.

use std::collections::BTreeMap;

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error},
    poly::PolynomialLabel,
};

use super::{
    AssignedVk, SelfEmulation, VerifierGadget, VerifyingKey, fixed_bases, pcs::InCircuitPCS,
    verifier_gadget::assemble_vk,
};
use crate::{
    field::AssignedNative,
    instructions::{
        AssertionInstructions, AssignmentInstructions, HashInstructions, PublicInputInstructions,
        hash::HashCPU,
    },
    types::Instantiable,
};

/// A privately assigned verifying key that has not yet been bound to anything.
///
/// Nothing about the witnessed key is constrained, beyond its commitments
/// being on the curve. The only way to use it is to bind it to a trusted hash,
/// through [`VerifierGadget::bind_vk_to_hash`], which returns the usable
/// [`AssignedVk`].
#[derive(Clone, Debug)]
pub struct UnboundVk<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    vk: AssignedVk<S, PCS>,
    // The commitments of `vk`, in the order of `vk_base_labels`. They are kept
    // here since they cannot be read back from `vk`'s PCS commitments.
    bases: Vec<S::AssignedPoint>,
}

/// The labels of the commitments of a verifying key, in the order they are
/// hashed by [`vk_hash`]: every fixed column, then every fixed permutation
/// polynomial.
fn vk_base_labels<F: ff::Field>(cs: &ConstraintSystem<F>) -> Vec<PolynomialLabel> {
    (0..cs.num_fixed_columns())
        .map(PolynomialLabel::Fixed)
        .chain((0..cs.permutation().columns.len()).map(PolynomialLabel::PermutationFixed))
        .collect()
}

/// The encoding of a verifying key as hash inputs:
/// `transcript_repr || k || omega || bases`.
fn vk_hash_inputs<S: SelfEmulation>(vk: &VerifyingKey<S>) -> Vec<S::F> {
    let domain = vk.get_domain();
    let bases = fixed_bases::<S>(vk);
    [
        vk.transcript_repr(),
        S::F::from(domain.k() as u64),
        domain.get_omega(),
    ]
    .into_iter()
    .chain(
        vk_base_labels(vk.cs())
            .iter()
            .flat_map(|label| S::AssignedPoint::as_public_input(&bases[label])),
    )
    .collect()
}

/// Computes the hash of a verifying key,
/// `H(transcript_repr || k || omega || bases)`.
///
/// This is the off-circuit counterpart of [`VerifierGadget::bind_vk_to_hash`].
pub fn vk_hash<S: SelfEmulation>(vk: &VerifyingKey<S>) -> S::F {
    <S::SpongeChip as HashCPU<S::F, S::F>>::hash(&vk_hash_inputs::<S>(vk))
}

impl<S: SelfEmulation> VerifierGadget<S> {
    /// Assigns a verifying key privately.
    ///
    /// Contrary to [`Self::assign_vk_as_public_input`], all the commitments of
    /// the key are witnessedThe resulting key must be bound before it can be
    /// used, see [`UnboundVk`].
    ///
    /// `cs` must be finalized, i.e. its selectors must have been converted to
    /// fixed columns, as in the constraint system of a verifying key.
    pub fn assign_private_vk<PCS: InCircuitPCS<S>>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        cs: &ConstraintSystem<S::F>,
        vk: Value<&VerifyingKey<S>>,
    ) -> Result<UnboundVk<S, PCS>, Error> {
        if cs.num_selectors() != 0 {
            return Err(Error::Synthesis(
                "the constraint system has selectors, it must be finalized".into(),
            ));
        }

        let domain = vk.map(|vk| vk.get_domain());
        let transcript_repr: AssignedNative<S::F> =
            self.scalar_chip.assign(layouter, vk.map(|vk| vk.transcript_repr()))?;
        let k: AssignedNative<S::F> =
            self.scalar_chip.assign(layouter, domain.map(|d| S::F::from(d.k() as u64)))?;
        let omega: AssignedNative<S::F> =
            self.scalar_chip.assign(layouter, domain.map(|d| d.get_omega()))?;

        let labels = vk_base_labels(cs);
        let base_values = vk.map(|vk| fixed_bases::<S>(vk));
        let bases = (labels.iter())
            .map(|label| {
                let value = base_values.as_ref().map(|bases| bases[label]);
                S::assign_without_subgroup_check(layouter, &self.curve_chip, value)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let domain = self.derive_domain(layouter, k, omega)?;
        let bases_map: BTreeMap<_, _> = labels.into_iter().zip(bases.iter().cloned()).collect();
        let vk = assemble_vk(domain, cs, transcript_repr, Some(&bases_map));

        Ok(UnboundVk { vk, bases })
    }

    /// In-circuit counterpart of [`vk_hash_inputs`].
    fn vk_hash_inputs<PCS: InCircuitPCS<S>>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        vk: &UnboundVk<S, PCS>,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        let mut inputs = vec![
            vk.vk.transcript_repr().clone(),
            vk.vk.k().clone(),
            vk.vk.omega().clone(),
        ];
        for base in vk.bases.iter() {
            inputs.extend(self.curve_chip.as_public_input(layouter, base)?);
        }
        Ok(inputs)
    }

    /// Binds the given verifying key by asserting that its [`vk_hash`] equals
    /// `expected`.
    ///
    /// `expected` must be trusted, e.g. a public input, a constant, part of a
    /// public set, or a witness bound by other means (e.g. added to a hash
    /// chain that the verifier recomputes).
    pub fn bind_vk_to_hash<PCS: InCircuitPCS<S>>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        vk: UnboundVk<S, PCS>,
        expected: &AssignedNative<S::F>,
    ) -> Result<AssignedVk<S, PCS>, Error> {
        let inputs = self.vk_hash_inputs(layouter, &vk)?;
        let hash = self.sponge_chip.hash(layouter, &inputs)?;
        self.scalar_chip.assert_equal(layouter, &hash, expected)?;
        Ok(vk.vk)
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use group::Group;
    use midnight_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, create_proof, keygen_pk, keygen_vk_with_k, prepare},
        poly::kzg::{KZGCommitmentScheme, commitment::KZGMultiCommitment, params::ParamsKZG},
        transcript::{CircuitTranscript, Transcript},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        ecc::foreign::weierstrass_chip::ForeignWeierstrassEccChip,
        field::{NativeChip, NativeGadget, decomposition::chip::P2RDecompositionChip},
        hash::poseidon::{PoseidonChip, PoseidonState},
        types::ComposableChip,
        verifier::{
            Accumulator, AssignedAccumulator, AssignedKZGCommitment, AssignedKZGMultiCommitment,
            BlstrsEmulation, InCircuitKZG,
            verifier_gadget::tests::{InnerCircuit, TestCircuit},
        },
    };

    type S = BlstrsEmulation;
    type F = <S as SelfEmulation>::F;
    type C = <S as SelfEmulation>::C;
    type E = <S as SelfEmulation>::Engine;

    #[derive(Clone, Debug)]
    struct PrivateVkCircuit {
        inner_cs: ConstraintSystem<F>,
        inner_vk: Value<VerifyingKey<S>>,
        inner_instances: Value<[F; 1]>,
        inner_proof: Value<Vec<u8>>,
        // The hash the key is bound to, given as public input.
        expected_hash: Value<F>,
    }

    impl Circuit<F> for PrivateVkCircuit {
        type Config = <TestCircuit as Circuit<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            TestCircuit::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
            let core_decomp_chip = P2RDecompositionChip::new(&config.1, &16);
            let native_gadget = NativeGadget::new(core_decomp_chip.clone(), native_chip.clone());
            let curve_chip =
                ForeignWeierstrassEccChip::new(&config.2, &native_gadget, &native_gadget);
            let poseidon_chip = PoseidonChip::new(&config.3, &native_chip);
            let verifier_chip =
                VerifierGadget::<S>::new(&curve_chip, &native_gadget, &poseidon_chip);

            let unbound_vk: UnboundVk<S, InCircuitKZG<S>> = verifier_chip.assign_private_vk(
                &mut layouter,
                &self.inner_cs,
                self.inner_vk.as_ref(),
            )?;

            let expected_hash =
                native_gadget.assign_as_public_input(&mut layouter, self.expected_hash)?;
            let inner_vk =
                verifier_chip.bind_vk_to_hash(&mut layouter, unbound_vk, &expected_hash)?;

            let committed_instance =
                AssignedKZGMultiCommitment(vec![AssignedKZGCommitment::assign(
                    &mut layouter,
                    &curve_chip,
                    Value::known(C::identity()),
                    PolynomialLabel::CommittedInstance(0),
                )?]);
            let inner_pi = native_gadget
                .assign_many(&mut layouter, &self.inner_instances.transpose_array())?;

            let mut acc = verifier_chip.prepare(
                &mut layouter,
                &inner_vk,
                &[committed_instance],
                &[&inner_pi],
                self.inner_proof.clone(),
            )?;
            acc.collapse(&mut layouter, &curve_chip, &native_gadget)?;
            verifier_chip.constrain_as_public_input(&mut layouter, &acc)?;

            core_decomp_chip.load(&mut layouter)
        }
    }

    struct Setup {
        vk: VerifyingKey<S>,
        other_vk: VerifyingKey<S>,
        output: F,
        proof: Vec<u8>,
        /// Public inputs of the collapsed inner accumulator.
        acc_pi: Vec<F>,
    }

    fn setup() -> Setup {
        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);

        let k = 10;
        let params = ParamsKZG::unsafe_setup(k, &mut rng);
        let vk = keygen_vk_with_k(&params, &InnerCircuit::default(), k).unwrap();
        let pk = keygen_pk(vk.clone(), &InnerCircuit::default()).unwrap();

        // A key with the same constraint system but a different domain.
        let other_params = ParamsKZG::unsafe_setup(k + 1, &mut rng);
        let other_vk = keygen_vk_with_k(&other_params, &InnerCircuit::default(), k + 1).unwrap();

        let preimage = [F::random(&mut rng), F::random(&mut rng)];
        let output = <PoseidonChip<F> as HashCPU<F, F>>::hash(&preimage);

        let proof = {
            let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
            create_proof::<F, KZGCommitmentScheme<E>, _, InnerCircuit>(
                &params,
                &pk,
                &InnerCircuit::from_witness(preimage),
                1,
                &[&[], &[output]],
                &mut transcript,
                &mut rng,
            )
            .unwrap();
            transcript.finalize()
        };

        let dual_msm = {
            let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&proof);
            prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                &vk,
                &[KZGMultiCommitment::commitment_to_zero(
                    PolynomialLabel::CommittedInstance(0),
                )],
                &[&[output]],
                &mut transcript,
            )
            .unwrap()
        };
        assert!(dual_msm.clone().check(&params.verifier_params()));

        // The private key's commitments are variable bases in-circuit, so only
        // `-G` stays fixed.
        let neg_g = BTreeMap::from([(PolynomialLabel::Custom("-G".into()), -C::generator())]);
        let mut acc = Accumulator::<S>::from_dual_msm(dual_msm, &neg_g);
        acc.collapse();
        let acc_pi = AssignedAccumulator::as_public_input(&acc);

        Setup {
            vk,
            other_vk,
            output,
            proof,
            acc_pi,
        }
    }

    fn run(setup: &Setup, expected_hash: F) -> Result<(), ()> {
        let circuit = PrivateVkCircuit {
            inner_cs: setup.vk.cs().clone(),
            inner_vk: Value::known(setup.vk.clone()),
            inner_instances: Value::known([setup.output]),
            inner_proof: Value::known(setup.proof.clone()),
            expected_hash: Value::known(expected_hash),
        };
        let public_inputs = [vec![expected_hash], setup.acc_pi.clone()].concat();
        let prover = MockProver::run(&circuit, vec![vec![], public_inputs]).unwrap();
        prover.verify().map_err(|_| ())
    }

    #[test]
    fn test_bind_vk_to_hash() {
        let setup = setup();
        let hash = vk_hash::<S>(&setup.vk);
        let other_hash = vk_hash::<S>(&setup.other_vk);
        assert_ne!(hash, other_hash);

        assert!(run(&setup, hash).is_ok());

        // The witnessed key does not match the expected hash.
        assert!(run(&setup, other_hash).is_err());
    }
}
