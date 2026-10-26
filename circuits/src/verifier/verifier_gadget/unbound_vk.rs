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

//! A privately assigned verifying key, which must be bound before it can be
//! used: its hash is computed in-circuit and constrained to equal a trusted
//! value.
//!
//! # WARNING
//!
//! Binding only guarantees that the key's hash equals the given value. It is
//! the responsibility of the caller to guarantee the integrity of that value
//! (e.g. by making it a public input or a constant). Not binding the key, or
//! binding it to an unconstrained witness, results in an overall relation of
//! the form "I know a proof of *some* statement", which is trivially
//! satisfiable and thus meaningless.

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error},
};

use crate::{
    field::AssignedNative,
    instructions::{
        AssertionInstructions, AssignmentInstructions, HashInstructions, hash::HashCPU,
    },
    types::Instantiable,
    verifier::{
        AssignedVk, SelfEmulation, VerifierGadget, VerifyingKey,
        pcs::{AssignedCommitment, InCircuitPCS},
    },
};

/// A privately assigned verifying key that has not yet been bound to anything.
///
/// Nothing about the witnessed key is constrained, beyond its commitments
/// being on the curve. It must be bound through
/// [`VerifierGadget::bind_vk_to_hash`], which constrains its [`vk_hash`] to
/// equal a trusted value and returns the usable [`AssignedVk`].
///
/// Its commitments are witnessed. Keys with fixed commitments (not witnessed
/// in-circuit) must be assigned with
/// [`VerifierGadget::assign_vk_as_public_input`] or
/// [`VerifierGadget::assign_fixed_vk`] instead.
#[derive(Clone, Debug)]
pub struct UnboundVk<S: SelfEmulation>(AssignedVk<S>);

/// Computes the hash of a verifying key,
/// `H(transcript_repr || k || omega || phase0_commitment)`.
///
/// This is the off-circuit counterpart of [`VerifierGadget::bind_vk_to_hash`].
pub fn vk_hash<S: SelfEmulation>(vk: &VerifyingKey<S>) -> S::F {
    let domain = vk.get_domain();
    let inputs = [
        vec![
            vk.transcript_repr(),
            S::F::from(domain.k() as u64),
            domain.get_omega(),
        ],
        AssignedCommitment::<S>::as_public_input(vk.phase0_commitment()),
    ]
    .concat();
    <S::SpongeChip as HashCPU<S::F, S::F>>::hash(&inputs)
}

impl<S: SelfEmulation> VerifierGadget<S> {
    /// Assigns a verifying key privately.
    ///
    /// The resulting key must be bound before it can be used, see
    /// [`UnboundVk`].
    ///
    /// The circuit layout is taken off-circuit from `cs`, so `vk` may be
    /// unknown (e.g. at keygen). `cs` must be the constraint system of the key
    /// whose hash it will be bound to; this is not checked in-circuit.
    ///
    /// `cs` must be finalized, i.e. its selectors must have been converted to
    /// fixed columns, as in the constraint system of a verifying key.
    pub fn assign_unbound_vk(
        &self,
        layouter: &mut impl Layouter<S::F>,
        vk: Value<&VerifyingKey<S>>,
        cs: &ConstraintSystem<S::F>,
    ) -> Result<UnboundVk<S>, Error> {
        let transcript_repr: AssignedNative<S::F> =
            self.scalar_chip.assign(layouter, vk.map(|vk| vk.transcript_repr()))?;
        let k: AssignedNative<S::F> = self.scalar_chip.assign(
            layouter,
            vk.map(|vk| S::F::from(vk.get_domain().k() as u64)),
        )?;
        let omega: AssignedNative<S::F> =
            self.scalar_chip.assign(layouter, vk.map(|vk| vk.get_domain().get_omega()))?;
        let phase0_commitment = S::PCS::assign_commitment(
            layouter,
            &self.curve_chip,
            vk.map(|vk| vk.phase0_commitment().clone()),
            &cs.fixed_polys_labels(),
        )?;

        let domain = self.derive_domain(layouter, k, omega)?;
        let vk = AssignedVk {
            phase0_commitment,
            ..self.assemble_vk(cs, domain, transcript_repr)?
        };

        Ok(UnboundVk(vk))
    }

    /// Binds the given verifying key by asserting that its [`vk_hash`] equals
    /// `expected`.
    ///
    /// # WARNING
    ///
    /// It is the responsibility of the caller to guarantee the integrity of
    /// `expected`, e.g. by making it a public input, a constant, a member of a
    /// public set, or a witness bound by other means (such as a hash chain that
    /// the verifier recomputes).
    pub fn bind_vk_to_hash(
        &self,
        layouter: &mut impl Layouter<S::F>,
        vk: UnboundVk<S>,
        expected: &AssignedNative<S::F>,
    ) -> Result<AssignedVk<S>, Error> {
        let vk = vk.0;
        let mut inputs = vec![
            vk.transcript_repr().clone(),
            vk.k().clone(),
            vk.omega().clone(),
        ];
        inputs.extend(S::PCS::commitment_as_public_input(
            layouter,
            &self.curve_chip,
            &vk.phase0_commitment,
        )?);
        let hash = self.sponge_chip.hash(layouter, &inputs)?;
        self.scalar_chip.assert_equal(layouter, &hash, expected)?;
        Ok(vk)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ff::Field;
    use group::Group;
    use midnight_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, create_proof, keygen_pk, keygen_vk_with_k, prepare},
        poly::{
            PolynomialLabel,
            kzg::{KZGCommitmentScheme, params::ParamsKZG},
        },
        transcript::{CircuitTranscript, Transcript},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        ecc::foreign::weierstrass_chip::ForeignWeierstrassEccChip,
        field::{NativeChip, NativeGadget, decomposition::chip::P2RDecompositionChip},
        hash::poseidon::{PoseidonChip, PoseidonState},
        instructions::PublicInputInstructions,
        types::ComposableChip,
        verifier::{
            Accumulator, AssignedAccumulator, BlstrsEmulation,
            verifier_gadget::tests::{InnerCircuit, TestCircuit},
        },
    };

    type S = BlstrsEmulation;
    type F = <S as SelfEmulation>::F;
    type C = <S as SelfEmulation>::C;
    type E = <S as SelfEmulation>::Engine;

    #[derive(Clone, Debug)]
    struct UnboundVkCircuit {
        inner_cs: ConstraintSystem<F>,
        inner_vk: Value<VerifyingKey<S>>,
        inner_instances: Value<[F; 1]>,
        inner_proof: Value<Vec<u8>>,
        // The hash the key is bound to, given as public input.
        expected_hash: Value<F>,
    }

    impl Circuit<F> for UnboundVkCircuit {
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

            let unbound_vk: UnboundVk<S> = verifier_chip.assign_unbound_vk(
                &mut layouter,
                self.inner_vk.as_ref(),
                &self.inner_cs,
            )?;

            let expected_hash =
                native_gadget.assign_as_public_input(&mut layouter, self.expected_hash)?;
            let inner_vk =
                verifier_chip.bind_vk_to_hash(&mut layouter, unbound_vk, &expected_hash)?;

            let inner_pi = native_gadget
                .assign_many(&mut layouter, &self.inner_instances.transpose_array())?;

            let mut acc = verifier_chip.prepare(
                &mut layouter,
                &inner_vk,
                &[],
                &[&[], &inner_pi],
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
                0,
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
                &[],
                &[&[], &[output]],
                &mut transcript,
            )
            .unwrap()
        };
        assert!(dual_msm.clone().check(&params.verifier_params()));

        // The private key's commitments are variable bases in-circuit, so only
        // `-G` stays fixed.
        let fixed_bases = BTreeMap::from([(PolynomialLabel::Custom("-G".into()), -C::generator())]);
        let mut acc = Accumulator::<S>::from_dual_msm(dual_msm, &fixed_bases);
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
        let circuit = UnboundVkCircuit {
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
