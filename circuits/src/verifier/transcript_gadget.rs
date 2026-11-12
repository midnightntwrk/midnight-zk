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

//! Transcript gadget module, for in-circuit Fiat-Shamir.
//! Shall we adopt the [SAFE API](https://hackmd.io/bHgsH6mMStCVibM_wYvb2w)?

use std::io;

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    transcript::{CircuitTranscript, Hashable, Transcript, TranscriptHash},
};

use crate::{
    CircuitField,
    hash::poseidon::{PoseidonChip, PoseidonState, constants::PoseidonField},
    instructions::{AssignmentInstructions, SpongeInstructions},
    types::AssignedNative,
    verifier::ScalarChip,
};

type SpongeState<F> =
    <PoseidonChip<F> as SpongeInstructions<F, AssignedNative<F>, AssignedNative<F>>>::State;

/// Gadget used to run the transcript reader in-circuit.
#[derive(Clone, Debug)]
pub struct PoseidonTranscriptGadget<F: PoseidonField> {
    scalar_chip: ScalarChip<F>,
    sponge_chip: PoseidonChip<F>,
    sponge_state: Option<SpongeState<F>>,
    // Track the number of field elements we have in the buffer.
    input_len: usize,
    // Transcript reader is included, to help parse the proof. This parsing
    // *does not* need to be verified in-circuit.
    transcript_reader: Option<CircuitTranscript<PoseidonState<F>>>,
}

impl<F: PoseidonField> PoseidonTranscriptGadget<F> {
    /// Creates a new `PoseidonTranscriptGadget` from the corresponding chips.
    pub fn new(scalar_chip: &ScalarChip<F>, sponge_chip: &PoseidonChip<F>) -> Self {
        Self {
            scalar_chip: scalar_chip.clone(),
            sponge_chip: sponge_chip.clone(),
            sponge_state: None,
            input_len: 0,
            transcript_reader: None,
        }
    }
}

/// An in-circuit Fiat-Shamir transcript.
///
/// Analog of [`midnight_proofs::transcript::Transcript`] for the in-circuit
/// verifier.
pub trait InCircuitTranscript<F: CircuitField>: Clone {
    /// The off-circuit hash function of the transcript, which the proof is
    /// parsed with.
    type Hash: TranscriptHash;

    /// Initialises the transcript, by initialising the sponge buffer, from a
    /// given witnessed proof in the form of `Value<Vec<u8>>`.
    fn init_with_proof(
        &mut self,
        layouter: &mut impl Layouter<F>,
        proof: Value<Vec<u8>>,
    ) -> Result<(), Error>;

    /// Absorbs the given field elements into the transcript.
    fn common(
        &mut self,
        layouter: &mut impl Layouter<F>,
        inputs: &[AssignedNative<F>],
    ) -> Result<(), Error>;

    /// Absorbs a scalar into the transcript.
    fn common_scalar(
        &mut self,
        layouter: &mut impl Layouter<F>,
        scalar: &AssignedNative<F>,
    ) -> Result<(), Error> {
        self.common(layouter, std::slice::from_ref(scalar))
    }

    /// Derives a scalar challenge from the current transcript.
    fn squeeze_challenge(
        &mut self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<AssignedNative<F>, Error>;

    /// Reads a value from the proof, off-circuit. The value is neither
    /// constrained nor absorbed into the transcript.
    fn read_value<V: Hashable<Self::Hash>>(&mut self) -> io::Result<V>;

    /// Reads a scalar from the reader buffer, and adds it to the transcript.
    /// Think of the read scalar as a witness freely chosen by the prover.
    fn read_scalar(&mut self, layouter: &mut impl Layouter<F>) -> Result<AssignedNative<F>, Error>
    where
        F: Hashable<Self::Hash>;
}

impl<F: PoseidonField> InCircuitTranscript<F> for PoseidonTranscriptGadget<F> {
    type Hash = PoseidonState<F>;

    fn init_with_proof(
        &mut self,
        layouter: &mut impl Layouter<F>,
        proof: Value<Vec<u8>>,
    ) -> Result<(), Error> {
        self.sponge_state = Some(self.sponge_chip.init(layouter, None)?);

        // Unwrapping the witness. The amount of points read from the proof is
        // fixed for a given `Architecture`, and does not depend on the size of
        // the proof.
        // The caveat with this approach is that our in-circuit verifier will not
        // be able to verify that the proof did not include extra bytes after
        // all the relevant bytes have been read. This is not an issue anyway.
        let mut proof_bytes = Vec::new();
        proof.map(|pi| proof_bytes.extend_from_slice(&pi));
        self.transcript_reader = Some(CircuitTranscript::init_from_bytes(&proof_bytes));

        Ok(())
    }

    fn common(
        &mut self,
        layouter: &mut impl Layouter<F>,
        inputs: &[AssignedNative<F>],
    ) -> Result<(), Error> {
        self.input_len += inputs.len();
        let state = self.sponge_state.as_mut().expect("You must init the transcript gadget");
        self.sponge_chip.absorb(layouter, state, inputs)
    }

    fn squeeze_challenge(
        &mut self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let state = self.sponge_state.as_mut().expect("You must init the transcript gadget");
        self.sponge_chip.squeeze(layouter, state)
    }

    fn read_value<V: Hashable<PoseidonState<F>>>(&mut self) -> io::Result<V> {
        let reader = self.transcript_reader.as_mut().expect("You must init the transcript gadget");
        reader.read()
    }

    fn read_scalar(&mut self, layouter: &mut impl Layouter<F>) -> Result<AssignedNative<F>, Error>
    where
        F: Hashable<Self::Hash>,
    {
        // If an error, do not fail, assign a default scalar instead.
        // (This allows us to parse dummy proofs.)
        let scalar = Value::known(self.read_value().unwrap_or(F::ZERO));

        let assigned_scalar = self.scalar_chip.assign(layouter, scalar)?;
        self.common_scalar(layouter, &assigned_scalar)?;

        Ok(assigned_scalar)
    }
}

#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::{Advice, Column, ConstraintSystem, Fixed, Instance};

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;

#[cfg(any(test, feature = "testing"))]
impl<F: PoseidonField> FromScratch<F> for PoseidonTranscriptGadget<F>
where
    ScalarChip<F>: FromScratch<F>,
    PoseidonChip<F>: FromScratch<F>,
{
    type Config = (
        <ScalarChip<F> as FromScratch<F>>::Config,
        <PoseidonChip<F> as FromScratch<F>>::Config,
    );

    fn new_from_scratch(config: &Self::Config) -> Self {
        let scalar_chip = ScalarChip::<F>::new_from_scratch(&config.0);
        let sponge_chip = PoseidonChip::<F>::new_from_scratch(&config.1);
        PoseidonTranscriptGadget::new(&scalar_chip, &sponge_chip)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.scalar_chip.load_from_scratch(layouter)?;
        self.sponge_chip.load_from_scratch(layouter)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        advice_columns: &mut Vec<Column<Advice>>,
        fixed_columns: &mut Vec<Column<Fixed>>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        (
            ScalarChip::<F>::configure_from_scratch(
                meta,
                advice_columns,
                fixed_columns,
                instance_columns,
            ),
            PoseidonChip::<F>::configure_from_scratch(
                meta,
                advice_columns,
                fixed_columns,
                instance_columns,
            ),
        )
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use group::Group;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
        transcript::{CircuitTranscript, Transcript},
    };
    use rand::rngs::OsRng;

    use super::*;
    use crate::instructions::{PublicInputInstructions, ecc::EccInstructions};

    const SIZE: usize = 12;

    type F = midnight_curves::Fq;
    type C = midnight_curves::G1Projective;
    type CurveChip = crate::verifier::CurveChip<midnight_curves::Bls12>;

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
        points: Value<[C; SIZE]>,
        scalars: Value<[F; SIZE]>,
    }

    type Config = (
        <PoseidonTranscriptGadget<F> as FromScratch<F>>::Config,
        <CurveChip as FromScratch<F>>::Config,
    );

    fn configure(meta: &mut ConstraintSystem<F>) -> Config {
        let instance_columns = [meta.instance_column(), meta.instance_column()];
        let (mut advice_columns, mut fixed_columns) = (vec![], vec![]);
        (
            PoseidonTranscriptGadget::<F>::configure_from_scratch(
                meta,
                &mut advice_columns,
                &mut fixed_columns,
                &instance_columns,
            ),
            CurveChip::configure_from_scratch(
                meta,
                &mut advice_columns,
                &mut fixed_columns,
                &instance_columns,
            ),
        )
    }

    impl Circuit<F> for TestCircuit {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            TestCircuit::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let mut transcript_gadget = PoseidonTranscriptGadget::<F>::new_from_scratch(&config.0);
            let curve_chip = CurveChip::new_from_scratch(&config.1);
            transcript_gadget.init_with_proof(&mut layouter, Value::unknown())?;

            let assigned_scalars = transcript_gadget
                .scalar_chip
                .assign_many(&mut layouter, &self.scalars.transpose_array())?;

            let assigned_points = (self.points.transpose_array().iter())
                .map(|p| curve_chip.assign_without_subgroup_check(&mut layouter, *p))
                .collect::<Result<Vec<_>, Error>>()?;

            for i in 0..(SIZE / 2) {
                transcript_gadget.common_scalar(&mut layouter, &assigned_scalars[i])?;
                let point_pis = curve_chip.as_public_input(&mut layouter, &assigned_points[i])?;
                transcript_gadget.common(&mut layouter, &point_pis)?;
            }

            let challenge_1 = transcript_gadget.squeeze_challenge(&mut layouter)?;
            transcript_gadget
                .scalar_chip
                .constrain_as_public_input(&mut layouter, &challenge_1)?;

            for i in (SIZE / 2)..SIZE {
                transcript_gadget.common_scalar(&mut layouter, &assigned_scalars[i])?;
                let point_pis = curve_chip.as_public_input(&mut layouter, &assigned_points[i])?;
                transcript_gadget.common(&mut layouter, &point_pis)?;
            }

            let challenge_2 = transcript_gadget.squeeze_challenge(&mut layouter)?;
            transcript_gadget
                .scalar_chip
                .constrain_as_public_input(&mut layouter, &challenge_2)?;

            transcript_gadget.load_from_scratch(&mut layouter)?;
            curve_chip.load_from_scratch(&mut layouter)
        }
    }

    #[test]
    fn test_transcript_gadget() {
        let scalars: [F; SIZE] = core::array::from_fn(|_| F::random(OsRng));
        let points: [C; SIZE] = core::array::from_fn(|_| C::random(OsRng));

        let circuit = TestCircuit {
            points: Value::known(points),
            scalars: Value::known(scalars),
        };

        let mut off_circuit_transcript = CircuitTranscript::<PoseidonState<F>>::init();

        for i in 0..(SIZE / 2) {
            off_circuit_transcript.common(&scalars[i]).unwrap();
            off_circuit_transcript.common::<C>(&points[i]).unwrap();
        }

        let challenge_1: F = off_circuit_transcript.squeeze_challenge();

        for i in (SIZE / 2)..SIZE {
            off_circuit_transcript.common(&scalars[i]).unwrap();
            off_circuit_transcript.common::<C>(&points[i]).unwrap();
        }

        let challenge_2 = off_circuit_transcript.squeeze_challenge();

        let public_inputs = vec![vec![], vec![challenge_1, challenge_2]];
        let prover = MockProver::run(&circuit, public_inputs).unwrap();
        prover.assert_satisfied();
    }
}
