// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

use ff::Field;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    transcript::{CircuitTranscript, Transcript},
};

use crate::{
    instructions::{AssignmentInstructions, PublicInputInstructions, SpongeInstructions},
    types::AssignedNative,
    verifier::SelfEmulation,
};

type SpongeState<S> = <<S as SelfEmulation>::SpongeChip as SpongeInstructions<
    <S as SelfEmulation>::F,
    AssignedNative<<S as SelfEmulation>::F>,
    AssignedNative<<S as SelfEmulation>::F>,
>>::State;

/// Gadget used to run the transcript reader in-circuit.
#[derive(Clone, Debug)]
pub struct TranscriptGadget<S: SelfEmulation> {
    scalar_chip: S::ScalarChip,
    curve_chip: S::CurveChip,
    sponge_chip: S::SpongeChip,
    sponge_state: Option<SpongeState<S>>,
    // Track the number of field elements we have in the buffer.
    input_len: usize,
    // Transcript reader is included, to help parse the proof. This parsing
    // *does not* need to be verified in-circuit.
    transcript_reader: Option<CircuitTranscript<S::Hash>>,
}

impl<S: SelfEmulation> TranscriptGadget<S> {
    /// Creates a new `TranscriptGadget` from the corresponding chips.
    pub fn new(
        scalar_chip: &S::ScalarChip,
        curve_chip: &S::CurveChip,
        sponge_chip: &S::SpongeChip,
    ) -> Self {
        Self {
            scalar_chip: scalar_chip.clone(),
            curve_chip: curve_chip.clone(),
            sponge_chip: sponge_chip.clone(),
            sponge_state: None,
            input_len: 0,
            transcript_reader: None,
        }
    }

    /// Initialises the `TranscriptGadget`, by initialising the sponge buffer,
    /// from a given witnessed proof in the form of `Value<Vec<u8>>`.
    pub fn init_with_proof(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
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
        proof.clone().map(|pi| proof_bytes.extend_from_slice(&pi));
        self.transcript_reader = Some(CircuitTranscript::init_from_bytes(&proof_bytes));

        Ok(())
    }

    /// Absorbs a scalar into the transcript.
    pub fn common_scalar(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
        scalar: &AssignedNative<S::F>,
    ) -> Result<(), Error> {
        self.input_len += 1;
        let state = self
            .sponge_state
            .as_mut()
            .expect("You must init the transcript gadget");
        self.sponge_chip.absorb(layouter, state, &[scalar.clone()])
    }

    /// Absorbs a point into the transcript.
    pub fn common_point(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
        point: &S::AssignedPoint,
    ) -> Result<(), Error> {
        let pis = self.curve_chip.as_public_input(layouter, point)?;

        self.input_len += pis.len();

        let state = self
            .sponge_state
            .as_mut()
            .expect("You must init the transcript gadget");
        self.sponge_chip.absorb(layouter, state, &pis)
    }

    /// Derives a scalar challenge from the current transcript.
    pub fn squeeze_challenge(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
    ) -> Result<AssignedNative<S::F>, Error> {
        let state = self
            .sponge_state
            .as_mut()
            .expect("You must init the transcript gadget");
        self.sponge_chip.squeeze(layouter, state)
    }

    /// Reads a point from the reader buffer, and adds it to the transcript.
    /// Think of the read point as a witness freely chosen by the prover.
    pub fn read_point(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
    ) -> Result<S::AssignedPoint, Error> {
        let reader = self
            .transcript_reader
            .as_mut()
            .expect("You must init the transcript gadget");
        // If an error, do not fail, assign a default point instead.
        // (This allows us to parse dummy proofs.)
        let point: Value<S::C> = match reader.read::<S::C>() {
            Ok(point) => Value::known(point),
            Err(_) => Value::known(S::C::default()),
        };

        let assigned_point = self.curve_chip.assign(layouter, point)?;
        self.common_point(layouter, &assigned_point)?;

        Ok(assigned_point)
    }

    /// Reads a scalar from the reader buffer, and adds it to the transcript.
    /// Think of the read scalar as a witness freely chosen by the prover.
    pub fn read_scalar(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
    ) -> Result<AssignedNative<S::F>, Error> {
        let reader = self
            .transcript_reader
            .as_mut()
            .expect("You must init the transcript gadget");
        // If an error, do not fail, assign a default scalar instead.
        // (This allows us to parse dummy proofs.)
        let scalar: Value<S::F> = match reader.read::<S::F>() {
            Ok(scalar) => Value::known(scalar),
            Err(_) => Value::known(S::F::ZERO),
        };

        let assigned_scalar = self.scalar_chip.assign(layouter, scalar)?;
        self.common_scalar(layouter, &assigned_scalar)?;

        Ok(assigned_scalar)
    }
}

#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;

#[cfg(any(test, feature = "testing"))]
impl<S: SelfEmulation> FromScratch<S::F> for TranscriptGadget<S>
where
    S::ScalarChip: FromScratch<S::F>,
    S::CurveChip: FromScratch<S::F>,
    S::SpongeChip: FromScratch<S::F>,
{
    type Config = (
        <S::ScalarChip as FromScratch<S::F>>::Config,
        <S::CurveChip as FromScratch<S::F>>::Config,
        <S::SpongeChip as FromScratch<S::F>>::Config,
    );

    fn new_from_scratch(config: &Self::Config) -> Self {
        let scalar_chip = S::ScalarChip::new_from_scratch(&config.0);
        let curve_chip = S::CurveChip::new_from_scratch(&config.1);
        let sponge_chip = S::SpongeChip::new_from_scratch(&config.2);
        TranscriptGadget::new(&scalar_chip, &curve_chip, &sponge_chip)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<S::F>, config: &Self::Config) {
        S::ScalarChip::load_from_scratch(layouter, &config.0);
        S::CurveChip::load_from_scratch(layouter, &config.1);
        S::SpongeChip::load_from_scratch(layouter, &config.2);
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<S::F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        (
            S::ScalarChip::configure_from_scratch(meta, instance_columns),
            S::CurveChip::configure_from_scratch(meta, instance_columns),
            S::SpongeChip::configure_from_scratch(meta, instance_columns),
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
    use crate::{instructions::PublicInputInstructions, verifier::types::BlstrsEmulation};

    const SIZE: usize = 12;

    type S = BlstrsEmulation;

    type F = <S as SelfEmulation>::F;
    type C = <S as SelfEmulation>::C;

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
        points: Value<[C; SIZE]>,
        scalars: Value<[F; SIZE]>,
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> <TranscriptGadget<S> as FromScratch<F>>::Config {
        let committed_instance_column = meta.instance_column();
        let instance_column = meta.instance_column();
        TranscriptGadget::<S>::configure_from_scratch(
            meta,
            &[committed_instance_column, instance_column],
        )
    }

    impl Circuit<F> for TestCircuit {
        type Config = <TranscriptGadget<S> as FromScratch<F>>::Config;
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
            let mut transcript_gadget = TranscriptGadget::<S>::new_from_scratch(&config);
            transcript_gadget.init_with_proof(&mut layouter, Value::unknown())?;

            TranscriptGadget::<S>::load_from_scratch(&mut layouter, &config);

            let assigned_scalars = transcript_gadget
                .scalar_chip
                .assign_many(&mut layouter, &self.scalars.transpose_array())?;

            let assigned_points = transcript_gadget
                .curve_chip
                .assign_many(&mut layouter, &self.points.transpose_array())?;

            for i in 0..(SIZE / 2) {
                transcript_gadget.common_scalar(&mut layouter, &assigned_scalars[i])?;
                transcript_gadget.common_point(&mut layouter, &assigned_points[i])?;
            }

            let challenge_1 = transcript_gadget.squeeze_challenge(&mut layouter)?;
            transcript_gadget
                .scalar_chip
                .constrain_as_public_input(&mut layouter, &challenge_1)?;

            for i in (SIZE / 2)..SIZE {
                transcript_gadget.common_scalar(&mut layouter, &assigned_scalars[i])?;
                transcript_gadget.common_point(&mut layouter, &assigned_points[i])?;
            }

            let challenge_2 = transcript_gadget.squeeze_challenge(&mut layouter)?;
            transcript_gadget
                .scalar_chip
                .constrain_as_public_input(&mut layouter, &challenge_2)
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

        let mut off_circuit_transcript = CircuitTranscript::<<S as SelfEmulation>::Hash>::init();

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

        let k = 12;
        let public_inputs = vec![vec![], vec![challenge_1, challenge_2]];
        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        prover.assert_satisfied();
    }
}
