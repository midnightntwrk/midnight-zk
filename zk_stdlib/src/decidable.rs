//! A `Decidable` interface.
//!
//! A `Decidable` circuit knows how to partially verify a proof
//! into an accumulator whose decider is deferred to a final decider step.

use std::collections::BTreeMap;

use midnight_circuits::{
    hash::poseidon::PoseidonState,
    types::AssignedNative,
    verifier::{
        fixed_bases, Accumulator, AssignedAccumulator, AssignedKZGCommitment, AssignedVk,
        BlstrsEmulation, SelfEmulation,
    },
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, Error, VerifyingKey},
    poly::{
        kzg::{commitment::KZGCommitment, KZGCommitmentScheme},
        PolynomialLabel,
    },
    transcript::{CircuitTranscript, Transcript},
};

use crate::{ZkStdLib, F};

type S = BlstrsEmulation;
type Bls12 = midnight_curves::Bls12;
type PlonkVk = VerifyingKey<midnight_curves::Fq, KZGCommitmentScheme<Bls12>>;
type AssignedPoint = <S as SelfEmulation>::AssignedPoint;

/// Interface for partially verifying a proof into a deferred accumulator.
pub trait Decidable {
    /// Off-circuit verifying-key.
    type Vk;
    /// In-circuit verifying-key.
    type AssignedVk;

    /// Off-circuit partial verification.
    fn decide(
        vk: &Self::Vk,
        committed_instance: &[KZGCommitment<Bls12>],
        instance: &[&[F]],
        proof: &[u8],
    ) -> Result<Option<Accumulator<S>>, Error> {
        let _ = (vk, committed_instance, instance, proof);
        Ok(None)
    }

    /// In-circuit mirror of [`Self::decide`]. 
    fn in_circuit_decide(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &Self::AssignedVk,
        committed_instance: &[AssignedKZGCommitment<S>],
        instance: &[&[AssignedNative<F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<Option<AssignedAccumulator<S>>, Error> {
        let _ = (std_lib, layouter, vk, committed_instance, instance, proof);
        Ok(None)
    }
}

/// The standard decider: verify a proof and collapse to a canonical
/// (single-point-per-side, fixed bases resolved) accumulator. This is the
/// decider of every non-recursive circuit.
#[derive(Clone, Copy, Debug, Default)]
pub struct StandardDecider;

/// In-circuit verifying key for [`StandardDecider`]: the assigned vk together
/// with its assigned fixed bases (needed to resolve after collapsing).
#[derive(Clone, Debug)]
pub struct StandardAssignedVk {
    /// The assigned verifying key.
    pub vk: AssignedVk<S>,
    /// The assigned fixed-base points, keyed by label.
    pub fixed_bases: BTreeMap<PolynomialLabel, AssignedPoint>,
}

impl Decidable for StandardDecider {
    type Vk = PlonkVk;
    type AssignedVk = StandardAssignedVk;

    fn decide(
        vk: &PlonkVk,
        committed_instance: &[KZGCommitment<Bls12>],
        instance: &[&[F]],
        proof: &[u8],
    ) -> Result<Option<Accumulator<S>>, Error> {
        let bases = fixed_bases::<S>(vk);
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(proof);
        let dual_msm =
            plonk::prepare::<F, KZGCommitmentScheme<Bls12>, CircuitTranscript<PoseidonState<F>>>(
                vk,
                committed_instance,
                instance,
                &mut transcript,
            )?;
        let mut acc = Accumulator::from_dual_msm(dual_msm, &bases);
        acc.collapse();
        acc.resolve_fixed_bases(&bases);
        Ok(Some(acc))
    }

    fn in_circuit_decide(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &StandardAssignedVk,
        committed_instance: &[AssignedKZGCommitment<S>],
        instance: &[&[AssignedNative<F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<Option<AssignedAccumulator<S>>, Error> {
        let bls = std_lib.bls12_381();
        let mut acc =
            std_lib.verifier().prepare(layouter, &vk.vk, committed_instance, instance, proof)?;
        acc.collapse(layouter, bls, bls.scalar_field_chip())?;
        acc.resolve_fixed_bases(&vk.fixed_bases);
        Ok(Some(acc))
    }
}
