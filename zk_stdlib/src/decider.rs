//! A `Decider` interface.
//!
//! A `Decider` circuit knows how to partially verify a proof
//! into an accumulator whose decider is deferred to a final decider step.

use std::{collections::BTreeMap, io};

use group::Group;
use midnight_circuits::{
    hash::poseidon::PoseidonState, instructions::AssignmentInstructions, types::{AssignedNative, Instantiable}, verifier::{
        Accumulator, AssignedAccumulator, AssignedKZGCommitment, AssignedVk, BlstrsEmulation, SelfEmulation, fixed_bases,
    },
};
use midnight_curves::G1Projective;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, Error},
    poly::{
        kzg::{commitment::KZGCommitment, params::ParamsVerifierKZG, KZGCommitmentScheme},
        PolynomialLabel,
    },
    transcript::{CircuitTranscript, Transcript},
    utils::{helpers::ProcessedSerdeObject, SerdeFormat},
};

use crate::{MidnightVK, ZkStdLib, F};

type S = BlstrsEmulation;
type Bls12 = midnight_curves::Bls12;
type C = <S as SelfEmulation>::C;
type AssignedPoint = <S as SelfEmulation>::AssignedPoint;

/// Interface for partially verifying a proof into a deferred accumulator and,
/// finally, accepting or rejecting it.
///
/// Every decider is addressable *from data*: its verifying key is a
/// self-describing [`ProcessedSerdeObject`] blob tagged by a [`DeciderKind`]
/// discriminant, so [`encode_vk`] / [`decide`] /
/// [`ZkStdLib::verify_proof`](crate::ZkStdLib::verify_proof) can serialize the
/// key and dispatch to the right implementation. This is why `Vk` is bound to
/// [`ProcessedSerdeObject`].
pub trait Decider {
    /// Off-circuit verifying-key. Must be serializable so the key can be
    /// recovered from an opaque, self-describing blob.
    type Vk: ProcessedSerdeObject;
    /// In-circuit verifying-key.
    type AssignedVk;

    /// The discriminant identifying this decider.
    const KIND: DeciderKind;

    /// Serializes a decider's verifying key into a self-describing VK blob.
    fn encode_vk(vk: &Self::Vk) -> io::Result<Vec<u8>> {
        let mut blob = vec![Self::KIND.tag()];
        vk.write(&mut blob, SerdeFormat::Processed)?;
        Ok(blob)
    }

    /// Assigns the (fixed) verifying key in-circuit, producing
    /// [`Self::AssignedVk`].
    fn assign_vk(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &Self::Vk,
    ) -> Result<Self::AssignedVk, Error>;

    /// Off-circuit partial verification.
    fn prepare(
        vk: &Self::Vk,
        committed_instance: &[KZGCommitment<Bls12>],
        instance: &[&[F]],
        proof: &[u8],
    ) -> Result<Option<Accumulator<S>>, Error>;

    /// In-circuit mirror of [`Self::prepare`].
    fn in_circuit_prepare(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &Self::AssignedVk,
        committed_instance: &[AssignedKZGCommitment<S>],
        instance: &[&[AssignedNative<F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<Option<AssignedAccumulator<S>>, Error>;

    /// Final decider on a (deferred) accumulator.
    fn decide(
        acc: &Accumulator<S>,
        params: &ParamsVerifierKZG<Bls12>,
        vk: &Self::Vk,
    ) -> Result<(), Error>;
}

/// The standard decider: verify a proof and collapse to a canonical
/// (single-point-per-side, fixed bases resolved) accumulator.
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

impl Decider for StandardDecider {
    type Vk = MidnightVK;
    type AssignedVk = StandardAssignedVk;

    const KIND: DeciderKind = DeciderKind::Standard;

    fn assign_vk(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &MidnightVK,
    ) -> Result<StandardAssignedVk, Error> {
        let plonk_vk = vk.vk();
        let assigned_vk = std_lib.verifier().assign_fixed_vk(
            layouter,
            plonk_vk.get_domain(),
            plonk_vk.cs(),
            plonk_vk.transcript_repr(),
        )?;
        let mut fixed_bases_map = BTreeMap::new();
        for (label, base) in fixed_bases::<S>(plonk_vk) {
            fixed_bases_map.insert(label, std_lib.bls12_381().assign_fixed(layouter, base)?);
        }
        Ok(StandardAssignedVk {
            vk: assigned_vk,
            fixed_bases: fixed_bases_map,
        })
    }

    fn prepare(
        vk: &MidnightVK,
        committed_instance: &[KZGCommitment<Bls12>],
        instance: &[&[F]],
        proof: &[u8],
    ) -> Result<Option<Accumulator<S>>, Error> {
        let vk = vk.vk();
        let bases = fixed_bases::<S>(vk);
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(proof);
        let dual_msm = plonk::prepare::<
            F,
            KZGCommitmentScheme<Bls12>,
            CircuitTranscript<PoseidonState<F>>,
        >(vk, committed_instance, instance, &mut transcript)?;
        let mut acc = Accumulator::from_dual_msm(dual_msm, &bases);
        acc.collapse();
        acc.resolve_fixed_bases(&bases);

        // Collapse the fixed bases
        // todo: better to resolve fixed bases first?
        acc.collapse();
        Ok(Some(acc))
    }

    fn in_circuit_prepare(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &StandardAssignedVk,
        committed_instance: &[AssignedKZGCommitment<S>],
        instance: &[&[AssignedNative<F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<Option<AssignedAccumulator<S>>, Error> {
        let bls = std_lib.bls12_381();
        let mut acc =
            std_lib
                .verifier()
                .prepare(layouter, &vk.vk, committed_instance, instance, proof)?;
        acc.collapse(layouter, bls, bls.scalar_field_chip())?;
        acc.resolve_fixed_bases(&vk.fixed_bases);

        // Collapse the fixed bases
        // todo: better to resolve fixed bases first?
        acc.collapse(layouter, bls, bls.scalar_field_chip())?;
        Ok(Some(acc))
    }
    
    fn decide(
        acc: &Accumulator<S>,
        params: &ParamsVerifierKZG<Bls12>,
        vk: &MidnightVK,
    ) -> Result<(), Error> {
        let fixed_bases = fixed_bases::<S>(vk.vk());
        if acc.check(params, &fixed_bases) {Ok(())} else {Err(Error::Opening)}
    }
}

/// The IVC per-step decider: **prepare-only** partial verification of a step's
/// proof into a deferred accumulator. Unlike [`StandardDecider`], it does *not*
/// resolve its fixed bases. Those are deferred to a final decider step.
#[derive(Clone, Copy, Debug, Default)]
pub struct IvcDecider;

impl Decider for IvcDecider {
    type Vk = MidnightVK;
    type AssignedVk = AssignedVk<S>;

    const KIND: DeciderKind = DeciderKind::Ivc;

    fn assign_vk(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &MidnightVK,
    ) -> Result<AssignedVk<S>, Error> {
        let plonk_vk = vk.vk();
        std_lib.verifier().assign_fixed_vk(
            layouter,
            plonk_vk.get_domain(),
            plonk_vk.cs(),
            plonk_vk.transcript_repr(),
        )
    }

    fn prepare(
        vk: &Self::Vk,
        committed_instance: &[KZGCommitment<Bls12>],
        instance: &[&[F]],
        proof: &[u8],
    ) -> Result<Option<Accumulator<S>>, Error> {
        let bases = fixed_bases::<S>(vk.vk());
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(proof);
        let dual_msm = plonk::prepare::<
            F,
            KZGCommitmentScheme<Bls12>,
            CircuitTranscript<PoseidonState<F>>,
        >(vk.vk(), committed_instance, instance, &mut transcript)?;
        Ok(Some(Accumulator::from_dual_msm(dual_msm, &bases)))
    }

    fn in_circuit_prepare(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &Self::AssignedVk,
        committed_instance: &[AssignedKZGCommitment<S>],
        instance: &[&[AssignedNative<F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<Option<AssignedAccumulator<S>>, Error> {
        let acc = std_lib.verifier().prepare(layouter, vk, committed_instance, instance, proof)?;
        Ok(Some(acc))
    }
    
    fn decide(
        acc: &Accumulator<S>,
        params: &ParamsVerifierKZG<Bls12>,
        vk: &Self::Vk,
    ) -> Result<(), Error> {
        let fixed_bases = fixed_bases::<S>(vk.vk());
        if acc.check(params, &fixed_bases) {Ok(())} else {Err(Error::Opening)}
    }
}

/// The curated set of deciders a caller may select from data, and the bridge
/// from a serialized verifying key to a concrete [`Decider`] implementation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeciderKind {
    /// The standard, non-recursive decider ([`StandardDecider`]).
    Standard,
    /// The IVC per-step decider ([`IvcDecider`]).
    Ivc,
    /// Final IVC decider (Verifies the previous IVC check, and collapses it in 
    /// a single step).
    FinalIVC,
}

impl DeciderKind {
    /// Tag of each decider kind.
    pub fn tag(self) -> u8 {
        match self {
            DeciderKind::Standard => 0,
            DeciderKind::Ivc => 1,
            DeciderKind::FinalIVC => 2,
        }
    }

    /// Splits a self-describing VK blob into its leading discriminant byte and
    /// the remaining decider-specific verifying-key bytes.
    pub fn split(vk_blob: &[u8]) -> Result<(DeciderKind, &[u8]), Error> {
        let (tag, rest) = vk_blob
            .split_first()
            .ok_or_else(|| Error::Synthesis("empty verifying-key blob".into()))?;
        let kind = match tag {
            0 => DeciderKind::Standard,
            1 => DeciderKind::Ivc,
            2 => DeciderKind::FinalIVC,
            other => {
                return Err(Error::Synthesis(format!(
                    "unknown decider discriminant: {other}"
                )));
            }
        };
        Ok((kind, rest))
    }
}

/////////////
/// Wrappers and abstractions for midnight-ledger
/////////////

/// Off-circuit partial verification from a self-describing VK blob. This function resolves
/// the kind of decider, and executes the decide function.
pub fn decide(vk_blob: &[u8], instance: &[&[F]], proof: &[u8]) -> Result<Accumulator<S>, Error> {
    let (kind, vk_bytes) = DeciderKind::split(vk_blob)?;
    let committed_instance = [KZGCommitment::Simple(
        C::identity(),
        PolynomialLabel::Instance(0),
    )];
    match kind {
        DeciderKind::Standard => {
            decide_with::<StandardDecider>(vk_bytes, &committed_instance, instance, proof)
        }
        DeciderKind::Ivc => {
            decide_with::<IvcDecider>(vk_bytes, &committed_instance, instance, proof)
        }
        DeciderKind::FinalIVC => {
            todo!()
        }
    }
}

fn decide_with<D: Decider>(
    vk_bytes: &[u8],
    committed_instance: &[KZGCommitment<Bls12>],
    instance: &[&[F]],
    proof: &[u8],
) -> Result<Accumulator<S>, Error> {
    let vk = <D::Vk as ProcessedSerdeObject>::read(&mut { vk_bytes }, SerdeFormat::Processed)
        .map_err(|e| Error::Synthesis(format!("reading verifying key: {e}")))?;
    D::prepare(&vk, committed_instance, instance, proof)?
        .ok_or_else(|| Error::Synthesis("decider produced no accumulator".into()))
}

/// Field-element encoding of a (single-point) accumulator as public inputs.
pub fn accumulator_as_public_input(acc: &Accumulator<S>) -> Vec<F> {
    <AssignedAccumulator<S> as Instantiable<F>>::as_public_input(acc)
}

/// Number of public-input field elements a single-point-per-side accumulator
/// occupies.
pub fn accumulator_pi_len() -> usize {
    accumulator_as_public_input(&Accumulator::<S>::trivial(&[])).len()
}
