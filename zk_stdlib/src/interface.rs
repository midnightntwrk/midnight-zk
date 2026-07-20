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

//! Front-end interface to the proof system.

use std::{cell::RefCell, io, rc::Rc};

use ff::Field;
use group::{prime::PrimeCurveAffine, Group};
use midnight_circuits::types::ComposableChip;
use midnight_curves::{G1Affine, G1Projective};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::cost_model::{circuit_model, CircuitModel},
    plonk::{
        self, keygen_vk_with_k, prepare, Circuit, ConstraintSystem, Error, ProvingKey, VerifyingKey,
    },
    poly::{
        commitment::{Guard, Params, PolynomialCommitmentScheme},
        kzg::{
            params::{ParamsKZG, ParamsVerifierKZG},
            KZGCommitmentScheme,
        },
    },
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript, TranscriptHash},
    utils::SerdeFormat,
};
use rand::{CryptoRng, RngCore};

use crate::{
    utils::plonk_api::BlstPLONK, ZkStdLib, ZkStdLibArch, ZkStdLibConfig, F, NB_COMMITTED_INSTANCES,
};

/// Circuit structure which is used to create any circuit that can be compiled
/// into keys using the ZK standard library.
#[derive(Clone, Debug)]
pub struct MidnightCircuit<'a, R: Relation> {
    relation: &'a R,
    k: u32,
    instance: Value<R::Instance>,
    witness: Value<R::Witness>,
    nb_public_inputs: Rc<RefCell<Option<usize>>>,
    circuit_error: Rc<RefCell<Option<R::Error>>>,
}

impl<'a, R: Relation> MidnightCircuit<'a, R> {
    /// A MidnightCircuit with unknown instance-witness for the given relation.
    /// `k` is the log2 of the circuit size (i.e. the circuit has `2^k` rows).
    /// If `k` is `None`, the optimal value is computed automatically.
    pub fn from_relation(relation: &'a R, k: Option<u32>) -> Self {
        MidnightCircuit::new(relation, Value::unknown(), Value::unknown(), k)
    }

    /// Creates a new MidnightCircuit for the given relation.
    /// `k` is the log2 of the circuit size (i.e. the circuit has `2^k` rows).
    /// If `k` is `None`, the optimal value is computed automatically.
    pub fn new(
        relation: &'a R,
        instance: Value<R::Instance>,
        witness: Value<R::Witness>,
        k: Option<u32>,
    ) -> Self {
        let k = k.unwrap_or_else(|| optimal_k(relation));
        MidnightCircuit {
            relation,
            k,
            instance,
            witness,
            nb_public_inputs: Rc::new(RefCell::new(None)),
            circuit_error: Rc::new(RefCell::new(None)),
        }
    }

    /// Returns the log2 of the circuit size.
    pub fn k(&self) -> u32 {
        self.k
    }

    /// Takes the circuit error stashed during synthesis, if any.
    fn take_error(&self) -> Option<R::Error> {
        self.circuit_error.take()
    }
}

/// A verifier key of a Midnight circuit.
#[derive(Clone, Debug)]
pub struct MidnightVK {
    architecture: ZkStdLibArch,
    k: u8,
    nb_public_inputs: usize,
    vk: VerifyingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>>,
}

impl MidnightVK {
    /// Writes a verifying key to a buffer.
    ///
    /// Depending on the `format`:
    /// - `Processed`: Takes less space, but more time to read.
    /// - `RawBytes`: Takes more space, but faster to read.
    ///
    /// Using `RawBytesUnchecked` will have the same effect as `RawBytes`,
    /// but it is not recommended.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        self.architecture.write(writer)?;

        writer.write_all(&[self.k])?;

        writer.write_all(&(self.nb_public_inputs as u32).to_le_bytes())?;

        self.vk.write(writer, format)
    }

    /// Reads a verification key from a buffer.
    ///
    /// The `format` must match the one that was used when writing the key.
    /// If the key was written with `RawBytes`, it can be read with `RawBytes`
    /// or `RawBytesUnchecked` (which is faster).
    ///
    /// # WARNING
    /// Use `RawBytesUnchecked` only if you trust the party who wrote the key.
    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let architecture = ZkStdLibArch::read(reader)?;

        let mut byte = [0u8; 1];
        reader.read_exact(&mut byte)?;
        let k = byte[0];

        let mut bytes = [0u8; 4];
        reader.read_exact(&mut bytes)?;
        let nb_public_inputs = u32::from_le_bytes(bytes) as usize;

        let mut cs = ConstraintSystem::default();
        let _config = ZkStdLib::configure(&mut cs, (architecture, k - 1));

        let vk = VerifyingKey::read_from_cs::<R>(reader, format, cs)?;

        Ok(MidnightVK {
            architecture,
            k,
            nb_public_inputs,
            vk,
        })
    }

    /// The size of the domain associated to this verifying key.
    pub fn k(&self) -> u8 {
        self.k
    }

    /// The underlying midnight-proofs verifying key.
    pub fn vk(
        &self,
    ) -> &VerifyingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>> {
        &self.vk
    }
}

/// A proving key of a Midnight circuit.
#[derive(Clone, Debug)]
pub struct MidnightPK<R: Relation> {
    k: u8,
    relation: R,
    pk: ProvingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>>,
}

impl<Rel: Relation> MidnightPK<Rel> {
    /// Writes a proving key to a buffer.
    ///
    /// Depending on the `format`:
    /// - `Processed`: Takes less space, but more time to read.
    /// - `RawBytes`: Takes more space, but faster to read.
    ///
    /// Using `RawBytesUnchecked` will have the same effect as `RawBytes`,
    /// but it is not recommended.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        writer.write_all(&[self.k])?;

        Rel::write_relation(&self.relation, writer)?;

        self.pk.write(writer, format)
    }

    /// Reads a proving key from a buffer.
    ///
    /// The `format` must match the one that was used when writing the key.
    /// If the key was written with `RawBytes`, it can be read with `RawBytes`
    /// or `RawBytesUnchecked` (which is faster).
    ///
    /// # WARNING
    /// Use `RawBytesUnchecked` only if you trust the party who wrote the key.
    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let mut byte = [0u8; 1];

        reader.read_exact(&mut byte)?;
        let k = byte[0];

        let relation = Rel::read_relation(reader)?;

        let pk = ProvingKey::read::<R, MidnightCircuit<Rel>>(
            reader,
            format,
            MidnightCircuit::new(
                &relation,
                Value::unknown(),
                Value::unknown(),
                Some(k as u32),
            )
            .params(),
        )?;

        Ok(MidnightPK { k, relation, pk })
    }

    /// The size of the domain associated to this proving key.
    pub fn k(&self) -> u8 {
        self.k
    }

    /// The underlying midnight-proofs proving key.
    pub fn pk(
        &self,
    ) -> &ProvingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>> {
        &self.pk
    }
}

/// Helper trait, used to abstract the circuit developer from Halo2's
/// boilerplate.
///
/// `Relation` has a default implementation for loading only the tables
/// needed for the requested chips. The developer needs to implement the
/// function [Relation::circuit], which essentially contains the
/// statement of the proof we are creating.
///
/// # Important note
///
/// The API provided here guarantees that the number of public inputs
/// used during verification matches the number of public inputs (as raw
/// scalars) declared in [Relation::circuit] through the
/// [PublicInputInstructions] interface. Proof verification will fail if
/// this requirement is not met.
///
/// # Example
///
/// ```
/// # use midnight_circuits::{
/// #     instructions::{AssignmentInstructions, PublicInputInstructions},
/// #     types::{AssignedByte, Instantiable},
/// # };
/// # use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
/// # use midnight_proofs::{
/// #     circuit::{Layouter, Value},
/// #     plonk::Error,
/// # };
/// # use rand::{rngs::OsRng, Rng, SeedableRng};
/// # use rand_chacha::ChaCha8Rng;
/// # use sha2::Digest;
/// #
/// type F = midnight_curves::Fq;
///
/// #[derive(Clone, Default)]
/// struct ShaPreImageCircuit;
///
/// impl Relation for ShaPreImageCircuit {
///     // When defining a circuit, one must clearly state the instance and the witness
///     // of the underlying NP-relation.
///     type Instance = [u8; 32];
///     type Witness = [u8; 24]; // 192 = 24 * 8
///     type Error = Error;
///
///     // We must specify how the instance is converted into raw field elements to
///     // be process by the prover/verifier. The order here must be consistent with
///     // the order in which public inputs are constrained/assigned in [circuit].
///     fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
///         Ok(instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect())
///     }
///
///     // Define the logic of the NP-relation being proved.
///     fn circuit(
///         &self,
///         std_lib: &ZkStdLib,
///         layouter: &mut impl Layouter<F>,
///         _instance: Value<Self::Instance>,
///         witness: Value<Self::Witness>,
///     ) -> Result<(), Error> {
///         let assigned_input = std_lib.assign_many(layouter, &witness.transpose_array())?;
///         let output = std_lib.sha2_256(layouter, &assigned_input)?;
///         output.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
///     }
///
///     fn used_chips(&self) -> ZkStdLibArch {
///         ZkStdLibArch {
///             sha2_256: true,
///             ..ZkStdLibArch::default()
///         }
///     }
///
///     fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
///         Ok(())
///     }
///
///     fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
///         Ok(ShaPreImageCircuit)
///     }
/// }
///
/// let relation = ShaPreImageCircuit;
/// let srs = srs_for_test(&relation, Some(13));
///
/// let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
/// let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
///
/// let mut rng = ChaCha8Rng::from_entropy();
/// let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
/// let instance = sha2::Sha256::digest(witness).into();
///
/// let proof = midnight_zk_stdlib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
///     &srs, &pk, &relation, &instance, witness, OsRng,
/// )
/// .expect("Proof generation should not fail");
///
/// assert!(
///     midnight_zk_stdlib::verify::<ShaPreImageCircuit, blake2b_simd::State>(
///         &srs.verifier_params(),
///         &vk,
///         &instance,
///         None,
///         &proof
///     )
///     .is_ok()
/// )
/// ```
pub trait Relation: Clone {
    /// The instance of the NP-relation described by this circuit.
    type Instance: Clone;

    /// The witness of the NP-relation described by this circuit.
    type Witness: Clone;

    /// The error type returned by [Self::circuit] and [Self::format_instance].
    type Error: From<plonk::Error>;

    /// Produces a vector of field elements in PLONK format representing the
    /// given [Self::Instance].
    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Self::Error>;

    /// Produces a vector of field elements in PLONK format representing the
    /// data inside the committed instance.
    fn format_committed_instances(_witness: &Self::Witness) -> Vec<F> {
        vec![]
    }

    /// Defines the circuit's logic.
    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Self::Error>;

    /// Specifies what chips are enabled in the standard library. A chip needs
    /// to be enabled if it is used in [Self::circuit], but it can also be
    /// enabled even if it is not used (possibly to share the same architecture
    /// with other circuits).
    ///
    /// The blanket implementation enables none of them.
    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch::default()
    }

    /// Writes a relation to a buffer.
    fn write_relation<W: io::Write>(&self, writer: &mut W) -> io::Result<()>;

    /// Reads a relation from a buffer.
    fn read_relation<R: io::Read>(reader: &mut R) -> io::Result<Self>;
}

impl<R: Relation> Circuit<F> for MidnightCircuit<'_, R> {
    type Config = ZkStdLibConfig;

    // FIXME: this could be parametrised by MidnightCircuit.
    type FloorPlanner = SimpleFloorPlanner;

    type Params = (ZkStdLibArch, u8);

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn params(&self) -> Self::Params {
        (self.relation.used_chips(), (self.k - 1) as u8)
    }

    fn configure_with_params(
        meta: &mut ConstraintSystem<F>,
        params: (ZkStdLibArch, u8),
    ) -> Self::Config {
        ZkStdLib::configure(meta, params)
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ZkStdLib::configure(meta, (ZkStdLibArch::default(), 8))
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let max_bit_len = (self.k - 1) as usize;
        let zk_std_lib = ZkStdLib::new(&config, max_bit_len);

        self.relation
            .circuit(
                &zk_std_lib,
                &mut layouter.namespace(|| "Running logic circuit"),
                self.instance.clone(),
                self.witness.clone(),
            )
            .map_err(|e| {
                *self.circuit_error.borrow_mut() = Some(e);
                Error::Synthesis("Relation::circuit error".into())
            })?;

        // After the circuit function has been called, we can update the expected
        // number of raw public inputs in [Self] (via a RefCell). This number will
        // be stored in the MidnightVK so that we can make sure it matches the number of
        // public inputs provided during verification.
        *self.nb_public_inputs.borrow_mut() =
            Some(zk_std_lib.native_gadget.native_chip.nb_public_inputs());

        // We load the tables at the end, once we have figured out what chips/gadgets
        // were actually used.
        zk_std_lib.core_decomposition_chip.load(&mut layouter)?;

        if let Some(sha256_chip) = zk_std_lib.sha2_256_chip {
            if *zk_std_lib.used_sha2_256.borrow() {
                sha256_chip.load(&mut layouter)?;
            }
        }

        if let Some(sha512_chip) = zk_std_lib.sha2_512_chip {
            if *zk_std_lib.used_sha2_512.borrow() {
                sha512_chip.load(&mut layouter)?;
            }
        }

        if let Some(b64_chip) = zk_std_lib.base64_chip {
            if *zk_std_lib.used_base64.borrow() {
                b64_chip.load(&mut layouter)?;
            }
        }

        if let Some(scanner_chip) = zk_std_lib.scanner_chip {
            if *zk_std_lib.used_scanner.borrow() {
                scanner_chip.load(&mut layouter)?;
            }
        }

        if let Some(keccak_sha3_chip) = zk_std_lib.keccak_sha3_chip {
            if *zk_std_lib.used_keccak_or_sha3.borrow() {
                keccak_sha3_chip.load(&mut layouter)?;
            }
        }

        if let Some(blake2b_chip) = zk_std_lib.blake2b_chip {
            if *zk_std_lib.used_blake2b.borrow() {
                blake2b_chip.load(&mut layouter)?;
            }
        }

        Ok(())
    }
}

/// Generates a verifying key for a `MidnightCircuit<R>` circuit.
///
/// The log2 of the circuit size (`k`) is derived from the SRS parameters.
/// For optimal performance, downsize the SRS to the circuit's optimal `k`
/// beforehand (see [optimal_k]). Otherwise, the circuit will use the full
/// size of the SRS, which may be unnecessarily large.
pub fn setup_vk<R: Relation>(
    params: &ParamsKZG<midnight_curves::Bls12>,
    relation: &R,
) -> MidnightVK {
    let k = params.max_k();
    let circuit = MidnightCircuit::from_relation(relation, Some(k));
    let vk = keygen_vk_with_k(params, &circuit, k).expect("keygen_vk should not fail");

    // During the call to [setup_vk] the circuit RefCell on public inputs has been
    // mutated with the correct value. The following [unwrap] is safe here.
    let nb_public_inputs = circuit.nb_public_inputs.clone().borrow().unwrap();

    MidnightVK {
        architecture: relation.used_chips(),
        k: circuit.k as u8,
        nb_public_inputs,
        vk,
    }
}

/// Generates a proving key for a `MidnightCircuit<R>` circuit.
pub fn setup_pk<R: Relation>(relation: &R, vk: &MidnightVK) -> MidnightPK<R> {
    let circuit = MidnightCircuit::new(
        relation,
        Value::unknown(),
        Value::unknown(),
        Some(vk.k() as u32),
    );
    let pk = BlstPLONK::<MidnightCircuit<R>>::setup_pk(&circuit, &vk.vk);
    MidnightPK {
        k: vk.k(),
        relation: relation.clone(),
        pk,
    }
}

/// Produces a proof of relation `R` for the given instance (using the given
/// proving key and witness).
pub fn prove<R: Relation, H: TranscriptHash>(
    params: &ParamsKZG<midnight_curves::Bls12>,
    pk: &MidnightPK<R>,
    relation: &R,
    instance: &R::Instance,
    witness: R::Witness,
    rng: impl RngCore + CryptoRng,
) -> Result<Vec<u8>, R::Error>
where
    G1Projective: Hashable<H>,
    F: Hashable<H> + Sampleable<H>,
{
    let pi = R::format_instance(instance)?;
    let com_inst = R::format_committed_instances(&witness);
    let circuit = MidnightCircuit::new(
        relation,
        Value::known(instance.clone()),
        Value::known(witness),
        Some(pk.k as u32),
    );
    BlstPLONK::<MidnightCircuit<R>>::prove::<H>(
        params,
        &pk.pk,
        &circuit,
        NB_COMMITTED_INSTANCES,
        &[com_inst.as_slice(), &pi],
        rng,
    )
    .map_err(|e| circuit.take_error().unwrap_or_else(|| e.into()))
}

/// Verifies the given proof of relation `R` with respect to the given instance.
/// Returns `Ok(())` if the proof is valid.
pub fn verify<R: Relation, H: TranscriptHash>(
    params_verifier: &ParamsVerifierKZG<midnight_curves::Bls12>,
    vk: &MidnightVK,
    instance: &R::Instance,
    committed_instance: Option<G1Affine>,
    proof: &[u8],
) -> Result<(), R::Error>
where
    G1Projective: Hashable<H>,
    F: Hashable<H> + Sampleable<H>,
{
    let pi = R::format_instance(instance)?;
    let committed_pi = committed_instance.unwrap_or(G1Affine::identity());
    if pi.len() != vk.nb_public_inputs {
        return Err(Error::InvalidInstances.into());
    }
    Ok(BlstPLONK::<MidnightCircuit<R>>::verify::<H>(
        params_verifier,
        &vk.vk,
        &[committed_pi],
        &[&pi],
        proof,
    )?)
}

/// A per-proof verification guard (a deferred `DualMSM` pairing check) paired
/// with the transcript `summary` challenge used to derive the batching
/// randomness. Produced by [`compute_guards`] and consumed by
/// [`batch_verify_with_guards`].
type BatchGuard = (
    <KZGCommitmentScheme<midnight_curves::Bls12> as PolynomialCommitmentScheme<F>>::VerificationGuard,
    F,
);

/// Runs the expensive, per-proof preparation of a batch (transcript replay +
/// deferred MSM guard) in parallel, returning one [`BatchGuard`] per proof. The
/// guards can then be checked as a whole batch, or individually, without
/// re-doing this work — see [`batch_verify_with_guards`].
fn compute_guards<H: TranscriptHash + Send + Sync>(
    vks: &[MidnightVK],
    pis: &[Vec<F>],
    proofs: &[Vec<u8>],
) -> Result<Vec<BatchGuard>, Error>
where
    G1Projective: Hashable<H>,
    F: Hashable<H> + Sampleable<H>,
{
    use rayon::prelude::*;

    // TODO: For the moment, committed instances are not supported.
    let n = vks.len();
    if pis.len() != n || proofs.len() != n {
        // TODO: have richer types in halo2
        return Err(Error::InvalidInstances);
    }

    vks.par_iter()
        .zip(pis.par_iter())
        .zip(proofs.par_iter())
        .map(|((vk, pi), proof)| {
            if pi.len() != vk.nb_public_inputs {
                return Err(Error::InvalidInstances);
            }

            let mut transcript = CircuitTranscript::init_from_bytes(proof);
            let dual_msm = prepare::<
                midnight_curves::Fq,
                KZGCommitmentScheme<midnight_curves::Bls12>,
                CircuitTranscript<H>,
            >(
                &vk.vk,
                &[
                    midnight_proofs::poly::kzg::commitment::KZGCommitment::Simple(
                        midnight_curves::G1Projective::identity(),
                        midnight_proofs::poly::PolynomialLabel::Instance(0),
                    ),
                ],
                &[pi],
                &mut transcript,
            )?;
            let summary: F = transcript.squeeze_challenge();
            transcript.assert_empty().map_err(|_| Error::Opening)?;
            Ok((dual_msm, summary))
        })
        .collect()
}

/// Checks a set of already-prepared guards as a single batch: derives the
/// batching challenge from their summaries, folds them into one random linear
/// combination and runs a single pairing check. Returns `Ok(())` iff the
/// (possibly empty) set verifies, otherwise [`Error::Opening`].
///
/// The guards are cloned before scaling, so `prepared` is left intact and can
/// be re-checked over different subsets (e.g. singletons during failure
/// localization). No MSM is reused across calls — each call re-folds from the
/// untouched guards.
fn batch_verify_with_guards<H: TranscriptHash>(
    params_verifier: &ParamsVerifierKZG<midnight_curves::Bls12>,
    prepared: &[BatchGuard],
) -> Result<(), Error>
where
    F: Hashable<H> + Sampleable<H>,
{
    use rayon::prelude::*;

    let mut r_transcript = CircuitTranscript::<H>::init();
    for (_, summary) in prepared {
        r_transcript.common(summary)?;
    }
    let r: F = r_transcript.squeeze_challenge();

    let powers: Vec<F> =
        std::iter::successors(Some(F::ONE), |p| Some(*p * r)).take(prepared.len()).collect();
    let mut guards: Vec<_> = prepared
        .par_iter()
        .zip(powers.par_iter())
        .map(|((guard, _), power)| {
            let mut guard = guard.clone();
            guard.scale(*power);
            guard
        })
        .collect();

    let Some(mut acc_guard) = guards.pop() else {
        // Empty batch: nothing to reject.
        return Ok(());
    };
    for guard in guards {
        acc_guard.add_msm(guard);
    }
    acc_guard.verify(params_verifier).map_err(|_| Error::Opening)
}

/// Verifies a batch of proofs with respect to their corresponding vk.
/// This method does not need to know the `Relation` the proofs are associated
/// to and, indeed, it can verify proofs from different `Relation`s.
/// For that, this function does not take `instance`s, but public inputs
/// in raw format (`Vec<F>`).
///
/// The accept/reject decision is a single random-linear-combination batch
/// check: every proof is prepared once (in parallel), the resulting guards are
/// folded into one accumulator and a single pairing check is run. This is
/// strictly cheaper than verifying each proof individually.
///
/// Returns `Ok(())` if all proofs are valid. On failure the behaviour depends
/// on `identify_failures`:
/// - `false` (the default for consensus verification, where the whole batch is
///   simply rejected): returns [`Error::Opening`] without spending any effort
///   to pinpoint the offending proofs.
/// - `true`: performs a linear search over the already-prepared per-proof
///   guards (reusing the expensive `prepare` work, one cheap pairing per proof,
///   in parallel) and returns [`Error::BatchOpening`] carrying the ascending
///   indices of the invalid proofs.
pub fn batch_verify<H: TranscriptHash + Send + Sync>(
    params_verifier: &ParamsVerifierKZG<midnight_curves::Bls12>,
    vks: &[MidnightVK],
    pis: &[Vec<F>],
    proofs: &[Vec<u8>],
    identify_failures: bool,
) -> Result<(), Error>
where
    G1Projective: Hashable<H>,
    F: Hashable<H> + Sampleable<H>,
{
    use rayon::prelude::*;

    // Expensive per-proof preparation, retained so that, on failure, the search
    // below can reuse it instead of re-preparing.
    let prepared = compute_guards::<H>(vks, pis, proofs)?;

    // Fast path: one combined pairing check for the whole batch.
    if batch_verify_with_guards::<H>(params_verifier, &prepared).is_ok() {
        return Ok(());
    }
    if !identify_failures {
        return Err(Error::Opening);
    }

    // The batch failed: pinpoint the offending proofs. A proof is invalid iff
    // the singleton batch containing only its guard fails; this reuses the
    // prepared guards and costs one pairing per proof, run in parallel. A batch
    // of valid guards cannot fail while every singleton passes, so this always
    // finds at least one culprit; the empty-vector guard below is defensive.
    let mut failures: Vec<usize> = (0..prepared.len())
        .into_par_iter()
        .filter(|&i| batch_verify_with_guards::<H>(params_verifier, &prepared[i..i + 1]).is_err())
        .collect();
    failures.sort_unstable();

    if failures.is_empty() {
        Err(Error::Opening)
    } else {
        Err(Error::BatchOpening(failures))
    }
}

/// Returns the constraint-system degree relative to the given [`ZkStdLibArch`].
pub fn cs_degree(arch: ZkStdLibArch) -> usize {
    let mut cs = midnight_proofs::plonk::ConstraintSystem::<F>::default();
    // max_bit_len does not affect the CS degree, use an arbitrary value.
    ZkStdLib::configure(&mut cs, (arch, 8));
    cs.degree()
}

/// Cost model of the given relation for the given `k`.
/// `k` is the log2 of the circuit size. If `None`, the optimal value is
/// computed automatically.
pub fn cost_model<R: Relation>(relation: &R, k: Option<u32>) -> CircuitModel {
    let circuit = MidnightCircuit::from_relation(relation, k);
    circuit_model::<_, KZGCommitmentScheme<midnight_curves::Bls12>>(
        &circuit,
        NB_COMMITTED_INSTANCES,
    )
}

/// Finds the optimal `k` (log2 of the circuit size) for the given relation.
/// Tries different values of `k` (9..=25) and picks the smallest one where
/// the circuit fits. The pow2range table uses `max_bit_len = k - 1`.
pub fn optimal_k<R: Relation>(relation: &R) -> u32 {
    let mut best_k = u32::MAX;

    for k in 9..=25 {
        let model = cost_model(relation, Some(k));

        if model.k < best_k {
            best_k = model.k;
        }

        // Stop when the pow2range table (2^k rows) becomes the bottleneck.
        if model.rows < (1 << k) {
            break;
        }
    }

    best_k
}
