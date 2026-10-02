//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

use blake2b_simd::Params as Blake2bParams;
use group::ff::FromUniformBytes;

use crate::{
    plonk::permutation::expressions,
    poly::{
        Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, PinnedEvaluationDomain,
        Polynomial,
    },
    transcript::{Hashable, Transcript},
    utils::{
        SerdeFormat,
        helpers::{
            ProcessedSerdeObject, polynomial_slice_byte_length, read_polynomial_vec,
            write_polynomial_slice,
        },
    },
};

mod absorbed_vk;
pub(crate) mod argument;
mod circuit;
mod error;
pub(crate) mod evaluation;
mod keygen;
pub(crate) mod linearization;
pub(crate) mod logup;
pub mod permutation;
pub(crate) mod traces;
pub(crate) mod trash;

#[cfg(feature = "bench-internal")]
pub mod bench;

mod prover;
mod verifier;

use std::{collections::BTreeMap, io};

pub(crate) use absorbed_vk::AbsorbedVk;
pub use circuit::*;
pub use error::*;
pub(crate) use evaluation::Evaluator;
use ff::{PrimeField, WithSmallOrderMulGroup};
pub use keygen::*;
use midnight_curves::serde::SerdeObject;
pub use prover::*;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
pub use verifier::*;

use crate::poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme};

/// This is a verifying key which allows for the verification of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct VerifyingKey<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    domain: EvaluationDomain<F>,
    phase0_commitment: CS::Commitment,
    simple_selector_commitments: BTreeMap<usize, CS::Commitment>,
    cs: ConstraintSystem<F>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    transcript_repr: F,
}

// Current version of the VK
const VERSION: u8 = 0x03;

impl<F, CS> VerifyingKey<F, CS>
where
    F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
{
    /// Returns `n`
    pub fn n(&self) -> u64 {
        self.domain.n
    }
    /// Writes a verifying key to a buffer.
    ///
    /// Writes a curve element according to `format`:
    /// - `Processed`: Writes a compressed curve element with coordinates in
    ///   standard form. Writes a field element in standard form, with
    ///   endianness specified by the `PrimeField` implementation.
    /// - Otherwise: Writes an uncompressed curve element with coordinates in
    ///   Montgomery form Writes a field element into raw bytes in its internal
    ///   Montgomery representation, WITHOUT performing the expensive Montgomery
    ///   reduction.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        // Version byte that will be checked on read.
        writer.write_all(&[VERSION])?;
        let k = &self.domain.k();
        assert!(*k <= F::S);
        // k value fits in 1 byte
        writer.write_all(&[*k as u8])?;
        self.phase0_commitment.write(writer, format)?;
        for commitment in self.simple_selector_commitments.values() {
            commitment.write(writer, format)?;
        }

        Ok(())
    }

    /// Reads a verification key from a buffer for the associated [Circuit].
    ///
    /// Reads a curve element from the buffer and parses it according to the
    /// `format`:
    /// - `Processed`: Reads a compressed curve element and decompresses it.
    ///   Reads a field element in standard form, with endianness specified by
    ///   the `PrimeField` implementation, and checks that the element is less
    ///   than the modulus.
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in
    ///   Montgomery form. Checks that field elements are less than modulus, and
    ///   then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with
    ///   coordinates in Montgomery form; does not perform any checks.
    pub fn read<R: io::Read, ConcreteCircuit: Circuit<F>>(
        reader: &mut R,
        format: SerdeFormat,
        #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
    ) -> io::Result<Self> {
        let mut cs = ConstraintSystem::default();
        #[cfg(feature = "circuit-params")]
        let _config = ConcreteCircuit::configure_with_params(&mut cs, params);
        #[cfg(not(feature = "circuit-params"))]
        let _config = ConcreteCircuit::configure(&mut cs);

        Self::read_from_cs(reader, format, cs)
    }

    /// Reads a verification key from a buffer, using the provided
    /// [ConstraintSystem].
    ///
    /// Reads a curve element from the buffer and parses it according to the
    /// `format`:
    /// - `Processed`: Reads a compressed curve element and decompresses it.
    ///   Reads a field element in standard form, with endianness specified by
    ///   the `PrimeField` implementation, and checks that the element is less
    ///   than the modulus.
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in
    ///   Montgomery form. Checks that field elements are less than modulus, and
    ///   then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with
    ///   coordinates in Montgomery form; does not perform any checks.
    pub fn read_from_cs<R: io::Read>(
        reader: &mut R,
        format: SerdeFormat,
        cs: ConstraintSystem<F>,
    ) -> io::Result<Self> {
        let mut version_byte = [0u8; 1];
        reader.read_exact(&mut version_byte)?;
        if VERSION != version_byte[0] {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unexpected version byte",
            ));
        }

        let mut k = [0u8; 1];
        reader.read_exact(&mut k)?;
        let k = u8::from_le_bytes(k);
        if k as u32 > F::S {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("circuit size value (k): {} exceeds maxium: {}", k, F::S),
            ));
        }

        let domain = EvaluationDomain::new(cs.degree() as u32, k.into());

        // Finalizing `cs` replaces its selectors with fixed columns, which
        // decides which fixed columns are simple selectors.
        let cs = cs.into_finalized();

        let phase0_commitment =
            CS::deserialize_commitment(reader, format, &cs.fixed_polys_labels())?;

        let simple_selector_commitments = cs
            .simple_selector_columns()
            .into_iter()
            .map(|i| {
                let commitment =
                    CS::deserialize_commitment(reader, format, &[PolynomialLabel::Fixed(i)])?;
                Ok((i, commitment))
            })
            .collect::<io::Result<_>>()?;

        Ok(Self::from_parts(
            domain,
            phase0_commitment,
            simple_selector_commitments,
            cs,
        ))
    }

    /// Writes a verifying key to a vector of bytes using [`Self::write`].
    pub fn to_bytes(&self, format: SerdeFormat) -> Vec<u8> {
        let mut bytes = Vec::<u8>::with_capacity(self.bytes_length(format));
        Self::write(self, &mut bytes, format).expect("Writing to vector should not fail");
        bytes
    }

    /// Reads a verification key from a slice of bytes using [`Self::read`].
    pub fn from_bytes<ConcreteCircuit: Circuit<F>>(
        mut bytes: &[u8],
        format: SerdeFormat,
        #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
    ) -> io::Result<Self> {
        Self::read::<_, ConcreteCircuit>(
            &mut bytes,
            format,
            #[cfg(feature = "circuit-params")]
            params,
        )
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> VerifyingKey<F, CS> {
    /// Return the bytes_length of a VerifyingKey
    pub fn bytes_length(&self, format: SerdeFormat) -> usize {
        // The header [`Self::write`] emits: the version byte and `k`.
        const HEADER_BYTES: usize = 1 + 1;

        HEADER_BYTES
            + self.phase0_commitment.byte_length(format)
            + (self.simple_selector_commitments.values())
                .map(|c| c.byte_length(format))
                .sum::<usize>()
    }

    fn from_parts(
        domain: EvaluationDomain<F>,
        phase0_commitment: CS::Commitment,
        simple_selector_commitments: BTreeMap<usize, CS::Commitment>,
        cs: ConstraintSystem<F>,
    ) -> Self
    where
        F: FromUniformBytes<64>,
    {
        // Compute cached values.
        let cs_degree = cs.degree();

        let mut vk = Self {
            domain,
            phase0_commitment,
            simple_selector_commitments,
            cs,
            cs_degree,
            // Temporary, this is not pinned.
            transcript_repr: F::ZERO,
        };

        let mut hasher =
            Blake2bParams::new().hash_length(64).personal(b"Halo2-Verify-Key").to_state();

        // We serialise the commitments of the VK to get the `transcript_repr`.
        let mut buffer = Vec::new();
        buffer.push(VERSION);
        let k = &vk.domain.k();
        assert!(*k <= F::S);
        buffer.push(*k as u8);
        vk.phase0_commitment
            .write(&mut buffer, SerdeFormat::RawBytesUnchecked)
            .expect("Failed to write to buffer - this is a bug.");
        for commitment in vk.simple_selector_commitments.values() {
            commitment
                .write(&mut buffer, SerdeFormat::RawBytesUnchecked)
                .expect("Failed to write to buffer - this is a bug.");
        }

        // We use the debug implementation to add the gates and domain to the hashed
        // buffer. We should eventually move away from debug implementation for
        // this purpose. See https://github.com/midnightntwrk/halo2/issues/5
        buffer.extend_from_slice(format!("{:?}", vk.get_domain().pinned()).as_bytes());
        buffer.extend_from_slice(format!("{:?}", vk.cs().pinned()).as_bytes());

        hasher.update(&buffer);

        // Hash in final Blake2bState
        vk.transcript_repr = F::from_uniform_bytes(hasher.finalize().as_array());

        vk
    }

    /// Hashes a verification key into a transcript.
    pub fn hash_into<T: Transcript>(&self, transcript: &mut T) -> io::Result<()>
    where
        F: Hashable<T::Hash>,
    {
        self.absorb_into(transcript).map(|_| ())
    }

    /// Obtains a pinned representation of this verification key that contains
    /// the minimal information necessary to reconstruct the verification key.
    pub fn pinned(&self) -> PinnedVerificationKey<'_, F, CS> {
        PinnedVerificationKey {
            domain: self.domain.pinned(),
            phase0_commitment: &self.phase0_commitment,
            simple_selector_commitments: &self.simple_selector_commitments,
            cs: self.cs.pinned(),
        }
    }

    /// The commitment to the phase-0 group, the polynomials of
    /// [`ConstraintSystem::fixed_polys_labels`]: every fixed column but the
    /// simple selectors, then the fixed permutation polynomials.
    pub fn phase0_commitment(&self) -> &CS::Commitment {
        &self.phase0_commitment
    }

    /// The commitment to each simple-selector fixed column, keyed by column
    /// index. They are kept apart from the group: the linearization scales
    /// each by its own evaluated identity.
    pub fn simple_selector_commitments(&self) -> &BTreeMap<usize, CS::Commitment> {
        &self.simple_selector_commitments
    }

    /// Returns `ConstraintSystem`
    pub fn cs(&self) -> &ConstraintSystem<F> {
        &self.cs
    }

    /// Returns representative of this `VerifyingKey` in transcripts
    pub fn transcript_repr(&self) -> F {
        self.transcript_repr
    }
}

/// Minimal representation of a verification key that can be used to identify
/// its active contents.
#[allow(dead_code)]
#[derive(Debug)]
pub struct PinnedVerificationKey<'a, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    domain: PinnedEvaluationDomain<'a, F>,
    cs: PinnedConstraintSystem<'a, F>,
    phase0_commitment: &'a CS::Commitment,
    simple_selector_commitments: &'a BTreeMap<usize, CS::Commitment>,
}
/// This is a proving key which allows for the creation of proofs for a
/// particular circuit.
#[derive(Debug)]
pub struct ProvingKey<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) vk: VerifyingKey<F, CS>,
    pub(crate) l0: Polynomial<F, ExtendedLagrangeCoeff>,
    pub(crate) l_last: Polynomial<F, ExtendedLagrangeCoeff>,
    pub(crate) l_active_row: Polynomial<F, ExtendedLagrangeCoeff>,
    pub(crate) fixed_values: Vec<Polynomial<F, LagrangeCoeff>>,
    pub(crate) fixed_cosets: Vec<Polynomial<F, ExtendedLagrangeCoeff>>,
    pub(crate) phase0_polys: argument::prover::KeyGroup<F>,
    pub(crate) simple_selector_polys: BTreeMap<usize, Polynomial<F, Coeff>>,
    pub(crate) sigmas: permutation::Sigmas<F>,
    pub(crate) ev: Evaluator<F>,
    /// Region layout captured during keygen, consumed during proving to skip
    /// the shape pass. `None` means no cached layout is available (either the
    /// `FloorPlanner` does not support capture, or the key was deserialized);
    /// in that case the prover falls back to running the shape pass itself.
    pub(crate) region_starts: Option<Vec<crate::circuit::RegionStart>>,
}

/// The fixed polynomials of a proving key, derived from `fixed_values`, the
/// fixed columns in Lagrange form, and `sigmas`, the fixed permutation
/// polynomials in Lagrange form:
/// * the phase-0 group, of [`ConstraintSystem::fixed_polys_labels`], in
///   coefficient form; `vk_repr` is the `transcript_repr` of the verifying key
///   holding its commitment;
/// * the simple-selector columns, in coefficient form, keyed by column index;
/// * every fixed column over the extended domain;
/// * the permutation polynomials in the bases the prover reads them in.
///
/// # Panics
///
/// Panics if `sigmas` does not hold one polynomial per column of the
/// permutation argument.
#[allow(clippy::type_complexity)]
pub(in crate::plonk) fn build_phase0_polys<F: WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    cs: &ConstraintSystem<F>,
    vk_repr: F,
    fixed_values: &[Polynomial<F, LagrangeCoeff>],
    sigmas: Vec<Polynomial<F, LagrangeCoeff>>,
) -> (
    argument::prover::KeyGroup<F>,
    BTreeMap<usize, Polynomial<F, Coeff>>,
    Vec<Polynomial<F, ExtendedLagrangeCoeff>>,
    permutation::Sigmas<F>,
) {
    let sigma_labels = cs.permutation.polynomial_labels();
    assert_eq!(
        sigmas.len(),
        sigma_labels.len(),
        "the number of permutation polynomials does not match the number of permutation columns"
    );

    let fixed_coeffs: Vec<_> = fixed_values
        .par_iter()
        .map(|poly| domain.lagrange_to_coeff(poly.clone()))
        .collect();
    let fixed_cosets = fixed_coeffs
        .par_iter()
        .map(|poly| domain.coeff_to_extended(poly.clone()))
        .collect();

    let mut group = BTreeMap::new();
    let mut simple_selector_polys = BTreeMap::new();
    for (i, poly) in fixed_coeffs.into_iter().enumerate() {
        if cs.has_simple_selector_col(i) {
            simple_selector_polys.insert(i, poly);
        } else {
            group.insert(PolynomialLabel::Fixed(i), poly);
        }
    }

    let (sigma_coeffs, sigma_cosets) =
        permutation::keygen::compute_polys_and_cosets(domain, &cs.permutation, &sigmas);
    group.extend(sigma_labels.into_iter().zip(sigma_coeffs));

    (
        argument::prover::KeyGroup::new(group, vk_repr),
        simple_selector_polys,
        fixed_cosets,
        permutation::Sigmas {
            values: sigmas,
            cosets: sigma_cosets,
        },
    )
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProvingKey<F, CS>
where
    F: FromUniformBytes<64>,
{
    /// Get the underlying [`VerifyingKey`].
    pub fn get_vk(&self) -> &VerifyingKey<F, CS> {
        &self.vk
    }

    /// Gets the total number of bytes in the serialization of `self`
    pub fn bytes_length(&self, format: SerdeFormat) -> usize {
        // `l0`, `l_last`, `l_active_row`, the fixed polynomials and their
        // cosets are not written: [`Self::read`] recomputes them.
        self.vk.bytes_length(format)
            + polynomial_slice_byte_length(&self.fixed_values)
            + polynomial_slice_byte_length(&self.sigmas.values)
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProvingKey<F, CS>
where
    F: PrimeField + FromUniformBytes<64> + SerdeObject,
{
    /// Writes a proving key to a buffer.
    ///
    /// Writes a curve element according to `format`:
    /// - `Processed`: Writes a compressed curve element with coordinates in
    ///   standard form. Writes a field element in standard form, with
    ///   endianness specified by the `PrimeField` implementation.
    /// - Otherwise: Writes an uncompressed curve element with coordinates in
    ///   Montgomery form Writes a field element into raw bytes in its internal
    ///   Montgomery representation, WITHOUT performing the expensive Montgomery
    ///   reduction. Does so by first writing the verifying key and then
    ///   serializing the rest of the data (in the form of field polynomials)
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        self.vk.write(writer, format)?;
        write_polynomial_slice(&self.fixed_values, writer)?;
        // Only the Lagrange form is written: [`Self::read`] derives the
        // coefficient form and the cosets from it.
        write_polynomial_slice(&self.sigmas.values, writer)?;
        Ok(())
    }

    /// Reads a proving key from a buffer.
    /// Does so by reading verification key first, and then deserializing the
    /// rest of the file into the remaining proving key data.
    ///
    /// Reads a curve element from the buffer and parses it according to the
    /// `format`:
    /// - `Processed`: Reads a compressed curve element and decompresses it.
    ///   Reads a field element in standard form, with endianness specified by
    ///   the `PrimeField` implementation, and checks that the element is less
    ///   than the modulus.
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in
    ///   Montgomery form. Checks that field elements are less than modulus, and
    ///   then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with
    ///   coordinates in Montgomery form; does not perform any checks
    pub fn read<R: io::Read, ConcreteCircuit: Circuit<F>>(
        reader: &mut R,
        format: SerdeFormat,
        #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
    ) -> io::Result<Self> {
        let vk = VerifyingKey::<F, CS>::read::<R, ConcreteCircuit>(
            reader,
            format,
            #[cfg(feature = "circuit-params")]
            params,
        )?;
        let [l0, l_last, l_active_row] = compute_lagrange_polys(&vk, &vk.cs);
        let fixed_values: Vec<_> = read_polynomial_vec(reader, format)?;
        let permutations: Vec<_> = read_polynomial_vec(reader, format)?;
        if permutations.len() != vk.cs.permutation.columns.len() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "{} permutation polynomials, expected {}",
                    permutations.len(),
                    vk.cs.permutation.columns.len()
                ),
            ));
        }
        let (phase0_polys, simple_selector_polys, fixed_cosets, sigmas) = build_phase0_polys(
            &vk.domain,
            &vk.cs,
            vk.transcript_repr,
            &fixed_values,
            permutations,
        );
        let ev = Evaluator::new(vk.cs());
        Ok(Self {
            vk,
            l0,
            l_last,
            l_active_row,
            fixed_values,
            fixed_cosets,
            phase0_polys,
            simple_selector_polys,
            sigmas,
            ev,
            // The region layout is not serialized: the first proof produced
            // from a deserialized key will re-run the shape pass. Subsequent
            // proofs from the same in-memory key still pay that cost unless
            // the caller caches the layout externally.
            region_starts: None,
        })
    }

    /// Writes a proving key to a vector of bytes using [`Self::write`].
    pub fn to_bytes(&self, format: SerdeFormat) -> Vec<u8> {
        let mut bytes = Vec::<u8>::with_capacity(self.bytes_length(format));
        Self::write(self, &mut bytes, format).expect("Writing to vector should not fail");
        bytes
    }

    /// Reads a proving key from a slice of bytes using [`Self::read`].
    pub fn from_bytes<ConcreteCircuit: Circuit<F>>(
        mut bytes: &[u8],
        format: SerdeFormat,
        #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
    ) -> io::Result<Self> {
        Self::read::<_, ConcreteCircuit>(
            &mut bytes,
            format,
            #[cfg(feature = "circuit-params")]
            params,
        )
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> VerifyingKey<F, CS> {
    /// Get the underlying [`EvaluationDomain`].
    pub fn get_domain(&self) -> &EvaluationDomain<F> {
        &self.domain
    }
}

/// Partially evaluates the (batched) identities: all polynomials, except those
/// corresponding to simple, multiplicative selectors, are evaluated at the
/// evaluation challenge `x`.
///
/// This function is a boilerplate for, both, prover and verifier. The prover
/// uses it to compute the linearization polynomial, while the verifier needs it
/// to compute the commitment to the linearization polynomial.
///
/// # Returns
///
/// The partially evaluated batched identity. It is given as a [Vec] of 2-tuples
/// `(Option<usize>, F)` containing an evaluation point (representing a
/// partially or fully evaluated identity at `x`) and an [Option] which
/// references:
///     * the fixed column index of a simple, multiplicative selector, if this
///       evaluation point is multiplied by such a selector,
///     * `None` otherwise.
#[allow(clippy::too_many_arguments)]
pub(crate) fn partially_evaluate_identities<'a, F, CS>(
    vk: &'a VerifyingKey<F, CS>,
    instance_evals: &'a [F],
    phase0_evals: &BTreeMap<PolynomialLabel, Vec<argument::Evaluation<F>>>,
    phase1_evals: &BTreeMap<PolynomialLabel, Vec<argument::Evaluation<F>>>,
    phase2_evals: &BTreeMap<PolynomialLabel, Vec<argument::Evaluation<F>>>,
    x: F,
    xn: F,
    beta: F,
    gamma: F,
    theta: F,
    trash_challenge: F,
) -> Vec<(Option<usize>, F)>
where
    F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
{
    // The advice evaluations in the order of `cs.advice_queries`, which is how
    // the identities index them. In the phase1 group, each column's follow the
    // order of its queries.
    let mut next = vec![0; vk.cs.num_advice_columns];
    let advice_evals: Vec<F> = vk
        .cs
        .advice_queries
        .iter()
        .map(|(column, _)| {
            let i = column.index();
            let eval = phase1_evals[&PolynomialLabel::Advice(i)][next[i]].eval();
            next[i] += 1;
            eval
        })
        .collect();
    let advice_evals = &advice_evals[..];

    // Likewise for the fixed evaluations, from the phase-0 group. Simple
    // selectors are not opened.
    let mut next = vec![0; vk.cs.num_fixed_columns];
    let fixed_evals: Vec<F> = vk
        .cs
        .fixed_queries
        .iter()
        .map(|(column, _)| {
            let i = column.index();
            if vk.cs.has_simple_selector_col(i) {
                // The linearization scales the selector's commitment by this
                // evaluation, so the selector must contribute 1 here: another
                // value breaks completeness, and 0 lets the gate go unenforced.
                return F::ONE;
            }
            let eval = phase0_evals[&PolynomialLabel::Fixed(i)][next[i]].eval();
            next[i] += 1;
            eval
        })
        .collect();
    let fixed_evals = &fixed_evals[..];

    let blinding_factors = vk.cs.blinding_factors();
    let l_evals = vk.domain.l_i_range(x, xn, (-((blinding_factors + 1) as i32))..=0);
    assert_eq!(l_evals.len(), 2 + blinding_factors);
    let l_last = l_evals[0];
    let l_blind: F =
        l_evals[1..(1 + blinding_factors)].iter().fold(F::ZERO, |acc, eval| acc + eval);
    let l_0 = l_evals[1 + blinding_factors];
    // Evaluate the circuit using the custom gates provided
    vk.cs
        .gates
        .iter()
        .flat_map(move |gate| {
            gate.polynomials().iter().map(move |poly| {
                let evaluation = poly.evaluate(
                    &|scalar| scalar,
                    &|_| panic!("virtual selectors are removed during optimization"),
                    &|query| fixed_evals[query.index.unwrap()],
                    &|query| advice_evals[query.index.unwrap()],
                    &|query| instance_evals[query.index.unwrap()],
                    &|a| -a,
                    &|a, b| a + &b,
                    &|a, b| a * &b,
                    &|a, scalar| a * &scalar,
                );
                (
                    gate.queried_selectors()
                        .iter()
                        .filter(|s| s.is_simple())
                        .map(|s| s.index())
                        .next(),
                    evaluation,
                )
            })
        })
        .chain(
            expressions(
                vk,
                &vk.cs.permutation,
                phase0_evals,
                phase2_evals,
                advice_evals,
                fixed_evals,
                instance_evals,
                l_0,
                l_last,
                l_blind,
                beta,
                gamma,
                x,
            )
            .map(|e| (None, e)),
        )
        .chain(
            vk.cs
                .lookups
                .iter()
                .map(|l| l.chunk_by_degree(vk.cs_degree))
                .enumerate()
                .flat_map(move |(argument_index, argument)| {
                    argument
                        .expressions(
                            argument_index,
                            phase1_evals,
                            phase2_evals,
                            l_0,
                            l_last,
                            l_blind,
                            theta,
                            beta,
                            advice_evals,
                            fixed_evals,
                            instance_evals,
                        )
                        .collect::<Vec<_>>()
                })
                .map(|e| (None, e)),
        )
        .chain(
            vk.cs
                .trashcans
                .iter()
                .flat_map(move |argument| {
                    argument.expressions(
                        phase2_evals,
                        trash_challenge,
                        advice_evals,
                        fixed_evals,
                        instance_evals,
                    )
                })
                .map(|e| (None, e)),
        )
        .collect::<Vec<(Option<usize>, F)>>()
}
