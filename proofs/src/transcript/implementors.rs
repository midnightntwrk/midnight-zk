use std::{io, io::Read};

use blake2b_simd::{Params, State as Blake2bState};
use ff::{FromUniformBytes, PrimeField};
use group::GroupEncoding;
#[cfg(feature = "dev-curves")]
use midnight_curves::bn256::{Fr, G1};

use crate::transcript::{
    Hashable, Sampleable, TranscriptHash, BLAKE2B_PREFIX_CHALLENGE, BLAKE2B_PREFIX_COMMON,
};

impl TranscriptHash for Blake2bState {
    type Input = Vec<u8>;
    type Output = Vec<u8>;

    fn init() -> Self {
        Params::new().hash_length(64).key(b"Domain separator for transcript").to_state()
    }

    fn absorb(&mut self, input: &Self::Input) {
        self.update(&[BLAKE2B_PREFIX_COMMON]);
        self.update(input);
    }

    fn squeeze(&mut self) -> Self::Output {
        self.update(&[BLAKE2B_PREFIX_CHALLENGE]);
        self.finalize().as_bytes().to_vec()
    }
}

/// Custom Blake2b-256 transcript hash that accumulates data in a `Vec<u8>`
/// and resets to the hash output on squeeze, keeping the state compact.
///
/// This is designed for on-chain verification (e.g. Cardano/Plutus), where
/// blake2b-256 is available as a native built-in and memory efficiency matters.
///
/// Only BLS12-381 types (`G1Projective`, `Fq`) implement `Hashable` and
/// `Sampleable` for this hash, as it targets the Midnight proof system.
#[derive(Clone, Debug)]
pub struct Blake2b256 {
    transcript_data: Vec<u8>,
}

impl TranscriptHash for Blake2b256 {
    type Input = Vec<u8>;
    type Output = Vec<u8>;

    fn init() -> Self {
        Self {
            transcript_data: vec![],
        }
    }

    fn absorb(&mut self, input: &Self::Input) {
        self.transcript_data.extend_from_slice(input);
    }

    fn squeeze(&mut self) -> Self::Output {
        let h = Params::new().hash_length(32).hash(&self.transcript_data);
        let result = h.as_bytes().to_vec();
        self.transcript_data = result.clone();
        result
    }
}

impl<T: TranscriptHash<Input = Vec<u8>>> Hashable<T> for u32 {
    fn to_input(&self) -> Vec<u8> {
        self.to_le_bytes().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_le_bytes().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = [0u8; 4];
        buffer.read_exact(&mut bytes)?;
        Ok(u32::from_le_bytes(bytes))
    }
}

#[cfg(feature = "dev-curves")]
impl Hashable<Blake2bState> for G1 {
    /// Converts it to compressed form in bytes
    fn to_input(&self) -> Vec<u8> {
        Hashable::to_bytes(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        <Self as GroupEncoding>::to_bytes(self).as_ref().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as GroupEncoding>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_bytes(&bytes))
            .ok_or_else(|| io::Error::other("Invalid BN point encoding in proof"))
    }
}

#[cfg(feature = "dev-curves")]
impl Hashable<Blake2bState> for Fr {
    fn to_input(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes))
            .ok_or_else(|| io::Error::other("Invalid BN scalar encoding in proof"))
    }
}

#[cfg(feature = "dev-curves")]
impl Sampleable<Blake2bState> for Fr {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        Fr::from_uniform_bytes(&bytes)
    }
}

// //////////////////////////////////////////////////////////
// /// Implementation of Hashable for BLS12-381 with Blake //
// //////////////////////////////////////////////////////////

impl<H: TranscriptHash<Input = Vec<u8>>> Hashable<H> for midnight_curves::G1Projective {
    /// Converts it to compressed form in bytes
    fn to_input(&self) -> Vec<u8> {
        Hashable::<H>::to_bytes(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        <Self as GroupEncoding>::to_bytes(self).as_ref().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as GroupEncoding>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_bytes(&bytes))
            .ok_or_else(|| io::Error::other("Invalid BLS12-381 point encoding in proof"))
    }
}

impl<H: TranscriptHash<Input = Vec<u8>>> Hashable<H> for midnight_curves::Fq {
    fn to_input(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes))
            .ok_or_else(|| io::Error::other("Invalid BLS12-381 scalar encoding in proof"))
    }
}

impl Sampleable<Blake2bState> for midnight_curves::Fq {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        assert!(hash_output.len() >= (midnight_curves::Fq::NUM_BITS as usize / 8) + 12);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        midnight_curves::Fq::from_uniform_bytes(&bytes)
    }
}

/// WARNING: With a 32-byte hash output and a 255-bit scalar field, the
/// statistical distance to uniform is not negligible, some field elements are
/// about twice as likely as others. This is acceptable for Fiat-Shamir but
/// would not be for applications requiring near-uniform sampling.
impl Sampleable<Blake2b256> for midnight_curves::Fq {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert_eq!(hash_output.len(), 32);
        let mut bytes = [0u8; 64];
        bytes[..32].copy_from_slice(&hash_output);
        midnight_curves::Fq::from_uniform_bytes(&bytes)
    }
}
