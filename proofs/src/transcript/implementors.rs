use std::{io, io::Read};

use blake2b_simd::{Params, State as Blake2bState};
use ff::{FromUniformBytes, PrimeField};
use group::GroupEncoding;
use halo2curves::bn256::{Fr, G1};

use crate::transcript::{
    Hashable, Sampleable, TranscriptHash, BLAKE2B_PREFIX_CHALLENGE, BLAKE2B_PREFIX_COMMON,
};

impl TranscriptHash for Blake2bState {
    type Input = Vec<u8>;
    type Output = Vec<u8>;

    fn init() -> Self {
        Params::new()
            .hash_length(64)
            .key(b"Domain separator for transcript")
            .to_state()
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

// ///////////////////////////////////////////////////
// /// Implementation of Hashable for BN with Blake //
// ///////////////////////////////////////////////////

impl<T: TranscriptHash<Input = Vec<u8>>> Hashable<T> for u8 {
    fn to_input(&self) -> Vec<u8> {
        vec![*self]
    }

    fn to_bytes(&self) -> Vec<u8> {
        vec![*self]
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut byte = [0u8; 1];
        buffer.read_exact(&mut byte)?;
        Ok(byte[0])
    }
}

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

        Option::from(Self::from_bytes(&bytes)).ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "Invalid BN point encoding in proof")
        })
    }
}

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

        Option::from(Self::from_repr(bytes)).ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "Invalid BN scalar encoding in proof")
        })
    }
}

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

impl Hashable<Blake2bState> for midnight_curves::G1Projective {
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

        Option::from(Self::from_bytes(&bytes)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "Invalid BLS12-381 point encoding in proof",
            )
        })
    }
}

impl Hashable<Blake2bState> for midnight_curves::Fq {
    fn to_input(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "Invalid BLS12-381 scalar encoding in proof",
            )
        })
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

impl Hashable<Blake2bState> for halo2curves::bls12381::G1 {
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

        Option::from(Self::from_bytes(&bytes)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "Invalid BLS12-381 point encoding in proof",
            )
        })
    }
}

impl Hashable<Blake2bState> for halo2curves::bls12381::Fr {
    fn to_input(&self) -> Vec<u8> {
        self.to_repr().as_ref().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "Invalid BLS12-381 scalar encoding in proof",
            )
        })
    }
}

impl Sampleable<Blake2bState> for halo2curves::bls12381::Fr {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        halo2curves::bls12381::Fr::from_uniform_bytes(&bytes)
    }
}
