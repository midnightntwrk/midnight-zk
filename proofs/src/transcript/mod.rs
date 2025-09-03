//! This module contains utilities and traits for dealing with Fiat-Shamir
//! transcripts.
mod implementors;

use std::io::{self, Cursor, Read, Write};

/// Prefix to a prover's message soliciting a challenge
const BLAKE2B_PREFIX_CHALLENGE: u8 = 0;

/// Prefix to a prover's message
const BLAKE2B_PREFIX_COMMON: u8 = 1;

/// Hash function that can be used for transcript
pub trait TranscriptHash {
    /// Input type of the hash function
    type Input;
    /// Output type of the hash function
    type Output;

    /// Initialise the hasher
    fn init() -> Self;
    /// Absorb an element
    fn absorb(&mut self, input: &Self::Input);
    /// Squeeze an output
    fn squeeze(&mut self) -> Self::Output;
}

/// Traits to represent values that can be hashed with a `TranscriptHash`
pub trait Hashable<H: TranscriptHash>: Sized {
    /// Converts the hashable type to a format that can be hashed with `H`
    fn to_input(&self) -> H::Input;

    /// Converts the hashable type to bytes to be added to the transcript.
    fn to_bytes(&self) -> Vec<u8>;

    /// Reads bytes from a buffer and returns `Self`.
    fn read(buffer: &mut impl Read) -> io::Result<Self>;
}

/// Trait to represent values that can be sampled from a `TranscriptHash`
pub trait Sampleable<H: TranscriptHash> {
    /// Converts `H`'s output to Self
    fn sample(hash_output: H::Output) -> Self;
}

/// Generic transcript view
pub trait Transcript {
    /// Hash function
    type Hash: TranscriptHash;

    /// Initialises the transcript
    fn init() -> Self;

    /// Parses an existing transcript
    fn init_from_bytes(bytes: &[u8]) -> Self;

    /// Squeeze a challenge of type `T`, which only needs to be `Sampleable`
    /// with the corresponding hash function.
    fn squeeze_challenge<T: Sampleable<Self::Hash>>(&mut self) -> T;

    /// Writing a hashable element `T` to the transcript without writing it to
    /// the proof, treating it as a common commitment.
    fn common<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()>;

    /// Read a hashable element `T` from the prover.
    fn read<T: Hashable<Self::Hash>>(&mut self) -> io::Result<T>;

    /// Write a hashable element `T` to the proof and the transcript.
    fn write<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()>;

    /// Returns the buffer with the proof.
    fn finalize(self) -> Vec<u8>;

    /// Checks that the transcript is empty.
    /// This is used to make sure a transcript does not contain trailing bytes
    /// at the end of a proof verification.
    fn assert_empty(&mut self) -> io::Result<()>;
}

#[derive(Clone, Debug)]
/// Transcript used in proofs, parametrised by its hash function.
pub struct CircuitTranscript<H: TranscriptHash> {
    state: H,
    buffer: Cursor<Vec<u8>>,
}

impl<H: TranscriptHash> CircuitTranscript<H> {
    /// Returns the buffer for non default reading of the buffer (such as for
    /// reading an empty proof)
    pub fn buffer(&mut self) -> &mut Cursor<Vec<u8>> {
        &mut self.buffer
    }
}

impl<H: TranscriptHash> Transcript for CircuitTranscript<H> {
    type Hash = H;

    fn init() -> Self {
        Self {
            state: H::init(),
            buffer: Cursor::new(vec![]),
        }
    }

    fn init_from_bytes(bytes: &[u8]) -> Self {
        Self {
            state: H::init(),
            buffer: Cursor::new(bytes.to_vec()),
        }
    }

    fn squeeze_challenge<T: Sampleable<H>>(&mut self) -> T {
        T::sample(self.state.squeeze())
    }

    fn common<T: Hashable<H>>(&mut self, input: &T) -> io::Result<()> {
        self.state.absorb(&input.to_input());

        Ok(())
    }

    fn read<T: Hashable<H>>(&mut self) -> io::Result<T> {
        let val = T::read(&mut self.buffer)?;
        self.common(&val)?;

        Ok(val)
    }

    fn write<T: Hashable<H>>(&mut self, input: &T) -> io::Result<()> {
        self.common(input)?;
        let bytes = input.to_bytes();
        self.buffer.write_all(&bytes)
    }

    fn finalize(self) -> Vec<u8> {
        self.buffer.into_inner()
    }

    fn assert_empty(&mut self) -> io::Result<()> {
        if self.buffer.get_ref().len() == self.buffer.position() as usize {
            return Ok(());
        }

        Err(io::Error::new(
            io::ErrorKind::NotFound,
            "Transcript has unexpected trailing bytes.",
        ))
    }
}

pub(crate) fn read_n<C, T>(transcript: &mut T, n: usize) -> io::Result<Vec<C>>
where
    T: Transcript,
    C: Hashable<T::Hash>,
{
    (0..n).map(|_| transcript.read()).collect()
}
