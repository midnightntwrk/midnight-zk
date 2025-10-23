//! Error type for the support crate.

use std::{num::ParseIntError, str::ParseBoolError};

use num_bigint::{BigInt, ParseBigIntError, TryFromBigIntError};
use thiserror::Error;

use crate::fields::Blstrs;

/// Error type.
#[derive(Error, Debug)]
pub enum Error {
    /// Parsing error while loading a field element from a string.
    #[error("Failure while parsing field element")]
    FieldParsingError,
    /// The circuit requested more constants than provided.
    #[error("Not enough constants")]
    NotEnoughConstants,
    /// The circuit did not declare enough cells for input or output.
    #[error("IO cell iterator was exhausted")]
    NotEnoughIOCells,
    /// Integer parse error.
    #[error("Parse failure")]
    IntParse(#[from] ParseIntError),
    /// Boolean parse error.
    #[error("Parse failure")]
    BoolParse(#[from] ParseBoolError),
    /// BigUint parse error.
    #[error("Parse failure")]
    BigUintParse(#[from] ParseBigIntError),
    /// Plonk synthesis error.
    #[error("Synthesis error")]
    Plonk(#[from] PlonkError),
    /// An error represented with an static string.
    #[error("Error")]
    StrError(&'static str),
    /// Error when a constant point is not in the elliptic curve
    #[error("Point ({0}, {1}) is not in the curve")]
    PointNotInCurve(Blstrs, Blstrs),
    /// Int cast error.
    #[error(transparent)]
    IntCast(#[from] std::num::TryFromIntError),
    /// Big int cast error.
    #[error(transparent)]
    BigIntCast(#[from] TryFromBigIntError<BigInt>),
    /// Error when an encountered an unexpected number of elements.
    #[error("Was expected {expected} elements but got {actual}")]
    UnexpectedElements {
        /// The expected number of elements.
        expected: usize,
        /// The number of elements.
        actual: usize,
    },
}

impl From<&'static str> for Error {
    fn from(value: &'static str) -> Self {
        Self::StrError(value)
    }
}

/// Alias for the error emitted by Halo2 during synthesis.
pub type PlonkError = midnight_proofs::plonk::Error;

impl From<Error> for PlonkError {
    fn from(value: Error) -> Self {
        match value {
            Error::Plonk(err) => err,
            err => Self::Transcript(std::io::Error::other(err)),
        }
    }
}
