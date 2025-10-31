use std::fmt;

use midnight_proofs::plonk;

use crate::{instructions::operations::Operation, types::IrType};

type Name = String;

/// A ZKIR error.
#[derive(Clone, PartialEq)]
pub enum Error {
    /// The arity of the given operation was not properly met.
    ///
    /// This error typically occurs when an instruction has a different number
    /// of inputs/outputs than what the operation expects.
    InvalidArity(Operation),

    /// The given string cannot be parsed as a constant of the given type.
    ParsingError(IrType, String),

    /// The given name was not found in the memory.
    ///
    /// This error typically occurs when a certain witness is not provided, or
    /// if an instruction (supposed to produce some value) is missing.
    NotFound(Name),

    /// The given name already exists in the memory.
    ///
    /// This error occurs when a variable is being "shadowed", we do not allow
    /// this in ZKIR instructions, every output name should be unique.
    DuplicatedName(Name),

    /// The former type was expected, whereas the latter was given.
    ///
    /// This error can occur if an operation is called on the wrong type.
    /// For example "select" expects a [crate::types::IrValue::Bool] as its
    /// first argument. This error will be triggered if any other variant of
    /// [crate::types::IrValue] is provided instead.
    ExpectingType(IrType, IrType),

    /// The given operation is not supported on the given types.
    ///
    /// This error occurs, for example, when trying to add two Boolean values,
    /// since addition is not supported on this type.
    Unsupported(Operation, Vec<IrType>),

    /// Any other error not covered by the above cases, with a descriptive
    /// message.
    Other(String),
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidArity(op) => write!(f, "wrong arity: '{op:?}'"),
            Error::ParsingError(t, s) => write!(f, "'{s:?}' cannot be parsed as a {t:?}"),
            Error::NotFound(s) => write!(f, "'{s}' not found"),
            Error::DuplicatedName(s) => write!(f, "'{s}' already exists"),
            Error::ExpectingType(e, t) => write!(f, "type {e:?} was expected instead of {t:?}"),
            Error::Unsupported(op, t) => write!(f, "{op:?} is not supported on {t:?}"),
            Error::Other(s) => write!(f, "{s}"),
        }
    }
}

impl From<Error> for plonk::Error {
    fn from(error: Error) -> Self {
        plonk::Error::Synthesis(format!("{error:?}"))
    }
}

impl From<plonk::Error> for Error {
    fn from(error: plonk::Error) -> Self {
        Error::Other(format!("{error:?}"))
    }
}
