use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};

use crate::types::IrType;

/// A single IR operation that an IR [crate::Instruction] can perform.
#[derive(Clone, Copy, Debug, PartialEq, Encode, Decode, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Operation {
    /// Exhibits (potentially secret) values of the given IR type.
    /// This is the entry point of every non-constant value.
    ///
    /// Inputs:  0
    /// Outputs: >= 1 (variadic)
    ///
    /// Supported on all IR types.
    Load(IrType),

    /// Discloses the given inputs, adding them to the vector of public values.
    ///
    /// Inputs:  >= 1 (variadic)
    /// Outputs: 0
    ///
    /// Supported on all IR types.
    ///
    /// # Notes
    ///
    /// A value may be "published" more than once, in which case it will appear
    /// several times in the vector of public values.
    ///
    /// Constants can also be published if they are needed in the vector of
    /// public values for some reason.
    ///
    /// Inputs of different types can be published together in a single
    /// `Publish` operation.
    Publish,

    /// Constrains the given inputs to be equal.
    ///
    /// Inputs:  2
    /// Outputs: 0
    ///
    /// Supported on all types except: `JubjubScalar`.
    AssertEqual,

    /// Adds the given inputs, returns their sum.
    /// This function fails if the inputs types are not the same or if they are
    /// not supported.
    ///
    /// Inputs:  2
    /// Outputs: 1
    ///
    /// Supported on types:
    ///  - `Native`
    ///  - `BigUint`
    ///  - `JubjubPoint`
    Add,
}

mod add;
mod assert_equal;
mod load;
mod publish;

pub use add::*;
pub use assert_equal::*;
pub use load::*;
pub use publish::*;
