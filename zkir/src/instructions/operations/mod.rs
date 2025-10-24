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

    /// Returns a `Bool` indicating whether the given inputs are equal.
    ///
    /// Inputs:  2
    /// Outputs: 1
    ///
    /// Supported on all types except: `JubjubScalar`.
    IsEqual,

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

    /// Subtracts the given inputs, returns their difference.
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
    ///
    /// In the case of `BigUint`, trying to subtract a bigger value from a
    /// smaller one will result in an unsatisfiable circuit.
    /// (Or in a run-time error in an off-circuit execution.)
    Sub,

    /// Multiplies the given inputs, returns their product.
    /// The input types do not need to be the same, we list below the supported
    /// combinations of input types.
    ///
    /// Inputs:  2
    /// Outputs: 1
    ///
    /// Supported on types:
    ///  - `Native x Native -> Native`
    ///  - `BigUint x BigUint -> BigUint`
    ///  - `JubjubScalar x JubjubPoint -> JubjubPoint`
    Mul,

    /// Negates the given input, returns its additive inverse.
    /// This function fails if the inputs types are not the same or if they are
    /// not supported.
    ///
    /// Inputs:  1
    /// Outputs: 1
    ///
    /// Supported on types:
    ///  - `Native`
    ///  - `JubjubPoint`
    Neg,

    /// Computes the inner-product between the first half of inputs and the
    /// second half. Concretely, given 2n inputs, this instruction returns
    /// $\sum_{i = 0}^{n-1} inputs\[i\] * inputs\[n + i\]$.
    /// This instruction is potentially more efficient than a fold combining
    /// [Operation::Mul] and [Operation::Add].
    ///
    /// Inputs:  even
    /// Outputs: 1
    ///
    /// Supported on types:
    ///
    ///    inputs[..n/2]     inputs[n/2..]     output
    ///   ------------------------------------------------
    ///    `Native`          `Native`          `Native`
    ///    `BigUint`         `BigUint`         `BigUint`
    ///    `JubjubScalar`s   `JubjubPoint`s    `JubjubPoint`
    InnerProduct,
}

mod add;
mod assert_equal;
mod inner_product;
mod is_equal;
mod load;
mod mul;
mod neg;
mod publish;
mod sub;

pub use add::*;
pub use assert_equal::*;
pub use inner_product::*;
pub use is_equal::*;
pub use load::*;
pub use mul::*;
pub use neg::*;
pub use publish::*;
pub use sub::*;
