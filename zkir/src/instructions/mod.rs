use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};

pub mod arity;
pub mod operations;

#[derive(Clone, Debug, PartialEq, Encode, Decode, Serialize, Deserialize)]
/// A ZKIR instruction is parametrized by a ZKIR operation
/// and a series of inputs and outputs (in the form of value names).
///
/// Some operations have a specific fixed arity, see [arity::Arity].
/// The number of inputs and outputs must coincide with the input and output
/// arity of the operation. We perform run-time arity checks when reading
/// programs (list of instructions).
pub struct Instruction {
    /// The operation performed by this instruction.
    #[serde(rename = "op")]
    pub operation: operations::Operation,

    /// Names of the inputs of this instruction.
    #[serde(default)]
    pub inputs: Vec<String>,

    /// Names of the outputs of this instruction.
    #[serde(default)]
    pub outputs: Vec<String>,
}
