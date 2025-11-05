//! A toolkit for parsing ZKIR circuits.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

mod error;
mod instructions;
mod parser;
mod types;
mod utils;
mod zkir;

pub use error::Error;
pub use instructions::{operations::Operation, Instruction};
pub use types::{IrType, IrValue};
pub use zkir::ZkirRelation;
