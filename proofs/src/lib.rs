//! # midnight_proofs

#![cfg_attr(docsrs, feature(doc_cfg))]
// The actual lints we want to disable.
#![allow(clippy::op_ref, clippy::many_single_char_names)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

pub mod circuit;
#[cfg(feature = "gpu")]
pub mod gpu;
#[cfg(feature = "prover-par")]
pub(crate) mod par;
pub mod plonk;
pub mod poly;
#[cfg(any(test, feature = "gpu-test"))]
pub(crate) mod test_circuit;
pub mod transcript;

pub mod dev;
pub mod utils;
