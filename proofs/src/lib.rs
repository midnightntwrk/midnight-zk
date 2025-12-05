//! # midnight_proofs

#![cfg_attr(docsrs, feature(doc_cfg))]
// The actual lints we want to disable.
#![allow(clippy::op_ref, clippy::many_single_char_names)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![cfg_attr(not(feature = "gpu"), deny(unsafe_code))]
#![cfg_attr(feature = "gpu", allow(unsafe_code))]

pub mod circuit;
pub use halo2curves;
#[cfg(feature = "gpu")]
pub mod gpu;
pub mod plonk;
pub mod poly;
pub mod transcript;

pub mod dev;
pub mod utils;
