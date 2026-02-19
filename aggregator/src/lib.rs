//! A toolkit for proof aggregation of midnight-proofs.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

// #[doc = include_str!("../README.md")]

extern crate core;

// When truncated-challenges is enabled, don't compile any of the aggregator
// code as it's incompatible with this feature.
#[cfg(not(feature = "truncated-challenges"))]
pub mod light_aggregator;
