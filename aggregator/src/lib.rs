//! A toolkit for proof aggregation of midnight-proofs.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

// #[doc = include_str!("../README.md")]

// When truncated-challenges is enabled, don't compile any of the aggregator
// code as it's incompatible with this feature.
#[cfg(not(feature = "truncated-challenges"))]
extern crate core;

#[cfg(not(feature = "truncated-challenges"))]
mod inner_product_argument;
#[cfg(not(feature = "truncated-challenges"))]
mod light_fiat_shamir;
#[cfg(not(feature = "truncated-challenges"))]
mod light_self_emulation;

#[cfg(not(feature = "truncated-challenges"))]
pub mod light_aggregator;
