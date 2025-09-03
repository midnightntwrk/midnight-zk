//! A toolkit for proof aggregation of midnight-proofs.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

// #[doc = include_str!("../README.md")]

extern crate core;

mod inner_product_argument;
mod light_fiat_shamir;
mod light_self_emulation;

pub mod light_aggregator;
