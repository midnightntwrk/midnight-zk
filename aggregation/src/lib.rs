//! A toolkit for proof aggregation of midnight-proofs.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

// #[doc = include_str!("../README.md")]

extern crate core;

use midnight_proofs::poly::pcs::FflonkScheme;

/// Temporary alias for the polynomial commitment scheme used by every
/// aggregator circuit in this crate.
///
/// TODO: When the in-circuit verifier gains support for the bundled path,
/// replace this alias by [`midnight_proofs::MidnightPCS`].
pub type KZG<E> = FflonkScheme<E>;

pub mod ivc;
pub mod multi_circuit_aggregator;
