//! A toolkit for proof aggregation of midnight-proofs.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

// #[doc = include_str!("../README.md")]

extern crate core;

use midnight_proofs::poly::fflonk::FflonkScheme;

/// Temporary alias for the polynomial commitment scheme used by every
/// aggregator circuit in this crate.
///
/// All aggregator paths (light, IVC, multi-circuit) currently pin to
/// `FflonkScheme<_, 0>`, which is algebraically identical to GWC KZG.
/// This pin is forced by the in-circuit verifier gadget in
/// `midnight-circuits`, which does not yet implement fflonk's bundle
/// pre-expansion for `T_MAX_LOG > 0`.
///
/// When the in-circuit verifier gains support for the bundled path,
/// this alias either follows [`midnight_proofs::MidnightPCS`] or is
/// removed outright. Deleting it surfaces every site that still
/// hardcodes the pin via compilation errors.
pub type KZG<E> = FflonkScheme<E, 0>;

// When truncated-challenges is enabled, don't compile any of the aggregator
// code as it's incompatible with this feature.
#[cfg(not(feature = "truncated-challenges"))]
pub mod light_aggregator;

pub mod ivc;
pub mod multi_circuit_aggregator;
