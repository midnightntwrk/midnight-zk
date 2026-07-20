//! # midnight_proofs

#![cfg_attr(docsrs, feature(doc_cfg))]
// The actual lints we want to disable.
#![allow(clippy::op_ref, clippy::many_single_char_names)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

pub mod circuit;
pub mod plonk;
pub mod poly;
pub mod transcript;

pub mod dev;
pub mod utils;

/// Bundle-size cap for the fflonk PCS. `0` means no bundling (algebraically
/// identical to plain KZG); bumping it trades extra SRS / per-commit MSM cost
/// for verifier and proof-size savings.
pub use poly::pcs::FFLONK_T_MAX_LOG;

/// The polynomial commitment scheme used by all Midnight-ZK keys and proofs
/// in this build. Routed through a single alias so the choice of PCS is one
/// type-system flip rather than a workspace-wide find/replace.
pub type MidnightPCS = poly::pcs::FflonkScheme<midnight_curves::Bls12>;

/// KZG as a special case of fflonk: `FflonkScheme<E>`. Kept as a (temporary)
/// named alias for call sites (tests, examples, benches) that want the
/// KZG-equivalent scheme.
pub type KZG<E> = poly::pcs::FflonkScheme<E>;
