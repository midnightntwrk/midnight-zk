//! # midnight_proofs

#![cfg_attr(docsrs, feature(doc_cfg))]
// The actual lints we want to disable.
#![allow(clippy::op_ref, clippy::many_single_char_names)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

pub mod circuit;
pub mod pcs;
pub mod plonk;
pub mod poly;
pub mod transcript;

pub mod dev;
pub mod utils;

/// The polynomial commitment scheme Midnight's keys and proofs are built with,
/// over the pairing engine `E`. Everything that means "the scheme this library
/// ships" goes through this alias, so switching schemes is a single edit. Use
/// the following line to switch to Fflonk:
// pub type MidnightPCS<E> = pcs::fflonk::FflonkScheme<E>;
pub type MidnightPCS<E> = pcs::kzg::KZGCommitmentScheme<E>;

/// The commitment type of [`MidnightPCS`]. Callers that just mean "a commitment
/// as this library produces them" name this rather than a concrete scheme's
/// type, so it follows the alias above.
pub type MidnightCommitment<E> = <MidnightPCS<E> as pcs::PolynomialCommitmentScheme<
    <E as midnight_curves::pairing::Engine>::Fr,
>>::Commitment;
