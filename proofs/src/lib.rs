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

/// Bundle-size cap for the fflonk PCS in this build. `0` means no bundling
/// (singleton path, byte-equivalent to baseline KZG). Bumping this is how
/// the integration trades extra SRS / per-commit MSM cost for verifier and
/// proof-size savings; bench sweeps drive the choice.
pub const FFLONK_T_MAX_LOG: u32 = 0;

/// The polynomial commitment scheme used by all Midnight-ZK keys and proofs
/// in this build. Routed through a single alias so the choice of PCS is one
/// type-system flip rather than a workspace-wide find/replace.
///
/// At `FFLONK_T_MAX_LOG = 0`, [`poly::fflonk::FflonkScheme`] runs through
/// its singleton path: `commit` is `MSM(poly, monomial_bases)`, `multi_open`
/// is the standard Halo2 GWC argument, and the wire format matches
/// `KZGMultiCommitment` byte-for-byte (asserted by the
/// `fflonk_t_max_log_0_proof_matches_kzg` test in `poly::fflonk::tests`),
/// so proofs and VKs are bit-identical to the previous
/// `KZGCommitmentScheme` build.
pub type MidnightPCS =
    poly::fflonk::FflonkScheme<midnight_curves::Bls12, FFLONK_T_MAX_LOG>;
