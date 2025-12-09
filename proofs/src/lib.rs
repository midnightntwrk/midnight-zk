//! # midnight_proofs

#![cfg_attr(docsrs, feature(doc_cfg))]
// The actual lints we want to disable.
#![allow(clippy::op_ref, clippy::many_single_char_names)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

pub mod circuit;
pub use halo2curves;
pub mod plonk;
pub mod poly;
pub mod transcript;

pub mod dev;
pub mod utils;

/// Implementation of [`Halo2Types`](extractor_support::Halo2Types).
#[derive(Debug)]
#[cfg(feature = "extraction")]
pub struct ExtractionSupport;

#[cfg(feature = "extraction")]
impl<F: ff::Field> extractor_support::Halo2Types<F> for ExtractionSupport {
    type InstanceCol = crate::plonk::Column<crate::plonk::Instance>;

    type AdviceCol = crate::plonk::Column<crate::plonk::Advice>;

    type Cell = crate::circuit::Cell;

    type AssignedCell<V> = crate::circuit::AssignedCell<V, F>;

    type Region<'a> = crate::circuit::Region<'a, F>;

    type Error = crate::plonk::Error;

    type RegionIndex = crate::circuit::RegionIndex;

    type Expression = crate::plonk::Expression<F>;

    type Rational = crate::utils::rational::Rational<F>;
}
