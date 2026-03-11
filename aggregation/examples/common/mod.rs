//! Shared utilities for aggregation examples.
//!
//! Contains reusable inner circuit definitions that can be used as building
//! blocks in proof aggregation examples.

use midnight_proofs::poly::EvaluationDomain;
use midnight_zk_stdlib::{ZkStdLib, ZkStdLibArch};

type F = midnight_curves::Fq;

pub mod sha_preimage;

/// Returns the constraint system and evaluation domain for a circuit with the
/// given architecture and size parameter `k` (log2 of rows).
pub fn constraint_system(
    arch: ZkStdLibArch,
    k: u32,
) -> (
    midnight_proofs::plonk::ConstraintSystem<F>,
    EvaluationDomain<F>,
) {
    let mut cs = midnight_proofs::plonk::ConstraintSystem::default();
    ZkStdLib::configure(&mut cs, arch);
    let domain = EvaluationDomain::new(cs.degree() as u32, k);
    (cs, domain)
}
