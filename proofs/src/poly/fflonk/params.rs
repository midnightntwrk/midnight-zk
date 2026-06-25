//! fflonk parameters.
//!
//! fflonk reuses KZG's SRS as-is: the monomial basis `[s^i]_1` for
//! `0 ≤ i < t·n` is exactly the [`ParamsKZG::g`] vector, just sized to
//! `t·n` rather than `n`. We expose this via a type alias so the scheme's
//! `Parameters` is distinct at use sites but shares all infrastructure
//! (load/save/downsize, etc.).
//!
//! The Lagrange basis (`ParamsKZG::g_lagrange`) stays sized to the circuit
//! domain `n`; only the monomial basis is extended. This is structurally
//! identical to the `single-h-commitment` feature's extended monomial
//! basis, which already covers this case. Without that feature, the SRS
//! must still be loaded with `g.len() ≥ T_MAX · n`.

use crate::poly::kzg::params::ParamsKZG;

/// Parameters for fflonk: reuses the KZG SRS layout. The monomial basis
/// `params.g` must satisfy `params.g.len() ≥ T_MAX · n` where `n = 2^k` is
/// the circuit domain size and `T_MAX` is the largest bundle size used.
pub type ParamsFflonk<E> = ParamsKZG<E>;

/// Verifier parameters for fflonk: same as KZG's.
pub type ParamsVerifierFflonk<E> = crate::poly::kzg::params::ParamsVerifierKZG<E>;
