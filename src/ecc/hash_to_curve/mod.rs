//! This module provides a set of tools for in/off-circuit hashing into elliptic
//! curves.
//!
//! See RFC 9380 <https://www.rfc-editor.org/rfc/rfc9380.html>.
//!
//! We adapt the above techniques to also hash into Edwards curves.

mod htc_gadget;
mod mtc;
mod mtc_cpu;
mod mtc_params;

pub use htc_gadget::*;
pub use mtc::MapToCurveInstructions;
pub use mtc_cpu::MapToCurveCPU;
pub use mtc_params::MapToEdwardsParams;
