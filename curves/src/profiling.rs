//! Wall-time accounting for the prover's kernels: MSMs, FFTs and polynomial
//! evaluations.
//!
//! Kernels wrap their body in a [`span`] and the prover announces its current
//! [`Phase`] with [`set_phase`]. A caller brackets a proof with [`reset`] and
//! [`take_report`] to obtain the time spent in each kernel during each phase.
//!
//! Recording only happens with the `profiling` feature. Without it every
//! function here is an empty inline function and the report is empty.

use std::time::Duration;

/// A class of prover computation whose time is accounted separately.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kernel {
    /// Multi-scalar multiplications.
    Msm,
    /// Fast Fourier transforms, in either direction and over any domain.
    Fft,
    /// Evaluation of polynomials and of the circuit identities.
    PolyEval,
}

impl Kernel {
    /// All kernels, in reporting order.
    pub const ALL: [Kernel; 3] = [Kernel::Msm, Kernel::Fft, Kernel::PolyEval];

    /// A short human-readable name.
    pub fn name(self) -> &'static str {
        match self {
            Kernel::Msm => "msm",
            Kernel::Fft => "fft",
            Kernel::PolyEval => "poly_eval",
        }
    }
}

/// A stage of proof generation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Phase {
    /// Everything between [`reset`] and the first call to [`set_phase`].
    Preamble,
    /// Witness generation: synthesizing the circuit into the advice columns.
    Synthesis,
    /// Committing to the advice columns.
    AdviceCommit,
    /// The lookup argument.
    Lookups,
    /// The permutation argument.
    Permutation,
    /// Computing and committing to the quotient polynomial.
    Quotient,
    /// Evaluating the committed polynomials at the challenge points.
    Evals,
    /// The multi-opening argument.
    MultiOpen,
}

impl Phase {
    /// All phases, in the order the prover goes through them.
    pub const ALL: [Phase; 8] = [
        Phase::Preamble,
        Phase::Synthesis,
        Phase::AdviceCommit,
        Phase::Lookups,
        Phase::Permutation,
        Phase::Quotient,
        Phase::Evals,
        Phase::MultiOpen,
    ];

    /// A short human-readable name.
    pub fn name(self) -> &'static str {
        match self {
            Phase::Preamble => "preamble",
            Phase::Synthesis => "synthesis",
            Phase::AdviceCommit => "advice_commit",
            Phase::Lookups => "lookups",
            Phase::Permutation => "permutation",
            Phase::Quotient => "quotient",
            Phase::Evals => "evals",
            Phase::MultiOpen => "multi_open",
        }
    }
}

/// The time one kernel took during one phase.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelStats {
    /// Wall time during which at least one span of this kernel was open.
    pub wall: Duration,
    /// Sum of the durations of all spans, which exceeds `wall` when spans of
    /// this kernel run concurrently.
    pub busy: Duration,
    /// Number of spans.
    pub calls: u64,
}

/// The time spent in one phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhaseReport {
    /// The phase this entry describes.
    pub phase: Phase,
    /// Wall time of the phase.
    pub wall: Duration,
    /// Wall time during which at least one span of any kernel was open. The
    /// remainder of `wall` is time spent outside the kernels.
    pub covered: Duration,
    /// Per-kernel figures, indexed as [`Kernel::ALL`]. Their `wall` times may
    /// add up to more than `covered` when different kernels overlap.
    pub kernels: [KernelStats; 3],
}

/// The breakdown of the time between [`reset`] and [`take_report`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Report {
    /// Wall time between [`reset`] and [`take_report`].
    pub total: Duration,
    /// One entry per phase that was entered, in the order of [`Phase::ALL`].
    pub phases: Vec<PhaseReport>,
}

/// Whether this build records anything.
pub const ENABLED: bool = cfg!(feature = "profiling");

/// An open span, closed when dropped.
#[must_use = "the span closes when the guard is dropped"]
#[derive(Debug)]
pub struct Guard {
    _private: (),
}

/// Opens a span of `kernel` over an input of `size` elements.
#[inline(always)]
pub fn span(kernel: Kernel, size: usize) -> Guard {
    let _ = (kernel, size);
    Guard { _private: () }
}

/// Marks the start of `phase`, which lasts until the next call or until
/// [`take_report`].
#[inline(always)]
pub fn set_phase(phase: Phase) {
    let _ = phase;
}

/// Discards everything recorded so far and starts in [`Phase::Preamble`].
#[inline(always)]
pub fn reset() {}

/// Ends the current phase and returns the breakdown since [`reset`].
#[inline(always)]
pub fn take_report() -> Report {
    Report::default()
}
