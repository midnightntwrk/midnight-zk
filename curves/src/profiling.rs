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
    /// The trash argument.
    Trash,
    /// Committing to the polynomials of the lookup, permutation and trash
    /// arguments, which the prover commits to as one group.
    ArgumentsCommit,
    /// Computing and committing to the quotient polynomial.
    Quotient,
    /// Evaluating the committed polynomials at the challenge points.
    Evals,
    /// The multi-opening argument.
    MultiOpen,
}

impl Phase {
    /// All phases, in the order the prover goes through them.
    pub const ALL: [Phase; 10] = [
        Phase::Preamble,
        Phase::Synthesis,
        Phase::AdviceCommit,
        Phase::Lookups,
        Phase::Permutation,
        Phase::Trash,
        Phase::ArgumentsCommit,
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
            Phase::Trash => "trash",
            Phase::ArgumentsCommit => "arguments_commit",
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
    #[cfg(feature = "profiling")]
    open: Option<recorder::Open>,
    #[cfg(not(feature = "profiling"))]
    _private: (),
}

#[cfg(feature = "profiling")]
impl Drop for Guard {
    #[inline]
    fn drop(&mut self) {
        if let Some(open) = self.open.take() {
            recorder::close(open);
        }
    }
}

/// Opens a span of `kernel` over an input of `size` elements.
///
/// A span opened on a thread that already has an open span counts as a call
/// but adds no time, so that the time of a kernel calling another one, or of
/// a blocked thread stealing a task, is counted once.
#[inline(always)]
pub fn span(kernel: Kernel, size: usize) -> Guard {
    let _ = size;
    #[cfg(feature = "profiling")]
    {
        Guard {
            open: recorder::open(kernel),
        }
    }
    #[cfg(not(feature = "profiling"))]
    {
        let _ = kernel;
        Guard { _private: () }
    }
}

/// Marks the start of `phase`, which lasts until the next call or until
/// [`take_report`].
#[inline(always)]
pub fn set_phase(phase: Phase) {
    #[cfg(feature = "profiling")]
    recorder::set_phase(phase);
    #[cfg(not(feature = "profiling"))]
    let _ = phase;
}

/// Discards everything recorded so far and starts in [`Phase::Preamble`].
#[inline(always)]
pub fn reset() {
    #[cfg(feature = "profiling")]
    recorder::reset();
}

/// Ends the current phase and returns the breakdown since [`reset`].
///
/// Nothing is recorded from this call until the next [`reset`], and a second
/// call without one returns an empty report.
#[inline(always)]
pub fn take_report() -> Report {
    #[cfg(feature = "profiling")]
    {
        recorder::take_report()
    }
    #[cfg(not(feature = "profiling"))]
    {
        Report::default()
    }
}

#[cfg(feature = "profiling")]
mod recorder {
    use std::{
        cell::Cell,
        sync::{
            Arc, Mutex, MutexGuard, PoisonError,
            atomic::{AtomicBool, Ordering},
        },
        time::{Duration, Instant},
    };

    use super::{Kernel, KernelStats, Phase, PhaseReport, Report};

    /// A span that has been opened but not closed yet.
    #[derive(Debug)]
    pub(super) struct Open {
        kernel: Kernel,
        start: Instant,
    }

    /// A closed span.
    #[derive(Clone, Copy, Debug)]
    pub(super) struct Span {
        pub(super) kernel: Kernel,
        pub(super) start: Instant,
        pub(super) end: Instant,
    }

    type Buffer = Arc<Mutex<Vec<Span>>>;

    struct State {
        /// When the current recording started, if there is one.
        start: Option<Instant>,
        /// The phases entered since `start`, with the time of entry.
        marks: Vec<(Phase, Instant)>,
        /// The span buffer of every thread that ever recorded. Threads of a
        /// pool outlive the proof, so their spans are collected from here.
        buffers: Vec<Buffer>,
    }

    static STATE: Mutex<State> = Mutex::new(State {
        start: None,
        marks: Vec::new(),
        buffers: Vec::new(),
    });

    /// Whether spans and phases are being recorded. Outside a recording they
    /// are dropped, so that the buffers do not grow without a reader.
    static RECORDING: AtomicBool = AtomicBool::new(false);

    struct Local {
        /// Whether this thread has an open span.
        open: Cell<bool>,
        /// The closed spans of this thread. Only `reset` and `take_report`
        /// ever contend for the lock.
        spans: Buffer,
    }

    thread_local! {
        static LOCAL: Local = {
            let spans = Buffer::default();
            lock(&STATE).buffers.push(spans.clone());
            Local { open: Cell::new(false), spans }
        };
    }

    // A panic while holding a lock leaves the data consistent enough for
    // timing purposes, and profiling must not turn it into a second panic.
    fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
        mutex.lock().unwrap_or_else(PoisonError::into_inner)
    }

    #[inline]
    pub(super) fn open(kernel: Kernel) -> Option<Open> {
        if !RECORDING.load(Ordering::Relaxed) {
            return None;
        }
        // The thread-local is gone while the thread is being torn down.
        let start = Instant::now();
        let outermost = LOCAL
            .try_with(|local| {
                let outermost = !local.open.replace(true);
                if !outermost {
                    // An empty span counts the call without adding time.
                    lock(&local.spans).push(Span {
                        kernel,
                        start,
                        end: start,
                    });
                }
                outermost
            })
            .unwrap_or(false);
        outermost.then_some(Open { kernel, start })
    }

    #[inline]
    pub(super) fn close(open: Open) {
        let end = Instant::now();
        let _ = LOCAL.try_with(|local| {
            local.open.set(false);
            if RECORDING.load(Ordering::Relaxed) {
                lock(&local.spans).push(Span {
                    kernel: open.kernel,
                    start: open.start,
                    end,
                });
            }
        });
    }

    pub(super) fn set_phase(phase: Phase) {
        if !RECORDING.load(Ordering::Relaxed) {
            return;
        }
        let mut state = lock(&STATE);
        // The time is read under the lock so that the marks are in order.
        let now = Instant::now();
        if state.start.is_some() {
            state.marks.push((phase, now));
        }
    }

    pub(super) fn reset() {
        let mut state = lock(&STATE);
        RECORDING.store(false, Ordering::Relaxed);
        // A buffer whose thread has exited is only referenced from here.
        state.buffers.retain(|buffer| Arc::strong_count(buffer) > 1);
        for buffer in &state.buffers {
            lock(buffer).clear();
        }
        state.marks.clear();
        state.start = Some(Instant::now());
        RECORDING.store(true, Ordering::Relaxed);
    }

    pub(super) fn take_report() -> Report {
        let mut state = lock(&STATE);
        RECORDING.store(false, Ordering::Relaxed);
        let end = Instant::now();
        let Some(start) = state.start.take() else {
            return Report::default();
        };
        let spans: Vec<Span> = (state.buffers.iter())
            .flat_map(|buffer| std::mem::take(&mut *lock(buffer)))
            .collect();
        let marks = std::mem::take(&mut state.marks);
        drop(state);
        build_report(start, end, &marks, &spans)
    }

    /// The total length of the union of `intervals`.
    pub(super) fn union(intervals: &mut [(Instant, Instant)]) -> Duration {
        intervals.sort_unstable();
        let mut total = Duration::ZERO;
        // The latest end among the intervals seen so far.
        let mut reach: Option<Instant> = None;
        for &(start, end) in intervals.iter() {
            let uncovered_from = reach.map_or(start, |reach| reach.max(start));
            total += end.saturating_duration_since(uncovered_from);
            reach = Some(reach.map_or(end, |reach| reach.max(end)));
        }
        total
    }

    /// The report of a recording from `start` to `end`, given the phases
    /// entered in between, in order of entry, and the closed spans.
    ///
    /// A span belongs to the phase during which it started. It is cut at the
    /// end of that stay in the phase, so that the time covered in a phase
    /// never exceeds the time of the phase. Spans that started outside the
    /// recording are ignored.
    pub(super) fn build_report(
        start: Instant,
        end: Instant,
        marks: &[(Phase, Instant)],
        spans: &[Span],
    ) -> Report {
        #[derive(Default)]
        struct PhaseAcc {
            entered: bool,
            wall: Duration,
            stats: [KernelStats; Kernel::ALL.len()],
            intervals: [Vec<(Instant, Instant)>; Kernel::ALL.len()],
        }

        let mut phases: Vec<PhaseAcc> = Phase::ALL.iter().map(|_| PhaseAcc::default()).collect();

        // The stays in a phase, `(phase, from, to)`, in chronological order.
        let froms = [(Phase::Preamble, start)].into_iter().chain(marks.iter().copied());
        let tos = marks.iter().map(|&(_, at)| at).chain([end]);
        let stays: Vec<(Phase, Instant, Instant)> =
            froms.zip(tos).map(|((phase, from), to)| (phase, from, to)).collect();

        for &(phase, from, to) in &stays {
            let acc = &mut phases[phase as usize];
            acc.entered = true;
            acc.wall += to.saturating_duration_since(from);
        }

        for span in spans {
            let next = stays.partition_point(|&(_, from, _)| from <= span.start);
            let Some(&(phase, _, to)) = next.checked_sub(1).and_then(|i| stays.get(i)) else {
                continue;
            };
            if span.start >= to {
                continue;
            }
            let span_end = span.end.min(to);
            let acc = &mut phases[phase as usize];
            let kernel = span.kernel as usize;
            acc.stats[kernel].calls += 1;
            acc.stats[kernel].busy += span_end.saturating_duration_since(span.start);
            acc.intervals[kernel].push((span.start, span_end));
        }

        let phases = (Phase::ALL.iter().zip(phases))
            .filter(|(_, acc)| acc.entered)
            .map(|(&phase, mut acc)| {
                for (stats, intervals) in acc.stats.iter_mut().zip(acc.intervals.iter_mut()) {
                    stats.wall = union(intervals);
                }
                PhaseReport {
                    phase,
                    wall: acc.wall,
                    covered: union(&mut acc.intervals.concat()),
                    kernels: acc.stats,
                }
            })
            .collect();

        Report {
            total: end.saturating_duration_since(start),
            phases,
        }
    }
}

#[cfg(all(test, not(feature = "profiling")))]
mod tests {
    use super::*;

    #[test]
    fn disabled_build_records_nothing() {
        const { assert!(!ENABLED) };
        assert_eq!(std::mem::size_of::<Guard>(), 0);
        assert!(!std::mem::needs_drop::<Guard>());

        reset();
        set_phase(Phase::Quotient);
        drop(span(Kernel::Msm, 1));
        assert_eq!(take_report(), Report::default());
    }
}

#[cfg(all(test, feature = "profiling"))]
mod tests {
    use std::{
        sync::{Barrier, Mutex, MutexGuard, PoisonError},
        thread,
        time::{Duration, Instant},
    };

    use super::{
        recorder::{Span, build_report, union},
        *,
    };

    const MSM: usize = 0;
    const FFT: usize = 1;
    const POLY_EVAL: usize = 2;

    /// Instants at the given numbers of milliseconds after a common origin.
    struct Clock(Instant);

    impl Clock {
        fn new() -> Self {
            Clock(Instant::now())
        }

        fn at(&self, ms: u64) -> Instant {
            self.0 + Duration::from_millis(ms)
        }

        fn span(&self, kernel: Kernel, start: u64, end: u64) -> Span {
            Span {
                kernel,
                start: self.at(start),
                end: self.at(end),
            }
        }

        fn union(&self, intervals: &[(u64, u64)]) -> Duration {
            let mut intervals: Vec<_> =
                intervals.iter().map(|&(start, end)| (self.at(start), self.at(end))).collect();
            union(&mut intervals)
        }
    }

    fn ms(ms: u64) -> Duration {
        Duration::from_millis(ms)
    }

    fn stats(wall: u64, busy: u64, calls: u64) -> KernelStats {
        KernelStats {
            wall: ms(wall),
            busy: ms(busy),
            calls,
        }
    }

    fn phase(report: &Report, phase: Phase) -> &PhaseReport {
        report.phases.iter().find(|p| p.phase == phase).expect("the phase was entered")
    }

    // The recorder is global, so the tests that drive it must not overlap.
    fn exclusive() -> MutexGuard<'static, ()> {
        static LOCK: Mutex<()> = Mutex::new(());
        LOCK.lock().unwrap_or_else(PoisonError::into_inner)
    }

    #[test]
    fn indices_follow_reporting_order() {
        for (i, kernel) in Kernel::ALL.iter().enumerate() {
            assert_eq!(*kernel as usize, i);
        }
        for (i, phase) in Phase::ALL.iter().enumerate() {
            assert_eq!(*phase as usize, i);
        }
        assert_eq!(Kernel::ALL[MSM], Kernel::Msm);
        assert_eq!(Kernel::ALL[FFT], Kernel::Fft);
        assert_eq!(Kernel::ALL[POLY_EVAL], Kernel::PolyEval);
    }

    #[test]
    fn union_of_intervals() {
        let clock = Clock::new();
        assert_eq!(clock.union(&[]), ms(0));
        // Disjoint.
        assert_eq!(clock.union(&[(0, 10), (20, 30)]), ms(20));
        // Disjoint, out of order.
        assert_eq!(clock.union(&[(20, 30), (0, 10), (40, 45)]), ms(25));
        // Touching.
        assert_eq!(clock.union(&[(0, 10), (10, 30)]), ms(30));
        // Overlapping.
        assert_eq!(clock.union(&[(0, 10), (5, 30)]), ms(30));
        // Nested.
        assert_eq!(clock.union(&[(0, 30), (5, 10)]), ms(30));
        assert_eq!(clock.union(&[(0, 30), (5, 10), (25, 40), (50, 60)]), ms(50));
        // Identical.
        assert_eq!(clock.union(&[(5, 10), (5, 10), (5, 10)]), ms(5));
        // Empty intervals.
        assert_eq!(clock.union(&[(5, 5), (7, 7)]), ms(0));
    }

    #[test]
    fn concurrent_spans_are_not_summed() {
        let clock = Clock::new();
        let spans = [
            clock.span(Kernel::Fft, 10, 30),
            clock.span(Kernel::Fft, 20, 40),
            clock.span(Kernel::Fft, 20, 40),
            clock.span(Kernel::Fft, 60, 70),
        ];
        let report = build_report(clock.at(0), clock.at(100), &[], &spans);

        assert_eq!(report.total, ms(100));
        assert_eq!(report.phases.len(), 1);
        let preamble = &report.phases[0];
        assert_eq!(preamble.phase, Phase::Preamble);
        assert_eq!(preamble.wall, ms(100));
        assert_eq!(preamble.covered, ms(40));
        assert_eq!(preamble.kernels[FFT], stats(40, 70, 4));
        assert_eq!(preamble.kernels[MSM], KernelStats::default());
        assert_eq!(preamble.kernels[POLY_EVAL], KernelStats::default());
    }

    #[test]
    fn kernels_are_separate_and_covered_is_their_union() {
        let clock = Clock::new();
        let spans = [
            clock.span(Kernel::Msm, 0, 20),
            clock.span(Kernel::Fft, 10, 30),
            clock.span(Kernel::PolyEval, 50, 60),
            clock.span(Kernel::Msm, 55, 58),
        ];
        let report = build_report(clock.at(0), clock.at(100), &[], &spans);

        let preamble = &report.phases[0];
        assert_eq!(preamble.kernels[MSM], stats(23, 23, 2));
        assert_eq!(preamble.kernels[FFT], stats(20, 20, 1));
        assert_eq!(preamble.kernels[POLY_EVAL], stats(10, 10, 1));
        // The kernels overlap, so their wall times add up to more.
        assert_eq!(preamble.covered, ms(40));
    }

    #[test]
    fn spans_belong_to_the_phase_they_start_in() {
        let clock = Clock::new();
        let marks = [
            (Phase::Synthesis, clock.at(10)),
            (Phase::Lookups, clock.at(30)),
            (Phase::AdviceCommit, clock.at(40)),
            (Phase::Lookups, clock.at(60)),
            (Phase::Quotient, clock.at(70)),
        ];
        let spans = [
            // Before and after the recording.
            clock.span(Kernel::Msm, 0, 5),
            clock.span(Kernel::Msm, 100, 105),
            clock.span(Kernel::Fft, 2, 8),
            clock.span(Kernel::PolyEval, 32, 38),
            clock.span(Kernel::Msm, 40, 55),
            clock.span(Kernel::Msm, 41, 56),
            clock.span(Kernel::PolyEval, 62, 66),
            // Running past the end of the phase, and of the recording.
            clock.span(Kernel::PolyEval, 68, 75),
            clock.span(Kernel::Fft, 85, 120),
        ];
        let report = build_report(clock.at(1), clock.at(90), &marks, &spans);

        assert_eq!(report.total, ms(89));
        let order: Vec<_> = report.phases.iter().map(|p| p.phase).collect();
        assert_eq!(
            order,
            [
                Phase::Preamble,
                Phase::Synthesis,
                Phase::AdviceCommit,
                Phase::Lookups,
                Phase::Quotient
            ]
        );
        assert_eq!(
            report.phases.iter().map(|p| p.wall).sum::<Duration>(),
            report.total
        );

        let preamble = phase(&report, Phase::Preamble);
        assert_eq!(preamble.wall, ms(9));
        assert_eq!(preamble.covered, ms(6));
        assert_eq!(preamble.kernels[MSM], KernelStats::default());
        assert_eq!(preamble.kernels[FFT], stats(6, 6, 1));

        let synthesis = phase(&report, Phase::Synthesis);
        assert_eq!(synthesis.wall, ms(20));
        assert_eq!(synthesis.covered, ms(0));

        let advice_commit = phase(&report, Phase::AdviceCommit);
        assert_eq!(advice_commit.wall, ms(20));
        assert_eq!(advice_commit.covered, ms(16));
        assert_eq!(advice_commit.kernels[MSM], stats(16, 30, 2));

        // Both stays in the phase are merged.
        let lookups = phase(&report, Phase::Lookups);
        assert_eq!(lookups.wall, ms(20));
        assert_eq!(lookups.covered, ms(12));
        assert_eq!(lookups.kernels[POLY_EVAL], stats(12, 12, 3));

        let quotient = phase(&report, Phase::Quotient);
        assert_eq!(quotient.wall, ms(20));
        assert_eq!(quotient.kernels[POLY_EVAL], KernelStats::default());
        assert_eq!(quotient.kernels[FFT], stats(5, 5, 1));
    }

    #[test]
    fn nested_spans_add_no_time() {
        let _exclusive = exclusive();
        reset();
        {
            let _outer = span(Kernel::Msm, 8);
            thread::sleep(ms(2));
            {
                let _inner = span(Kernel::Fft, 8);
                let _innermost = span(Kernel::Msm, 8);
                thread::sleep(ms(2));
            }
            drop(span(Kernel::PolyEval, 8));
        }
        // The thread accepts spans again once the outermost one is closed.
        drop(span(Kernel::PolyEval, 8));
        let report = take_report();

        let preamble = phase(&report, Phase::Preamble);
        assert_eq!(preamble.kernels[MSM].calls, 2);
        assert!(preamble.kernels[MSM].busy >= ms(4));
        assert_eq!(preamble.kernels[MSM].busy, preamble.kernels[MSM].wall);
        assert_eq!(preamble.kernels[FFT], stats(0, 0, 1));
        assert_eq!(preamble.kernels[POLY_EVAL].calls, 2);
    }

    #[test]
    fn spans_of_other_threads_are_collected() {
        const THREADS: usize = 4;

        let _exclusive = exclusive();
        reset();
        set_phase(Phase::Quotient);
        let barrier = Barrier::new(THREADS);
        thread::scope(|scope| {
            for _ in 0..THREADS {
                scope.spawn(|| {
                    barrier.wait();
                    let _span = span(Kernel::Fft, 8);
                    thread::sleep(ms(50));
                });
            }
        });
        drop(span(Kernel::Msm, 8));
        let report = take_report();

        let quotient = phase(&report, Phase::Quotient);
        let fft = quotient.kernels[FFT];
        assert_eq!(fft.calls, THREADS as u64);
        assert!(fft.busy >= ms(50) * THREADS as u32);
        assert!(fft.wall >= ms(50));
        // The threads sleep at the same time, so the union is shorter.
        assert!(fft.wall < fft.busy);
        assert_eq!(quotient.kernels[MSM].calls, 1);
        assert!(fft.wall <= quotient.covered);
        assert!(quotient.covered <= quotient.wall);
        assert!(quotient.wall <= report.total);
    }

    #[test]
    fn recording_is_bracketed_by_reset_and_take_report() {
        let _exclusive = exclusive();
        // Leftovers of an earlier recording, and a span open across the reset.
        reset();
        set_phase(Phase::MultiOpen);
        drop(span(Kernel::Msm, 8));
        let straddling = span(Kernel::Fft, 8);

        reset();
        drop(straddling);
        set_phase(Phase::Synthesis);
        set_phase(Phase::Evals);
        drop(span(Kernel::PolyEval, 8));
        set_phase(Phase::Synthesis);
        let report = take_report();

        let order: Vec<_> = report.phases.iter().map(|p| p.phase).collect();
        assert_eq!(order, [Phase::Preamble, Phase::Synthesis, Phase::Evals]);
        assert_eq!(
            report.phases.iter().map(|p| p.wall).sum::<Duration>(),
            report.total
        );
        let calls = |phase: &PhaseReport| phase.kernels.map(|kernel| kernel.calls);
        assert_eq!(calls(phase(&report, Phase::Preamble)), [0, 0, 0]);
        assert_eq!(calls(phase(&report, Phase::Synthesis)), [0, 0, 0]);
        assert_eq!(calls(phase(&report, Phase::Evals)), [0, 0, 1]);

        // Nothing is recorded until the next reset.
        set_phase(Phase::Quotient);
        drop(span(Kernel::Msm, 8));
        assert_eq!(take_report(), Report::default());
    }
}
