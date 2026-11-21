// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Concurrent proving of independent proofs (a batch).
//!
//! Several independent proofs run at once: the host phases of one proof
//! (synthesis, CPU work) overlap the device phases of the others. Each job
//! runs the caller's ordinary proof entry point with its own transcript.
//! Every hook call still serves exactly one MSM, one transform or one
//! quotient of one proof and returns its result to that proof only; no
//! device work of two proofs is ever grouped.
//!
//! The batch adds, removes and reorders no random draw and no transcript
//! operation of any job, so with the same random stream a proof of a batch
//! is byte-identical to the same proof made alone.
//!
//! Fresh randomness (per proof): the RNG factory is called once for every
//! proof that is started — every job, and again by the caller for every
//! retry or warm-up, which are further calls of these functions — and the
//! generator it returns is owned by that one proof. The default factory
//! ([`prove_batch`]) returns the operating-system generator. Nothing in
//! this module keeps a seed, a blinder, or a seed derived from a job.
//! [`prove_batch_with_rng`] takes a caller factory: a production caller
//! must return a fresh cryptographically secure generator on every call.
//! A seeded factory is provided only under the cargo feature `gpu-test`
//! (`seeded_rng_factory`); it does not exist in a build without it.
//!
//! One batch runs at a time. Hold the device session for the entire call
//! and pass its batch entries as scoped hooks. While the batch runs,
//! its scoped hook table is visible only on the batch pool's threads,
//! nested parallel work of a job on that pool included. Every other caller
//! of [`super::hooks`] — an ordinary proof on other threads using the
//! process-wide installed hooks — gets `None` and runs the stock CPU code,
//! so no ordinary device call interleaves with the batch's device calls
//! without the batch's isolation. This flag is a fast path only: the
//! device crate holds the admission boundary itself (its ordinary
//! entries decline while a batch session holds its gate, including a
//! call already past the hook lookup, a saved function pointer and a
//! direct caller), so correctness does not depend on the flag. Jobs
//! therefore must prove on the threads they are called on (or on rayon
//! work inside the same pool); a job that moves its proving to a thread
//! of its own proves on the CPU.
//!
//! Admission: jobs run in waves. A wave holds at most `in_flight` jobs
//! whose `weights` sum to at most `budget`. The weights are the caller's
//! device-memory estimate per job (for the quotient, the bytes its job
//! needs on the device); they bound the host and device working set of a
//! wave. A job whose weight is above `budget` runs alone on the CPU.
//! `after_wave` runs after every wave, once all its jobs have joined — also
//! when a job of the wave panicked, when the wave had no device hooks and
//! when an earlier failure switched the wave to the CPU. That is
//! the caller's request boundary: end the accelerator request there so
//! every device buffer of the wave is erased before the next wave starts.
//! `after_wave` does not run for a wave without jobs and not for an
//! oversized CPU job, which used no device.
//!
//! A job that panics yields [`JobPanicked`] for that job only; the other
//! jobs run to completion and `after_wave` still runs for its wave, so a
//! panicked proof does not leak its device buffers past the wave boundary.
//! Each nonempty batch scopes a process panic hook to its call. Batch workers
//! and batch device requests unwind silently. Other threads call the
//! embedding's previous hook. The scheduler drops payloads
//! unread. After eight consecutive destructor panics it leaks the last
//! payload and reports a failed boundary. A device operation outside a
//! batch that hits the same limit also latches the batch failure: from then
//! on every batch session in the process fails to begin (fail closed).
//!
//! A false result from `after_wave` records an erasure failure and switches
//! all remaining jobs and their nested work to CPU hooks. A call that finds
//! a batch already running returns [`BatchError::Busy`], including a
//! recursive call from a job or from wave cleanup.
//!
//! The batch pool has the caller's rayon width, so a job's nested parallel
//! sections see the thread count its caller runs with.
//!
//! A retired device (an accelerator that declines after a teardown) needs
//! no handling here: its hooks decline, and every later job of the batch
//! runs the stock CPU code.

use std::sync::{Arc, OnceLock};

use rand_core::{CryptoRng, OsRng, RngCore};

use super::GpuHooks;

/// A batch job panicked. The payload is dropped unread.
#[derive(Debug)]
pub struct JobPanicked;

/// The result of one job of a batch.
pub type JobResult<T> = Result<T, JobPanicked>;

/// Ordered job outcomes and the erasure status of the wave boundaries.
#[must_use]
pub struct BatchOutcome<T> {
    /// One outcome for each input, including jobs completed on the CPU.
    pub jobs: Vec<JobResult<T>>,
    /// A wave failed its erasure check or a panic payload could not be dropped.
    pub erasure_failed: bool,
}

impl<T> std::fmt::Debug for BatchOutcome<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BatchOutcome")
            .field("job_count", &self.jobs.len())
            .field("erasure_failed", &self.erasure_failed)
            .finish()
    }
}

/// A batch could not start.
#[derive(Debug, PartialEq, Eq)]
pub enum BatchError {
    /// Another caller holds the batch lock.
    Busy,
    /// The worker pool could not be created.
    PoolCreation,
    /// A nonempty batch was requested during unwinding.
    Unwinding,
}

std::thread_local! {
    /// Marks a batch worker or device request for the process panic hook.
    /// Pass this key to the device session so its owner uses the same flag.
    pub static BATCH_THREAD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static FAILURE: std::cell::RefCell<Option<Arc<OnceLock<()>>>> = const { std::cell::RefCell::new(None) };
}

/// The one-way failure flag on a scoped worker, including nested parallel work.
/// Outside that pool this returns `None`. Convert the flag to the budget or
/// channel's `Shutdown` with `Shutdown::from`.
pub fn failure_signal() -> Option<Arc<OnceLock<()>>> {
    FAILURE.with_borrow(Clone::clone)
}

/// The caller holds the batch lock and has rejected entry during unwind.
fn with_panic_hook<T>(run: impl FnOnce() -> T) -> T {
    use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind, set_hook, take_hook};

    let previous = Arc::new(std::sync::RwLock::new(Some(take_hook())));
    let chained = previous.clone();
    set_hook(Box::new(move |info| {
        if !BATCH_THREAD.get()
            && let Some(hook) = chained.read().unwrap().as_ref()
        {
            hook(info);
        }
    }));

    // Hook changes are forbidden on an unwinding thread. Restore the hook
    // before resuming the same panic, while the batch lock is still held.
    let result = catch_unwind(AssertUnwindSafe(run));
    let displaced = take_hook();
    // The embedding may still own the removed wrapper.
    let original = previous.write().unwrap().take().unwrap();
    set_hook(original);
    drop(displaced);
    result.unwrap_or_else(|payload| resume_unwind(payload))
}

/// Whether a batch is running in this process.
#[cfg(test)]
fn batch_active() -> bool {
    super::batch_active()
}

/// The test-only seeded RNG factory: job `i` gets the generator seeded
/// from `seed` and `i`, so seeded proofs are reproducible. Test builds
/// only (feature `gpu-test`); production proofs must use [`prove_batch`]
/// or a factory that returns fresh generators (see the module text).
#[cfg(feature = "gpu-test")]
pub fn seeded_rng_factory(seed: u64) -> impl Fn(usize) -> rand_chacha::ChaCha20Rng + Sync {
    use rand_core::SeedableRng;
    move |i| {
        rand_chacha::ChaCha20Rng::seed_from_u64(
            seed ^ (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15),
        )
    }
}

/// The scheduler sends `Err(slot)` once on the caller before jobs start so a
/// bound session can supply its failure flag. It sends `Ok(enabled)` on each
/// worker to grant or revoke admission. Forward both to the session's
/// `set_worker` method.
pub type WorkerAction<'a> = Result<bool, &'a mut Option<Arc<OnceLock<()>>>>;

/// The hook table and the session callback that grants or revokes access
/// on each scoped worker. Plain hook tables need no worker callback.
#[derive(Clone, Copy)]
pub struct BatchHooks<'a> {
    table: Option<&'static GpuHooks>,
    set_worker: Option<&'a (dyn Fn(WorkerAction<'_>) + Sync)>,
    stack_size: Option<usize>,
}

impl std::fmt::Debug for BatchHooks<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BatchHooks").finish_non_exhaustive()
    }
}

impl<'a> BatchHooks<'a> {
    /// Associates a table with the worker admission of the session that owns
    /// it.
    pub fn new(
        table: Option<&'static GpuHooks>,
        set_worker: &'a (dyn Fn(WorkerAction<'_>) + Sync),
    ) -> Self {
        Self {
            table,
            set_worker: Some(set_worker),
            stack_size: None,
        }
    }

    /// Sets the stack size in bytes for each scoped worker. While one job
    /// waits in a nested Rayon scope, the worker can start another job
    /// on the same stack. Allow space for all jobs that can nest, up to
    /// the number of jobs in the wave.
    pub fn with_stack_size(mut self, bytes: usize) -> Self {
        self.stack_size = Some(bytes);
        self
    }

    fn install(self, table: Option<&'static GpuHooks>) {
        if let Some(set) = self.set_worker {
            set(Ok(table.is_some()));
        }
        super::set_scoped_hooks(Some(table));
    }
}

impl From<Option<&'static GpuHooks>> for BatchHooks<'_> {
    fn from(table: Option<&'static GpuHooks>) -> Self {
        Self {
            table,
            set_worker: None,
            stack_size: None,
        }
    }
}

fn drop_payload(mut payload: Box<dyn std::any::Any + Send>, failure: &OnceLock<()>) {
    for _ in 0..8 {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(payload))) {
            Ok(()) => return,
            Err(next) => payload = next,
        }
    }
    std::mem::forget(payload);
    let _ = failure.set(());
}

/// Runs the jobs of a batch, each with a fresh operating-system generator.
/// Device exclusivity requires a live device `BatchSession` with its worker
/// admission callback. See [`prove_batch_with_rng`].
/// Use [`BatchHooks::with_stack_size`] to allow for jobs nesting on one worker.
/// Jobs waiting on shared resources must observe [`failure_signal`], as budget
/// waits do.
pub fn prove_batch<'a, T: Send>(
    weights: &[u64],
    budget: u64,
    in_flight: usize,
    hooks: impl Into<BatchHooks<'a>>,
    prove: impl Fn(usize, OsRng) -> T + Sync,
    after_wave: impl Fn() -> bool,
) -> Result<BatchOutcome<T>, BatchError> {
    prove_batch_with_rng(
        weights,
        budget,
        in_flight,
        hooks,
        |_| OsRng,
        prove,
        after_wave,
    )
}

/// Runs the jobs of a batch. `new_rng` is called exactly once for every
/// job that is started, oversized (CPU) jobs included, and its generator
/// is moved into that job's `prove` call. Results are in input order.
/// See the module text for the contracts on randomness, exclusivity,
/// waves, `after_wave` and panics. A plain hook table grants no device
/// exclusivity. Hold a device `BatchSession` and pass its worker callback.
/// The pool uses the default worker stack size unless the caller sets
/// [`BatchHooks::with_stack_size`]. Size it for the jobs of a wave that can
/// nest on one worker.
/// An embedding that lets jobs wait on a shared resource must use
/// [`failure_signal`] for those waits, as the budget does. Pass a clone to work
/// on other threads.
///
/// Each nonempty batch wraps the embedding's current panic hook. An OS
/// thread that a job spawns and joins is unmarked and reaches that hook
/// with the original panic information. The standard library has no atomic
/// hook swap. A panic on another thread reaches the default handler between
/// `take_hook` and `set_hook` at the start, while installing the batch hook,
/// and at the end, while restoring the embedding's hook. A hook installed
/// by the embedding during the batch is replaced by the earlier hook on
/// return or unwind. Outside the batch the embedding has its own hook again.
/// Taking and setting the hook wait for every thread that is inside a panic
/// hook at that moment (the standard library's hook lock), so the
/// embedding's hook must not block on anything that the caller holds across
/// the batch, such as the stderr lock.
pub fn prove_batch_with_rng<'a, T: Send, R: RngCore + CryptoRng>(
    weights: &[u64],
    budget: u64,
    in_flight: usize,
    hooks: impl Into<BatchHooks<'a>>,
    new_rng: impl Fn(usize) -> R + Sync,
    prove: impl Fn(usize, R) -> T + Sync,
    after_wave: impl Fn() -> bool,
) -> Result<BatchOutcome<T>, BatchError> {
    static BATCH_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _batch = match BATCH_LOCK.try_lock() {
        Ok(guard) => guard,
        Err(std::sync::TryLockError::Poisoned(e)) => e.into_inner(),
        Err(std::sync::TryLockError::WouldBlock) => return Err(BatchError::Busy),
    };
    if !weights.is_empty() && std::thread::panicking() {
        return Err(BatchError::Unwinding);
    }
    if weights.is_empty() {
        return Ok(BatchOutcome {
            jobs: Vec::new(),
            erasure_failed: false,
        });
    }
    with_panic_hook(|| {
        run_batch(
            weights,
            budget,
            in_flight,
            hooks.into(),
            new_rng,
            prove,
            after_wave,
        )
    })
}

fn run_batch<T: Send, R: RngCore + CryptoRng>(
    weights: &[u64],
    budget: u64,
    in_flight: usize,
    worker_hooks: BatchHooks<'_>,
    new_rng: impl Fn(usize) -> R + Sync,
    prove: impl Fn(usize, R) -> T + Sync,
    after_wave: impl Fn() -> bool,
) -> Result<BatchOutcome<T>, BatchError> {
    use rayon::prelude::*;

    let mut results = BatchOutcome {
        jobs: Vec::with_capacity(weights.len()),
        erasure_failed: false,
    };
    let hooks = worker_hooks.table;
    let mut session_failure = None;
    if let Some(bind) = worker_hooks.set_worker {
        bind(Err(&mut session_failure));
    }
    let failure = session_failure.unwrap_or_default();
    struct Active;
    impl Drop for Active {
        fn drop(&mut self) {
            super::set_batch_active(false);
        }
    }
    super::set_batch_active(true);
    let _active = Active;

    // One started job: one factory call, its generator moved into the
    // proof, its panic caught for this job only (payload unread).
    let run_one = |i: usize| -> JobResult<T> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove(i, new_rng(i)))) {
            Ok(v) => Ok(v),
            Err(payload) => {
                drop_payload(payload, &failure);
                Err(JobPanicked)
            }
        }
    };

    // The caller's rayon width, so nested parallel sections of a job see
    // the thread count of its caller. The scoped hooks are set on every
    // pool worker before it runs, so nested rayon work of a job on this
    // pool sees them too.
    // A plain caller may initialize the global pool while reading its width.
    let width = std::panic::catch_unwind(rayon::current_num_threads).map_err(|payload| {
        drop_payload(payload, &failure);
        BatchError::PoolCreation
    })?;
    let builder = rayon::ThreadPoolBuilder::new().num_threads(width);
    let builder = if let Some(bytes) = worker_hooks.stack_size {
        builder.stack_size(bytes)
    } else {
        builder
    };
    builder
        .build_scoped(
            |worker| {
                struct PanicScope;
                impl Drop for PanicScope {
                    fn drop(&mut self) {
                        FAILURE.set(None);
                        BATCH_THREAD.set(false);
                    }
                }
                BATCH_THREAD.set(true);
                FAILURE.set(Some(failure.clone()));
                let _scope = PanicScope;
                struct Exit<'a>(BatchHooks<'a>);
                impl Drop for Exit<'_> {
                    fn drop(&mut self) {
                        self.0.install(None);
                        super::set_scoped_hooks(None);
                    }
                }
                let _exit = Exit(worker_hooks);
                super::set_scoped_hooks(Some(None));
                worker.run();
            },
            |pool| {
                let mut next = 0;
                let mut hooks = hooks;
                while next < weights.len() {
                    if weights[next] > budget {
                        // Oversized: alone, on the CPU. The installed
                        // hooks must stay off too, for the job and all
                        // its nested parallel work.
                        results.jobs.push(pool.install(|| run_one(next)));
                        if failure.get().is_some() {
                            results.erasure_failed = true;
                            hooks = None;
                        }
                        next += 1;
                        continue;
                    }
                    let start = next;
                    let mut remaining = budget;
                    while next < weights.len() && next - start < in_flight.max(1) {
                        let weight = weights[next];
                        if weight > remaining {
                            break;
                        }
                        remaining -= weight;
                        next += 1;
                    }
                    if hooks.is_some() {
                        pool.broadcast(|_| worker_hooks.install(hooks));
                    }
                    let wave = pool.install(|| {
                        (start..next).into_par_iter().map(&run_one).collect::<Vec<_>>()
                    });
                    if hooks.is_some() {
                        pool.broadcast(|_| worker_hooks.install(None));
                    }
                    // The request boundary of the wave, after all its
                    // jobs joined, panicked jobs included.
                    let clean = after_wave();
                    if !clean {
                        let _ = failure.set(());
                    }
                    if failure.get().is_some() {
                        results.erasure_failed = true;
                        hooks = None;
                    }
                    results.jobs.extend(wave);
                }
            },
        )
        .map_err(|_| BatchError::PoolCreation)?;
    Ok(results)
}

#[cfg(test)]
mod tests {
    use std::{
        sync::atomic::{AtomicUsize, Ordering},
        time::{Duration, Instant},
    };

    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;
    use rayon::prelude::*;

    use super::*;

    fn in_child(body: impl FnOnce()) -> std::process::Output {
        let name = std::thread::current().name().unwrap().to_owned();
        const DONE: i32 = 42;
        if std::env::var("MIDNIGHT_BATCH_UNIT_TEST").as_deref() == Ok(&name) {
            body();
            std::process::exit(DONE);
        }
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", &name, "--nocapture"])
            .env("MIDNIGHT_BATCH_UNIT_TEST", name)
            .env("RUST_BACKTRACE", "0")
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                child.kill().unwrap();
                panic!("batch test child timed out");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        let output = child.wait_with_output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(DONE),
            "child did not complete the test"
        );
        output
    }

    static DUMMY: GpuHooks = GpuHooks {
        msm_g1: None,
        fft: None,
        ifft: None,
        quotient: None,
    };

    /// Waves by weight, the oversized job alone on the CPU, the scoped
    /// hooks on every pool thread (nested parallel work included), the
    /// caller's pool width, results in input order.
    #[test]
    fn waves_weights_scope_and_order() {
        in_child(|| {
            let waves = AtomicUsize::new(0);
            let draws = AtomicUsize::new(0);
            let caller = rayon::ThreadPoolBuilder::new().num_threads(3).build().unwrap();
            let results = caller
                .install(|| {
                    prove_batch_with_rng(
                        &[2, 2, 8, 3, 2],
                        4,
                        3,
                        Some(&DUMMY),
                        |_| {
                            draws.fetch_add(1, Ordering::Relaxed);
                            ChaCha20Rng::seed_from_u64(1)
                        },
                        |i, _rng| {
                            assert_eq!(rayon::current_num_threads(), 3);
                            let scoped = super::super::hooks().is_some();
                            assert_eq!(scoped, i != 2, "scoped hooks of job {i}");
                            assert!(
                                (0..32)
                                    .into_par_iter()
                                    .all(|_| super::super::hooks().is_some() == scoped),
                                "nested work of job {i} sees the same scope"
                            );
                            i
                        },
                        || {
                            waves.fetch_add(1, Ordering::Relaxed);
                            true
                        },
                    )
                })
                .unwrap()
                .jobs;
            let values: Vec<usize> =
                results.into_iter().map(|r| r.expect("no job panicked")).collect();
            assert_eq!(values, [0, 1, 2, 3, 4]);
            assert_eq!(waves.load(Ordering::Relaxed), 3, "waves [0,1], [3], [4]");
            assert_eq!(
                draws.load(Ordering::Relaxed),
                5,
                "one factory call per started job"
            );
            assert!(
                super::super::scoped_hooks().is_none(),
                "caller thread is not scoped"
            );
        });
    }

    /// Empty and single-job batches; `in_flight` 0 counts as 1.
    #[test]
    fn empty_and_single() {
        in_child(|| {
            let draws = AtomicUsize::new(0);
            let factory = |_| {
                draws.fetch_add(1, Ordering::Relaxed);
                ChaCha20Rng::seed_from_u64(2)
            };
            let empty = prove_batch_with_rng::<usize, _>(
                &[],
                0,
                0,
                None,
                factory,
                |i, _| i,
                || panic!("after_wave must not run for an empty batch"),
            );
            assert!(empty.unwrap().jobs.is_empty());
            let one = prove_batch_with_rng(&[7], 0, 0, None, factory, |i, _| i + 10, || true)
                .unwrap()
                .jobs;
            assert_eq!(one.len(), 1);
            assert_eq!(one[0].as_ref().expect("job ran"), &10);
            assert_eq!(draws.load(Ordering::Relaxed), 1);
        });
    }

    /// A panicking job fails alone; the others finish; the wave cleanup
    /// still runs.
    #[test]
    fn panic_isolated_to_its_job() {
        in_child(|| {
            let waves = AtomicUsize::new(0);
            let results = prove_batch(
                &[1, 1, 1],
                3,
                3,
                Some(&DUMMY),
                |i, _rng| {
                    if i == 1 {
                        panic!("job failure");
                    }
                    i
                },
                || {
                    waves.fetch_add(1, Ordering::Relaxed);
                    true
                },
            )
            .unwrap()
            .jobs;
            assert_eq!(results[0].as_ref().expect("job 0 ran"), &0);
            assert!(
                matches!(results[1], Err(JobPanicked)),
                "job 1 is reported panicked"
            );
            assert_eq!(results[2].as_ref().expect("job 2 ran"), &2);
            assert_eq!(
                waves.load(Ordering::Relaxed),
                1,
                "wave cleanup ran despite the panic"
            );
        });
    }

    #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
    #[test]
    fn pool_creation_failure_returns_an_error() {
        in_child(|| {
            let hooks = BatchHooks::from(None).with_stack_size(1 << 62);
            let outcome = prove_batch(&[1], 1, 1, hooks, |_, _| (), || true);
            assert!(matches!(outcome, Err(BatchError::PoolCreation)));
            let hooks = BatchHooks::from(None).with_stack_size(8 << 20);
            let outcome = prove_batch(
                &[1],
                1,
                1,
                hooks,
                |_, _| {
                    let mut scratch = [0u8; 3 << 20];
                    std::hint::black_box(&mut scratch);
                },
                || true,
            )
            .unwrap();
            assert!(matches!(outcome.jobs[..], [Ok(())]));
        });
    }

    #[test]
    fn one_thread_caller_rejects_queued_batch() {
        in_child(|| {
            let caller = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
            let outer = caller
                .install(|| {
                    prove_batch(
                        &[1],
                        1,
                        1,
                        None,
                        |_, _| {
                            let (send, receive) = std::sync::mpsc::channel();
                            caller.spawn(move || {
                                let inner = prove_batch(&[], 1, 1, None, |_, _| (), || true);
                                send.send(matches!(inner, Err(BatchError::Busy))).unwrap();
                            });
                            receive.recv_timeout(Duration::from_secs(10)).unwrap()
                        },
                        || true,
                    )
                })
                .unwrap();
            assert!(matches!(outer.jobs[..], [Ok(true)]));
        });
    }

    #[test]
    fn joined_thread_gets_busy() {
        in_child(|| {
            let outcome = prove_batch(
                &[1],
                1,
                1,
                None,
                |_, _| {
                    std::thread::spawn(|| {
                        for weights in [&[][..], &[1][..]] {
                            assert!(matches!(
                                prove_batch(weights, 1, 1, None, |_, _| (), || true),
                                Err(BatchError::Busy)
                            ));
                        }
                    })
                    .join()
                    .is_ok()
                },
                || true,
            )
            .unwrap();
            assert!(matches!(outcome.jobs[..], [Ok(true)]));
        });
    }

    #[test]
    fn destructor_bound_latches_failure_and_jobs_continue() {
        in_child(|| {
            static DROPS: AtomicUsize = AtomicUsize::new(0);
            struct Again;
            impl Drop for Again {
                fn drop(&mut self) {
                    if DROPS.fetch_add(1, Ordering::Relaxed) < 8 {
                        std::panic::panic_any(Again);
                    }
                }
            }
            for weight in [1, 2] {
                DROPS.store(0, Ordering::Relaxed);
                let result = prove_batch(
                    &[weight, 1],
                    1,
                    1,
                    Some(&DUMMY),
                    |i, _| {
                        if i == 0 {
                            std::panic::panic_any(Again);
                        }
                        super::super::hooks().is_none()
                    },
                    || true,
                )
                .unwrap();
                assert_eq!(DROPS.load(Ordering::Relaxed), 8);
                assert!(result.erasure_failed);
                assert!(matches!(result.jobs[..], [Err(JobPanicked), Ok(true)]));
            }
        });
    }

    #[test]
    fn first_batch_during_unwind_skips_hook_installation() {
        in_child(|| {
            struct DuringUnwind;
            impl Drop for DuringUnwind {
                fn drop(&mut self) {
                    assert!(prove_batch(&[], 0, 1, None, |_, _| (), || true).is_ok());
                    assert!(matches!(
                        prove_batch(&[1], 1, 1, None, |_, _| (), || true),
                        Err(BatchError::Unwinding)
                    ));
                }
            }
            assert!(
                std::panic::catch_unwind(|| {
                    let _during = DuringUnwind;
                    panic!("test unwind");
                })
                .is_err()
            );
        });
    }

    #[test]
    fn nested_batch_is_refused() {
        in_child(|| {
            let nested = || prove_batch(&[], 0, 1, None, |_, _| (), || true);
            let result = prove_batch(
                &[1],
                1,
                1,
                None,
                |_, _| matches!(nested(), Err(BatchError::Busy)),
                || matches!(nested(), Err(BatchError::Busy)),
            )
            .unwrap();
            assert!(!result.erasure_failed);
            assert!(matches!(result.jobs[..], [Ok(true)]));
        });
    }

    #[test]
    fn cpu_waves_respect_the_budget() {
        in_child(|| {
            let waves = AtomicUsize::new(0);
            let boundary = || {
                waves.fetch_add(1, Ordering::Relaxed);
                true
            };
            // Oversized jobs run alone and skip the wave callback.
            let active = AtomicUsize::new(0);
            let oversized = prove_batch(
                &[9, 9],
                8,
                2,
                None,
                |i, _| {
                    assert_eq!(active.fetch_add(1, Ordering::Relaxed), 0);
                    rayon::yield_now();
                    active.fetch_sub(1, Ordering::Relaxed);
                    i
                },
                boundary,
            )
            .unwrap();
            assert!(matches!(oversized.jobs[..], [Ok(0), Ok(1)]));
            assert_eq!(waves.load(Ordering::Relaxed), 0);

            // Each job fits, but their combined weight exceeds the budget.
            let split = prove_batch(
                &[5, 5],
                8,
                2,
                None,
                |_, _| waves.load(Ordering::Relaxed),
                boundary,
            )
            .unwrap();
            assert!(matches!(split.jobs[..], [Ok(0), Ok(1)]));
            assert_eq!(waves.load(Ordering::Relaxed), 2);
        });
    }

    #[test]
    fn failed_wave_runs_remaining_jobs_on_cpu() {
        in_child(|| {
            let waves = AtomicUsize::new(0);
            let result = prove_batch(
                &[1; 3],
                1,
                2,
                Some(&DUMMY),
                |_, _| (0..16).into_par_iter().all(|_| super::super::hooks().is_some()),
                || waves.fetch_add(1, Ordering::Relaxed) != 0,
            )
            .unwrap();
            assert!(result.erasure_failed);
            assert!(matches!(result.jobs[..], [Ok(true), Ok(false), Ok(false)]));
            assert_eq!(waves.load(Ordering::Relaxed), 3);
        });
    }

    /// While a batch runs, a caller outside the batch pool declines
    /// (hooks `None`) at the same moment a batch job sees its scoped
    /// hooks.
    #[test]
    fn non_batch_caller_declines_during_batch() {
        in_child(|| {
            let result = prove_batch(
                &[1],
                1,
                1,
                Some(&DUMMY),
                |_, _| {
                    let (tx, rx) = std::sync::mpsc::channel();
                    std::thread::spawn(move || {
                        tx.send((batch_active(), super::super::hooks().is_none())).unwrap();
                    });
                    super::super::hooks().is_some()
                        && rx.recv_timeout(Duration::from_secs(10)).unwrap() == (true, true)
                },
                || true,
            )
            .unwrap();
            assert!(matches!(result.jobs[..], [Ok(true)]));
        });
    }

    /// Fingerprints (hashes only, no draw is printed) of the first bytes
    /// each job draws: distinct within and across two batches of the
    /// same jobs, with the production (OS) factory.
    #[test]
    fn os_factory_draws_do_not_repeat() {
        in_child(|| {
            let run = || {
                prove_batch(
                    &[1, 1, 1, 1],
                    4,
                    2,
                    None,
                    |_, mut rng| {
                        let mut buf = [0u8; 32];
                        rng.fill_bytes(&mut buf);
                        blake2b_simd::Params::new().hash_length(16).hash(&buf).to_hex().to_string()
                    },
                    || true,
                )
            };
            let mut all = std::collections::HashSet::new();
            for results in [run().unwrap().jobs, run().unwrap().jobs] {
                for r in results {
                    let fp = r.expect("job ran");
                    assert!(all.insert(fp), "a draw repeated across batches");
                }
            }
            assert_eq!(all.len(), 8);
        });
    }

    /// Two batches of the same real jobs with the production factory:
    /// every proof verifies and no two proofs are equal.
    #[test]
    fn two_batches_of_same_jobs_give_distinct_proofs() {
        in_child(|| {
            let (params, pk) = crate::test_circuit::setup(5, true, 6);
            let run = || {
                prove_batch(
                    &[1, 1],
                    2,
                    2,
                    None,
                    |_, rng| super::super::prove_direct(&params, &pk, 5, true, rng),
                    || true,
                )
            };
            let mut proofs = Vec::new();
            for results in [run().unwrap().jobs, run().unwrap().jobs] {
                for r in results {
                    let (proof, ok) = r.expect("job ran");
                    assert!(ok, "every proof verifies");
                    assert!(!proof.is_empty());
                    proofs.push(proof);
                }
            }
            for (i, a) in proofs.iter().enumerate() {
                for b in &proofs[i + 1..] {
                    assert!(a != b, "two proofs of the same job are byte-equal");
                }
            }
        });
    }

    /// With the seeded path, every proof of a batch is byte-identical to
    /// the same proof made alone.
    #[test]
    fn seeded_batch_proofs_equal_alone() {
        in_child(|| {
            struct Restore;
            impl Drop for Restore {
                fn drop(&mut self) {
                    crate::plonk::prover::test_blinding::set(None);
                }
            }
            let (params, pk) = crate::test_circuit::setup(3, true, 6);
            let _restore = Restore;
            crate::plonk::prover::test_blinding::set(Some(31));
            let rng = |_| ChaCha20Rng::seed_from_u64(89);
            let prove = |_, rng| super::super::prove_direct(&params, &pk, 3, true, rng);
            let (alone, ok) = prove(0, rng(0));
            assert!(ok);
            let results =
                prove_batch_with_rng(&[1; 3], 3, 2, None, rng, prove, || true).unwrap().jobs;
            for r in results {
                let (proof, ok) = r.expect("job ran");
                assert!(ok, "batch proof verifies");
                assert!(
                    proof == alone,
                    "batch proof differs from the proof made alone"
                );
            }
        });
    }

    #[test]
    fn panicking_job_value_reaches_no_output() {
        let output = in_child(|| {
            static HOST: AtomicUsize = AtomicUsize::new(0);
            static HELPER: AtomicUsize = AtomicUsize::new(0);
            static OTHER: AtomicUsize = AtomicUsize::new(0);
            std::panic::set_hook(Box::new(|info| {
                let count = match info.payload().downcast_ref::<&str>().copied() {
                    Some("host marker") => &HOST,
                    Some("joined helper marker") => &HELPER,
                    _ => &OTHER,
                };
                count.fetch_add(1, Ordering::Relaxed);
            }));
            static DROPPED: AtomicUsize = AtomicUsize::new(0);
            struct FinalPayload;
            impl Drop for FinalPayload {
                fn drop(&mut self) {
                    DROPPED.fetch_add(1, Ordering::Relaxed);
                }
            }
            struct PanicOnDrop;
            impl Drop for PanicOnDrop {
                fn drop(&mut self) {
                    std::panic::panic_any(FinalPayload);
                }
            }
            let waves = AtomicUsize::new(0);
            let results = prove_batch(
                &[1, 1, 1, 1],
                4,
                4,
                Some(&DUMMY),
                |i, _rng| {
                    if i == 0 {
                        assert!(
                            std::thread::spawn(|| panic!("joined helper marker")).join().is_err()
                        );
                    }
                    if i == 1 {
                        rayon::join(|| (), || assert!(i != 1, "worker marker"));
                    }
                    if i == 2 {
                        std::panic::panic_any(PanicOnDrop);
                    }
                    i
                },
                || {
                    waves.fetch_add(1, Ordering::Relaxed);
                    true
                },
            )
            .unwrap()
            .jobs;
            assert_eq!(DROPPED.load(Ordering::Relaxed), 1);
            assert_eq!(results[0].as_ref().expect("job 0 ran"), &0);
            assert!(matches!(results[1], Err(JobPanicked)));
            assert!(matches!(results[2], Err(JobPanicked)));
            assert_eq!(results[3].as_ref().expect("job 3 ran"), &3);
            assert_eq!(waves.load(Ordering::Relaxed), 1, "after_wave ran");
            assert!(std::panic::catch_unwind(|| panic!("host marker")).is_err());
            assert_eq!(HOST.load(Ordering::Relaxed), 1);
            assert_eq!(HELPER.load(Ordering::Relaxed), 1);
            assert_eq!(OTHER.load(Ordering::Relaxed), 0);
        });
        assert!(output.stderr.is_empty());
        assert!(!String::from_utf8_lossy(&output.stdout).contains("worker marker"));
    }

    #[test]
    fn job_unwinds_while_caller_holds_stderr() {
        in_child(|| {
            let _stderr = std::io::stderr().lock();
            let outcome = prove_batch(&[1], 1, 1, None, |_, _| panic!("job interrupted"), || true);
            assert!(matches!(outcome.unwrap().jobs[..], [Err(JobPanicked)]));
        });
    }

    #[test]
    fn batch_restores_embedding_hook() {
        in_child(|| {
            let calls = Arc::new(AtomicUsize::new(0));
            let marker = install_recording_hook(calls.clone());
            let outcome = prove_batch(&[1], 1, 1, None, |_, _| panic!("worker"), || true);
            assert!(matches!(outcome.unwrap().jobs[..], [Err(JobPanicked)]));
            assert_eq!(calls.load(Ordering::Relaxed), 0);
            assert!(std::panic::catch_unwind(|| panic!("host")).is_err());
            assert_eq!(calls.load(Ordering::Relaxed), 1);
            let restored = std::panic::take_hook();
            assert_eq!(std::ptr::from_ref(&*restored).cast::<()>(), marker);
            drop(restored);
            assert_eq!(Arc::strong_count(&calls), 1);
        });
    }

    fn install_recording_hook(calls: Arc<AtomicUsize>) -> *const () {
        let hook = Box::new(move |_: &std::panic::PanicHookInfo<'_>| {
            calls.fetch_add(1, Ordering::Relaxed);
        });
        let marker = std::ptr::from_ref(&*hook).cast::<()>();
        std::panic::set_hook(hook);
        marker
    }

    #[test]
    fn batch_wraps_temporary_hook_while_earlier_hook_is_held() {
        in_child(|| {
            let first = prove_batch(&[1], 1, 1, None, |_, _| (), || true).unwrap();
            assert!(matches!(first.jobs[..], [Ok(())]));
            let saved = std::panic::take_hook();
            let calls = Arc::new(AtomicUsize::new(0));
            install_recording_hook(calls.clone());
            let second = prove_batch(&[1], 1, 1, None, |_, _| panic!("worker"), || true).unwrap();
            assert!(matches!(second.jobs[..], [Err(JobPanicked)]));
            assert_eq!(calls.load(Ordering::Relaxed), 0);
            std::panic::set_hook(saved);
        });
    }

    #[test]
    fn batch_restores_embedding_hook_on_callback_unwind() {
        in_child(|| {
            let calls = Arc::new(AtomicUsize::new(0));
            let marker = install_recording_hook(calls.clone());
            let panic = std::panic::catch_unwind(|| {
                prove_batch(&[1], 1, 1, None, |_, _| (), || panic!("wave marker"))
            })
            .unwrap_err();
            assert_eq!(panic.downcast_ref::<&str>(), Some(&"wave marker"));
            assert_eq!(calls.load(Ordering::Relaxed), 1);
            let restored = std::panic::take_hook();
            assert_eq!(std::ptr::from_ref(&*restored).cast::<()>(), marker);
        });
    }

    #[test]
    fn batch_restores_embedding_hook_after_replacement() {
        in_child(|| {
            let calls = Arc::new(AtomicUsize::new(0));
            let marker = install_recording_hook(calls.clone());
            let outcome = prove_batch(
                &[1],
                1,
                1,
                None,
                |_, _| {
                    let wrapper = std::panic::take_hook();
                    std::panic::set_hook(Box::new(|_| ()));
                    wrapper
                },
                || true,
            )
            .unwrap();
            let [Ok(_wrapper)] = outcome.jobs.as_slice() else {
                panic!("job did not retain the hook");
            };
            let restored = std::panic::take_hook();
            assert_eq!(std::ptr::from_ref(&*restored).cast::<()>(), marker);
            drop(restored);
            assert_eq!(Arc::strong_count(&calls), 1);
        });
    }

    /// Timing only, not a correctness gate: serial proofs against a
    /// batch (CPU, no hooks), medians of 5 runs.
    #[test]
    #[ignore]
    fn timing_serial_vs_batch() {
        let (params, pk) = crate::test_circuit::setup(7, true, 12);
        let jobs = 4usize;
        let median = |mut v: Vec<std::time::Duration>| {
            v.sort_unstable();
            v[v.len() / 2]
        };
        let mut serial = Vec::new();
        let mut batch = Vec::new();
        for _ in 0..5 {
            let t = std::time::Instant::now();
            for _ in 0..jobs {
                let (proof, ok) = super::super::prove_direct(&params, &pk, 7, true, OsRng);
                assert!(ok && !proof.is_empty());
            }
            serial.push(t.elapsed());
            let t = std::time::Instant::now();
            let weights = vec![1u64; jobs];
            let results = prove_batch(
                &weights,
                jobs as u64,
                jobs,
                None,
                |_, rng| super::super::prove_direct(&params, &pk, 7, true, rng),
                || true,
            )
            .unwrap()
            .jobs;
            for r in results {
                let (proof, ok) = r.expect("job ran");
                assert!(ok && !proof.is_empty());
            }
            batch.push(t.elapsed());
        }
        eprintln!(
            "timing: {jobs} proofs k=12, serial median {:?}, batch median {:?}, threads {}",
            median(serial),
            median(batch),
            rayon::current_num_threads()
        );
    }
}
