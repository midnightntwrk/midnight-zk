//! Optional CPU and memory profiler for the PLONK prover.
//!
//! Enable with `--features profiling`. Instrument code with [`start`] / [`end`]
//! around named scopes, optionally launch a per-core CPU sampler with
//! [`start_cpu_sampler`] / [`stop_cpu_sampler`], then call [`to_full_json`] to
//! retrieve all data.
//!
//! ## Timing records
//!
//! Each [`Record`] covers one named scope and reports wall time, CPU user/sys
//! time (from `getrusage`, summed across all threads), and the OS peak-RSS
//! high-water mark at the start and end of the scope.
//!
//! ## Per-core CPU samples
//!
//! [`start_cpu_sampler`] spawns a background thread that reads per-core CPU tick
//! counters at a configurable interval and tags each sample with the name of the
//! innermost profiling scope that was active at sample time.  On macOS the data
//! comes from `host_processor_info(PROCESSOR_CPU_LOAD_INFO)`; on Linux from
//! `/proc/stat`.
//!
//! Call [`stop_cpu_sampler`] (which joins the thread) before [`to_full_json`] to
//! ensure all samples are flushed.

// We need unsafe for libc / mach calls; overrides the crate-level deny.
#![allow(unsafe_code)]

use std::{
    cell::RefCell,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex, OnceLock,
    },
    thread,
    time::{Duration, Instant},
};

// ── public types ─────────────────────────────────────────────────────────────

/// A single timing and memory record emitted when a named scope closes.
#[derive(Debug, Clone)]
pub struct Record {
    /// Scope name, e.g. `"fft::coeff_to_extended"` or `"nu_poly::advice_cosets"`.
    pub name: String,
    /// Wall-clock time from profiler initialisation to the *start* of this scope, in ms.
    pub start_wall_ms: f64,
    /// Wall-clock duration of this scope, in ms.
    pub wall_ms: f64,
    /// CPU user-space time consumed during this scope across all threads, in ms.
    pub cpu_user_ms: f64,
    /// CPU kernel time consumed during this scope across all threads, in ms.
    pub cpu_sys_ms: f64,
    /// OS RSS high-water mark at scope start, in KiB.
    pub peak_rss_start_kib: i64,
    /// OS RSS high-water mark at scope end, in KiB.
    pub peak_rss_end_kib: i64,
    /// Growth in peak RSS during this scope (`end − start`), in KiB.
    pub peak_rss_delta_kib: i64,
}

/// Per-core CPU utilization for one sample interval.
#[derive(Debug, Clone)]
pub struct CoreUsage {
    /// Percentage of this core's time spent in user-space during the interval.
    pub user_pct: f64,
    /// Percentage of this core's time spent in the kernel during the interval.
    pub sys_pct: f64,
}

/// One snapshot of per-core CPU utilization, associated with an active phase.
#[derive(Debug, Clone)]
pub struct CpuSample {
    /// Milliseconds from sampler start to this measurement.
    pub time_ms: f64,
    /// The innermost profiling phase active when this sample was taken.
    pub phase: String,
    /// Per-core usage — one entry per logical CPU.
    pub cores: Vec<CoreUsage>,
}

// ── internal types (timing records) ──────────────────────────────────────────

struct Frame {
    name: String,
    wall_start: Instant,
    cpu_user_us: i64,
    cpu_sys_us: i64,
    peak_rss_kib: i64,
}

struct Profiler {
    init: Instant,
    records: Vec<Record>,
    stack: Vec<Frame>,
}

impl Profiler {
    fn new() -> Self {
        Profiler { init: Instant::now(), records: Vec::new(), stack: Vec::new() }
    }

    fn push(&mut self, name: &str) {
        let (user_us, sys_us) = cpu_time_us();
        self.stack.push(Frame {
            name: name.to_string(),
            wall_start: Instant::now(),
            cpu_user_us: user_us,
            cpu_sys_us: sys_us,
            peak_rss_kib: peak_rss_kib(),
        });
    }

    fn pop(&mut self) {
        let Some(frame) = self.stack.pop() else { return };
        let wall_ms = frame.wall_start.elapsed().as_secs_f64() * 1000.0;
        let start_wall_ms =
            frame.wall_start.saturating_duration_since(self.init).as_secs_f64() * 1000.0;
        let (user_us, sys_us) = cpu_time_us();
        let rss_end = peak_rss_kib();
        self.records.push(Record {
            name: frame.name,
            start_wall_ms,
            wall_ms,
            cpu_user_ms: (user_us - frame.cpu_user_us).max(0) as f64 / 1000.0,
            cpu_sys_ms: (sys_us - frame.cpu_sys_us).max(0) as f64 / 1000.0,
            peak_rss_start_kib: frame.peak_rss_kib,
            peak_rss_end_kib: rss_end,
            peak_rss_delta_kib: rss_end - frame.peak_rss_kib,
        });
    }

    fn reset(&mut self) {
        self.records.clear();
        self.stack.clear();
        self.init = Instant::now();
    }
}

// ── per-core sampler ──────────────────────────────────────────────────────────

/// Raw per-core tick counters (cumulative since boot).
#[derive(Clone, Default)]
struct CoreTicks {
    user: u64,
    sys: u64,
    idle: u64,
    nice: u64,
}

struct SamplerState {
    /// Name of the innermost active scope (updated by [`start`]).
    current_phase: Mutex<String>,
    samples: Mutex<Vec<CpuSample>>,
    stop: AtomicBool,
    init: Instant,
}

struct SamplerHandle {
    state: Arc<SamplerState>,
    thread: Option<thread::JoinHandle<()>>,
}

static SAMPLER: OnceLock<Mutex<Option<SamplerHandle>>> = OnceLock::new();

fn sampler_mutex() -> &'static Mutex<Option<SamplerHandle>> {
    SAMPLER.get_or_init(|| Mutex::new(None))
}

// ── thread-local profiler ─────────────────────────────────────────────────────

thread_local! {
    static PROFILER: RefCell<Profiler> = RefCell::new(Profiler::new());
}

// ── public API ────────────────────────────────────────────────────────────────

/// Begin a named profiling scope. Must be paired with a later call to [`end`].
pub fn start(name: &str) {
    PROFILER.with(|p| p.borrow_mut().push(name));
    // Keep the sampler informed about the current phase.
    if let Ok(guard) = sampler_mutex().lock() {
        if let Some(s) = guard.as_ref() {
            *s.state.current_phase.lock().unwrap() = name.to_string();
        }
    }
}

/// Close the innermost scope opened by [`start`] and emit a [`Record`].
pub fn end() {
    PROFILER.with(|p| p.borrow_mut().pop());
    // Restore the parent phase name in the sampler, if any.
    let parent = PROFILER.with(|p| {
        p.borrow().stack.last().map(|f| f.name.clone()).unwrap_or_default()
    });
    if let Ok(guard) = sampler_mutex().lock() {
        if let Some(s) = guard.as_ref() {
            *s.state.current_phase.lock().unwrap() = parent;
        }
    }
}

/// Clear all timing records and reset the wall-clock origin to now.
/// The CPU sampler (if running) keeps its samples; start a new one to reset those.
pub fn reset() {
    PROFILER.with(|p| p.borrow_mut().reset());
}

/// Apply `f` to the slice of all completed [`Record`]s (read-only).
pub fn with_records<F: FnOnce(&[Record])>(f: F) {
    PROFILER.with(|p| f(&p.borrow().records));
}

/// Launch a background thread that samples per-core CPU utilization every
/// `interval_ms` milliseconds.  Any previously running sampler is stopped first.
///
/// Call [`stop_cpu_sampler`] before [`to_full_json`] to ensure the thread has
/// flushed all samples.
pub fn start_cpu_sampler(interval_ms: u64) {
    // Stop an existing sampler (if any) and discard its samples.
    stop_cpu_sampler();

    let state = Arc::new(SamplerState {
        current_phase: Mutex::new(String::new()),
        samples: Mutex::new(Vec::new()),
        stop: AtomicBool::new(false),
        init: Instant::now(),
    });

    let state_clone = Arc::clone(&state);
    let handle = thread::spawn(move || {
        let mut prev = sample_core_ticks();
        loop {
            thread::sleep(Duration::from_millis(interval_ms));
            if state_clone.stop.load(Ordering::Relaxed) {
                break;
            }
            let curr = sample_core_ticks();
            let time_ms = state_clone.init.elapsed().as_secs_f64() * 1000.0;
            let phase = state_clone.current_phase.lock().unwrap().clone();
            let cores = compute_utilization(&prev, &curr);
            state_clone.samples.lock().unwrap().push(CpuSample { time_ms, phase, cores });
            prev = curr;
        }
    });

    *sampler_mutex().lock().unwrap() = Some(SamplerHandle { state, thread: Some(handle) });
}

/// Signal the background sampler to stop and wait for it to finish.
/// Collected samples are preserved and included in [`to_full_json`].
pub fn stop_cpu_sampler() {
    if let Ok(mut guard) = sampler_mutex().lock() {
        if let Some(s) = guard.as_mut() {
            s.state.stop.store(true, Ordering::Relaxed);
            if let Some(t) = s.thread.take() {
                let _ = t.join();
            }
        }
    }
}

/// Serialize timing records *and* CPU samples into a single JSON object:
/// `{ "records": [...], "cpu_samples": [...] }`.
pub fn to_full_json() -> String {
    let records_json = PROFILER.with(|p| records_to_json(&p.borrow().records));
    let samples_json = sampler_mutex()
        .lock()
        .ok()
        .and_then(|g| {
            g.as_ref()
                .map(|s| cpu_samples_to_json(&s.state.samples.lock().unwrap()))
        })
        .unwrap_or_else(|| "[]".to_string());

    format!("{{\n  \"records\": {},\n  \"cpu_samples\": {}\n}}", records_json, samples_json)
}

/// Serialize only timing records (backward-compatible flat array).
pub fn to_json() -> String {
    PROFILER.with(|p| records_to_json(&p.borrow().records))
}

// ── JSON serialisation ────────────────────────────────────────────────────────

fn records_to_json(records: &[Record]) -> String {
    let mut out = String::from("[\n");
    for (i, r) in records.iter().enumerate() {
        let comma = if i + 1 < records.len() { "," } else { "" };
        out += &format!(
            "  {{\"name\":\"{name}\",\"start_wall_ms\":{start:.3},\"wall_ms\":{wall:.3},\
\"cpu_user_ms\":{user:.3},\"cpu_sys_ms\":{sys:.3},\
\"peak_rss_start_kib\":{rs},\"peak_rss_end_kib\":{re},\"peak_rss_delta_kib\":{rd}}}{comma}\n",
            name = r.name,
            start = r.start_wall_ms,
            wall = r.wall_ms,
            user = r.cpu_user_ms,
            sys = r.cpu_sys_ms,
            rs = r.peak_rss_start_kib,
            re = r.peak_rss_end_kib,
            rd = r.peak_rss_delta_kib,
        );
    }
    out += "]";
    out
}

fn cpu_samples_to_json(samples: &[CpuSample]) -> String {
    let mut out = String::from("[\n");
    for (i, s) in samples.iter().enumerate() {
        let comma = if i + 1 < samples.len() { "," } else { "" };
        let cores: Vec<String> = s
            .cores
            .iter()
            .map(|c| format!("{{\"user_pct\":{:.1},\"sys_pct\":{:.1}}}", c.user_pct, c.sys_pct))
            .collect();
        out += &format!(
            "  {{\"time_ms\":{:.1},\"phase\":\"{}\",\"cores\":[{}]}}{}\n",
            s.time_ms,
            s.phase,
            cores.join(","),
            comma,
        );
    }
    out += "]";
    out
}

// ── per-core tick sampling ────────────────────────────────────────────────────

fn compute_utilization(prev: &[CoreTicks], curr: &[CoreTicks]) -> Vec<CoreUsage> {
    prev.iter()
        .zip(curr.iter())
        .map(|(p, c)| {
            let du = c.user.saturating_sub(p.user) as f64;
            let ds = c.sys.saturating_sub(p.sys) as f64;
            let di = c.idle.saturating_sub(p.idle) as f64;
            let dn = c.nice.saturating_sub(p.nice) as f64;
            let total = du + ds + di + dn;
            if total > 0.0 {
                CoreUsage { user_pct: du / total * 100.0, sys_pct: ds / total * 100.0 }
            } else {
                CoreUsage { user_pct: 0.0, sys_pct: 0.0 }
            }
        })
        .collect()
}

/// macOS: read per-core tick counters via `host_processor_info`.
#[cfg(target_os = "macos")]
fn sample_core_ticks() -> Vec<CoreTicks> {
    use std::mem;

    // Constants from <mach/processor_info.h>
    const PROCESSOR_CPU_LOAD_INFO: i32 = 2;
    const CPU_STATE_USER: usize = 0;
    const CPU_STATE_SYSTEM: usize = 1;
    const CPU_STATE_IDLE: usize = 2;
    const CPU_STATE_NICE: usize = 3;
    const CPU_STATE_MAX: usize = 4;
    const KERN_SUCCESS: i32 = 0;

    #[repr(C)]
    struct ProcessorCpuLoadInfo {
        cpu_ticks: [u32; CPU_STATE_MAX],
    }

    extern "C" {
        fn host_processor_info(
            host: u32,
            flavor: i32,
            out_processor_count: *mut u32,
            out_processor_info: *mut *mut i32,
            out_processor_info_cnt: *mut u32,
        ) -> i32;

        fn mach_host_self() -> u32;

        fn vm_deallocate(target_task: u32, address: usize, size: usize) -> i32;

        static mach_task_self_: u32;
    }

    unsafe {
        let host = mach_host_self();
        let mut num_cpus: u32 = 0;
        let mut cpu_info_ptr: *mut i32 = std::ptr::null_mut();
        let mut cpu_info_cnt: u32 = 0;

        let ret = host_processor_info(
            host,
            PROCESSOR_CPU_LOAD_INFO,
            &mut num_cpus,
            &mut cpu_info_ptr,
            &mut cpu_info_cnt,
        );

        if ret != KERN_SUCCESS || cpu_info_ptr.is_null() {
            return vec![];
        }

        let cpu_loads = std::slice::from_raw_parts(
            cpu_info_ptr as *const ProcessorCpuLoadInfo,
            num_cpus as usize,
        );

        let result = cpu_loads
            .iter()
            .map(|load| CoreTicks {
                user: load.cpu_ticks[CPU_STATE_USER] as u64,
                sys: load.cpu_ticks[CPU_STATE_SYSTEM] as u64,
                idle: load.cpu_ticks[CPU_STATE_IDLE] as u64,
                nice: load.cpu_ticks[CPU_STATE_NICE] as u64,
            })
            .collect();

        vm_deallocate(
            mach_task_self_,
            cpu_info_ptr as usize,
            cpu_info_cnt as usize * mem::size_of::<i32>(),
        );

        result
    }
}

/// Linux: read per-core tick counters from `/proc/stat`.
#[cfg(target_os = "linux")]
fn sample_core_ticks() -> Vec<CoreTicks> {
    let content = match std::fs::read_to_string("/proc/stat") {
        Ok(s) => s,
        Err(_) => return vec![],
    };
    content
        .lines()
        // Lines like "cpu0 user nice sys idle ..."
        .filter(|l| l.starts_with("cpu") && !l.starts_with("cpu "))
        .map(|line| {
            let mut it = line.split_whitespace().skip(1);
            let user = it.next().and_then(|s| s.parse().ok()).unwrap_or(0u64);
            let nice = it.next().and_then(|s| s.parse().ok()).unwrap_or(0u64);
            let sys = it.next().and_then(|s| s.parse().ok()).unwrap_or(0u64);
            let idle = it.next().and_then(|s| s.parse().ok()).unwrap_or(0u64);
            CoreTicks { user, sys, idle, nice }
        })
        .collect()
}

/// Fallback: no per-core data available.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn sample_core_ticks() -> Vec<CoreTicks> {
    vec![]
}

// ── getrusage helpers ─────────────────────────────────────────────────────────

fn peak_rss_kib() -> i64 {
    #[cfg(unix)]
    {
        let r = getrusage_self();
        #[cfg(target_os = "macos")]
        return r.ru_maxrss as i64 / 1024; // macOS: bytes
        #[cfg(not(target_os = "macos"))]
        return r.ru_maxrss as i64; // Linux: KiB
    }
    #[cfg(not(unix))]
    0
}

fn cpu_time_us() -> (i64, i64) {
    #[cfg(unix)]
    {
        let r = getrusage_self();
        let user = r.ru_utime.tv_sec as i64 * 1_000_000 + r.ru_utime.tv_usec as i64;
        let sys = r.ru_stime.tv_sec as i64 * 1_000_000 + r.ru_stime.tv_usec as i64;
        return (user, sys);
    }
    #[cfg(not(unix))]
    (0, 0)
}

#[cfg(unix)]
fn getrusage_self() -> libc::rusage {
    unsafe {
        let mut r: libc::rusage = std::mem::zeroed();
        libc::getrusage(libc::RUSAGE_SELF, &mut r);
        r
    }
}
