//! The utils module contains small, reusable functions

pub mod arithmetic;
pub mod helpers;
pub mod rational;

pub use helpers::SerdeFormat;

/// Temporary profiling helper: process CPU time (user+sys) in ms.
#[allow(unsafe_code)]
pub fn perf2_cpu_ms() -> f64 {
    unsafe extern "C" {
        fn getrusage(who: i32, usage: *mut [i64; 18]) -> i32;
    }
    let mut buf = [0i64; 18];
    unsafe { getrusage(0, &mut buf) };
    let tv = |s: i64, us: i64| s as f64 * 1e3 + (us & 0xffff_ffff) as f64 / 1e3;
    tv(buf[0], buf[1]) + tv(buf[2], buf[3])
}
