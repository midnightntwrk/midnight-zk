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

//! The admission ladder: which phases of a request may run on the device.
//!
//! Before any phase starts, the service compares the computed need
//! ([`DeviceNeed`]) with the free device memory and takes the first step that
//! fits:
//!
//! 1. `gpu`: every configured phase.
//! 2. `wait`: the same after a wait of at most `wait_s` for another device user
//!    to free memory.
//! 3. `evict`: the resident proving-key copies are freed and the quotient runs
//!    on the CPU; MSMs and base-domain NTTs stay on the device.
//! 4. `cpu`: nothing on the device.
//!
//! No phase starts that cannot finish in memory: the phases returned fit the
//! free memory at the decision.
//!
//! Under the WSL2 profile the free-memory query does not see other device
//! users. There the device is exclusive under the lock: without a validated
//! lease the request runs on the CPU, and with one the ladder runs against a
//! fixed budget (device total minus a reserve) with no wait. The wait under
//! WSL2 is the caller's wait for the lock.

use std::time::{Duration, Instant};

use serde::Serialize;

use crate::{
    device::{Held, Phases},
    need::DeviceNeed,
};

/// The step of the ladder a request was admitted at.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Step {
    /// Every configured phase on the device at once.
    Gpu,
    /// Every configured phase after a wait for another device user.
    Wait,
    /// Resident copies freed, the quotient on the CPU.
    Evict,
    /// Nothing on the device.
    Cpu,
    /// No device or no device phase configured.
    None,
}

impl Step {
    /// Whether the step serves the request with fewer device phases than
    /// configured.
    pub fn degraded(self) -> bool {
        matches!(self, Step::Evict | Step::Cpu)
    }
}

/// The decision for one request.
#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
pub struct Admission {
    /// The step taken.
    pub step: Step,
    /// The phases the proof runs with on the device.
    pub phases: Phases,
    /// The computed need of those phases, bytes.
    pub need: u64,
    /// Free bytes (or the WSL2 budget) at the decision.
    pub free: u64,
    /// Seconds waited.
    pub waited_s: f64,
    /// Why the request runs with fewer phases than configured, if it does.
    pub reason: Option<&'static str>,
}

/// Reason of a request admitted at step `evict`.
pub const EVICT_REASON: &str = "device memory short: resident copies freed, quotient on the CPU";
/// Reason of a request admitted at step `cpu` for memory.
pub const CPU_REASON: &str = "device memory short: every phase on the CPU";
/// Reason of a request without a lease when a lease is required.
pub const NO_LEASE_REASON: &str =
    "the device lock is not held by the caller: every phase on the CPU";

/// The parameters of one ladder run.
pub struct Ladder<'a> {
    /// The computed need.
    pub need: &'a DeviceNeed,
    /// The configured phases.
    pub phases: Phases,
    /// Longest wait, seconds.
    pub wait_s: f64,
    /// Poll interval of the wait.
    pub poll: Duration,
    /// Reads the free device bytes.
    pub free: &'a dyn Fn() -> u64,
    /// Reads the bytes this process holds.
    pub held: &'a dyn Fn() -> Held,
    /// Frees the resident copies (and with `true` the tables).
    pub evict: &'a dyn Fn(bool),
}

/// Runs the ladder.
pub fn admit(l: &Ladder) -> Admission {
    let t = Instant::now();
    let at = |step, phases, need, free, reason| Admission {
        step,
        phases,
        need,
        free,
        waited_s: t.elapsed().as_secs_f64(),
        reason,
    };
    if l.phases.is_empty() {
        return at(Step::None, Phases::NONE, 0, 0, None);
    }
    let want = |p: Phases| l.need.of_phases(p, (l.held)());
    let (mut n, mut f) = (want(l.phases), (l.free)());
    if f >= n {
        return at(Step::Gpu, l.phases, n, f, None);
    }
    let limit = std::time::Duration::from_secs_f64(l.wait_s.max(0.0));
    while t.elapsed() < limit {
        // the last sleep ends at the limit, not one poll after it
        std::thread::sleep(l.poll.min(limit.saturating_sub(t.elapsed())));
        (n, f) = (want(l.phases), (l.free)());
        if f >= n {
            return at(Step::Wait, l.phases, n, f, None);
        }
    }
    let reduced = l.phases.without(Phases::QUOTIENT);
    if l.phases.contains(Phases::QUOTIENT) && !reduced.is_empty() {
        (l.evict)(false);
        (n, f) = (want(reduced), (l.free)());
        if f >= n {
            return at(Step::Evict, reduced, n, f, Some(EVICT_REASON));
        }
    }
    (l.evict)(true);
    at(Step::Cpu, Phases::NONE, 0, (l.free)(), Some(CPU_REASON))
}

/// The WSL2 device budget: device total minus the reserve.
pub fn wsl_budget(total: u64, reserve_mib: u64) -> u64 {
    total.saturating_sub(reserve_mib << 20)
}

/// The ladder under the WSL2 profile: without a lease, `cpu`; with one, the
/// ladder against `budget` with no wait.
pub fn admit_wsl(l: &Ladder, leased: bool, budget: u64) -> Admission {
    if !leased {
        return no_lease(l.phases);
    }
    admit(&Ladder {
        wait_s: 0.0,
        poll: Duration::ZERO,
        free: &|| budget,
        ..*l
    })
}

/// The decision for a request that needs a lease and has none.
pub fn no_lease(phases: Phases) -> Admission {
    let (step, reason) = if phases.is_empty() {
        (Step::None, None)
    } else {
        (Step::Cpu, Some(NO_LEASE_REASON))
    };
    Admission {
        step,
        phases: Phases::NONE,
        need: 0,
        free: 0,
        waited_s: 0.0,
        reason,
    }
}

#[cfg(test)]
mod tests {
    use std::cell::{Cell, RefCell};

    use super::*;
    use crate::device::Shape;

    const GIB: u64 = 1 << 30;

    fn need() -> DeviceNeed {
        DeviceNeed::of(
            &Shape {
                k: 21,
                ext_k: 23,
                proof_cosets: 17,
                resident_polys: 30,
                nslots: 90,
                grid_threads: 80 * 1024,
                quotient_bytes: 0,
            },
            768 << 20,
        )
    }

    /// A fake device: free memory follows a script, eviction releases what
    /// the process holds.
    struct Fake {
        free: RefCell<Vec<u64>>,
        held: Cell<Held>,
        evicts: RefCell<Vec<bool>>,
    }

    impl Fake {
        fn new(free: &[u64], held: Held) -> Fake {
            Fake {
                free: RefCell::new(free.to_vec()),
                held: Cell::new(held),
                evicts: RefCell::new(vec![]),
            }
        }
        fn read(&self) -> u64 {
            let mut f = self.free.borrow_mut();
            if f.len() > 1 { f.remove(0) } else { f[0] }
        }
        fn run(&self, n: &DeviceNeed, phases: Phases, wait_s: f64) -> Admission {
            admit(&Ladder {
                need: n,
                phases,
                wait_s,
                poll: Duration::from_millis(1),
                free: &|| self.read(),
                held: &|| self.held.get(),
                evict: &|t| {
                    self.evicts.borrow_mut().push(t);
                    let h = self.held.get();
                    self.held.set(Held {
                        resident: 0,
                        tables: if t { 0 } else { h.tables },
                    });
                },
            })
        }
    }

    #[test]
    fn gpu_when_it_fits() {
        let n = need();
        let f = Fake::new(&[32 * GIB], Held::default());
        let a = f.run(&n, Phases::ALL, 0.0);
        assert_eq!(a.step, Step::Gpu);
        assert_eq!(a.phases, Phases::ALL);
        assert_eq!(a.need, n.full(Held::default()));
        assert!(f.evicts.borrow().is_empty());
        assert!(!a.step.degraded());
    }

    #[test]
    fn wait_then_gpu() {
        let n = need();
        let f = Fake::new(&[GIB, GIB, 32 * GIB], Held::default());
        let a = f.run(&n, Phases::ALL, 5.0);
        assert_eq!(a.step, Step::Wait);
        assert_eq!(a.phases, Phases::ALL);
    }

    #[test]
    fn evict_then_reduced() {
        let n = need();
        let free = n.reduced(Held::default()) + 1;
        let f = Fake::new(
            &[free],
            Held {
                resident: n.resident,
                tables: 0,
            },
        );
        let a = f.run(&n, Phases::ALL, 0.0);
        assert_eq!(a.step, Step::Evict);
        assert_eq!(a.phases, Phases::ALL.without(Phases::QUOTIENT));
        assert_eq!(*f.evicts.borrow(), vec![false]);
        assert_eq!(f.held.get().resident, 0);
        assert!(a.step.degraded());
        assert_eq!(a.reason, Some(EVICT_REASON));
    }

    #[test]
    fn cpu_when_nothing_fits() {
        let n = need();
        let f = Fake::new(
            &[100 << 20],
            Held {
                resident: n.resident,
                tables: 2 * n.table_points(),
            },
        );
        let a = f.run(&n, Phases::ALL, 0.0);
        assert_eq!(a.step, Step::Cpu);
        assert_eq!(a.phases, Phases::NONE);
        assert_eq!(*f.evicts.borrow(), vec![false, true]);
        assert_eq!(f.held.get(), Held::default());
    }

    #[test]
    fn nothing_configured_is_none() {
        let f = Fake::new(&[0], Held::default());
        assert_eq!(f.run(&need(), Phases::NONE, 0.0).step, Step::None);
    }

    #[test]
    fn resident_held_lowers_the_need() {
        let n = need();
        let warm = Held {
            resident: n.resident,
            tables: 2 * n.table_points(),
        };
        let free = n.full(warm);
        let f = Fake::new(&[free], warm);
        assert_eq!(f.run(&n, Phases::ALL, 0.0).step, Step::Gpu);
        let f = Fake::new(&[free], Held::default());
        assert_ne!(f.run(&n, Phases::ALL, 0.0).step, Step::Gpu);
    }

    #[test]
    fn wsl_budget_and_lease() {
        let n = need();
        // 32 GiB device, 4 GiB reserve: the cold need fits the budget
        let b = wsl_budget(32 * GIB, 4096);
        assert_eq!(b, 28 * GIB);
        // the free-memory query is never read under WSL2
        let l = Ladder {
            need: &n,
            phases: Phases::ALL,
            wait_s: 20.0,
            poll: Duration::from_secs(1),
            free: &|| panic!("free memory is not read under WSL2"),
            held: &Held::default,
            evict: &|_| {},
        };
        let a = admit_wsl(&l, true, b);
        assert_eq!((a.step, a.free, a.waited_s < 1.0), (Step::Gpu, b, true));
        // no lease: CPU, marked
        let a = admit_wsl(&l, false, b);
        assert_eq!(
            (a.step, a.phases, a.reason),
            (Step::Cpu, Phases::NONE, Some(NO_LEASE_REASON))
        );
        // a budget below the cold need: evict, then cpu, with no wait
        let a = admit_wsl(&l, true, n.reduced(Held::default()));
        assert_eq!(a.step, Step::Evict);
        let a = admit_wsl(&l, true, 1 << 20);
        assert_eq!(a.step, Step::Cpu);
        // a reserve above the total gives a zero budget
        assert_eq!(wsl_budget(GIB, 4096), 0);
    }

    /// The wait ends at `wait_s`, not one poll interval after it.
    #[test]
    fn wait_never_overshoots_by_a_poll() {
        let n = need();
        let l = Ladder {
            need: &n,
            phases: Phases::ALL,
            wait_s: 0.05,
            poll: Duration::from_secs(2),
            free: &|| 0,
            held: &Held::default,
            evict: &|_| {},
        };
        let t = Instant::now();
        assert_eq!(admit(&l).step, Step::Cpu);
        assert!(
            t.elapsed() < Duration::from_millis(1000),
            "{:?}",
            t.elapsed()
        );
    }
}
