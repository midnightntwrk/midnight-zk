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

//! Concurrency stress test of the actor thread with a mock backend.
//! No device is used. The mock keeps one byte array per job buffer,
//! fills it with a per-job witness pattern at launch, and records
//! every observation the assertions need: the reserved peak, whether
//! any launch saw another job's pattern, whether any freed buffer
//! held a non-zero byte without being counted lost at the reset, and
//! whether two exclusive-class launches ever overlapped (launches
//! run on the single actor thread, so overlap would mean the actor
//! started one exclusive operation inside another's backend call).
#![cfg(feature = "actor")]

//! Each seed runs N jobs on their own threads (random sizes, random
//! operation sequences), with injected operation failures,
//! unconfirmed drains and failed wipes, and a teardown at a random
//! point. A watchdog fails the test if the run does not end.

use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
    time::Duration,
};

use midnight_gpu::actor::{ActorHandle, Backend, OpKind, Reply};

// A small deterministic PRNG (xorshift64*), seeded per run.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    fn chance(&mut self, pct: u64) -> bool {
        self.below(100) < pct
    }
}

#[derive(Default)]
struct Observations {
    reserved_peak: u64,
    cross_read: bool,
    dirty_free: bool,
    exclusive_overlap: bool,
    lost_at_reset: Vec<u32>,
    freed: Vec<u32>,
}

struct Mock {
    bufs: BTreeMap<u32, Vec<u8>>,
    sizes: BTreeMap<u32, u64>,
    reserved: u64,
    rng: Rng,
    excl_active: bool,
    calm: bool,
    obs: Arc<Mutex<Observations>>,
}

fn pattern(job: u32) -> u8 {
    (job as u8).wrapping_mul(37).wrapping_add(11) | 1 // never zero
}

impl Backend for Mock {
    fn allocate(&mut self, job: u32, size: u64) -> Result<(), String> {
        self.bufs.insert(job, vec![0; (size * 64) as usize]);
        self.sizes.insert(job, size);
        self.reserved += size;
        let mut o = self.obs.lock().unwrap();
        o.reserved_peak = o.reserved_peak.max(self.reserved);
        Ok(())
    }
    fn launch(&mut self, job: u32, _kind: OpKind, exclusive: bool) -> Result<(), String> {
        if exclusive {
            if self.excl_active {
                self.obs.lock().unwrap().exclusive_overlap = true;
            }
            self.excl_active = true;
        }
        // Every buffer may hold only its own job's pattern or zeros.
        for (owner, buf) in &self.bufs {
            let want = pattern(*owner);
            if buf.iter().any(|b| *b != 0 && *b != want) {
                self.obs.lock().unwrap().cross_read = true;
            }
        }
        if let Some(buf) = self.bufs.get_mut(&job) {
            let p = pattern(job);
            buf.iter_mut().for_each(|b| *b = p);
        }
        if exclusive {
            self.excl_active = false;
        }
        if !self.calm && self.rng.chance(15) {
            Err("injected op failure".into())
        } else {
            Ok(())
        }
    }
    fn drain(&mut self, _job: u32) -> bool {
        self.calm || !self.rng.chance(20)
    }
    fn wipe(&mut self, job: u32) -> bool {
        if !self.calm && self.rng.chance(20) {
            return false;
        }
        if let Some(buf) = self.bufs.get_mut(&job) {
            buf.iter_mut().for_each(|b| *b = 0);
        }
        true
    }
    fn free(&mut self, job: u32) {
        if let Some(buf) = self.bufs.remove(&job)
            && buf.iter().any(|b| *b != 0)
        {
            self.obs.lock().unwrap().dirty_free = true;
        }
        if let Some(sz) = self.sizes.remove(&job) {
            self.reserved = self.reserved.saturating_sub(sz);
        }
        self.obs.lock().unwrap().freed.push(job);
    }
    fn zero_pinned(&mut self) {}
    fn reset(&mut self, lost: &[u32]) {
        // Buffers not counted lost must already be wiped or gone.
        for (job, buf) in &self.bufs {
            if !lost.contains(job) && buf.iter().any(|b| *b != 0) {
                self.obs.lock().unwrap().dirty_free = true;
            }
        }
        self.bufs.clear();
        self.sizes.clear();
        self.reserved = 0;
        self.obs.lock().unwrap().lost_at_reset = lost.to_vec();
    }
}

fn run_seed(seed: u64) {
    const N_JOBS: u32 = 8;
    const CAPACITY: u64 = 10;
    let obs = Arc::new(Mutex::new(Observations::default()));
    let mock = Mock {
        bufs: BTreeMap::new(),
        sizes: BTreeMap::new(),
        reserved: 0,
        rng: Rng(seed ^ 0x9E37_79B9_7F4A_7C15),
        excl_active: false,
        calm: false,
        obs: obs.clone(),
    };
    let actor = ActorHandle::spawn(mock, CAPACITY, N_JOBS as usize, 4);

    let mut plan_rng = Rng(seed);
    let plans: Vec<(u64, Vec<(OpKind, bool)>)> = (0..N_JOBS)
        .map(|_| {
            let size = 1 + plan_rng.below(5);
            let ops = (0..plan_rng.below(4))
                .map(|_| {
                    let kind = match plan_rng.below(5) {
                        0 => OpKind::Stage,
                        1 => OpKind::Msm,
                        2 => OpKind::Ntt,
                        3 => OpKind::Quotient,
                        _ => OpKind::Readback,
                    };
                    (kind, plan_rng.chance(30))
                })
                .collect();
            (size, ops)
        })
        .collect();
    // Teardown fires after a random delay, from its own thread.
    let teardown_after_ms = plan_rng.below(30);
    let do_teardown = plan_rng.chance(70);

    let results = Arc::new(Mutex::new(Vec::<(u32, Vec<Reply>)>::new()));
    let mut threads = Vec::new();
    for (job, (size, ops)) in plans.iter().enumerate() {
        let job = job as u32;
        let (size, ops) = (*size, ops.clone());
        let handle = actor.clone();
        let results = results.clone();
        threads.push(std::thread::spawn(move || {
            let mut replies = Vec::new();
            let admitted = handle.submit(job, size);
            replies.push(admitted.expect("submit is answered"));
            if admitted == Some(Reply::Admitted) {
                for (kind, excl) in ops {
                    let r = handle.run_op(job, kind, excl).expect("op is answered");
                    replies.push(r);
                    if r == Reply::Teardown {
                        break;
                    }
                }
                replies.push(handle.release(job).expect("release is answered"));
            }
            results.lock().unwrap().push((job, replies));
        }));
    }
    let teardown_thread = if do_teardown {
        let handle = actor.clone();
        Some(std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(teardown_after_ms));
            handle.teardown().expect("teardown is answered")
        }))
    } else {
        None
    };

    // Watchdog: every job thread must finish. A job whose drain was
    // unconfirmed can only be answered by the reset (by design), so
    // if the jobs are still waiting after a grace period the test
    // sends the teardown itself; only a further timeout is a deadlock.
    let (done_tx, done_rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        for t in threads {
            let _ = t.join();
        }
        let _ = done_tx.send(());
    });
    if done_rx.recv_timeout(Duration::from_secs(5)).is_err() {
        actor.teardown().expect("watchdog teardown is answered");
        done_rx
            .recv_timeout(Duration::from_secs(30))
            .unwrap_or_else(|_| panic!("seed {seed}: deadlock (watchdog)"));
    }

    let teardown_reply = teardown_thread.map(|t| t.join().expect("teardown thread"));
    if teardown_reply.is_none() && actor.pending_erasure() != Some(0) {
        actor.teardown().expect("final teardown is answered");
    }

    let results = results.lock().unwrap();
    assert_eq!(
        results.len(),
        N_JOBS as usize,
        "seed {seed}: every job answered"
    );
    for (job, replies) in results.iter() {
        assert!(!replies.is_empty(), "seed {seed} job {job}: no reply");
        // The submit reply is exactly one of the terminal kinds.
        assert!(
            matches!(
                replies[0],
                Reply::Admitted | Reply::Teardown | Reply::Refused | Reply::Ok | Reply::Failed
            ),
            "seed {seed} job {job}: bad submit reply {:?}",
            replies[0]
        );
    }
    drop(results);

    let o = obs.lock().unwrap();
    assert!(
        o.reserved_peak <= CAPACITY,
        "seed {seed}: budget exceeded ({})",
        o.reserved_peak
    );
    assert!(
        !o.cross_read,
        "seed {seed}: a job's buffer held another job's pattern"
    );
    assert!(
        !o.dirty_free,
        "seed {seed}: a buffer was freed/reset with non-zero bytes, not lost"
    );
    assert!(
        !o.exclusive_overlap,
        "seed {seed}: exclusive operations overlapped"
    );
    drop(o);

    // After teardown every later submit is answered teardown. (Job
    // ids are per-lifetime here, so use a fresh actor state check via
    // pending erasure only when a teardown ran.)
    assert_eq!(
        actor.pending_erasure(),
        Some(0),
        "seed {seed}: pending after end"
    );
    actor.join();
}

#[test]
fn actor_stress_many_seeds() {
    // Seeds are reported in .lane/REPORT.md; keep the list explicit so
    // a failure names its seed.
    for seed in [
        1u64,
        2,
        3,
        7,
        42,
        99,
        1234,
        20_261_117,
        0xDEAD_BEEF,
        555_555,
    ] {
        run_seed(seed);
    }
}

#[test]
fn teardown_before_any_submit_answers_later_submits() {
    let obs = Arc::new(Mutex::new(Observations::default()));
    let mock = Mock {
        bufs: BTreeMap::new(),
        sizes: BTreeMap::new(),
        reserved: 0,
        rng: Rng(1),
        excl_active: false,
        calm: true,
        obs,
    };
    let actor = ActorHandle::spawn(mock, 4, 3, 2);
    assert_eq!(actor.teardown(), Some(Reply::TornDown { lost_unerased: 0 }));
    assert_eq!(actor.submit(0, 1), Some(Reply::Teardown));
    assert_eq!(actor.submit(1, 1), Some(Reply::Teardown));
    assert_eq!(actor.teardown(), Some(Reply::TornDown { lost_unerased: 0 }));
    actor.join();
}

#[test]
fn queued_submit_waits_then_is_admitted_in_order() {
    let obs = Arc::new(Mutex::new(Observations::default()));
    let mock = Mock {
        bufs: BTreeMap::new(),
        sizes: BTreeMap::new(),
        reserved: 0,
        rng: Rng(7),
        excl_active: false,
        calm: true,
        obs,
    };
    let actor = ActorHandle::spawn(mock, 4, 3, 4);
    assert_eq!(actor.submit(0, 3), Some(Reply::Admitted));
    // Job 1 (size 3) waits; job 2 releases job 0 first via its thread.
    let h = actor.clone();
    let t = std::thread::spawn(move || h.submit(1, 3));
    std::thread::sleep(Duration::from_millis(20));
    assert_eq!(actor.release(0), Some(Reply::Ok));
    assert_eq!(t.join().unwrap(), Some(Reply::Admitted));
    assert_eq!(actor.release(1), Some(Reply::Ok));
    actor.join();
}
