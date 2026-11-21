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

//! Teardown, admission and permit tests for the actor channel layer.
//! Device-free (mock backend). Every blocked phase of a caller
//! (budget wait, channel send, reply wait) must return the teardown
//! answer within a bounded time when teardown begins, even while the
//! actor thread is inside a backend call.
#![cfg(feature = "actor")]

use std::{
    sync::{Arc, Condvar, Mutex, mpsc},
    time::Duration,
};

use midnight_gpu::actor::{ActorHandle, Backend, OpKind, Reply};

#[derive(Default)]
struct Gate {
    state: Mutex<(bool, bool)>, // (entered, open)
    cvar: Condvar,
}

impl Gate {
    fn enter_and_wait(&self) {
        let mut s = self.state.lock().unwrap();
        s.0 = true;
        self.cvar.notify_all();
        while !s.1 {
            s = self.cvar.wait(s).unwrap();
        }
    }
    fn wait_entered(&self) {
        let mut s = self.state.lock().unwrap();
        while !s.0 {
            s = self.cvar.wait(s).unwrap();
        }
    }
    fn open(&self) {
        let mut s = self.state.lock().unwrap();
        s.1 = true;
        self.cvar.notify_all();
    }
}

struct Mock {
    gate: Option<Arc<Gate>>,
    drain_ok: bool,
    wipe_ok: bool,
}

impl Mock {
    fn calm() -> Mock {
        Mock {
            gate: None,
            drain_ok: true,
            wipe_ok: true,
        }
    }
    fn blocking(gate: Arc<Gate>) -> Mock {
        Mock {
            gate: Some(gate),
            drain_ok: true,
            wipe_ok: true,
        }
    }
}

impl Backend for Mock {
    fn allocate(&mut self, _job: u32, _size: u64) -> Result<(), String> {
        Ok(())
    }
    fn launch(&mut self, _job: u32, _kind: OpKind, _exclusive: bool) -> Result<(), String> {
        if let Some(g) = &self.gate {
            g.enter_and_wait();
        }
        Ok(())
    }
    fn drain(&mut self, _job: u32) -> bool {
        self.drain_ok
    }
    fn wipe(&mut self, _job: u32) -> bool {
        self.wipe_ok
    }
    fn free(&mut self, _job: u32) {}
    fn zero_pinned(&mut self) {}
    fn reset(&mut self, _lost: &[u32]) {}
}

fn within_2s<T>(rx: &mpsc::Receiver<T>, what: &str) -> T {
    rx.recv_timeout(Duration::from_secs(2))
        .unwrap_or_else(|_| panic!("{what}: not answered within 2 s"))
}

#[test]
fn teardown_answers_a_caller_waiting_for_its_reply() {
    let gate = Arc::new(Gate::default());
    let actor = ActorHandle::spawn(Mock::blocking(gate.clone()), 4, 3, 4);
    assert_eq!(actor.submit(0, 2), Some(Reply::Admitted));
    let (tx, rx) = mpsc::channel();
    let h = actor.clone();
    std::thread::spawn(move || {
        let _ = tx.send(h.run_op(0, OpKind::Ntt, false));
    });
    gate.wait_entered(); // the actor is inside the backend call
    let td = actor.clone();
    let td_thread = std::thread::spawn(move || td.teardown());
    assert_eq!(
        within_2s(&rx, "caller waiting for its reply"),
        Some(Reply::Teardown)
    );
    gate.open();
    assert!(matches!(
        td_thread.join().unwrap(),
        Some(Reply::TornDown { .. })
    ));
    actor.join();
}

#[test]
fn teardown_answers_a_caller_waiting_in_the_budget() {
    let gate = Arc::new(Gate::default());
    let actor = ActorHandle::spawn(Mock::blocking(gate.clone()), 4, 3, 4);
    assert_eq!(actor.submit(0, 4), Some(Reply::Admitted));
    let h = actor.clone();
    std::thread::spawn(move || h.run_op(0, OpKind::Msm, true));
    gate.wait_entered();
    let (tx, rx) = mpsc::channel();
    let h = actor.clone();
    std::thread::spawn(move || {
        let _ = tx.send(h.submit(1, 4));
    });
    std::thread::sleep(Duration::from_millis(100)); // blocked on admission
    let td = actor.clone();
    let td_thread = std::thread::spawn(move || td.teardown());
    assert_eq!(
        within_2s(&rx, "caller waiting in the budget"),
        Some(Reply::Teardown)
    );
    gate.open();
    assert!(matches!(
        td_thread.join().unwrap(),
        Some(Reply::TornDown { .. })
    ));
    actor.join();
}

#[test]
fn teardown_answers_a_caller_blocked_on_a_full_channel() {
    let gate = Arc::new(Gate::default());
    let actor = ActorHandle::spawn(Mock::blocking(gate.clone()), 4, 3, 1);
    assert_eq!(actor.submit(0, 1), Some(Reply::Admitted));
    let h = actor.clone();
    std::thread::spawn(move || h.run_op(0, OpKind::Stage, false));
    gate.wait_entered(); // actor busy; the next send fills the channel
    let h = actor.clone();
    std::thread::spawn(move || h.pending_erasure());
    std::thread::sleep(Duration::from_millis(100));
    let (tx, rx) = mpsc::channel();
    let h = actor.clone();
    std::thread::spawn(move || {
        let _ = tx.send(h.run_op(0, OpKind::Readback, false));
    });
    std::thread::sleep(Duration::from_millis(100)); // blocked in the send
    let td = actor.clone();
    let td_thread = std::thread::spawn(move || td.teardown());
    assert_eq!(
        within_2s(&rx, "caller blocked on a full channel"),
        Some(Reply::Teardown)
    );
    gate.open();
    assert!(matches!(
        td_thread.join().unwrap(),
        Some(Reply::TornDown { .. })
    ));
    actor.join();
}

#[test]
fn fifo_head_is_not_overtaken_in_the_budget() {
    let actor = ActorHandle::spawn(Mock::calm(), 4, 3, 4);
    assert_eq!(actor.submit(0, 3), Some(Reply::Admitted));
    let (tx, rx) = mpsc::channel();
    let h = actor.clone();
    let tx1 = tx.clone();
    std::thread::spawn(move || {
        let r = h.submit(1, 3);
        let _ = tx1.send((1u32, r));
    });
    std::thread::sleep(Duration::from_millis(100)); // job 1 is the head
    let h = actor.clone();
    std::thread::spawn(move || {
        let r = h.submit(2, 2);
        let _ = tx.send((2u32, r));
    });
    std::thread::sleep(Duration::from_millis(100));
    assert_eq!(actor.release(0), Some(Reply::Ok));
    let first = within_2s(&rx, "first admission after release");
    assert_eq!(first, (1, Some(Reply::Admitted)), "the head goes first");
    assert_eq!(actor.release(1), Some(Reply::Ok));
    assert_eq!(
        within_2s(&rx, "second admission"),
        (2, Some(Reply::Admitted))
    );
    assert_eq!(actor.release(2), Some(Reply::Ok));
    actor.join();
}

#[test]
fn over_budget_submit_is_refused_at_submit() {
    let actor = ActorHandle::spawn(Mock::calm(), 4, 3, 4);
    let (tx, rx) = mpsc::channel();
    let h = actor.clone();
    std::thread::spawn(move || {
        let _ = tx.send(h.submit(0, 5));
    });
    assert_eq!(within_2s(&rx, "over-budget submit"), Some(Reply::Refused));
    actor.join();
}

#[test]
fn permits_return_only_after_wipe_confirmed() {
    let mock = Mock {
        gate: None,
        drain_ok: false, // the wipe can never confirm
        wipe_ok: true,
    };
    let actor = ActorHandle::spawn(mock, 4, 3, 4);
    assert_eq!(actor.submit(0, 4), Some(Reply::Admitted));
    assert_eq!(actor.run_op(0, OpKind::Ntt, false), Some(Reply::OpDone));
    let h = actor.clone();
    std::thread::spawn(move || h.release(0)); // stays pending
    std::thread::sleep(Duration::from_millis(100));
    let (tx, rx) = mpsc::channel();
    let h = actor.clone();
    std::thread::spawn(move || {
        let _ = tx.send(h.submit(1, 4));
    });
    assert!(
        rx.recv_timeout(Duration::from_millis(300)).is_err(),
        "job 1 was admitted before job 0's wipe confirmed"
    );
    assert!(matches!(actor.teardown(), Some(Reply::TornDown { .. })));
    assert_eq!(
        within_2s(&rx, "queued job at teardown"),
        Some(Reply::Teardown)
    );
    actor.join();
}

#[test]
fn synchronous_calls_inside_async_task_finish() {
    let (done, completed) = mpsc::channel();
    std::thread::spawn(move || {
        let runtime = tokio::runtime::Builder::new_current_thread().build().unwrap();
        runtime.block_on(async {
            let actor = ActorHandle::spawn(Mock::calm(), 4, 3, 1);
            for _ in 0..400 {
                assert_eq!(actor.pending_erasure(), Some(0));
            }
            assert_eq!(actor.submit(0, 1), Some(Reply::Admitted));
            assert_eq!(actor.release(0), Some(Reply::Ok));
            tokio::task::spawn_blocking(move || {
                assert!(actor.pending_erasure().is_some());
                actor.join();
            })
            .await
            .unwrap();
        });
        done.send(()).unwrap();
    });
    completed.recv_timeout(Duration::from_secs(5)).expect("actor calls timed out");
}
