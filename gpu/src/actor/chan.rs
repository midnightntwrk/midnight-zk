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

//! Blocking request, reply and budget waits use standard thread primitives.
//! A shutdown-aware wait checks the signal at least every two milliseconds.
//! A caller lending data to the actor waits unconditionally for its reply.

use std::{
    collections::VecDeque,
    future::Future,
    sync::{Arc, Condvar, Mutex, mpsc},
    task::{Context, Poll, Wake, Waker},
    thread::Thread,
    time::Duration,
};

const WAKE_BACKSTOP: Duration = Duration::from_millis(2);

/// One budget permit per MiB, with reservations rounded up.
pub const UNIT_BYTES: u64 = 1 << 20;

/// Why a channel-layer wait ended without its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChanError {
    /// Teardown began; every waiter is answered with this.
    Teardown,
    /// The other side is gone (channel closed, reply never sent).
    Closed,
    /// The reservation exceeds the entire budget.
    Refused,
}

pub use crate::batch::Shutdown;

struct Parker(Thread);

impl Wake for Parker {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}

fn parker() -> Waker {
    Waker::from(Arc::new(Parker(std::thread::current())))
}

/// Runs one future to completion on the calling thread, parking the
/// thread while the future is pending and unparking it from the
/// waker. Std only; about the smallest executor there is.
pub fn block_on<F: Future>(fut: F) -> F::Output {
    let waker = parker();
    let mut cx = Context::from_waker(&waker);
    let mut fut = Box::pin(fut);
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(v) => return v,
            Poll::Pending => std::thread::park(),
        }
    }
}

/// The sending side of the bounded request channel.
#[derive(Debug)]
pub struct Tx<T> {
    inner: mpsc::SyncSender<T>,
}

impl<T> Clone for Tx<T> {
    fn clone(&self) -> Tx<T> {
        Tx {
            inner: self.inner.clone(),
        }
    }
}

/// The receiving side of the bounded request channel (actor only).
#[derive(Debug)]
pub struct Rx<T> {
    inner: mpsc::Receiver<T>,
}

/// A bounded request channel holding at most `bound` messages.
pub fn channel<T>(bound: usize) -> (Tx<T>, Rx<T>) {
    let (tx, rx) = mpsc::sync_channel(bound.max(1));
    (Tx { inner: tx }, Rx { inner: rx })
}

impl<T> Tx<T> {
    /// Sends a request, checking for shutdown while the queue is full.
    pub fn blocking_send(&self, mut msg: T, shutdown: &Shutdown) -> Result<(), ChanError> {
        loop {
            if shutdown.is_triggered() {
                return Err(ChanError::Teardown);
            }
            match self.inner.try_send(msg) {
                Ok(()) => return Ok(()),
                Err(mpsc::TrySendError::Disconnected(_)) => return Err(ChanError::Closed),
                Err(mpsc::TrySendError::Full(returned)) => msg = returned,
            }
            std::thread::sleep(WAKE_BACKSTOP);
        }
    }
}

impl<T> Rx<T> {
    /// The next request, parking the actor thread while the channel
    /// is empty; `None` when every sender is gone.
    pub fn blocking_recv(&mut self) -> Option<T> {
        self.inner.recv().ok()
    }

    /// A buffered request without waiting, if one is there.
    pub fn try_recv(&mut self) -> Option<T> {
        self.inner.try_recv().ok()
    }
}

/// The sending side of a per-request reply (actor only).
#[derive(Debug)]
pub struct ReplyTx<T> {
    inner: mpsc::Sender<T>,
}

/// The receiving side of a per-request reply (the caller).
#[derive(Debug)]
pub struct ReplyRx<T> {
    inner: mpsc::Receiver<T>,
}

/// A fresh per-request reply channel.
pub fn reply_channel<T>() -> (ReplyTx<T>, ReplyRx<T>) {
    let (tx, rx) = mpsc::channel();
    (ReplyTx { inner: tx }, ReplyRx { inner: rx })
}

impl<T> ReplyTx<T> {
    /// Sends the single reply. `Err(value)` when the caller is gone
    /// (it already returned, for example with teardown).
    pub fn send(self, value: T) -> Result<(), T> {
        self.inner.send(value).map_err(|e| e.0)
    }
}

impl<T> ReplyRx<T> {
    /// Waits for the reply on a synchronous thread. Returns
    /// [`ChanError::Teardown`] within a bounded time when teardown
    /// begins, even while the actor is inside a device call, and
    /// teardown takes precedence over a reply ready at the same
    /// moment.
    pub fn blocking_wait(self, shutdown: &Shutdown) -> Result<T, ChanError> {
        loop {
            if shutdown.is_triggered() {
                return Err(ChanError::Teardown);
            }
            match self.inner.recv_timeout(WAKE_BACKSTOP) {
                _ if shutdown.is_triggered() => return Err(ChanError::Teardown),
                Ok(value) => return Ok(value),
                Err(mpsc::RecvTimeoutError::Disconnected) => return Err(ChanError::Closed),
                Err(mpsc::RecvTimeoutError::Timeout) => {}
            }
        }
    }

    /// Waits for the reply with no shutdown signal (the teardown
    /// caller itself, and queries that stay valid after teardown).
    pub fn blocking_wait_unconditional(self) -> Result<T, ChanError> {
        self.inner.recv().map_err(|_| ChanError::Closed)
    }
}

/// Held budget permits for one job's reservation. The actor's job
/// record owns it; dropping it returns the permits to the budget,
/// which the actor does only when the job's buffers are
/// wipe-confirmed (or counted lost at the reset, after which no
/// buffer of the old context can be reused).
#[derive(Debug, Default)]
pub struct BudgetPermit {
    inner: Option<(Budget, u32)>,
}

impl Drop for BudgetPermit {
    fn drop(&mut self) {
        if let Some((budget, count)) = self.inner.take() {
            let (state, changed) = &*budget.shared;
            state.lock().unwrap().free += count;
            changed.notify_all();
        }
    }
}

fn permits_for(bytes: u64, unit: u64) -> u64 {
    if bytes == 0 {
        return 0;
    }
    bytes.div_ceil(unit.max(1))
}

#[derive(Debug, Default)]
struct BudgetState {
    free: u32,
    next: u64,
    queue: VecDeque<u64>,
}

/// A memory budget shared in reservation order.
#[derive(Clone, Debug)]
pub struct Budget {
    shared: Arc<(Mutex<BudgetState>, Condvar)>,
    total: u32,
    unit: u64,
}

impl Budget {
    /// A budget of `capacity` bytes at `unit` bytes per permit.
    pub fn new(capacity: u64, unit: u64) -> Budget {
        // A permit count above `u32::MAX` saturates (it must not wrap to a
        // small or empty budget).
        let total = permits_for(capacity, unit).min(u32::MAX as u64) as u32;
        Budget {
            shared: Arc::new((
                Mutex::new(BudgetState {
                    free: total,
                    ..Default::default()
                }),
                Condvar::new(),
            )),
            total,
            unit: unit.max(1),
        }
    }

    /// A device-memory budget at the default unit ([`UNIT_BYTES`]).
    pub fn from_bytes(capacity: u64) -> Budget {
        Budget::new(capacity, UNIT_BYTES)
    }

    /// The total permit count.
    pub fn total_permits(&self) -> u32 {
        self.total
    }

    /// Reserves `bytes`, parking the calling (synchronous) thread
    /// until the whole reservation fits, in request order. A
    /// reservation above the whole budget is
    /// [`ChanError::Refused`] at once; teardown answers
    /// [`ChanError::Teardown`] within a bounded time.
    pub fn reserve(&self, bytes: u64, shutdown: &Shutdown) -> Result<BudgetPermit, ChanError> {
        let want = permits_for(bytes, self.unit);
        if want > self.total as u64 {
            return Err(ChanError::Refused);
        }
        if want == 0 {
            return if shutdown.is_triggered() {
                Err(ChanError::Teardown)
            } else {
                Ok(BudgetPermit { inner: None })
            };
        }
        let want = want as u32;
        let (state, changed) = &*self.shared;
        let mut state = state.lock().unwrap();
        let ticket = state.next;
        state.next = state.next.wrapping_add(1);
        state.queue.push_back(ticket);
        loop {
            if shutdown.is_triggered() {
                state.queue.retain(|&t| t != ticket);
                changed.notify_all();
                return Err(ChanError::Teardown);
            }
            if state.queue.front() == Some(&ticket) && state.free >= want {
                state.queue.pop_front();
                state.free -= want;
                changed.notify_all();
                return Ok(BudgetPermit {
                    inner: Some((self.clone(), want)),
                });
            }
            state = changed.wait_timeout(state, WAKE_BACKSTOP).unwrap().0;
        }
    }

    /// Permits currently free (for tests and reports).
    pub fn available_permits(&self) -> u32 {
        self.shared.0.lock().unwrap().free
    }

    #[cfg(test)]
    pub(crate) fn has_waiter(&self) -> bool {
        !self.shared.0.lock().unwrap().queue.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn block_on_runs_a_future_and_wakes() {
        assert_eq!(block_on(async { 7 }), 7);
        // A future completed from another thread wakes the parker.
        let (tx, rx) = reply_channel::<u32>();
        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(20));
            let _ = tx.send(9);
        });
        assert_eq!(rx.blocking_wait_unconditional(), Ok(9));
    }

    #[test]
    fn permit_count_above_u32_saturates() {
        // one-byte permits: 2^32 permits do not fit and must not wrap to 0
        assert_eq!(Budget::new(1 << 32, 1).total_permits(), u32::MAX);
        assert_eq!(Budget::new(u64::MAX, 1).total_permits(), u32::MAX);
        assert_eq!(Budget::new(u32::MAX as u64, 1).total_permits(), u32::MAX);
    }

    #[test]
    fn permits_round_up_and_refuse_over_budget() {
        assert_eq!(permits_for(0, UNIT_BYTES), 0);
        assert_eq!(permits_for(1, UNIT_BYTES), 1);
        assert_eq!(permits_for(UNIT_BYTES + 1, UNIT_BYTES), 2);
        let b = Budget::from_bytes(4 * UNIT_BYTES);
        assert_eq!(b.total_permits(), 4);
        let sd = Shutdown::new();
        assert_eq!(
            b.reserve(5 * UNIT_BYTES, &sd).unwrap_err(),
            ChanError::Refused
        );
        let p = b.reserve(3 * UNIT_BYTES + 1, &sd).expect("fits");
        assert_eq!(b.available_permits(), 0);
        drop(p);
        assert_eq!(b.available_permits(), 4);
    }

    #[test]
    fn budget_wait_answers_teardown() {
        let b = Budget::new(2, 1);
        let sd = Shutdown::new();
        let _held = b.reserve(2, &sd).expect("fits");
        let (b2, sd2) = (b, sd.clone());
        let t = std::thread::spawn(move || b2.reserve(1, &sd2).map(|_| ()));
        std::thread::sleep(Duration::from_millis(50));
        sd.trigger();
        assert_eq!(t.join().unwrap(), Err(ChanError::Teardown));
    }

    #[test]
    fn reply_wait_teardown_takes_precedence() {
        let (tx, rx) = reply_channel::<u32>();
        let _ = tx.send(3); // the reply is already ready
        let sd = Shutdown::new();
        sd.trigger();
        assert_eq!(rx.blocking_wait(&sd), Err(ChanError::Teardown));
    }
}
