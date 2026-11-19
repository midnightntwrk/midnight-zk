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

//! The device-owner actor: one thread owns the (future) CUDA context
//! of one GPU, and jobs reach it only through typed messages on a
//! bounded channel. This round is device-free: effects go through
//! [`Backend`], which a mock implements in tests and the real device
//! will implement in the integration round. Nothing here calls CUDA,
//! and no existing device path routes through the actor yet.
//!
//! The actor loop applies the pure protocol ([`protocol::step`]) and
//! calls the backend for each effect. Every request gets exactly one
//! reply on its own channel:
//! - [`Request::Submit`] is answered when the job is admitted
//!   ([`Reply::Admitted`]), or at once with [`Reply::Teardown`] /
//!   [`Reply::Refused`]. A queued submit never fails for lack of memory; it
//!   waits for admission or teardown.
//! - [`Request::RunOp`] is answered when the operation completes.
//! - [`Request::Release`] is answered when the job's buffer was wiped and
//!   freed, or counted lost at the reset. Until then the job's bytes stay
//!   reserved and the buffer stays in the pending-erasure count.
//! - [`Request::Teardown`] stops admission, drives every admitted job through
//!   drain/wipe/free (bounded retries), resets, and answers every waiting
//!   request before it replies. After that the actor stays alive only to answer
//!   later submits with teardown, until every handle is dropped.
//!
//! Refinement in this round: a backend operation completes inside
//! the actor loop (`StartOp`, `launch`, `CompleteOp` in one message),
//! so the in-flight window the protocol models is not yet used for
//! real overlap; exclusivity is still enforced by the protocol step,
//! and the integration round turns backend completion into its own
//! loop event (one stream per job) without changing the protocol.
//! Drain and wipe are each retried up to `MAX_ATTEMPTS` times; a job
//! that still cannot confirm stays pending until teardown's reset
//! counts it lost unerased, exactly as the protocol states.

pub mod budget;
#[cfg(feature = "actor")]
pub mod chan;
pub mod protocol;

#[cfg(feature = "actor")]
use std::{collections::BTreeMap, thread::JoinHandle};

#[cfg(feature = "actor")]
use budget::JobId;
#[cfg(feature = "actor")]
use chan::ChanError;
#[cfg(feature = "actor")]
use protocol::{Action, Phase, ReplyKind, State, Teardown, step};

/// Operation classes the design names (stage, MSM, NTT/coset,
/// quotient, read-back). The protocol only needs the exclusive flag;
/// the class is carried for the backend.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(feature = "actor")]
pub enum OpKind {
    /// Host-to-device staging.
    Stage,
    /// Multi-scalar multiplication.
    Msm,
    /// NTT / coset transform.
    Ntt,
    /// Quotient.
    Quotient,
    /// Device-to-host read-back.
    Readback,
}

/// A typed request to the actor. Each carries its own reply channel;
/// the actor sends exactly one [`Reply`] on it.
#[derive(Debug)]
#[cfg(feature = "actor")]
pub enum Request {
    /// Submit a job asking for `size` bytes. Job ids are chosen by
    /// the caller and must be below the actor's job count and unused.
    Submit {
        /// The job.
        job: JobId,
        /// Reservation size.
        size: u64,
        /// The job's budget permits, acquired by the caller and
        /// owned by the actor's job record from here on; they return
        /// to the budget only when the job's buffer is
        /// wipe-confirmed and freed (or counted lost at the reset).
        permit: chan::BudgetPermit,
        /// Reply channel (answered on admission or teardown/refusal).
        reply: chan::ReplyTx<Reply>,
    },
    /// Run one operation on the job's own buffer and stream.
    RunOp {
        /// The job (must be admitted).
        job: JobId,
        /// Operation class.
        kind: OpKind,
        /// Exclusive-class operation.
        exclusive: bool,
        /// Reply channel.
        reply: chan::ReplyTx<Reply>,
    },
    /// Release the job: drain its stream, wipe and free its buffer.
    Release {
        /// The job.
        job: JobId,
        /// Reply channel (answered at free, or at the reset).
        reply: chan::ReplyTx<Reply>,
    },
    /// The pending-erasure report (exact, from the protocol state).
    PendingErasure {
        /// Reply channel.
        reply: chan::ReplyTx<Reply>,
    },
    /// Tear the device down: stop admission, drain and wipe every
    /// job, reset, answer every waiter (see the module text).
    Teardown {
        /// Reply channel.
        reply: chan::ReplyTx<Reply>,
    },
}

/// The single reply to a [`Request`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(feature = "actor")]
pub enum Reply {
    /// The job is admitted; its bytes are reserved.
    Admitted,
    /// The operation completed.
    OpDone,
    /// The job finished: buffer wiped and freed (release answer).
    Ok,
    /// An operation of the job failed; its buffer was still wiped and
    /// freed, or counted lost at the reset (release answer).
    Failed,
    /// The device was torn down; the request was not (or will not be)
    /// admitted.
    Teardown,
    /// The reservation is above the budget capacity.
    Refused,
    /// The request does not apply (unknown or wrong-phase job).
    RefusedRequest,
    /// The pending-erasure count at the time of the request.
    PendingErasure(u64),
    /// Teardown finished; carries the lost-unerased count.
    TornDown {
        /// Buffers counted lost unerased at the reset.
        lost_unerased: u64,
    },
}

/// Effects the actor needs from the device owner. The integration
/// round implements this with CUDA calls on the actor thread; tests
/// implement it with host memory. Every method runs on the actor
/// thread only.
#[cfg(feature = "actor")]
pub trait Backend: Send {
    /// Allocates the job's buffer of `size` bytes.
    fn allocate(&mut self, job: JobId, size: u64) -> Result<(), String>;
    /// Runs one operation on the job's buffer/stream. `Ok` or failed.
    fn launch(&mut self, job: JobId, kind: OpKind, exclusive: bool) -> Result<(), String>;
    /// Drains the job's stream; `true` when the drain is confirmed.
    fn drain(&mut self, job: JobId) -> bool;
    /// Wipes the job's buffer; `true` when the wipe is confirmed.
    fn wipe(&mut self, job: JobId) -> bool;
    /// Frees the job's (wipe-confirmed) buffer.
    fn free(&mut self, job: JobId);
    /// Zeroes the page-locked staging buffer (before any reset).
    fn zero_pinned(&mut self);
    /// Discards buffers counted lost at the reset, then resets.
    fn reset(&mut self, lost: &[JobId]);
}

#[cfg(feature = "actor")]
const MAX_ATTEMPTS: usize = 3;

/// A handle to a running actor. Dropping the last handle closes the
/// request channel; the actor thread then exits (after teardown it
/// has nothing left to answer).
#[derive(Debug)]
#[cfg(feature = "actor")]
pub struct ActorHandle {
    tx: chan::Tx<Request>,
    budget: chan::Budget,
    shutdown: chan::Shutdown,
    join: Option<JoinHandle<()>>,
}

#[cfg(feature = "actor")]
impl Clone for ActorHandle {
    fn clone(&self) -> ActorHandle {
        ActorHandle {
            tx: self.tx.clone(),
            budget: self.budget.clone(),
            shutdown: self.shutdown.clone(),
            join: None,
        }
    }
}

#[cfg(feature = "actor")]
impl ActorHandle {
    /// Spawns the actor thread: budget `capacity` (in the same units
    /// as submit sizes, one permit per unit), `n_jobs` job ids,
    /// request channel bounded to `bound` messages.
    pub fn spawn<B: Backend + Send + 'static>(
        backend: B,
        capacity: u64,
        n_jobs: usize,
        bound: usize,
    ) -> ActorHandle {
        Self::spawn_with_unit(backend, capacity, n_jobs, bound, 1)
    }

    /// [`ActorHandle::spawn`] with `unit` bytes per budget permit
    /// (device memory uses [`chan::UNIT_BYTES`]).
    pub fn spawn_with_unit<B: Backend + Send + 'static>(
        backend: B,
        capacity: u64,
        n_jobs: usize,
        bound: usize,
        unit: u64,
    ) -> ActorHandle {
        let (tx, rx) = chan::channel::<Request>(bound.max(1));
        let budget = chan::Budget::new(capacity, unit);
        let shutdown = chan::Shutdown::new();
        let actor_shutdown = shutdown.clone();
        let join = std::thread::spawn(move || run(backend, capacity, n_jobs, rx, actor_shutdown));
        ActorHandle {
            tx,
            budget,
            shutdown,
            join: Some(join),
        }
    }

    /// Sends one request and waits for its single reply. Every
    /// blocked phase (the send, the reply wait) observes the
    /// shutdown signal: when teardown begins the call returns
    /// [`Reply::Teardown`] within a bounded time, never hangs.
    pub fn call(&self, make: impl FnOnce(chan::ReplyTx<Reply>) -> Request) -> Option<Reply> {
        let (rtx, rrx) = chan::reply_channel();
        match self.tx.blocking_send(make(rtx), &self.shutdown) {
            Ok(()) => {}
            Err(ChanError::Teardown) => return Some(Reply::Teardown),
            Err(ChanError::Closed) => return None,
            Err(ChanError::Refused) => return Some(Reply::Refused),
        }
        match rrx.blocking_wait(&self.shutdown) {
            Ok(r) => Some(r),
            Err(ChanError::Teardown) => Some(Reply::Teardown),
            Err(ChanError::Closed) => None,
            Err(ChanError::Refused) => Some(Reply::Refused),
        }
    }

    // A call that stays valid after teardown began (the teardown
    // request itself, the pending-erasure query): no shutdown
    // observation, the actor answers from its loop.
    fn call_unconditional(
        &self,
        make: impl FnOnce(chan::ReplyTx<Reply>) -> Request,
    ) -> Option<Reply> {
        let (rtx, rrx) = chan::reply_channel();
        let never = chan::Shutdown::new();
        self.tx.blocking_send(make(rtx), &never).ok()?;
        rrx.blocking_wait_unconditional().ok()
    }

    /// Submits a job and waits until it is admitted (or answered).
    /// The caller first reserves the job's permits in the budget
    /// (FIFO, see [`chan::Budget`]); a reservation above the whole
    /// budget is [`Reply::Refused`] at once. The permits move to
    /// the actor's job record with the request.
    pub fn submit(&self, job: JobId, size: u64) -> Option<Reply> {
        let permit = match self.budget.reserve(size, &self.shutdown) {
            Ok(p) => p,
            Err(ChanError::Teardown) => return Some(Reply::Teardown),
            Err(ChanError::Refused) => return Some(Reply::Refused),
            Err(ChanError::Closed) => return None,
        };
        self.call(|reply| Request::Submit {
            job,
            size,
            permit,
            reply,
        })
    }

    /// Runs one operation for an admitted job.
    pub fn run_op(&self, job: JobId, kind: OpKind, exclusive: bool) -> Option<Reply> {
        self.call(|reply| Request::RunOp {
            job,
            kind,
            exclusive,
            reply,
        })
    }

    /// Releases a job and waits for wipe-confirmed free (or the reset).
    pub fn release(&self, job: JobId) -> Option<Reply> {
        self.call(|reply| Request::Release { job, reply })
    }

    /// The exact pending-erasure count. Valid after teardown (the
    /// actor answers it from its loop), so it does not observe the
    /// shutdown signal.
    pub fn pending_erasure(&self) -> Option<u64> {
        match self.call_unconditional(|reply| Request::PendingErasure { reply }) {
            Some(Reply::PendingErasure(n)) => Some(n),
            _ => None,
        }
    }

    /// Tears the device down and waits for the reset to finish. The
    /// shutdown signal is triggered first, so every caller blocked
    /// in a budget wait, a channel send or a reply wait returns
    /// [`Reply::Teardown`] within a bounded time even while the
    /// actor thread is still inside a backend call; this call then
    /// waits (unconditionally) for the actor to drain, wipe, reset
    /// and fail every pending reply sender.
    pub fn teardown(&self) -> Option<Reply> {
        self.shutdown.trigger();
        self.call_unconditional(|reply| Request::Teardown { reply })
    }

    /// Whether teardown has begun on this actor.
    pub fn is_tearing_down(&self) -> bool {
        self.shutdown.is_triggered()
    }

    /// Waits for the actor thread to exit (the owner handle only;
    /// clones hold no thread). Call after dropping other handles.
    pub fn join(self) {
        let ActorHandle { tx, join, .. } = self;
        drop(tx);
        if let Some(j) = join {
            let _ = j.join();
        }
    }
}

#[cfg(feature = "actor")]
struct Pending {
    submit: BTreeMap<JobId, chan::ReplyTx<Reply>>,
    release: BTreeMap<JobId, chan::ReplyTx<Reply>>,
    // The actor's job records: each admitted or queued job's budget
    // permits. An entry is dropped (permits returned) only when the
    // protocol replies to the job, which for an admitted job happens
    // at the wipe-confirmed free or at the reset, never earlier.
    permits: BTreeMap<JobId, chan::BudgetPermit>,
}

#[cfg(feature = "actor")]
fn reply_for(kind: ReplyKind) -> Reply {
    match kind {
        ReplyKind::Ok => Reply::Ok,
        ReplyKind::Failed => Reply::Failed,
        ReplyKind::Teardown => Reply::Teardown,
        ReplyKind::Refused => Reply::Refused,
        ReplyKind::None => Reply::RefusedRequest,
    }
}

#[cfg(feature = "actor")]
fn answer_replied(state: &State, pending: &mut Pending) {
    for (j, replied) in state.replied.iter().enumerate() {
        if !replied {
            continue;
        }
        let job = j as JobId;
        if let Some(tx) = pending.submit.remove(&job) {
            let _ = tx.send(reply_for(state.reply_kind[j]));
        }
        if let Some(tx) = pending.release.remove(&job) {
            let _ = tx.send(reply_for(state.reply_kind[j]));
        }
        // The protocol replied: for an admitted job this is the
        // wipe-confirmed free (or the reset), so its permits may
        // return to the budget now, and not before.
        pending.permits.remove(&job);
    }
}

#[cfg(feature = "actor")]
fn apply(state: State, action: &Action) -> State {
    step(&state, action).unwrap_or(state)
}

// Admits while the head fits, allocating each admitted job's buffer.
// A backend allocate failure is treated as a failed job that still
// goes through release with an empty (secret-free) buffer; admission
// itself never fails for lack of memory.
#[cfg(feature = "actor")]
fn admit_ready<B: Backend>(mut state: State, backend: &mut B, pending: &mut Pending) -> State {
    while state.teardown == Teardown::None {
        let Some(head) = state.budget.head() else {
            break;
        };
        match step(&state, &Action::Admit) {
            Ok(next) => {
                state = next;
                let size = state.size[head as usize];
                if backend.allocate(head, size).is_err() {
                    state = apply(state, &Action::RequestRelease { job: head });
                    state = drive_release(state, backend, head);
                } else if let Some(tx) = pending.submit.remove(&head) {
                    let _ = tx.send(Reply::Admitted);
                }
            }
            Err(_) => break,
        }
    }
    state
}

// Drives one Draining job through drain, wipe and free with bounded
// retries. If the wipe can never confirm (unconfirmed drain, or the
// retries run out), the job stays pending for teardown's reset.
#[cfg(feature = "actor")]
fn drive_release<B: Backend>(mut state: State, backend: &mut B, job: JobId) -> State {
    let j = job as usize;
    for _ in 0..MAX_ATTEMPTS {
        if state.phase[j] != Phase::Draining {
            break;
        }
        if backend.drain(job) {
            state = apply(state, &Action::DrainConfirmed { job });
        } else {
            state = apply(state, &Action::DrainUnconfirmed { job });
        }
    }
    for _ in 0..MAX_ATTEMPTS {
        if state.phase[j] != Phase::Wiping {
            break;
        }
        if state.drain_bad[j] {
            break; // the protocol refuses WipeConfirmed from here
        }
        if backend.wipe(job) {
            state = apply(state, &Action::WipeConfirmed { job });
        } else {
            state = apply(state, &Action::WipeFailed { job });
        }
    }
    if state.phase[j] == Phase::Wiped {
        backend.free(job);
        state = apply(state, &Action::FreeBuffer { job });
    }
    state
}

#[cfg(feature = "actor")]
fn run<B: Backend>(
    mut backend: B,
    capacity: u64,
    n_jobs: usize,
    mut rx: chan::Rx<Request>,
    shutdown: chan::Shutdown,
) {
    let mut state = State::new(capacity, n_jobs);
    let mut pending = Pending {
        submit: BTreeMap::new(),
        release: BTreeMap::new(),
        permits: BTreeMap::new(),
    };
    while let Some(req) = rx.blocking_recv() {
        match req {
            Request::Submit {
                job,
                size,
                permit,
                reply,
            } => {
                pending.permits.insert(job, permit);
                match step(&state, &Action::Submit { job, size }) {
                    Ok(next) => {
                        state = next;
                        if state.replied.get(job as usize) == Some(&true) {
                            pending.permits.remove(&job);
                            let _ = reply.send(reply_for(state.reply_kind[job as usize]));
                        } else {
                            pending.submit.insert(job, reply);
                            state = admit_ready(state, &mut backend, &mut pending);
                            answer_replied(&state, &mut pending);
                        }
                    }
                    Err(_) => {
                        pending.permits.remove(&job);
                        let _ = reply.send(Reply::RefusedRequest);
                    }
                }
            }
            Request::RunOp {
                job,
                kind,
                exclusive,
                reply,
            } => {
                match step(
                    &state,
                    &Action::StartOp {
                        job,
                        buf: job,
                        exclusive,
                    },
                ) {
                    Ok(next) => {
                        state = next;
                        let ok = backend.launch(job, kind, exclusive).is_ok();
                        state = apply(state, &Action::CompleteOp { job, ok });
                        let _ = reply.send(Reply::OpDone);
                    }
                    Err(protocol::Refusal::Teardown) => {
                        let _ = reply.send(Reply::Teardown);
                    }
                    Err(_) => {
                        let _ = reply.send(Reply::RefusedRequest);
                    }
                }
            }
            Request::Release { job, reply } => {
                match step(&state, &Action::RequestRelease { job }) {
                    Ok(next) => {
                        state = drive_release(next, &mut backend, job);
                        if state.replied.get(job as usize) == Some(&true) {
                            pending.permits.remove(&job);
                            let _ = reply.send(reply_for(state.reply_kind[job as usize]));
                            state = admit_ready(state, &mut backend, &mut pending);
                            answer_replied(&state, &mut pending);
                        } else {
                            pending.release.insert(job, reply);
                        }
                    }
                    Err(_) => {
                        // Already released/answered jobs answer from
                        // the recorded reply kind; anything else does
                        // not apply.
                        if state.replied.get(job as usize) == Some(&true) {
                            let _ = reply.send(reply_for(state.reply_kind[job as usize]));
                        } else if state.teardown == Teardown::Dead {
                            let _ = reply.send(Reply::Teardown);
                        } else {
                            let _ = reply.send(Reply::RefusedRequest);
                        }
                    }
                }
            }
            Request::PendingErasure { reply } => {
                let _ = reply.send(Reply::PendingErasure(state.pending_erasure));
            }
            Request::Teardown { reply } => {
                // Every blocked caller observes this signal and
                // returns teardown within a bounded time, including
                // requests still buffered in the channel behind this
                // one; the replies sent below then land on callers
                // that may already have returned, which is fine.
                shutdown.trigger();
                if state.teardown == Teardown::Dead {
                    let _ = reply.send(Reply::TornDown {
                        lost_unerased: state.lost_unerased,
                    });
                    continue;
                }
                backend.zero_pinned();
                state = apply(state, &Action::TeardownBegin);
                // Drain and wipe every admitted job that can still
                // confirm; the rest are counted lost at the reset.
                for job in 0..n_jobs as JobId {
                    if state.phase[job as usize] == Phase::Admitted {
                        state = apply(state, &Action::RequestRelease { job });
                    }
                    if matches!(state.phase[job as usize], Phase::Draining | Phase::Wiping) {
                        state = drive_release(state, &mut backend, job);
                    }
                }
                let lost: Vec<JobId> = (0..n_jobs as JobId)
                    .filter(|job| {
                        matches!(
                            state.buf[*job as usize],
                            protocol::BufState::HoldsSecret | protocol::BufState::WipeRequested
                        )
                    })
                    .collect();
                backend.reset(&lost);
                state = apply(state, &Action::TeardownFinish);
                answer_replied(&state, &mut pending);
                // No submit stays pending past the reset (queued jobs
                // were answered by the finish step above).
                debug_assert!(pending.submit.is_empty());
                debug_assert!(pending.release.is_empty());
                debug_assert!(pending.permits.is_empty());
                let _ = reply.send(Reply::TornDown {
                    lost_unerased: state.lost_unerased,
                });
            }
        }
    }
    // Channel closed: dropping the pending reply senders closes
    // their reply channels, so no waiter hangs; it gets the closed
    // answer. Callers that need teardown semantics send Teardown
    // before dropping their handles.
    drop(pending);
}
