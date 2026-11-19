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

//! The device-owner actor protocol as a pure state machine. No CUDA
//! call is made here; effects go through [`super::Backend`].
//!
//! The transition function [`step`] corresponds action for action to
//! the Quint model `gpu-spec/quint/device_actor.qnt`: same action
//! names, same state field names, same op encoding
//! (`code + 100 * a + 10000 * b` in [`Action::op_code`]). ITF traces of
//! the model replay against it with [`replay_itf`].
//!
//! Refinements of the design note, kept in sync with the model:
//! - Strict FIFO admission, no bypass (see [`super::budget`]). A reservation
//!   above capacity is answered [`ReplyKind::Refused`] at submit; queued
//!   reservations wait and never fail for lack of memory.
//! - A completed operation, ok or failed, leaves its buffer holding a secret. A
//!   failed job still drains, wipes and frees before its reply
//!   ([`ReplyKind::Failed`]).
//! - An unconfirmed drain sets `drainBad`: draining may be retried but a wipe
//!   then never confirms, so the buffer stays counted in `pendingErasure` until
//!   the reset at teardown counts it [`BufState::LostUnerased`]. A failed wipe
//!   may be retried.
//! - Teardown is two steps. `TeardownBegin` stops admission and new operations
//!   and zeroes the page-locked staging buffer (a reset unmaps it). Admitted
//!   jobs may still drain, wipe and free. `TeardownFinish` is the reset: it
//!   needs no operation in flight, counts every still-unerased buffer lost,
//!   returns every admitted job's bytes, answers every queued job
//!   [`ReplyKind::Teardown`], and every later submit is answered teardown in
//!   the submit step. A submit while teardown drains is also answered at once.

use super::budget::{Budget, JobId};

/// Per-job lifecycle phase (Quint: the `phase` codes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Never submitted (0).
    Absent,
    /// Waiting in the admission queue (1).
    Queued,
    /// Admitted: bytes reserved, buffer allocated (2).
    Admitted,
    /// An operation is in flight (3).
    Running,
    /// Release requested, draining its stream (4).
    Draining,
    /// Drain confirmed, wiping (5).
    Wiping,
    /// Wipe confirmed, not yet freed (6).
    Wiped,
    /// Freed and replied (7).
    Released,
    /// Answered without admission: teardown or refused (8).
    Answered,
}

impl Phase {
    fn code(self) -> i64 {
        match self {
            Phase::Absent => 0,
            Phase::Queued => 1,
            Phase::Admitted => 2,
            Phase::Running => 3,
            Phase::Draining => 4,
            Phase::Wiping => 5,
            Phase::Wiped => 6,
            Phase::Released => 7,
            Phase::Answered => 8,
        }
    }
    fn from_code(c: i64) -> Option<Phase> {
        Some(match c {
            0 => Phase::Absent,
            1 => Phase::Queued,
            2 => Phase::Admitted,
            3 => Phase::Running,
            4 => Phase::Draining,
            5 => Phase::Wiping,
            6 => Phase::Wiped,
            7 => Phase::Released,
            8 => Phase::Answered,
            _ => return None,
        })
    }
}

/// Per-job buffer state (Quint: the `buf` codes). One buffer per job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BufState {
    /// No buffer (0).
    None,
    /// Allocated, holds no secret yet (1).
    Allocated,
    /// Holds witness-dependent values (2).
    HoldsSecret,
    /// Wipe requested, not yet confirmed (3).
    WipeRequested,
    /// Wipe confirmed (4).
    WipeConfirmed,
    /// Freed; its bytes are back in the budget (5).
    Freed,
    /// Counted lost unerased at a reset (6).
    LostUnerased,
}

impl BufState {
    fn code(self) -> i64 {
        match self {
            BufState::None => 0,
            BufState::Allocated => 1,
            BufState::HoldsSecret => 2,
            BufState::WipeRequested => 3,
            BufState::WipeConfirmed => 4,
            BufState::Freed => 5,
            BufState::LostUnerased => 6,
        }
    }
    fn from_code(c: i64) -> Option<BufState> {
        Some(match c {
            0 => BufState::None,
            1 => BufState::Allocated,
            2 => BufState::HoldsSecret,
            3 => BufState::WipeRequested,
            4 => BufState::WipeConfirmed,
            5 => BufState::Freed,
            6 => BufState::LostUnerased,
            _ => return None,
        })
    }
    fn holds_secret(self) -> bool {
        matches!(self, BufState::HoldsSecret | BufState::WipeRequested)
    }
}

/// The kind of a job's single reply (Quint: the `replyKind` codes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReplyKind {
    /// No reply yet (0).
    None,
    /// The job finished and its buffer was wiped and freed (1).
    Ok,
    /// Answered by teardown without admission (2).
    Teardown,
    /// An operation failed; the buffer was still wiped and freed, or
    /// counted lost at the reset (3).
    Failed,
    /// Reservation above capacity, refused at submit (4).
    Refused,
}

impl ReplyKind {
    fn code(self) -> i64 {
        match self {
            ReplyKind::None => 0,
            ReplyKind::Ok => 1,
            ReplyKind::Teardown => 2,
            ReplyKind::Failed => 3,
            ReplyKind::Refused => 4,
        }
    }
    fn from_code(c: i64) -> Option<ReplyKind> {
        Some(match c {
            0 => ReplyKind::None,
            1 => ReplyKind::Ok,
            2 => ReplyKind::Teardown,
            3 => ReplyKind::Failed,
            4 => ReplyKind::Refused,
            _ => return None,
        })
    }
}

/// Teardown phase (Quint: the `teardown` codes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Teardown {
    /// No teardown (0).
    None,
    /// Requested: admission stopped, admitted jobs drain and wipe (1).
    Draining,
    /// Reset done; every later submit is answered teardown (2).
    Dead,
}

impl Teardown {
    fn code(self) -> i64 {
        match self {
            Teardown::None => 0,
            Teardown::Draining => 1,
            Teardown::Dead => 2,
        }
    }
    fn from_code(c: i64) -> Option<Teardown> {
        Some(match c {
            0 => Teardown::None,
            1 => Teardown::Draining,
            2 => Teardown::Dead,
            _ => return None,
        })
    }
}

/// One protocol action. Names match the Quint actions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Action {
    /// `submitJob`: a new job asks for `size` bytes.
    Submit {
        /// The job.
        job: JobId,
        /// Reservation size.
        size: u64,
    },
    /// `admitStep`: admit the head of the queue (it must fit).
    Admit,
    /// `startOpJob`: start an operation of `job` on buffer `buf`
    /// (which must be the job's own). `exclusive` marks an operation
    /// class that must not run beside another exclusive-class one.
    StartOp {
        /// The job.
        job: JobId,
        /// The buffer the operation touches.
        buf: JobId,
        /// Exclusive-class operation.
        exclusive: bool,
    },
    /// `completeOpJob`: the in-flight operation finished.
    CompleteOp {
        /// The job.
        job: JobId,
        /// Whether it succeeded.
        ok: bool,
    },
    /// `requestReleaseJob`: the job is done; drain its stream.
    RequestRelease {
        /// The job.
        job: JobId,
    },
    /// `drainConfirmedJob`: the stream drain is confirmed.
    DrainConfirmed {
        /// The job.
        job: JobId,
    },
    /// `drainUnconfirmedJob`: the drain could not be confirmed.
    DrainUnconfirmed {
        /// The job.
        job: JobId,
    },
    /// `wipeConfirmedJob`: the wipe is confirmed.
    WipeConfirmed {
        /// The job.
        job: JobId,
    },
    /// `wipeFailedJob`: the wipe failed; it may be retried.
    WipeFailed {
        /// The job.
        job: JobId,
    },
    /// `freeBufferJob`: free the wiped buffer, return its bytes, reply.
    FreeBuffer {
        /// The job.
        job: JobId,
    },
    /// `teardownBeginStep`: stop admission, zero the page-locked buffer.
    TeardownBegin,
    /// `teardownFinishStep`: the reset (see the module text).
    TeardownFinish,
}

impl Action {
    /// The Quint op encoding `code + 100 * a + 10000 * b`, the value
    /// the model puts in `lastOp`. `Admit` encodes `a = 0` here; the
    /// model encodes the admitted (head) job, which
    /// [`Action::from_op_code`] ignores for that code.
    pub fn op_code(&self) -> i64 {
        let (c, a, b): (i64, i64, i64) = match *self {
            Action::Submit { job, size } => (1, job as i64, size as i64),
            Action::Admit => (2, 0, 0),
            Action::StartOp { job, exclusive, .. } => (3, job as i64, exclusive as i64),
            Action::CompleteOp { job, ok } => (4, job as i64, ok as i64),
            Action::RequestRelease { job } => (5, job as i64, 0),
            Action::DrainConfirmed { job } => (6, job as i64, 0),
            Action::DrainUnconfirmed { job } => (7, job as i64, 0),
            Action::WipeConfirmed { job } => (8, job as i64, 0),
            Action::WipeFailed { job } => (9, job as i64, 0),
            Action::FreeBuffer { job } => (10, job as i64, 0),
            Action::TeardownBegin => (11, 0, 0),
            Action::TeardownFinish => (12, 0, 0),
        };
        c + 100 * a + 10000 * b
    }

    /// Decodes a Quint `lastOp` value. For `StartOp` the buffer is the
    /// job's own (the only buffer a model step can name successfully).
    pub fn from_op_code(op: i64) -> Option<Action> {
        let c = op.rem_euclid(100);
        let a = (op / 100).rem_euclid(100);
        let b = op / 10000;
        let job = a as JobId;
        Some(match c {
            1 => Action::Submit {
                job,
                size: b.max(0) as u64,
            },
            2 => Action::Admit,
            3 => Action::StartOp {
                job,
                buf: job,
                exclusive: b == 1,
            },
            4 => Action::CompleteOp { job, ok: b == 1 },
            5 => Action::RequestRelease { job },
            6 => Action::DrainConfirmed { job },
            7 => Action::DrainUnconfirmed { job },
            8 => Action::WipeConfirmed { job },
            9 => Action::WipeFailed { job },
            10 => Action::FreeBuffer { job },
            11 => Action::TeardownBegin,
            12 => Action::TeardownFinish,
            _ => return None,
        })
    }
}

/// Why [`step`] refused an action. A refusal changes nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// The job id is outside the state's job set.
    UnknownJob,
    /// The job is not in the phase the action needs.
    WrongPhase,
    /// Admit with an empty queue.
    QueueEmpty,
    /// The head's reservation does not fit yet; it keeps waiting.
    DoesNotFit,
    /// An operation named a buffer that is not its job's own.
    WrongBuffer,
    /// An exclusive-class operation is already in flight.
    ExclusiveBusy,
    /// Free before a confirmed wipe.
    NotWiped,
    /// A wipe on a stream whose drain was once unconfirmed.
    DrainBad,
    /// Teardown has begun; the action is no longer taken.
    Teardown,
    /// The reset while an operation is in flight, or out of order.
    Busy,
}

/// The actor state. Field names in JSON match the Quint record `s`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    /// The memory budget (capacity, reserved bytes, FIFO queue).
    pub budget: Budget,
    /// Per-job phase.
    pub phase: Vec<Phase>,
    /// Per-job reservation size.
    pub size: Vec<u64>,
    /// Per-job submission order (0 = never submitted).
    pub submit_seq: Vec<u64>,
    /// Next submission order value.
    pub next_seq: u64,
    /// Per-job buffer state.
    pub buf: Vec<BufState>,
    /// Per-buffer owner job (`-1` = none). Buffer id = index.
    pub buf_owner: Vec<i64>,
    /// Per-job: an operation is in flight on its stream.
    pub in_flight: Vec<bool>,
    /// Per-job: the in-flight operation is of an exclusive class.
    pub op_exclusive: Vec<bool>,
    /// Per-job: buffer the in-flight operation touches (`-1` = none).
    pub op_buf: Vec<i64>,
    /// Per-job: an operation of this job failed.
    pub op_failed: Vec<bool>,
    /// Per-job: a drain was unconfirmed.
    pub drain_bad: Vec<bool>,
    /// Per-job: the single reply was sent.
    pub replied: Vec<bool>,
    /// Per-job reply kind.
    pub reply_kind: Vec<ReplyKind>,
    /// Submits taken.
    pub submits: u64,
    /// Replies sent.
    pub replies: u64,
    /// Reported count of unerased buffers; always exact.
    pub pending_erasure: u64,
    /// Buffers counted lost unerased at resets.
    pub lost_unerased: u64,
    /// The page-locked staging buffer was zeroed (before any reset).
    pub pinned_zeroed: bool,
    /// Teardown phase.
    pub teardown: Teardown,
}

impl State {
    /// The initial state: `capacity` budget, `n_jobs` absent jobs.
    pub fn new(capacity: u64, n_jobs: usize) -> State {
        State {
            budget: Budget::new(capacity),
            phase: vec![Phase::Absent; n_jobs],
            size: vec![0; n_jobs],
            submit_seq: vec![0; n_jobs],
            next_seq: 1,
            buf: vec![BufState::None; n_jobs],
            buf_owner: vec![-1; n_jobs],
            in_flight: vec![false; n_jobs],
            op_exclusive: vec![false; n_jobs],
            op_buf: vec![-1; n_jobs],
            op_failed: vec![false; n_jobs],
            drain_bad: vec![false; n_jobs],
            replied: vec![false; n_jobs],
            reply_kind: vec![ReplyKind::None; n_jobs],
            submits: 0,
            replies: 0,
            pending_erasure: 0,
            lost_unerased: 0,
            pinned_zeroed: false,
            teardown: Teardown::None,
        }
    }

    fn pending_of(&self) -> u64 {
        self.buf.iter().filter(|b| b.holds_secret()).count() as u64
    }

    fn excl_in_flight(&self) -> bool {
        self.in_flight.iter().zip(&self.op_exclusive).any(|(f, e)| *f && *e)
    }

    /// Whether every submitted job has its reply and nothing waits.
    pub fn terminal(&self) -> bool {
        self.budget.queue().is_empty()
            && self.replies == self.submits
            && self
                .phase
                .iter()
                .all(|p| matches!(p, Phase::Absent | Phase::Released | Phase::Answered))
    }
}

fn job_ix(s: &State, job: JobId) -> Result<usize, Refusal> {
    let j = job as usize;
    if j < s.phase.len() {
        Ok(j)
    } else {
        Err(Refusal::UnknownJob)
    }
}

fn reply(s: &mut State, j: usize, kind: ReplyKind) {
    s.replied[j] = true;
    s.reply_kind[j] = kind;
    s.replies += 1;
}

/// One protocol step: applies `action` to a copy of `state`, or refuses
/// it and changes nothing. Mirrors the Quint actions one for one.
pub fn step(state: &State, action: &Action) -> Result<State, Refusal> {
    let mut s = state.clone();
    match *action {
        Action::Submit { job, size } => {
            let j = job_ix(&s, job)?;
            if s.phase[j] != Phase::Absent || size == 0 {
                return Err(Refusal::WrongPhase);
            }
            s.submits += 1;
            s.submit_seq[j] = s.next_seq;
            s.next_seq += 1;
            s.size[j] = size;
            if s.teardown != Teardown::None {
                s.phase[j] = Phase::Answered;
                reply(&mut s, j, ReplyKind::Teardown);
            } else if size > s.budget.capacity() {
                s.phase[j] = Phase::Answered;
                reply(&mut s, j, ReplyKind::Refused);
            } else {
                s.phase[j] = Phase::Queued;
                s.budget.enqueue(job);
            }
        }
        Action::Admit => {
            if s.teardown != Teardown::None {
                return Err(Refusal::Teardown);
            }
            let head = s.budget.head().ok_or(Refusal::QueueEmpty)?;
            let j = job_ix(&s, head)?;
            if !s.budget.fits(s.size[j]) {
                return Err(Refusal::DoesNotFit);
            }
            let size = s.size[j];
            s.budget.admit_head(size);
            s.phase[j] = Phase::Admitted;
            s.buf[j] = BufState::Allocated;
            s.buf_owner[j] = head as i64;
        }
        Action::StartOp {
            job,
            buf,
            exclusive,
        } => {
            let j = job_ix(&s, job)?;
            if s.teardown != Teardown::None {
                return Err(Refusal::Teardown);
            }
            if s.phase[j] != Phase::Admitted {
                return Err(Refusal::WrongPhase);
            }
            if buf != job || s.buf_owner.get(buf as usize) != Some(&(job as i64)) {
                return Err(Refusal::WrongBuffer);
            }
            if exclusive && s.excl_in_flight() {
                return Err(Refusal::ExclusiveBusy);
            }
            s.phase[j] = Phase::Running;
            s.in_flight[j] = true;
            s.op_exclusive[j] = exclusive;
            s.op_buf[j] = buf as i64;
        }
        Action::CompleteOp { job, ok } => {
            let j = job_ix(&s, job)?;
            if !s.in_flight[j] {
                return Err(Refusal::WrongPhase);
            }
            s.phase[j] = Phase::Admitted;
            s.in_flight[j] = false;
            s.op_exclusive[j] = false;
            s.op_buf[j] = -1;
            s.buf[j] = BufState::HoldsSecret;
            s.op_failed[j] |= !ok;
            s.pending_erasure = s.pending_of();
        }
        Action::RequestRelease { job } => {
            let j = job_ix(&s, job)?;
            if s.phase[j] != Phase::Admitted || s.in_flight[j] {
                return Err(Refusal::WrongPhase);
            }
            s.phase[j] = Phase::Draining;
        }
        Action::DrainConfirmed { job } => {
            let j = job_ix(&s, job)?;
            if s.phase[j] != Phase::Draining {
                return Err(Refusal::WrongPhase);
            }
            s.phase[j] = Phase::Wiping;
            if s.buf[j] == BufState::HoldsSecret {
                s.buf[j] = BufState::WipeRequested;
            }
            s.pending_erasure = s.pending_of();
        }
        Action::DrainUnconfirmed { job } => {
            let j = job_ix(&s, job)?;
            if s.phase[j] != Phase::Draining {
                return Err(Refusal::WrongPhase);
            }
            s.drain_bad[j] = true;
        }
        Action::WipeConfirmed { job } => {
            let j = job_ix(&s, job)?;
            if s.phase[j] != Phase::Wiping {
                return Err(Refusal::WrongPhase);
            }
            if s.drain_bad[j] {
                return Err(Refusal::DrainBad);
            }
            s.phase[j] = Phase::Wiped;
            s.buf[j] = BufState::WipeConfirmed;
            s.pending_erasure = s.pending_of();
        }
        Action::WipeFailed { job } => {
            let j = job_ix(&s, job)?;
            if s.phase[j] != Phase::Wiping {
                return Err(Refusal::WrongPhase);
            }
            // No change: the wipe may be retried.
        }
        Action::FreeBuffer { job } => {
            let j = job_ix(&s, job)?;
            if s.phase[j] != Phase::Wiped || s.buf[j] != BufState::WipeConfirmed {
                return Err(Refusal::NotWiped);
            }
            s.phase[j] = Phase::Released;
            s.buf[j] = BufState::Freed;
            s.buf_owner[j] = -1;
            let size = s.size[j];
            s.budget.release(size);
            let kind = if s.op_failed[j] {
                ReplyKind::Failed
            } else {
                ReplyKind::Ok
            };
            reply(&mut s, j, kind);
        }
        Action::TeardownBegin => {
            if s.teardown != Teardown::None {
                return Err(Refusal::Teardown);
            }
            s.teardown = Teardown::Draining;
            s.pinned_zeroed = true;
        }
        Action::TeardownFinish => {
            if s.teardown != Teardown::Draining || !s.pinned_zeroed {
                return Err(Refusal::Busy);
            }
            if s.in_flight.iter().any(|f| *f) || s.phase.contains(&Phase::Running) {
                return Err(Refusal::Busy);
            }
            for j in 0..s.phase.len() {
                match s.phase[j] {
                    Phase::Queued => {
                        s.phase[j] = Phase::Answered;
                        reply(&mut s, j, ReplyKind::Teardown);
                    }
                    Phase::Admitted | Phase::Draining | Phase::Wiping | Phase::Wiped => {
                        let lost = s.buf[j].holds_secret();
                        s.buf[j] = if lost {
                            BufState::LostUnerased
                        } else {
                            BufState::Freed
                        };
                        if lost {
                            s.lost_unerased += 1;
                        }
                        s.buf_owner[j] = -1;
                        let size = s.size[j];
                        s.budget.release(size);
                        s.phase[j] = Phase::Released;
                        let kind = if s.op_failed[j] {
                            ReplyKind::Failed
                        } else {
                            ReplyKind::Ok
                        };
                        reply(&mut s, j, kind);
                    }
                    _ => {}
                }
            }
            s.budget.clear_queue();
            s.teardown = Teardown::Dead;
            s.pending_erasure = s.pending_of();
        }
    }
    debug_assert_eq!(s.pending_erasure, s.pending_of());
    debug_assert!(s.budget.reserved() <= s.budget.capacity());
    Ok(s)
}

// ---- JSON codec (field names match the Quint record `s`) ----
//
// A small self-contained JSON reader/writer: this crate's library
// dependencies do not include a JSON crate, and the codec only needs
// objects, arrays, integers, booleans and strings. ITF encodes large
// integers as {"#bigint": "..."}; both forms are read. Sets would be
// {"#set": [...]} and maps {"#map": [[k, v], ...]}; this state has
// neither (lists and records only), matching `itf_value` in
// gpu-spec/scripts/quint_replay.py.

fn ints(v: &[i64]) -> String {
    v.iter().map(i64::to_string).collect::<Vec<_>>().join(",")
}
fn bools(v: &[bool]) -> String {
    v.iter()
        .map(|b| if *b { "true" } else { "false" })
        .collect::<Vec<_>>()
        .join(",")
}

impl State {
    /// The state as one JSON object with the Quint field names.
    pub fn to_json(&self) -> String {
        let queue: Vec<i64> = self.budget.queue().iter().map(|j| *j as i64).collect();
        format!(
            "{{\"capacity\":{},\"reserved\":{},\"queue\":[{}],\"phase\":[{}],\"size\":[{}],\
             \"submitSeq\":[{}],\"nextSeq\":{},\"buf\":[{}],\"bufOwner\":[{}],\
             \"inFlight\":[{}],\"opExclusive\":[{}],\"opBuf\":[{}],\"opFailed\":[{}],\
             \"drainBad\":[{}],\"replied\":[{}],\"replyKind\":[{}],\"submits\":{},\
             \"replies\":{},\"pendingErasure\":{},\"lostUnerased\":{},\
             \"pinnedZeroed\":{},\"teardown\":{}}}",
            self.budget.capacity(),
            self.budget.reserved(),
            ints(&queue),
            ints(&self.phase.iter().map(|p| p.code()).collect::<Vec<_>>()),
            ints(&self.size.iter().map(|v| *v as i64).collect::<Vec<_>>()),
            ints(&self.submit_seq.iter().map(|v| *v as i64).collect::<Vec<_>>()),
            self.next_seq,
            ints(&self.buf.iter().map(|b| b.code()).collect::<Vec<_>>()),
            ints(&self.buf_owner),
            bools(&self.in_flight),
            bools(&self.op_exclusive),
            ints(&self.op_buf),
            bools(&self.op_failed),
            bools(&self.drain_bad),
            bools(&self.replied),
            ints(&self.reply_kind.iter().map(|r| r.code()).collect::<Vec<_>>()),
            self.submits,
            self.replies,
            self.pending_erasure,
            self.lost_unerased,
            self.pinned_zeroed,
            self.teardown.code(),
        )
    }

    /// Parses a state written by [`State::to_json`] or decoded from an
    /// ITF trace frame's `s` field.
    pub fn from_json(text: &str) -> Result<State, String> {
        let v = parse_json(text)?;
        state_from_value(&v)
    }
}

fn state_from_value(v: &Value) -> Result<State, String> {
    let get = |k: &str| v.get(k).ok_or_else(|| format!("missing field {k}"));
    let int = |k: &str| get(k)?.as_int().ok_or_else(|| format!("field {k} is not an int"));
    let int_list = |k: &str| -> Result<Vec<i64>, String> {
        get(k)?
            .as_list()
            .ok_or_else(|| format!("field {k} is not a list"))?
            .iter()
            .map(|x| x.as_int().ok_or_else(|| format!("field {k} holds a non-int")))
            .collect()
    };
    let bool_list = |k: &str| -> Result<Vec<bool>, String> {
        get(k)?
            .as_list()
            .ok_or_else(|| format!("field {k} is not a list"))?
            .iter()
            .map(|x| x.as_bool().ok_or_else(|| format!("field {k} holds a non-bool")))
            .collect()
    };
    let phase: Vec<Phase> = int_list("phase")?
        .iter()
        .map(|c| Phase::from_code(*c).ok_or_else(|| format!("bad phase code {c}")))
        .collect::<Result<_, _>>()?;
    let n = phase.len();
    let mut budget = Budget::new(int("capacity")?.max(0) as u64);
    for j in int_list("queue")? {
        budget.enqueue(j as JobId);
    }
    budget.restore(int("reserved")?.max(0) as u64);
    let st = State {
        budget,
        phase,
        size: int_list("size")?.iter().map(|v| (*v).max(0) as u64).collect(),
        submit_seq: int_list("submitSeq")?.iter().map(|v| (*v).max(0) as u64).collect(),
        next_seq: int("nextSeq")?.max(0) as u64,
        buf: int_list("buf")?
            .iter()
            .map(|c| BufState::from_code(*c).ok_or_else(|| format!("bad buf code {c}")))
            .collect::<Result<_, _>>()?,
        buf_owner: int_list("bufOwner")?,
        in_flight: bool_list("inFlight")?,
        op_exclusive: bool_list("opExclusive")?,
        op_buf: int_list("opBuf")?,
        op_failed: bool_list("opFailed")?,
        drain_bad: bool_list("drainBad")?,
        replied: bool_list("replied")?,
        reply_kind: int_list("replyKind")?
            .iter()
            .map(|c| ReplyKind::from_code(*c).ok_or_else(|| format!("bad reply code {c}")))
            .collect::<Result<_, _>>()?,
        submits: int("submits")?.max(0) as u64,
        replies: int("replies")?.max(0) as u64,
        pending_erasure: int("pendingErasure")?.max(0) as u64,
        lost_unerased: int("lostUnerased")?.max(0) as u64,
        pinned_zeroed: get("pinnedZeroed")?.as_bool().ok_or("pinnedZeroed is not a bool")?,
        teardown: Teardown::from_code(int("teardown")?).ok_or("bad teardown code")?,
    };
    if st.size.len() != n || st.buf.len() != n || st.replied.len() != n {
        return Err("per-job lists have different lengths".into());
    }
    Ok(st)
}

/// Replays one ITF trace (the JSON `quint run --out-itf` writes):
/// frame 0 is the initial state; each later frame's `lastOp` decodes
/// to the action that must step the previous decoded state to exactly
/// that frame's `s`. Returns the number of transitions checked.
pub fn replay_itf(text: &str) -> Result<usize, String> {
    let root = parse_json(text)?;
    let states = root
        .get("states")
        .and_then(|v| v.as_list())
        .ok_or("ITF trace has no states list")?;
    if states.is_empty() {
        return Err("ITF trace has no frames".into());
    }
    let frame_state = |f: &Value| -> Result<State, String> {
        state_from_value(f.get("s").ok_or("ITF frame has no s")?)
    };
    let mut cur = frame_state(&states[0])?;
    for (i, frame) in states.iter().enumerate().skip(1) {
        let op = frame
            .get("lastOp")
            .and_then(|v| v.as_int())
            .ok_or_else(|| format!("frame {i} has no lastOp"))?;
        if op == 0 {
            continue; // an init frame
        }
        let action = Action::from_op_code(op).ok_or_else(|| format!("bad lastOp {op}"))?;
        let next =
            step(&cur, &action).map_err(|r| format!("frame {i}: {action:?} refused ({r:?})"))?;
        let want = frame_state(frame)?;
        if next != want {
            return Err(format!(
                "frame {i}: step disagrees with the trace\n got: {}\nwant: {}",
                next.to_json(),
                want.to_json()
            ));
        }
        cur = next;
    }
    Ok(states.len() - 1)
}

// Minimal JSON value + parser (objects, arrays, strings, ints, bools,
// null). Numbers with a fraction or exponent are refused: the codec
// only carries integers.
#[derive(Clone, Debug, PartialEq)]
enum Value {
    Null,
    Bool(bool),
    Int(i64),
    Str(String),
    List(Vec<Value>),
    Obj(Vec<(String, Value)>),
}

impl Value {
    fn get(&self, key: &str) -> Option<&Value> {
        match self {
            Value::Obj(kvs) => kvs
                .iter()
                .find(|(k, _)| k == key)
                .or_else(|| {
                    // The simulator namespaces variables, e.g.
                    // `actor_default::device_actor::s`; accept a key by
                    // its last path segment.
                    kvs.iter().find(|(k, _)| k.rsplit("::").next() == Some(key))
                })
                .map(|(_, v)| v),
            _ => None,
        }
    }
    fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(n) => Some(*n),
            // ITF big integers: {"#bigint": "123"}
            Value::Obj(_) => self.get("#bigint")?.as_str()?.parse().ok(),
            _ => None,
        }
    }
    fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }
    fn as_str(&self) -> Option<&str> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
    }
    fn as_list(&self) -> Option<&[Value]> {
        match self {
            Value::List(l) => Some(l),
            _ => None,
        }
    }
}

fn parse_json(text: &str) -> Result<Value, String> {
    let bytes = text.as_bytes();
    let mut pos = 0usize;
    let v = parse_value(bytes, &mut pos)?;
    skip_ws(bytes, &mut pos);
    if pos != bytes.len() {
        return Err(format!("trailing input at byte {pos}"));
    }
    Ok(v)
}

fn skip_ws(b: &[u8], pos: &mut usize) {
    while *pos < b.len() && b[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
}

fn parse_value(b: &[u8], pos: &mut usize) -> Result<Value, String> {
    skip_ws(b, pos);
    match b.get(*pos) {
        Some(b'{') => {
            *pos += 1;
            let mut kvs = Vec::new();
            skip_ws(b, pos);
            if b.get(*pos) == Some(&b'}') {
                *pos += 1;
                return Ok(Value::Obj(kvs));
            }
            loop {
                let key = match parse_value(b, pos)? {
                    Value::Str(s) => s,
                    _ => return Err("object key is not a string".into()),
                };
                skip_ws(b, pos);
                if b.get(*pos) != Some(&b':') {
                    return Err("expected ':' in object".into());
                }
                *pos += 1;
                let val = parse_value(b, pos)?;
                kvs.push((key, val));
                skip_ws(b, pos);
                match b.get(*pos) {
                    Some(b',') => *pos += 1,
                    Some(b'}') => {
                        *pos += 1;
                        return Ok(Value::Obj(kvs));
                    }
                    _ => return Err("expected ',' or '}' in object".into()),
                }
            }
        }
        Some(b'[') => {
            *pos += 1;
            let mut items = Vec::new();
            skip_ws(b, pos);
            if b.get(*pos) == Some(&b']') {
                *pos += 1;
                return Ok(Value::List(items));
            }
            loop {
                items.push(parse_value(b, pos)?);
                skip_ws(b, pos);
                match b.get(*pos) {
                    Some(b',') => *pos += 1,
                    Some(b']') => {
                        *pos += 1;
                        return Ok(Value::List(items));
                    }
                    _ => return Err("expected ',' or ']' in array".into()),
                }
            }
        }
        Some(b'"') => {
            *pos += 1;
            let start = *pos;
            let mut out = String::new();
            loop {
                match b.get(*pos) {
                    Some(b'"') => {
                        if out.is_empty() {
                            out = String::from_utf8_lossy(&b[start..*pos]).into_owned();
                        }
                        *pos += 1;
                        return Ok(Value::Str(out));
                    }
                    Some(b'\\') => {
                        out.push_str(&String::from_utf8_lossy(&b[start..*pos]));
                        *pos += 1;
                        match b.get(*pos) {
                            Some(b'n') => out.push('\n'),
                            Some(b't') => out.push('\t'),
                            Some(b'r') => out.push('\r'),
                            Some(c) => out.push(*c as char),
                            None => return Err("unterminated string".into()),
                        }
                        *pos += 1;
                        // Continue scanning the remainder as a fresh segment.
                        let rest_start = *pos;
                        while !matches!(b.get(*pos), Some(b'"') | Some(b'\\') | None) {
                            *pos += 1;
                        }
                        out.push_str(&String::from_utf8_lossy(&b[rest_start..*pos]));
                        if b.get(*pos) == Some(&b'"') {
                            *pos += 1;
                            return Ok(Value::Str(out));
                        }
                        if b.get(*pos).is_none() {
                            return Err("unterminated string".into());
                        }
                        // Another escape: loop with start reset.
                        return finish_escaped(b, pos, out);
                    }
                    Some(_) => *pos += 1,
                    None => return Err("unterminated string".into()),
                }
            }
        }
        Some(b't') if b[*pos..].starts_with(b"true") => {
            *pos += 4;
            Ok(Value::Bool(true))
        }
        Some(b'f') if b[*pos..].starts_with(b"false") => {
            *pos += 5;
            Ok(Value::Bool(false))
        }
        Some(b'n') if b[*pos..].starts_with(b"null") => {
            *pos += 4;
            Ok(Value::Null)
        }
        Some(c) if *c == b'-' || c.is_ascii_digit() => {
            let start = *pos;
            if *c == b'-' {
                *pos += 1;
            }
            while b.get(*pos).is_some_and(|d| d.is_ascii_digit()) {
                *pos += 1;
            }
            if matches!(b.get(*pos), Some(b'.') | Some(b'e') | Some(b'E')) {
                return Err("non-integer number in actor JSON".into());
            }
            std::str::from_utf8(&b[start..*pos])
                .map_err(|e| e.to_string())?
                .parse::<i64>()
                .map(Value::Int)
                .map_err(|e| e.to_string())
        }
        _ => Err(format!("unexpected input at byte {pos}")),
    }
}

fn finish_escaped(b: &[u8], pos: &mut usize, mut out: String) -> Result<Value, String> {
    loop {
        match b.get(*pos) {
            Some(b'"') => {
                *pos += 1;
                return Ok(Value::Str(out));
            }
            Some(b'\\') => {
                *pos += 1;
                match b.get(*pos) {
                    Some(b'n') => out.push('\n'),
                    Some(b't') => out.push('\t'),
                    Some(b'r') => out.push('\r'),
                    Some(c) => out.push(*c as char),
                    None => return Err("unterminated string".into()),
                }
                *pos += 1;
            }
            Some(c) => {
                out.push(*c as char);
                *pos += 1;
            }
            None => return Err("unterminated string".into()),
        }
    }
}
