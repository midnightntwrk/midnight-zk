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

//! Protocol-core tests: budget FIFO, buffer lifecycle, teardown,
//! exclusivity, pending-erasure exactness, and ITF trace replay.
//! No device is used.

use midnight_gpu::actor::protocol::{
    Action, BufState, Phase, Refusal, ReplyKind, State, Teardown, step,
};

fn run(mut s: State, actions: &[Action]) -> State {
    for a in actions {
        s = step(&s, a).unwrap_or_else(|r| panic!("{a:?} refused: {r:?} in {s:?}"));
    }
    s
}

fn whole_job(s: State, job: u32, size: u64) -> State {
    run(
        s,
        &[
            Action::Submit { job, size },
            Action::Admit,
            Action::StartOp {
                job,
                buf: job,
                exclusive: false,
            },
            Action::CompleteOp { job, ok: true },
            Action::RequestRelease { job },
            Action::DrainConfirmed { job },
            Action::WipeConfirmed { job },
            Action::FreeBuffer { job },
        ],
    )
}

#[test]
fn whole_job_releases_and_returns_bytes() {
    let s = whole_job(State::new(4, 3), 0, 2);
    assert_eq!(s.phase[0], Phase::Released);
    assert_eq!(s.reply_kind[0], ReplyKind::Ok);
    assert_eq!(s.budget.reserved(), 0);
    assert_eq!(s.pending_erasure, 0);
    assert_eq!(s.buf[0], BufState::Freed);
    assert_eq!(s.replies, 1);
}

#[test]
fn budget_never_admits_over_capacity() {
    let s = run(
        State::new(4, 3),
        &[Action::Submit { job: 0, size: 3 }, Action::Admit],
    );
    let s = run(s, &[Action::Submit { job: 1, size: 3 }]);
    assert_eq!(step(&s, &Action::Admit), Err(Refusal::DoesNotFit));
    assert!(s.budget.reserved() <= s.budget.capacity());
}

#[test]
fn fifo_head_is_not_overtaken_or_starved() {
    // capacity 4: job0 holds 3, job1 (3) heads the queue, job2 (1) fits
    // in the free unit but must not pass job1.
    let s = run(
        State::new(4, 3),
        &[
            Action::Submit { job: 0, size: 3 },
            Action::Admit,
            Action::Submit { job: 1, size: 3 },
            Action::Submit { job: 2, size: 1 },
        ],
    );
    assert_eq!(step(&s, &Action::Admit), Err(Refusal::DoesNotFit));
    assert_eq!(s.phase[2], Phase::Queued);
    // Finish job0; the head (job1) is admitted next, not job2.
    let s = run(
        s,
        &[
            Action::StartOp {
                job: 0,
                buf: 0,
                exclusive: false,
            },
            Action::CompleteOp { job: 0, ok: true },
            Action::RequestRelease { job: 0 },
            Action::DrainConfirmed { job: 0 },
            Action::WipeConfirmed { job: 0 },
            Action::FreeBuffer { job: 0 },
            Action::Admit,
        ],
    );
    assert_eq!(s.phase[1], Phase::Admitted);
    assert_eq!(s.phase[2], Phase::Queued);
}

#[test]
fn bytes_return_only_after_wipe_confirmed() {
    let s = run(
        State::new(4, 3),
        &[
            Action::Submit { job: 0, size: 2 },
            Action::Admit,
            Action::StartOp {
                job: 0,
                buf: 0,
                exclusive: false,
            },
            Action::CompleteOp { job: 0, ok: true },
            Action::RequestRelease { job: 0 },
        ],
    );
    assert_eq!(s.pending_erasure, 1);
    assert_eq!(
        step(&s, &Action::FreeBuffer { job: 0 }),
        Err(Refusal::NotWiped)
    );
    assert_eq!(s.budget.reserved(), 2);
    let s = run(s, &[Action::DrainConfirmed { job: 0 }]);
    assert_eq!(s.pending_erasure, 1, "wipe-requested still counts");
    assert_eq!(
        step(&s, &Action::FreeBuffer { job: 0 }),
        Err(Refusal::NotWiped)
    );
    let s = run(s, &[Action::WipeConfirmed { job: 0 }]);
    assert_eq!(s.pending_erasure, 0);
    let s = run(s, &[Action::FreeBuffer { job: 0 }]);
    assert_eq!(s.budget.reserved(), 0);
}

#[test]
fn cross_job_buffer_is_refused() {
    let s = run(
        State::new(4, 3),
        &[
            Action::Submit { job: 0, size: 2 },
            Action::Submit { job: 1, size: 2 },
            Action::Admit,
            Action::Admit,
        ],
    );
    assert_eq!(
        step(
            &s,
            &Action::StartOp {
                job: 0,
                buf: 1,
                exclusive: false
            }
        ),
        Err(Refusal::WrongBuffer)
    );
}

#[test]
fn exclusive_ops_never_concurrent_but_plain_ops_are() {
    let s = run(
        State::new(4, 3),
        &[
            Action::Submit { job: 0, size: 2 },
            Action::Submit { job: 1, size: 2 },
            Action::Admit,
            Action::Admit,
            Action::StartOp {
                job: 0,
                buf: 0,
                exclusive: true,
            },
        ],
    );
    assert_eq!(
        step(
            &s,
            &Action::StartOp {
                job: 1,
                buf: 1,
                exclusive: true
            }
        ),
        Err(Refusal::ExclusiveBusy)
    );
    let s = run(
        s,
        &[Action::StartOp {
            job: 1,
            buf: 1,
            exclusive: false,
        }],
    );
    assert!(
        s.in_flight[0] && s.in_flight[1],
        "two ops in flight at once"
    );
}

#[test]
fn unconfirmed_drain_blocks_wipe_and_reset_counts_lost() {
    let s = run(
        State::new(4, 3),
        &[
            Action::Submit { job: 0, size: 2 },
            Action::Admit,
            Action::StartOp {
                job: 0,
                buf: 0,
                exclusive: false,
            },
            Action::CompleteOp { job: 0, ok: true },
            Action::RequestRelease { job: 0 },
            Action::DrainUnconfirmed { job: 0 },
            Action::DrainConfirmed { job: 0 },
        ],
    );
    assert_eq!(
        step(&s, &Action::WipeConfirmed { job: 0 }),
        Err(Refusal::DrainBad)
    );
    assert_eq!(s.pending_erasure, 1);
    let s = run(s, &[Action::TeardownBegin, Action::TeardownFinish]);
    assert_eq!(s.buf[0], BufState::LostUnerased);
    assert_eq!(s.lost_unerased, 1);
    assert_eq!(s.pending_erasure, 0);
    assert_eq!(s.budget.reserved(), 0);
    assert!(s.replied[0]);
}

#[test]
fn teardown_answers_queued_and_every_later_submit() {
    let s = run(
        State::new(4, 3),
        &[
            Action::Submit { job: 0, size: 3 },
            Action::Admit,
            Action::Submit { job: 1, size: 3 },
            Action::TeardownBegin,
            Action::TeardownFinish,
        ],
    );
    assert_eq!(s.teardown, Teardown::Dead);
    assert_eq!(s.reply_kind[1], ReplyKind::Teardown);
    assert_eq!(s.replies, s.submits);
    assert!(s.budget.queue().is_empty());
    let s = run(s, &[Action::Submit { job: 2, size: 1 }]);
    assert_eq!(s.reply_kind[2], ReplyKind::Teardown);
    assert_eq!(s.phase[2], Phase::Answered);
    assert_eq!(s.replies, s.submits, "no reply is lost");
}

#[test]
fn over_capacity_submit_is_refused_at_once() {
    let s = run(State::new(4, 3), &[Action::Submit { job: 0, size: 5 }]);
    assert_eq!(s.reply_kind[0], ReplyKind::Refused);
    assert!(s.budget.queue().is_empty());
}

#[test]
fn failed_op_still_wipes_and_replies_failed() {
    let s = run(
        State::new(4, 3),
        &[
            Action::Submit { job: 0, size: 2 },
            Action::Admit,
            Action::StartOp {
                job: 0,
                buf: 0,
                exclusive: false,
            },
            Action::CompleteOp { job: 0, ok: false },
            Action::RequestRelease { job: 0 },
            Action::DrainConfirmed { job: 0 },
            Action::WipeConfirmed { job: 0 },
            Action::FreeBuffer { job: 0 },
        ],
    );
    assert_eq!(s.reply_kind[0], ReplyKind::Failed);
    assert_eq!(s.pending_erasure, 0);
}

#[test]
fn json_roundtrip_and_op_encoding() {
    let s = whole_job(State::new(4, 3), 0, 2);
    let text = s.to_json();
    let back = State::from_json(&text).expect("state json parses");
    assert_eq!(s, back);
    for a in [
        Action::Submit { job: 1, size: 3 },
        Action::Admit,
        Action::StartOp {
            job: 2,
            buf: 2,
            exclusive: true,
        },
        Action::CompleteOp { job: 0, ok: false },
        Action::TeardownFinish,
    ] {
        assert_eq!(Action::from_op_code(a.op_code()), Some(a));
    }
}

#[test]
fn itf_traces_replay_when_present() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../gpu-spec/vectors/actor");
    if !dir.is_dir() {
        return;
    }
    let mut files = 0;
    for entry in std::fs::read_dir(&dir).expect("read vectors/actor") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_some_and(|e| e == "json") {
            let text = std::fs::read_to_string(&path).expect("read trace");
            let steps = midnight_gpu::actor::protocol::replay_itf(&text)
                .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
            assert!(steps > 0, "{} has no steps", path.display());
            files += 1;
        }
    }
    assert!(files > 0, "trace directory is present but holds no traces");
}

#[test]
fn namespaced_itf_keys_replay() {
    // The simulator namespaces variables by instance module and encodes
    // integers as {"#bigint": "N"}; the codec must accept both.
    let s0 = State::new(4, 3);
    let s1 = step(&s0, &Action::Submit { job: 0, size: 4 }).expect("submit");
    let trace = format!(
        "{{\"states\":[\
         {{\"test_actor::device_actor::s\":{},\"test_actor::device_actor::lastOp\":{{\"#bigint\":\"0\"}}}},\
         {{\"test_actor::device_actor::s\":{},\"test_actor::device_actor::lastOp\":{{\"#bigint\":\"40001\"}}}}]}}",
        s0.to_json(),
        s1.to_json()
    );
    assert_eq!(
        midnight_gpu::actor::protocol::replay_itf(&trace).expect("namespaced trace replays"),
        1
    );
}
