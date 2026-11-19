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

//! The device lock protocol and the socket helpers it needs.
//!
//! When a lock file is configured, the device is exclusive under an
//! exclusive `flock` on that file, and the caller of a request holds the lock.
//! The service never takes the lock for itself. The caller proves that it
//! holds the lock by passing the locked file descriptor with its request
//! (`SCM_RIGHTS` over the Unix socket). The service accepts the descriptor as
//! a [`Lease`] when:
//!
//! 1. it names the configured lock file (same device and inode), and
//! 2. a fresh open of the lock file cannot take the lock (someone holds it),
//!    and
//! 3. the passed descriptor can take the lock without blocking. `flock` locks
//!    belong to the open file description, so this succeeds only when the
//!    caller's own open file description is the holder.
//!
//! A lock held by an unrelated process therefore gives no lease. The service
//! keeps its copy of the descriptor until the request has ended and its
//! buffers are wiped, so the lock stays held for the whole request even when
//! the client disconnects early.
//!
//! Limit: a device user that ignores the lock is not seen and not protected
//! against.

use std::{
    fs::File,
    io,
    os::{
        fd::{AsRawFd, FromRawFd, OwnedFd, RawFd},
        unix::{fs::MetadataExt, net::UnixStream},
    },
    path::Path,
};

/// Why a passed descriptor is not a lease.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeaseError {
    /// The request carried no descriptor.
    NoDescriptor,
    /// The lock file does not exist or cannot be opened.
    NoLockFile,
    /// The descriptor names another file.
    OtherFile,
    /// Nobody holds the lock.
    NotHeld,
    /// Another open file description holds the lock.
    HeldByOther,
}

impl LeaseError {
    /// A fixed text for replies and logs.
    pub fn as_str(self) -> &'static str {
        match self {
            LeaseError::NoDescriptor => "no-descriptor",
            LeaseError::NoLockFile => "no-lock-file",
            LeaseError::OtherFile => "other-file",
            LeaseError::NotHeld => "not-held",
            LeaseError::HeldByOther => "held-by-other",
        }
    }
}

/// A validated hold of the device lock for one request.
#[derive(Debug)]
pub struct Lease {
    _fd: OwnedFd,
    path: std::path::PathBuf,
    dev: u64,
    ino: u64,
}

fn flock(fd: RawFd, op: libc::c_int) -> io::Result<()> {
    loop {
        // SAFETY: `flock` takes any descriptor value and reports bad ones.
        if unsafe { libc::flock(fd, op) } == 0 {
            return Ok(());
        }
        let e = io::Error::last_os_error();
        if e.kind() != io::ErrorKind::Interrupted {
            return Err(e);
        }
    }
}

impl Lease {
    /// Validates `fd` as a hold of the lock at `lock_path`.
    pub fn validate(lock_path: &Path, fd: Option<OwnedFd>) -> Result<Lease, LeaseError> {
        let fd = fd.ok_or(LeaseError::NoDescriptor)?;
        let want = std::fs::metadata(lock_path).map_err(|_| LeaseError::NoLockFile)?;
        // SAFETY: `st` is written by `fstat` before it is read.
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        // SAFETY: `fd` is an open descriptor and `st` a valid out pointer.
        if unsafe { libc::fstat(fd.as_raw_fd(), &mut st) } != 0
            || st.st_dev != want.dev()
            || st.st_ino != want.ino()
        {
            return Err(LeaseError::OtherFile);
        }
        let probe = File::open(lock_path).map_err(|_| LeaseError::NoLockFile)?;
        if flock(probe.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB).is_ok() {
            let _ = flock(probe.as_raw_fd(), libc::LOCK_UN);
            return Err(LeaseError::NotHeld);
        }
        drop(probe);
        if flock(fd.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB).is_err() {
            return Err(LeaseError::HeldByOther);
        }
        Ok(Lease {
            _fd: fd,
            path: lock_path.to_path_buf(),
            dev: want.dev(),
            ino: want.ino(),
        })
    }

    /// A check that is `true` once the lease is lost: the lock path no
    /// longer names the locked file (it was removed or replaced, so another
    /// process can lock the new file and use the device).
    ///
    /// It is also `true` once the leased open file description no longer
    /// holds the lock on that file (its holder unlocked it, so another
    /// process may take it). The check is synchronous: the service runs it
    /// before each device phase.
    pub fn watch(&self) -> impl Fn() -> bool + Send + Sync + 'static {
        let (path, dev, ino) = (self.path.clone(), self.dev, self.ino);
        // the same open file description (close-on-exec)
        let fd = self._fd.try_clone().ok();
        move || {
            let moved = std::fs::metadata(&path).map_or(true, |m| m.dev() != dev || m.ino() != ino);
            moved || !fd.as_ref().is_some_and(|fd| holds(&path, fd))
        }
    }
}

/// Whether the open file description of `fd` holds the exclusive lock of
/// `path`.
fn holds(path: &Path, fd: &OwnedFd) -> bool {
    // a second open of the path takes the lock: nobody holds it
    if let Ok(probe) = File::open(path)
        && flock(probe.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB).is_ok()
    {
        let _ = flock(probe.as_raw_fd(), libc::LOCK_UN);
        return false;
    }
    // somebody holds it: this description does when it takes it again
    // without waiting (a no-op for the holder)
    flock(fd.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB).is_ok()
}

/// Whether the peer of `s` closed its end: a peek reads end-of-file. Bytes
/// the peer sent after its request line do not count as a hang-up.
pub fn peer_hung_up(s: &std::os::unix::net::UnixStream) -> bool {
    let mut b = [0u8; 1];
    // SAFETY: `b` is a valid buffer of one byte; `recv` with MSG_PEEK and
    // MSG_DONTWAIT neither consumes data nor blocks.
    let n = unsafe {
        libc::recv(
            s.as_raw_fd(),
            b.as_mut_ptr().cast(),
            1,
            libc::MSG_PEEK | libc::MSG_DONTWAIT,
        )
    };
    n == 0
}

/// Takes an exclusive `flock` on `path` (created owner-only if missing),
/// blocking until it is free. The lock is held while the returned file is
/// open.
pub fn lock_exclusive(path: &Path) -> io::Result<File> {
    use std::os::unix::fs::OpenOptionsExt;
    let f = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .open(path)?;
    flock(f.as_raw_fd(), libc::LOCK_EX)?;
    Ok(f)
}

/// The uid of the peer of a Unix stream (`getpeereid` where `SO_PEERCRED`
/// does not exist).
#[cfg(not(any(target_os = "linux", target_os = "android")))]
pub fn peer_uid(s: &UnixStream) -> Option<u32> {
    let (mut uid, mut gid) = (0, 0);
    // SAFETY: `uid` and `gid` are valid out pointers.
    let r = unsafe { libc::getpeereid(s.as_raw_fd(), &mut uid, &mut gid) };
    (r == 0).then_some(uid)
}

/// The uid of the peer of a Unix stream (`SO_PEERCRED`).
#[cfg(any(target_os = "linux", target_os = "android"))]
pub fn peer_uid(s: &UnixStream) -> Option<u32> {
    let mut c = libc::ucred {
        pid: 0,
        uid: 0,
        gid: 0,
    };
    let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    // SAFETY: `c` and `len` are valid out pointers of the right size.
    let r = unsafe {
        libc::getsockopt(
            s.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            (&mut c as *mut libc::ucred).cast(),
            &mut len,
        )
    };
    (r == 0).then_some(c.uid)
}

/// The effective uid of this process.
pub fn own_uid() -> u32 {
    // SAFETY: `geteuid` has no preconditions.
    unsafe { libc::geteuid() }
}

const CMSG_BUF: usize = 64;

/// `sendmsg` flags: no SIGPIPE where the flag exists (elsewhere the Rust
/// runtime ignores SIGPIPE).
#[cfg(any(target_os = "linux", target_os = "android"))]
const SEND_FLAGS: libc::c_int = libc::MSG_NOSIGNAL;
#[cfg(not(any(target_os = "linux", target_os = "android")))]
const SEND_FLAGS: libc::c_int = 0;

/// `recvmsg` flags: received descriptors close-on-exec where the flag
/// exists; elsewhere [`recv_with_fd`] sets `FD_CLOEXEC` after the call.
#[cfg(any(target_os = "linux", target_os = "android"))]
const RECV_FLAGS: libc::c_int = libc::MSG_CMSG_CLOEXEC;
#[cfg(not(any(target_os = "linux", target_os = "android")))]
const RECV_FLAGS: libc::c_int = 0;

/// Writes `data` with `fd` attached as `SCM_RIGHTS`.
pub fn send_with_fd(s: &UnixStream, data: &[u8], fd: RawFd) -> io::Result<usize> {
    let mut iov = libc::iovec {
        iov_base: data.as_ptr() as *mut _,
        iov_len: data.len(),
    };
    let mut cbuf = [0u64; CMSG_BUF / 8];
    // SAFETY: the message header points at live buffers of the stated sizes;
    // the control buffer is aligned and large enough for one descriptor.
    unsafe {
        let mut msg: libc::msghdr = std::mem::zeroed();
        msg.msg_iov = &mut iov;
        msg.msg_iovlen = 1;
        msg.msg_control = cbuf.as_mut_ptr().cast();
        msg.msg_controllen = libc::CMSG_SPACE(std::mem::size_of::<RawFd>() as u32) as _;
        let c = libc::CMSG_FIRSTHDR(&msg);
        (*c).cmsg_level = libc::SOL_SOCKET;
        (*c).cmsg_type = libc::SCM_RIGHTS;
        (*c).cmsg_len = libc::CMSG_LEN(std::mem::size_of::<RawFd>() as u32) as _;
        std::ptr::write_unaligned(libc::CMSG_DATA(c).cast::<RawFd>(), fd);
        let n = libc::sendmsg(s.as_raw_fd(), &msg, SEND_FLAGS);
        if n < 0 {
            Err(io::Error::last_os_error())
        } else {
            Ok(n as usize)
        }
    }
}

/// Reads into `buf`, taking at most one passed descriptor. Descriptors are
/// received close-on-exec; any extra descriptor is closed.
pub fn recv_with_fd(s: &UnixStream, buf: &mut [u8]) -> io::Result<(usize, Option<OwnedFd>)> {
    let mut iov = libc::iovec {
        iov_base: buf.as_mut_ptr().cast(),
        iov_len: buf.len(),
    };
    let mut cbuf = [0u64; CMSG_BUF / 8];
    // SAFETY: as in `send_with_fd`; every descriptor the kernel passes is
    // taken into an `OwnedFd` exactly once.
    unsafe {
        let mut msg: libc::msghdr = std::mem::zeroed();
        msg.msg_iov = &mut iov;
        msg.msg_iovlen = 1;
        msg.msg_control = cbuf.as_mut_ptr().cast();
        msg.msg_controllen = CMSG_BUF as _;
        let n = libc::recvmsg(s.as_raw_fd(), &mut msg, RECV_FLAGS);
        if n < 0 {
            return Err(io::Error::last_os_error());
        }
        let mut got = None;
        let mut c = libc::CMSG_FIRSTHDR(&msg);
        while !c.is_null() {
            if (*c).cmsg_level == libc::SOL_SOCKET && (*c).cmsg_type == libc::SCM_RIGHTS {
                let data = libc::CMSG_DATA(c).cast::<RawFd>();
                let count = ((*c).cmsg_len as usize - libc::CMSG_LEN(0) as usize)
                    / std::mem::size_of::<RawFd>();
                for i in 0..count {
                    let raw = std::ptr::read_unaligned(data.add(i));
                    if RECV_FLAGS == 0 {
                        libc::fcntl(raw, libc::F_SETFD, libc::FD_CLOEXEC);
                    }
                    let fd = OwnedFd::from_raw_fd(raw);
                    if got.is_none() {
                        got = Some(fd);
                    }
                }
            }
            c = libc::CMSG_NXTHDR(&msg, c);
        }
        Ok((n as usize, got))
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::os::fd::AsFd;

    use super::*;

    /// Tests that start a child process, and tests that check a lock or a
    /// socket is released once its holders are gone, run one at a time. Between
    /// `fork` and `exec` a child holds a copy of every descriptor of this
    /// process, close-on-exec ones included, so a child started by another
    /// test thread keeps the lock until its `exec`.
    pub(crate) static SPAWN: std::sync::Mutex<()> = std::sync::Mutex::new(());

    pub(crate) fn spawn_guard() -> std::sync::MutexGuard<'static, ()> {
        SPAWN.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn dup(f: &File) -> OwnedFd {
        f.as_fd().try_clone_to_owned().unwrap()
    }

    /// The descriptors of this process and of its live children that name
    /// `path` (diagnostic of a lock that outlives its holder).
    fn fd_report(path: &Path) -> String {
        let mut pids = vec![std::process::id().to_string()];
        if let Ok(tasks) = std::fs::read_dir("/proc/self/task") {
            for t in tasks.flatten() {
                let c = std::fs::read_to_string(t.path().join("children")).unwrap_or_default();
                pids.extend(c.split_whitespace().map(str::to_string));
            }
        }
        let mut out = String::new();
        for pid in pids {
            let comm = std::fs::read_to_string(format!("/proc/{pid}/comm")).unwrap_or_default();
            let Ok(fds) = std::fs::read_dir(format!("/proc/{pid}/fd")) else {
                continue;
            };
            for e in fds.flatten() {
                let Ok(l) = std::fs::read_link(e.path()) else {
                    continue;
                };
                let flags = std::fs::read_to_string(format!(
                    "/proc/{pid}/fdinfo/{}",
                    e.file_name().to_string_lossy()
                ))
                .unwrap_or_default();
                let flags = flags.lines().find(|l| l.starts_with("flags")).unwrap_or("");
                let mark = if l == path { " <== lock file" } else { "" };
                out.push_str(&format!(
                    "pid {pid} ({}) fd {} -> {} [{flags}]{mark}\n",
                    comm.trim(),
                    e.file_name().to_string_lossy(),
                    l.display()
                ));
            }
        }
        out
    }

    #[test]
    fn lease_needs_the_holders_descriptor() {
        let _g = spawn_guard();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("device.lock");
        // no lock file
        let other = tempfile::tempfile().unwrap();
        assert_eq!(
            Lease::validate(&path, Some(dup(&other))).unwrap_err(),
            LeaseError::NoLockFile
        );
        let held = lock_exclusive(&path).unwrap();
        // no descriptor
        assert_eq!(
            Lease::validate(&path, None).unwrap_err(),
            LeaseError::NoDescriptor
        );
        // a descriptor of another file
        assert_eq!(
            Lease::validate(&path, Some(dup(&other))).unwrap_err(),
            LeaseError::OtherFile
        );
        // the holder's descriptor
        let lease = Lease::validate(&path, Some(dup(&held))).unwrap();
        // a descriptor of the right file that does not hold the lock
        let stranger = File::open(&path).unwrap();
        assert_eq!(
            Lease::validate(&path, Some(dup(&stranger))).unwrap_err(),
            LeaseError::HeldByOther
        );
        // the lease keeps the lock after the caller closes its descriptor
        drop(held);
        let probe = File::open(&path).unwrap();
        assert!(flock(probe.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB).is_err());
        drop(lease);
        let free = flock(probe.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB).is_ok();
        assert!(free, "the lock outlived the lease:\n{}", fd_report(&path));
        let _ = flock(probe.as_raw_fd(), libc::LOCK_UN);
        // nobody holds it
        let f = File::open(&path).unwrap();
        assert_eq!(
            Lease::validate(&path, Some(dup(&f))).unwrap_err(),
            LeaseError::NotHeld
        );
    }

    /// A child process does not keep the lock: every descriptor that holds
    /// it is close-on-exec, so once the child runs its program the lock is
    /// free when its holder drops it.
    #[test]
    fn a_child_process_does_not_keep_the_lock() {
        let _g = spawn_guard();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("device.lock");
        let held = lock_exclusive(&path).unwrap();
        let lease = Lease::validate(&path, Some(dup(&held))).unwrap();
        // `spawn` returns once the child runs `sleep`
        let mut child = std::process::Command::new("sleep")
            .arg("30")
            .stdin(std::process::Stdio::null())
            .spawn()
            .unwrap();
        drop(held);
        drop(lease);
        let probe = File::open(&path).unwrap();
        let free = flock(probe.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB).is_ok();
        let report = if free {
            String::new()
        } else {
            fd_report(&path)
        };
        let _ = child.kill();
        let _ = child.wait();
        assert!(free, "a child kept the lock:\n{report}");
    }

    #[test]
    fn descriptor_passing_and_peer_uid() {
        let (a, b) = UnixStream::pair().unwrap();
        let f = tempfile::tempfile().unwrap();
        assert_eq!(send_with_fd(&a, b"hello\n", f.as_raw_fd()).unwrap(), 6);
        let mut buf = [0u8; 16];
        let (n, fd) = recv_with_fd(&b, &mut buf).unwrap();
        assert_eq!(&buf[..n], b"hello\n");
        let fd = fd.expect("descriptor");
        let (m1, m2) = (f.metadata().unwrap(), File::from(fd).metadata().unwrap());
        assert_eq!((m1.dev(), m1.ino()), (m2.dev(), m2.ino()));
        assert_eq!(peer_uid(&b), Some(own_uid()));
    }
}
