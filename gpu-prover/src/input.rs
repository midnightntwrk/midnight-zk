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

//! Request input and proof output files.
//!
//! An input file holds witness data. It is opened once, without following a
//! symbolic link, and the checks run on the opened file: a regular file,
//! owned by the service's user, not readable or writable by group or others,
//! and at most [`MAX_INPUT`] bytes. The bytes come from the same open file,
//! into a buffer that is zeroed when it is dropped.
//!
//! A proof is written owner-only to a new temporary file next to the output
//! path and renamed into place, so a reader never sees a partial proof.

use std::{
    fs::{File, OpenOptions},
    io::{Read, Write},
    os::unix::fs::{MetadataExt, OpenOptionsExt},
    path::{Path, PathBuf},
};

use crate::Error;

/// Largest input file, bytes.
pub const MAX_INPUT: u64 = 1 << 30;

/// Bytes that may hold witness data. Zeroed on drop.
pub struct SecretBytes(Vec<u8>);

impl SecretBytes {
    /// Takes ownership of `v`.
    pub fn new(v: Vec<u8>) -> SecretBytes {
        SecretBytes(v)
    }
    /// The bytes.
    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }
}

impl std::fmt::Debug for SecretBytes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SecretBytes({} bytes)", self.0.len())
    }
}

/// Overwrites `b` with zeros in a way the compiler does not remove.
pub fn wipe(b: &mut [u8]) {
    for x in b.iter_mut() {
        // SAFETY: `x` is a valid, aligned, exclusive reference.
        unsafe { std::ptr::write_volatile(x, 0) };
    }
    std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
}

impl Drop for SecretBytes {
    fn drop(&mut self) {
        let len = self.0.capacity();
        // zero the whole allocation, including spare capacity
        self.0.resize(len, 0);
        wipe(&mut self.0);
    }
}

/// Opens and reads an input file under the rules of this module.
pub fn read_input(path: &Path) -> Result<SecretBytes, Error> {
    let f = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .map_err(|e| Error::Input(format!("cannot open the input file: {}", e.kind())))?;
    check_input(&f)?;
    let len = f.metadata().map_err(|e| Error::Input(e.kind().to_string()))?.len();
    // one buffer of the checked size, never reallocated, so no copy of the
    // bytes is left behind unwiped
    let mut v = SecretBytes::new(vec![0u8; len as usize]);
    let mut f = f;
    f.read_exact(&mut v.0)
        .map_err(|e| Error::Input(format!("cannot read the input file: {}", e.kind())))?;
    let mut extra = [0u8; 1];
    if f.read(&mut extra).map_err(|e| Error::Input(e.kind().to_string()))? != 0 {
        wipe(&mut extra);
        return Err(Error::Input(
            "the input file changed while it was read".into(),
        ));
    }
    Ok(v)
}

/// The checks on an opened input file.
pub fn check_input(f: &File) -> Result<(), Error> {
    let m = f.metadata().map_err(|e| Error::Input(e.kind().to_string()))?;
    if !m.file_type().is_file() {
        return Err(Error::Input("the input is not a regular file".into()));
    }
    if m.uid() != crate::lock::own_uid() {
        return Err(Error::Input(
            "the input file is owned by another user".into(),
        ));
    }
    if m.mode() & 0o077 != 0 {
        return Err(Error::Input(format!(
            "the input file has mode {:o}: group or others may access it; set mode 600",
            m.mode() & 0o777
        )));
    }
    if m.len() > MAX_INPUT {
        return Err(Error::Input(format!("input file above {MAX_INPUT} bytes")));
    }
    Ok(())
}

/// Writes `data` owner-only to `path` through a temporary file in the same
/// directory and a rename.
pub fn write_owner_only(path: &Path, data: &[u8]) -> Result<(), Error> {
    let name = path
        .file_name()
        .ok_or_else(|| Error::Output("the output path has no file name".into()))?;
    let mut tmp_name = std::ffi::OsString::from(".");
    tmp_name.push(name);
    tmp_name.push(format!(".{}.tmp", std::process::id()));
    let tmp: PathBuf = path.with_file_name(tmp_name);
    let res = (|| {
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_CLOEXEC)
            .open(&tmp)?;
        f.write_all(data)?;
        f.sync_all()?;
        std::fs::rename(&tmp, path)
    })();
    if let Err(e) = res {
        let _ = std::fs::remove_file(&tmp);
        return Err(Error::Output(format!(
            "cannot write the output file: {}",
            e.kind()
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::PermissionsExt;

    use super::*;

    #[test]
    fn input_mode_and_kind_are_checked() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("in.bin");
        std::fs::write(&p, b"abc").unwrap();
        std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o644)).unwrap();
        assert!(matches!(read_input(&p), Err(Error::Input(m)) if m.contains("mode 644")));
        std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o640)).unwrap();
        assert!(read_input(&p).is_err());
        std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(read_input(&p).unwrap().as_slice(), b"abc");
        // a symbolic link is not followed
        let l = dir.path().join("link.bin");
        std::os::unix::fs::symlink(&p, &l).unwrap();
        assert!(read_input(&l).is_err());
        // a directory is not an input
        assert!(read_input(dir.path()).is_err());
        // a missing file names no path in the error
        let e = read_input(&dir.path().join("missing")).unwrap_err().to_string();
        assert!(!e.contains("missing"), "{e}");
    }

    #[test]
    fn output_is_owner_only() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("proof.bin");
        write_owner_only(&p, b"proof").unwrap();
        let m = std::fs::metadata(&p).unwrap();
        assert_eq!(m.mode() & 0o777, 0o600);
        assert_eq!(std::fs::read(&p).unwrap(), b"proof");
        // replacing works and leaves no temporary file
        write_owner_only(&p, b"proof2").unwrap();
        assert_eq!(std::fs::read_dir(dir.path()).unwrap().count(), 1);
    }

    #[test]
    fn wipe_zeroes() {
        let mut v = vec![7u8; 64];
        wipe(&mut v);
        assert!(v.iter().all(|b| *b == 0));
    }
}
