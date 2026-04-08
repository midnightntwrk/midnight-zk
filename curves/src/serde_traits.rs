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

//! Serialization traits for curve elements and field elements.

use std::io::{self, Read, Write};

/// Trait for converting raw bytes to/from the internal representation of a
/// type. For example, field elements are represented in Montgomery form and
/// serialized/deserialized without Montgomery reduction.
pub trait SerdeObject: Sized {
    /// The purpose of unchecked functions is to read the internal memory
    /// representation of a type from bytes as quickly as possible. No
    /// sanitization checks are performed to ensure the bytes represent a
    /// valid object. As such this function should only be used internally
    /// as an extension of machine memory. It should not be used to deserialize
    /// externally provided data.
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self;

    /// Read the internal memory representation from bytes.
    /// Returns None if the bytes do not represent a valid object.
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self>;

    /// Convert the internal memory representation to bytes.
    fn to_raw_bytes(&self) -> Vec<u8>;

    /// The purpose of unchecked functions is to read the internal memory
    /// representation of a type from disk as quickly as possible. No
    /// sanitization checks are performed to ensure the bytes represent a
    /// valid object. This function should only be used internally when some
    /// machine state cannot be kept in memory (e.g., between runs)
    /// and needs to be reloaded as quickly as possible.
    fn read_raw_unchecked<R: Read>(reader: &mut R) -> Self;

    /// Read the internal memory representation from a reader.
    fn read_raw<R: Read>(reader: &mut R) -> io::Result<Self>;

    /// Write the internal memory representation to a writer.
    fn write_raw<W: Write>(&self, writer: &mut W) -> io::Result<()>;
}
