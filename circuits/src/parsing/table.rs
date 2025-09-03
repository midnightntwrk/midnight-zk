// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

use std::collections::HashMap;

use lazy_static::lazy_static;

lazy_static! {
    static ref BASE64_MAP: HashMap<char, u8> = {
        let mut m = HashMap::new();
        BASE64_TABLE.iter().for_each(|(k, v)| {
            m.insert(*k, *v);
        });
        m
    };
}

// The base64 alphabet, from:
// <https://datatracker.ietf.org/doc/html/rfc4648#section-4>
pub(super) const BASE64_TABLE: [(char, u8); 64] = [
    ('A', 0),
    ('B', 1),
    ('C', 2),
    ('D', 3),
    ('E', 4),
    ('F', 5),
    ('G', 6),
    ('H', 7),
    ('I', 8),
    ('J', 9),
    ('K', 10),
    ('L', 11),
    ('M', 12),
    ('N', 13),
    ('O', 14),
    ('P', 15),
    ('Q', 16),
    ('R', 17),
    ('S', 18),
    ('T', 19),
    ('U', 20),
    ('V', 21),
    ('W', 22),
    ('X', 23),
    ('Y', 24),
    ('Z', 25),
    ('a', 26),
    ('b', 27),
    ('c', 28),
    ('d', 29),
    ('e', 30),
    ('f', 31),
    ('g', 32),
    ('h', 33),
    ('i', 34),
    ('j', 35),
    ('k', 36),
    ('l', 37),
    ('m', 38),
    ('n', 39),
    ('o', 40),
    ('p', 41),
    ('q', 42),
    ('r', 43),
    ('s', 44),
    ('t', 45),
    ('u', 46),
    ('v', 47),
    ('w', 48),
    ('x', 49),
    ('y', 50),
    ('z', 51),
    ('0', 52),
    ('1', 53),
    ('2', 54),
    ('3', 55),
    ('4', 56),
    ('5', 57),
    ('6', 58),
    ('7', 59),
    ('8', 60),
    ('9', 61),
    ('+', 62),
    ('/', 63),
    // ( =, pad)
];

/// Based on the original table [`BASE64_TABLE`], this function
/// returns a new table (as a vector of tuples) that instead of
/// matching 1 base64 character to 1 value, matches 2 base64 combined
/// characgters to their combinded value.
///
/// This function is meant to generate a table that allows the
/// lookup of 2 base64 characters.
///
/// The combination of 2 characters is represented by a 16 bit value
/// corresponding to the concatenation of their ascii values. This is computed
/// by shifting the first character 8 bits to the left, then adding the second
/// character. The value of the combination is computed in analogous fashion,
/// but with a 6 bit shift, since the values are in the [0, 64) range.
pub(super) fn two_entry_table() -> Vec<(u16, u16)> {
    let len = BASE64_TABLE.len();
    let mut ret = vec![(0u16, 0u16); len * len];
    for (i, (char_1, val_1)) in BASE64_TABLE.iter().enumerate() {
        for (j, (char_2, val_2)) in BASE64_TABLE.iter().enumerate() {
            let char = ((*char_1 as u16) << 8) ^ (*char_2 as u16);
            let val = ((*val_1 as u16) << 6) ^ (*val_2 as u16);
            ret[i * len + j] = (char, val)
        }
    }
    ret
}

/// Returns the default element of the first column of the table.
/// This must be the element corresponding to the 0 value in the second column.
/// It is used when the lookup is disabled.
pub(super) fn two_entry_default() -> u64 {
    (('A' as u64) << 8) ^ ('A' as u64)
}

/// Decodes a single b64 character into its u8 value.
pub(super) fn decode_char(input: char) -> u8 {
    *BASE64_MAP.get(&input).expect("Valid base64 character.")
}
