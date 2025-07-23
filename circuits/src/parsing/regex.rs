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

// This module implements a type of regular expressions. As in `automaton.rs`,
// regex include a notion of markers, that allow to identify some parts of the
// expression by integers (one marker maximum per byte).
//
// The `Regex` type is opaque so that functions outside of this module only use
// the dedicated set of public methods (`RegexInstructions`) to construct
// regular expressions. A method `to_automaton()` is also defined to convert
// them into a finite automata as they are easier to process in circuits.

use std::{collections::HashSet, iter::once};

use super::automaton::{Automaton, RawAutomaton, ALPHABET_MAX_SIZE};

/// A type for formal languages described as regular expressions.
#[derive(Clone, Debug)]
pub struct Regex {
    // The acutal regular expression.
    content: RegexInternal,
    // Marker of the regular expression, with 0 meaning the expession will not output anything. The
    // code will panic when attempting to use nested non-zero values for this field.
    toplevel_marker: usize,
    // Stores all non-zero markers of the regular expression, except the one at toplevel.
    other_markers: HashSet<usize>,
}

#[derive(Clone, Debug)]
enum RegexInternal {
    // A language accepting a word of one arbitrary byte from the range (`Vec`) taken as an
    // argument. Working with ranges instead of single bytes allows to precompute some single-byte
    // operations that weight heavy on the determinisation process.
    Single(Vec<u8>),
    // Concatenation of a vector of languages.
    Concat(Vec<Regex>),
    // Union of a vector of languages.
    Union(Vec<Regex>),
    // Intersection of a vector of languages. Similarly as for `automaton::inter`, letters with
    // different markers are always treated as different letters, except when one of the markers
    // is 0 (in which case they are unified into the non-zero marker).
    Inter(Vec<Regex>),
    // Iteration of a given language (including the empty word for 0 iteration). The boolean
    // indicates whether the iteration is strict, that is, the boolean being true means that the
    // empty word is not accepted.
    Star(bool, Box<Regex>),
    // Complement of a language. The code enforces that its argument does not contain markers
    // (panics if attempted to put any).
    Complement(Box<Regex>),
}

// Conversion from the internal representation of a regex to an actual one,
// without marker at toplevel. The `other_marker` field is computed consistently
// with the internal data.
impl From<RegexInternal> for Regex {
    fn from(value: RegexInternal) -> Self {
        let mut other_markers = HashSet::new();
        match &value {
            RegexInternal::Single(_) => (),
            RegexInternal::Concat(l) | RegexInternal::Union(l) | RegexInternal::Inter(l) => l
                .iter()
                .for_each(|r| other_markers.extend(&r.other_markers)),
            RegexInternal::Star(_, r) | RegexInternal::Complement(r) => {
                other_markers.extend(&r.other_markers)
            }
        };
        Regex {
            content: value,
            toplevel_marker: 0,
            other_markers,
        }
    }
}

/// Public instructions that can be used to build a regular expression. Other
/// functions will require that the constructed expressions are
/// output-deterministic, i.e., that each word matching a given regex can only
/// be marked in a unique way.
pub trait RegexInstructions
where
    Self: Sized + Clone,
{
    /// Updates all markers appearing on bytes satisfying the predicate `pred`
    /// to the new value `marker`. If `pred` is always true and `self` is not
    /// already marked, it is more efficient to call `add_marker`.
    fn update_markers_when(&self, pred: &impl Fn(u8) -> bool, marker: usize) -> Self;

    /// Analogue of `update_markers_when`, but uses a slice of bytes rather than
    /// a predicate.
    fn update_markers_on(&self, bytes: &[u8], marker: usize) -> Self {
        self.update_markers_when(&|b| bytes.contains(&b), marker)
    }

    /// Marks all bytes from an unmarked regular expression with `marker`.
    /// Panics if `marker == 0`, or if any prior marker exists in `self`. In
    /// exchange, is more efficient than `update_markers_when` for this specific
    /// task.
    fn add_marker(self, marker: usize) -> Self;

    /// Removes all markers from `self`. More efficient than
    /// `update_markers_when` for this specific task.
    fn remove_markers(&self) -> Self;

    /// A regular expression matching any single unmarked byte from a
    /// collection.
    fn byte_from(l: impl IntoIterator<Item = u8>) -> Self;

    /// The complement of a regular expression, that is, it characterises any
    /// sequence of bytes that does not match the regular expression. Fails if
    /// any marker is under an odd number of negations.
    fn neg(self) -> Self;

    /// Union of the languages of a finite sequence of regular expressions.
    /// Yields the empty language for empty iterators.
    ///
    /// Note: Avoid using this method (and `Self::and`) when alternatives exist,
    /// such as `Self::byte_from`. This method is generic and tends to create a
    /// large number of additional states which are costly to handle during the
    /// (exponential) determinisation process.
    fn union<S: IntoIterator<Item = Self>>(l: S) -> Self;

    /// Intersection of the languages of a finite sequence of regular
    /// expressions. Yields the universal language for empty iterators.
    ///
    /// Two identical bytes with different markers are considered different when
    /// intersecting, except when one of the two markers is 0 (in which case
    /// the intersection yields the letter with the non-zero marker).
    fn inter<S: IntoIterator<Item = Self>>(l: S) -> Self;

    /// Extension of `Regex::terminated` to the concatenation of a finite
    /// sequence of regular expressions. Yields the empty word
    /// (`Self::epsilon`) for empty iterators.
    fn cat<S: IntoIterator<Item = Self>>(l: S) -> Self;

    /// Matches any number of successive copies (0 or more) of a regular
    /// expression.
    fn list(self) -> Self;

    /// Regular expression matching the empty string.
    fn epsilon() -> Self {
        Self::cat([])
    }

    /// Matches any positive number of successive copies (1 or more) of a
    /// regular expression.
    fn non_empty_list(self) -> Self;

    /// A regular expression consisting of a single, arbitrary, and unmarked
    /// byte.
    fn any_byte() -> Self {
        Self::byte_from(0..=(ALPHABET_MAX_SIZE - 1) as u8)
    }

    /// Concatenates `other` after `self`. This is the binary version of
    /// `Self::cat`.
    fn terminated(self, other: Self) -> Self {
        Self::cat([self, other])
    }

    /// Union of the two languages represented by `self` and `other`. This is
    /// the binary version of `Self::union` and has the same limitations.
    fn or(self, other: Self) -> Self {
        Self::union([self, other])
    }

    /// Intersection of the two languages represented by `self` and `other`.
    /// This is the binary version of `Self::inter` and has the same
    /// behaviour regarding the intersection of marked strings.
    fn and(self, other: Self) -> Self {
        Self::inter([self, other])
    }

    /// A regular expression accepting any unmarked string. This is equivalent
    /// to `Self::any_byte().list()`, but more efficient to process.
    fn any() -> Self {
        Self::inter([])
    }

    /// Accepts any word accepted by `self` but not `other`. Is equivalent to
    /// `and([self, other.neg()])`, in particular regarding markers being
    /// forbidden in `other`, and markers of `self` not being erased because of
    /// the absence of markers in `other`.
    fn minus(self, other: Self) -> Self {
        self.and(other.neg())
    }

    /// Regular expression matching a single string.
    fn word(word: &str) -> Self {
        Self::cat(word.bytes().map(|b| Self::byte_from([b])))
    }

    /// Regular expression matching any digit (['0'..'9']).
    fn digit() -> Self {
        Self::byte_from(b'0'..=b'9')
    }

    /// Regular expression matching any lowercase letter (['a'..'z']).
    fn lowercase_letter() -> Self {
        Self::byte_from(b'a'..=b'z')
    }

    /// Regular expression matching any uppercase letter (['A'..'Z']).
    fn uppercase_letter() -> Self {
        Self::byte_from(b'A'..=b'Z')
    }

    /// Regular expression matching any letter (['a'..'z' 'A'..'Z']).
    fn letter() -> Self {
        Self::byte_from((b'a'..=b'z').chain(b'A'..=b'Z'))
    }

    /// Regular expression matching any alphanumeric character (['a'..'z'
    /// 'A'..'Z' '0'..'9']).
    fn alphanumeric() -> Self {
        Self::byte_from((b'a'..=b'z').chain(b'A'..=b'Z').chain(b'0'..=b'9'))
    }

    /// A blank character (space, newline, or tab).
    fn one_blank() -> Self {
        Self::byte_from(*b" \t\n")
    }

    /// Regular expression matching any sequence of 1 or more spaces.
    fn blanks_strict() -> Self {
        Self::one_blank().non_empty_list()
    }

    /// Regular expression matching any sequence of 0 or more spaces.
    fn blanks() -> Self {
        Self::one_blank().list()
    }

    /// Regular expression accepting any word of `self` and the empty string.
    fn optional(self) -> Self {
        self.or(Self::epsilon())
    }

    /// Regular expression matching `self` surrounded by two delimiters `op` and
    /// `cl`.
    fn delimited(self, opening: Self, closing: Self) -> Self {
        Self::cat([opening, self, closing])
    }

    /// Similar to `self.non_empty_list`, except that two consecutive
    /// occurrences of `self` are separated by the separator `sep`.
    fn separated_non_empty_list(self, sep: Self) -> Self {
        self.clone().terminated(Self::cat([sep, self]).list())
    }

    /// Similar to `self.list`, except that two consecutive
    /// occurrences of `self` are separated by the separator `sep`.
    fn separated_list(self, sep: Self) -> Self {
        Self::epsilon().or(self.separated_non_empty_list(sep))
    }

    /// Similar to `self::cat`, except that two consecutive
    /// occurrences of `self` are separated by the separator `sep`.
    fn separated_cat<S: IntoIterator<Item = Self>>(l: S, sep: Self) -> Self {
        l.into_iter()
            .reduce(|acc, r| Self::cat([acc, sep.clone(), r]))
            .unwrap_or(Self::epsilon())
    }

    /// Concatenates `self` exactly `n` times.
    fn repeat(self, n: usize) -> Self {
        Self::cat(vec![self; n])
    }

    /// Concatenates `self` between 0 and `n` times (inclusive).
    fn repeat_at_most(self, n: usize) -> Self {
        Self::union((0..=n).map(|i| self.clone().repeat(i)))
    }

    /// Same as `Self::repeat`, but uses `Self::separated_cat` instead of
    /// `Self::cat`.
    fn separated_repeat(self, n: usize, sep: Self) -> Self {
        Self::separated_cat(vec![self; n], sep)
    }

    /// Same as `Self::repeat_at_most`, but uses `Self::separated_cat` instead
    /// of `Self::cat`.
    fn separated_repeat_at_most(self, n: usize, sep: Self) -> Self {
        Self::union((0..=n).map(|i| self.clone().separated_repeat(i, sep.clone())))
    }
}

impl RegexInstructions for Regex {
    fn update_markers_when(&self, pred: &impl Fn(u8) -> bool, marker: usize) -> Self {
        let mut toplevel_marker = self.toplevel_marker;
        // This pattern matching updates the toplevel marker, and computes the field
        // `.content` of the regular expression to return.
        let content = match &self.content {
            // The case of single-letter languages is handled separately to return a simpler regex.
            // Not doing this sends a significantly higher load to the determinisation algorithm, as
            // single-letter ranges would otherwise be translated as automata with a number of
            // states proportional to the range size, which are extremely costly to determinise.
            RegexInternal::Single(range) => {
                if toplevel_marker == marker {
                    // Nothing to do if the new and previous markers are identical.
                    self.content.clone()
                } else {
                    // Otherwise, partition the range according to the `pred` predicate, and return
                    // the union of the two ranges with the corresponding markers.
                    let (pos, neg): (Vec<u8>, Vec<u8>) = range.iter().partition(|a| pred(**a));
                    if pos.is_empty() {
                        self.content.clone()
                    } else if neg.is_empty() {
                        toplevel_marker = marker;
                        RegexInternal::Single(pos)
                    } else {
                        let regex_pos = Regex {
                            content: RegexInternal::Single(pos),
                            toplevel_marker: marker,
                            other_markers: HashSet::new(),
                        };
                        let regex_neg = Regex {
                            content: RegexInternal::Single(neg),
                            toplevel_marker: self.toplevel_marker,
                            other_markers: HashSet::new(),
                        };
                        toplevel_marker = 0;
                        RegexInternal::Union(vec![regex_pos, regex_neg])
                    }
                }
            }
            RegexInternal::Concat(l) => RegexInternal::Concat(
                l.iter()
                    .map(|e| e.update_markers_when(pred, marker))
                    .collect::<Vec<_>>(),
            ),
            RegexInternal::Union(l) => RegexInternal::Union(
                l.iter()
                    .map(|e| e.update_markers_when(pred, marker))
                    .collect::<Vec<_>>(),
            ),
            RegexInternal::Inter(l) => RegexInternal::Inter(
                l.iter()
                    .map(|e| e.update_markers_when(pred, marker))
                    .collect::<Vec<_>>(),
            ),
            RegexInternal::Star(b, r) => {
                RegexInternal::Star(*b, Box::new(r.update_markers_when(pred, marker)))
            }
            RegexInternal::Complement(r) => {
                RegexInternal::Complement(Box::new(r.update_markers_when(pred, marker)))
            }
        };
        let mut regex: Regex = content.into();
        regex.toplevel_marker = toplevel_marker;
        regex
    }

    // All information is carried at toplevel with the fields `toplevel_marker` and
    // `other_markers`. No need to explore the regex recursively like in
    // `update_markers_when`.
    fn add_marker(self, index: usize) -> Self {
        assert!(index != 0, "Regex::add_marker cannot be called with index 0 (because 0 is the convention for no marking).");
        if self.toplevel_marker != 0 || !self.other_markers.is_empty() {
            panic!("Attempted to add the two markers {index} and {} to a part of a regular expression. Nested markers are not allowed.", self.other_markers.iter().chain(once(&self.toplevel_marker)).find(|&&b| b != 0).unwrap())
        } else {
            Self {
                toplevel_marker: index,
                ..self
            }
        }
    }

    fn remove_markers(&self) -> Self {
        match &self.content {
            RegexInternal::Single(_) => self.content.clone(),
            RegexInternal::Concat(l) => {
                RegexInternal::Concat(l.iter().map(|e| e.remove_markers()).collect::<Vec<_>>())
            }
            RegexInternal::Union(l) => {
                RegexInternal::Union(l.iter().map(|e| e.remove_markers()).collect::<Vec<_>>())
            }
            RegexInternal::Inter(l) => {
                RegexInternal::Inter(l.iter().map(|e| e.remove_markers()).collect::<Vec<_>>())
            }
            RegexInternal::Star(b, r) => RegexInternal::Star(*b, Box::new(r.remove_markers())),
            RegexInternal::Complement(r) => RegexInternal::Complement(Box::new(r.remove_markers())),
        }
        .into()
    }

    fn byte_from(l: impl IntoIterator<Item = u8>) -> Self {
        RegexInternal::Single(Vec::from_iter(l)).into()
    }

    fn cat<S: IntoIterator<Item = Self>>(l: S) -> Self {
        RegexInternal::Concat(l.into_iter().collect::<Vec<_>>()).into()
    }

    fn inter<S: IntoIterator<Item = Self>>(l: S) -> Self {
        RegexInternal::Inter(l.into_iter().collect::<Vec<_>>()).into()
    }

    fn union<S: IntoIterator<Item = Self>>(l: S) -> Self {
        RegexInternal::Union(l.into_iter().collect::<Vec<_>>()).into()
    }

    fn neg(self) -> Self {
        match self.content {
            // The first case is simply to reduce the Regex's depth.
            RegexInternal::Complement(e) => *e,
            // The second case additionally checks that `self` contains no markers.
            _ => {
                assert!(
                    self.other_markers.is_empty(),
                    "in regular expressions, markers are not allowed under complement/negation ({:?})", self
                );
                RegexInternal::Complement(Box::new(self)).into()
            }
        }
    }

    fn list(self) -> Self {
        RegexInternal::Star(false, Box::new(self)).into()
    }

    fn non_empty_list(self) -> Self {
        RegexInternal::Star(true, Box::new(self)).into()
    }
}

impl From<String> for Regex {
    fn from(value: String) -> Self {
        Self::word(&value)
    }
}

impl From<&str> for Regex {
    fn from(value: &str) -> Self {
        Self::word(value)
    }
}

impl From<u8> for Regex {
    fn from(value: u8) -> Self {
        Self::byte_from([value])
    }
}

impl From<&u8> for Regex {
    fn from(value: &u8) -> Self {
        Self::byte_from([*value])
    }
}

impl Regex {
    // Straightforward conversion of a regular expression into a non-deterministic
    // automaton, using the constructions provided in the `automaton` module.
    fn to_raw_automaton(&self, alphabet_size: usize) -> RawAutomaton<usize> {
        let automaton = match &self.content {
            RegexInternal::Single(a) => RawAutomaton::singleton(a, alphabet_size),
            RegexInternal::Concat(l) => l.iter().fold(RawAutomaton::epsilon(), |accu, r| {
                accu.concat(&r.to_raw_automaton(alphabet_size))
                    .normalise_states()
            }),
            RegexInternal::Union(l) => l.iter().fold(RawAutomaton::empty(), |accu, r| {
                accu.union(&r.to_raw_automaton(alphabet_size))
                    .normalise_states()
            }),
            RegexInternal::Inter(l) => {
                l.iter()
                    .fold(RawAutomaton::universal(alphabet_size), |accu, r| {
                        let mut r = r.to_raw_automaton(alphabet_size);
                        r.remove_epsilon_transitions();
                        accu.inter(&r).normalise_states()
                    })
            }
            RegexInternal::Star(strict, e) => {
                let mut automaton = e.to_raw_automaton(alphabet_size);
                automaton.repeat(*strict);
                automaton
            }
            RegexInternal::Complement(e) => {
                let mut automaton = e.to_raw_automaton(alphabet_size);
                // This determinisation assumes that when complement are constructed (see
                // `RegexInstructions`), it is ensured that `e` above only contains `0` as a
                // marker.
                automaton.determinise(alphabet_size, &[0]);
                automaton.complement();
                automaton.normalise_states()
            }
        };
        // After the determinisation is finished, add the markers if needed.
        if self.toplevel_marker == 0 {
            automaton
        } else {
            automaton.add_marker(self.toplevel_marker)
        }
    }

    // Converts a regular expression into a state automaton. This function can
    // specify the alphabet size, so that smaller alphabets can be considered for
    // more readable testing purpose. Only the instanciation with `alphabet_size
    // == ALPPHABET_MAX_SIZE` is accessible outside of this module.
    pub(super) fn to_automaton_param(&self, alphabet_size: usize) -> Automaton {
        assert!(alphabet_size <= ALPHABET_MAX_SIZE,"Attempt to generate an automaton with an alphabet of size {alphabet_size}. Letters are represented by bytes, hence the maximal alphabet size is {ALPHABET_MAX_SIZE}");
        self.to_raw_automaton(alphabet_size).normalise()
    }

    /// Converts a regular expression into a state automaton. All states of the
    /// automaton are reachable from the initial state, and can reach a final
    /// state. Being unable to find a transition from a given state upon reading
    /// a given letter means that the word is to be rejected.
    pub fn to_automaton(&self) -> Automaton {
        self.to_automaton_param(ALPHABET_MAX_SIZE)
    }
}

#[cfg(test)]
mod tests {

    use super::{Regex, RegexInstructions};
    use crate::parsing::{automaton, regex::ALPHABET_MAX_SIZE};

    // Tests whether a given regular expression accepts or rejects two sets of
    // corresponding strings. Uses the sub-method used in the `automaton.rs` test
    // module.
    fn regex_one_test(
        index: usize,
        regex: &Regex,
        accepted: &[(&str, &[usize])],
        rejected: &[&str],
    ) {
        let accepted: &[(&[u8], &[usize])] = &accepted
            .iter()
            .map(|(s, output)| (s.as_bytes(), *output))
            .collect::<Vec<_>>();
        let rejected: &[&[u8]] = &rejected.iter().map(|s| s.as_bytes()).collect::<Vec<_>>();
        automaton::tests::automaton_one_test(index, ALPHABET_MAX_SIZE, regex, accepted, rejected);
    }

    #[test]
    fn regex_test() {
        let hello = Regex::word("hello");
        let test = Regex::word("test");
        let lmao = Regex::word("lmao!");

        // hello( )+test( )+lmao!
        let regex0 = Regex::separated_cat(
            [hello.clone(), test.clone(), lmao.clone()],
            Regex::blanks_strict(),
        );

        let accepted0: Vec<(&str, &[usize])> = vec![
            ("hello test lmao!", &[0; 16]),
            ("hello    test    lmao!", &[0; 22]),
            ("hello \t\t test \n \t lmao!", &[0; 23]),
        ];
        let rejected0: Vec<&str> = vec![
            " hello    test    lmao!",
            "hello test lmao! ",
            "hello    test    lmao  !",
            "hellotest    lmao!",
            "hello testlmao!",
            "hello test lmoa!",
            "hello test lmoa!",
            "hello lma0!",
            "goodbye lmao!",
        ];

        // [{(hello)*}{(test)*}], with arbitrary blank characters between all words and
        // delimiters (and at least one space between each word). All lowercase letters
        // are marked as 1.
        fn bracket_list(r: Regex) -> Regex {
            r.separated_list(Regex::blanks_strict())
                .delimited(Regex::blanks(), Regex::blanks())
                .delimited("{".into(), "}".into())
        }

        let regex1 = Regex::separated_cat(
            [
                "[".into(),
                bracket_list(hello.clone()),
                bracket_list(test.clone()),
                "]".into(),
            ],
            Regex::blanks(),
        )
        .update_markers_when(&|b| b.is_ascii_lowercase(), 1);

        let accepted1: Vec<(&str, &[usize])> = vec![
            (
                "[ { hello hello hello } { test test test test } ]",
                &[
                    0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,
                    1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0,
                ],
            ),
            (
                "[ { } { test test test test } ]",
                &[
                    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1,
                    1, 0, 0, 0, 0,
                ],
            ),
            (
                "[ { hello hello hello } { } ]",
                &[
                    0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,
                    0, 0, 0,
                ],
            ),
            (
                "[ { hello      hello   hello } {  test    test test  test   } ]",
                &[
                    0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1,
                    1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0,
                    0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "[ { hello } { test } ]",
                &[
                    0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0,
                ],
            ),
            ("[ { hello}{}]", &[0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0]),
            ("[{}{}]", &[0; 6]),
            (
                "[{hello hello hello}{test test test test}]",
                &[
                    0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0,
                    1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0,
                ],
            ),
        ];
        let rejected1: Vec<&str> = vec![
            "[ { hello hellohello } { test test test } ]",
            "[ { hello hello hello } { test testtest test } ]",
            "[ { hell hello hello } { test test test test } ]",
            "[ { hello } { teste test } ]",
            "[ { { hello hello hello } } { test test test test } ]",
        ];

        // A regex that accepts any string, and outputs its blank spaces with marker 1.
        let regex2 = Regex::any_byte().update_markers_on(b" \n\t", 1).list();

        let accepted2: Vec<(&str, &[usize])> = vec![
            ("", &[]),
            (
                "hello test lmao!",
                &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
            ),
            (
                "hello test lmao!\n",
                &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
            ),
            (
                " hello    test    lmao!",
                &[
                    1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0,
                ],
            ),
            (
                " he\nllo  \n  test  \t  lmao!",
                &[
                    1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "[ { hello hello hello } { test test test test } ]",
                &[
                    0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1,
                    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0,
                ],
            ),
            (
                "[ { hello hellohello } { test test test } ]",
                &[
                    0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
                    0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0,
                ],
            ),
            ("lidhf8*&3@#!$", &[0; 13]),
            (
                "lid\n  \thf8 *&3@ #\t!$",
                &[0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0],
            ),
        ];
        let rejected2: Vec<&str> = vec![];

        // Same as regex2, but outputs spaces, newlines, and tabs with a different
        // marker (1,2,3 respectively).
        let regex3 = Regex::any_byte()
            .update_markers_on(b" ", 1)
            .update_markers_on(b"\n", 2)
            .update_markers_on(b"\t", 3)
            .list();

        let accepted3: Vec<(&str, &[usize])> = vec![
            ("", &[]),
            (
                "hello test lmao!",
                &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
            ),
            (
                "hello test lmao!\n",
                &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2],
            ),
            (
                " hello    test    lmao!",
                &[
                    1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0,
                ],
            ),
            (
                " he\nllo  \n  test  \t  lmao!",
                &[
                    1, 0, 0, 2, 0, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1, 1, 3, 1, 1, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "[ { hello hello hello } { test test test test } ]",
                &[
                    0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1,
                    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0,
                ],
            ),
            (
                "[ { hello hellohello } { test test test } ]",
                &[
                    0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
                    0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0,
                ],
            ),
            ("lidhf8*&3@#!$", &[0; 13]),
            (
                "lid\n  \thf8 *&3@ #\t!$",
                &[0, 0, 0, 2, 1, 1, 3, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 3, 0, 0],
            ),
        ];
        let rejected3: Vec<&str> = vec![];

        // Same as regex0, but outputs all blank characters. Harnesses the semantics of
        // the intersection, which permits to simply intersect regex0 with regex2.
        let regex4 = regex0.clone().and(regex3.clone());

        let accepted4: Vec<(&str, &[usize])> = vec![
            (
                "hello test lmao!",
                &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
            ),
            (
                "hello    test    lmao!",
                &[
                    0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "hello \t\t test \n \t lmao!",
                &[
                    0, 0, 0, 0, 0, 1, 3, 3, 1, 0, 0, 0, 0, 1, 2, 1, 3, 1, 0, 0, 0, 0, 0,
                ],
            ),
        ];
        let rejected4: Vec<&str> = rejected0.clone();

        regex_one_test(0, &regex0, &accepted0, &rejected0);
        regex_one_test(1, &regex1, &accepted1, &rejected1);
        regex_one_test(2, &regex2, &accepted2, &rejected2);
        regex_one_test(3, &regex3, &accepted3, &rejected3);
        regex_one_test(4, &regex4, &accepted4, &rejected4);
    }
}
