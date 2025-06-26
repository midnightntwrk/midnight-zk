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

// This module implements a type of regular expressions, `Regex` similar to
// the usual notion used in, e.g., the grep terminal command. Formally, a
// regular expression recognises a set of strings (seen as sequences of bytes),
// and are defined recursively by the closure of byte singletons by union,
// concatenation, and iteration ("Kleene star").
//
// The `Regex` type is opaque so that functions outside of this module only use
// the dedicated set of public methods (`RegexInstructions`) to construct
// regular expressions. A method `to_automaton()` is also defined to convert
// them into a finite automata as they are easier to process in circuits. This
// conversion is a straightforward traversal of the `Regex`, calling the more
// involved constructions defined in `automaton.rs`.
//
// The module includes a couple of tests on actual strings to test the
// conversion of regex into automata and how they recognise strings.

use super::{
    automaton::{Automaton, RawAutomaton},
    RegexLetter, REGEX_ALPHABET_MAX_SIZE,
};

/// A type for formal languages described as regular expressions.
#[derive(Clone, Debug)]
pub struct Regex {
    content: RegexInternal,
}

#[derive(Clone, Debug)]
enum RegexInternal {
    /// A language accepting a word of length 1. `Single(Some(x))` represents
    /// the singleton language {x}, and `Single(None)` represents the wildcard,
    /// i.e., {x | x of type RegexLetter}.
    Single(Option<RegexLetter>),
    /// Concatenation of a vector of languages.
    Concat(Vec<RegexInternal>),
    /// Union of a vector of languages.
    Union(Vec<RegexInternal>),
    /// Iteration of a given language (including the empty word for 0
    /// iteration). The boolean indicates whether the iteration is strict, that
    /// is, the boolean being true means that the empty word is not accepted.
    Star(bool, Box<RegexInternal>),
    /// Complement of a language.
    Complement(Box<RegexInternal>),
}

impl From<RegexInternal> for Regex {
    fn from(value: RegexInternal) -> Self {
        Regex { content: value }
    }
}

/// Public instructions that can be used to build a regular expression.
pub trait RegexInstructions
where
    Self: Sized + Clone,
{
    /// A regular expression consisting of a unique byte.
    fn once(u: RegexLetter) -> Self;

    /// A regular expression consisting of a unique, arbitrary byte.
    fn once_any() -> Self;

    /// The concatenation of a finite sequence of regular expressions. The empty
    /// sequence yields the empty word, i.e., `Self::epsilon`.
    fn cat<S: IntoIterator<Item = Self>>(l: S) -> Self;

    /// The union of a finite sequence of regular expressions.
    fn or<S: IntoIterator<Item = Self>>(l: S) -> Self;

    /// The complement of a regular expression, that is, it characterises any
    /// Sequence of bytes that does not match the regular expression.
    fn neg(self) -> Self;

    /// Matches any number of successive copies (0 or more) of a regular
    /// expression.
    fn list(self) -> Self;

    /// The intersection of a finite sequence of regular expressions.
    fn and<S: IntoIterator<Item = Self>>(l: S) -> Self {
        Self::or(l.into_iter().map(Self::neg)).neg()
    }

    /// Matches any sequence of bytes that matches `self` but not `other`.
    fn minus(self, other: Self) -> Self {
        Self::and([self, other.neg()])
    }

    /// Regular expression matching a single string.
    fn word(word: &str) -> Self {
        Self::cat(word.bytes().map(Self::once))
    }

    /// Regular expression matching the empty string.
    fn epsilon() -> Self {
        Self::word("")
    }

    /// Regular expression matching `{`.
    fn lbracket() -> Self {
        Self::word("{")
    }

    /// Regular expression matching `}`.
    fn rbracket() -> Self {
        Self::word("}")
    }

    /// Regular expression matching `[`.
    fn lsqbracket() -> Self {
        Self::word("[")
    }

    /// Regular expression matching `]`.
    fn rsqbracket() -> Self {
        Self::word("]")
    }

    /// Regular expression matching `(`.
    fn lparen() -> Self {
        Self::word("(")
    }

    /// Regular expression matching `)`.
    fn rparen() -> Self {
        Self::word(")")
    }

    /// Regular expression matching `"`.
    fn double_quote() -> Self {
        Self::word("\"")
    }

    /// Regular expression matching `'`.
    fn single_quote() -> Self {
        Self::word("'")
    }

    /// Regular expression matching `,`.
    fn comma() -> Self {
        Self::word(",")
    }

    /// Regular expression matching `:`.
    fn colon() -> Self {
        Self::word(":")
    }

    /// Regular expression matching `;`.
    fn semicolon() -> Self {
        Self::word(";")
    }

    /// Regular expression matching `_`.
    fn underscore() -> Self {
        Self::word("_")
    }

    /// Regular expression matching any digit (['0'..'9']).
    fn digit() -> Self {
        Self::or((0..9).map(|n| Self::word(&n.to_string())))
    }

    /// Regular expression matching any lowercase letter (['a'..'z']).
    fn lowercase_letter() -> Self {
        Self::or(('a'..='z').map(|n| Self::word(&n.to_string())))
    }

    /// Regular expression matching any uppercase letter (['A'..'Z']).
    fn uppercase_letter() -> Self {
        Self::or(('A'..='Z').map(|n| Self::word(&n.to_string())))
    }

    /// Regular expression matching any letter (['a'..'z' 'A'..'Z']).
    fn letter() -> Self {
        Self::or([Self::lowercase_letter(), Self::uppercase_letter()])
    }

    /// Regular expression matching any alphanumeric character (['a'..'z'
    /// 'A'..'Z' '0'..'9']).
    fn alphanumeric() -> Self {
        Self::or([
            Self::lowercase_letter(),
            Self::uppercase_letter(),
            Self::digit(),
        ])
    }

    /// Regular expression recognising `self` or the empty string.
    fn optional(self) -> Self {
        Self::or([self, Self::epsilon()])
    }

    /// Matches any positive number of successive copies (1 or more) of a
    /// regular expression.
    fn non_empty_list(self) -> Self {
        self.list().minus(Self::epsilon())
    }

    /// Regular expression matching the space character ` `.
    fn one_space() -> Self {
        Self::word(" ")
    }

    /// Regular expression matching any sequence of 1 or more spaces.
    fn spaces_strict() -> Self {
        Self::one_space().non_empty_list()
    }

    /// Regular expression matching any sequence of 0 or more spaces.
    fn spaces() -> Self {
        Self::one_space().list()
    }

    /// Regular expression matching `self` surrounded by two delimiters `op` and
    /// `cl`. Additionally, any number of spaces (0 or more) may appear between
    /// `op` and `self`, and between `self` and `cl`.
    fn delimited(self, opening: Self, closing: Self) -> Self {
        Self::cat([opening, Self::spaces(), self, Self::spaces(), closing])
    }

    /// Similar to `self.non_empty_list`, except that two consecutive
    /// occurrences of `self` are separated by an arbitrary number of spaces (0
    /// or more), the separator `sep`, and again another arbitrary number of
    /// spaces.
    fn separated_non_empty_list(self, sep: Self) -> Self {
        Self::cat([
            self.clone(),
            Self::list(Self::cat([Self::spaces(), sep, Self::spaces(), self])),
        ])
    }

    /// Similar to `self.list`, except that two consecutive
    /// occurrences of `self` are separated by an arbitrary number of spaces (0
    /// or more), the separator `sep`, and again another arbitrary number of
    /// spaces.
    fn separated_list(self, sep: Self) -> Self {
        Self::or([Self::epsilon(), self.separated_non_empty_list(sep)])
    }

    /// Concatenates two regular expressions: puts `self`, then an arbitrary
    /// number of spaces (0 or more), followed by the separator `sep`, again
    /// another arbitrary number of spaces, and `other`.
    fn separated(self, sep: Self, other: Self) -> Self {
        Self::cat([self, Self::spaces(), sep, Self::spaces(), other])
    }

    /// Similar to `self.cat`, except that two consecutive
    /// occurrences of `self` are separated by an arbitrary number of spaces (0
    /// or more), the separator `sep`, and again another arbitrary number of
    /// spaces.
    fn separated_cat<S: IntoIterator<Item = Self>>(l: S, sep: Self) -> Self {
        l.into_iter()
            .reduce(|acc, r| acc.separated(sep.clone(), r))
            .unwrap_or(Self::epsilon())
    }

    /// Concatenates `other` after `self`. This has the same behaviour as
    /// `Self::cat` for iterators of length 2.
    fn terminated(self, other: Self) -> Self {
        Self::cat([self, other])
    }

    /// Concatenates `self` exactly `n` times.
    fn repeat(self, n: usize) -> Self {
        Self::cat(vec![self; n])
    }

    /// Concatenates `self` between 0 and `n` times (inclusive).
    fn repeat_at_most(self, n: usize) -> Self {
        Self::or((0..=n).map(|i| self.clone().repeat(i)))
    }

    /// Same as `repeat`, but uses `separated_cat` instead of `cat`.
    fn separated_repeat(self, n: usize, sep: Self) -> Self {
        Self::separated_cat(vec![self; n], sep)
    }

    /// Same as `repeat_at_most`, but uses `separated_cat` instead of `cat`.
    fn separated_repeat_at_most(self, n: usize, sep: Self) -> Self {
        Self::or((0..=n).map(|i| self.clone().separated_repeat(i, sep.clone())))
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

impl RegexInstructions for Regex {
    fn once(u: RegexLetter) -> Self {
        RegexInternal::Single(Some(u)).into()
    }
    fn once_any() -> Self {
        RegexInternal::Single(None).into()
    }
    fn cat<S: IntoIterator<Item = Self>>(l: S) -> Self {
        RegexInternal::Concat(l.into_iter().map(|r| r.content).collect::<Vec<_>>()).into()
    }
    fn or<S: IntoIterator<Item = Self>>(l: S) -> Self {
        RegexInternal::Union(l.into_iter().map(|r| r.content).collect::<Vec<_>>()).into()
    }
    fn neg(self) -> Self {
        match self.content {
            // The first case is simply to reduce the Regex's depth.
            RegexInternal::Complement(e) => (*e).into(),
            _ => RegexInternal::Complement(Box::new(self.content)).into(),
        }
    }
    fn list(self) -> Self {
        RegexInternal::Star(false, Box::new(self.content)).into()
    }
    fn non_empty_list(self) -> Self {
        RegexInternal::Star(true, Box::new(self.content)).into()
    }
}

impl Regex {
    // Straightforward conversion of a regular expression into a non-deterministic
    // automaton, using the constructions provided in the `automaton` module.
    fn to_raw_automaton(&self, alphabet_size: usize) -> RawAutomaton<usize> {
        match self.content.clone() {
            RegexInternal::Single(a) => {
                assert!(a.iter().all(|&b| (b as usize) < alphabet_size), "conversion from regular expression to automaton uses inconsistent alphabet data");
                RawAutomaton::singleton(a, alphabet_size)
            }
            RegexInternal::Concat(l) => l.iter().fold(RawAutomaton::epsilon(), |automaton, e| {
                let e: Self = e.clone().into();
                automaton
                    .concat(&e.to_raw_automaton(alphabet_size))
                    .normalise_states()
            }),
            RegexInternal::Union(l) => l.iter().fold(RawAutomaton::empty(), |automaton, e| {
                let e: Self = e.clone().into();
                automaton
                    .union(&e.to_raw_automaton(alphabet_size))
                    .normalise_states()
            }),
            RegexInternal::Star(strict, e) => {
                let e: Self = (*e).into();
                let mut automaton = e.to_raw_automaton(alphabet_size);
                automaton.repeat(strict);
                automaton
            }
            RegexInternal::Complement(e) => {
                let e: Self = (*e).into();
                let mut automaton = e.to_raw_automaton(alphabet_size);
                automaton.determinise(alphabet_size);
                automaton.complement();
                automaton
            }
        }
    }

    // Converts a regular expression into a state automaton. All states of the
    // automaton are reachable from the initial state, and can reach a final
    // state. Being unable to find a transition from a given state upon reading
    // a given letter means that the word is to be rejected.
    //
    // Note: this function can specify the alphabet size, so that smaller alphabets
    // can be considered for more readable testing purpose. Only the instanciation
    // with `alphabet_size == ALPPHABET_MAX_SIZE` is accessible outside of this
    // module.
    pub(super) fn to_automaton_param(&self, alphabet_size: usize) -> Automaton {
        if alphabet_size > REGEX_ALPHABET_MAX_SIZE {
            panic!("Attempt to generate an automaton with an alphabet of size {alphabet_size}. Letters are represented by bytes, hence the maximal alphabet size is {REGEX_ALPHABET_MAX_SIZE}")
        }
        self.to_raw_automaton(alphabet_size)
            .normalise(alphabet_size)
    }

    /// Converts a regular expression into a state automaton. All states of the
    /// automaton are reachable from the initial state, and can reach a final
    /// state. Being unable to find a transition from a given state upon reading
    /// a given letter means that the word is to be rejected.
    pub fn to_automaton(&self) -> Automaton {
        self.to_automaton_param(REGEX_ALPHABET_MAX_SIZE)
    }
}

#[cfg(test)]
mod tests {

    use super::{Regex, RegexInstructions};
    use crate::json::{automaton, regex::REGEX_ALPHABET_MAX_SIZE};

    // Tests whether a given regular expression accepts or rejects two sets of
    // corresponding strings. Uses the sub-method used in the `automaton.rs` test
    // module.
    fn regex_one_test(index: usize, regex: &Regex, accepted: &[&str], rejected: &[&str]) {
        println!("\n>> Testing the regex:\n{:?}", regex);
        let accepted: &[&[u8]] = &accepted.iter().map(|s| s.as_bytes()).collect::<Vec<_>>();
        let rejected: &[&[u8]] = &rejected.iter().map(|s| s.as_bytes()).collect::<Vec<_>>();
        automaton::tests::automaton_one_test(
            index,
            REGEX_ALPHABET_MAX_SIZE,
            regex,
            accepted,
            rejected,
        );
    }

    #[test]
    fn regex_test() {
        let hello = Regex::word("hello");
        let test = Regex::word("test");
        let lmao = Regex::word("lmao!");

        // hello( )+test( )+lmao!
        let regex1 = Regex::separated_cat(
            [hello.clone(), test.clone(), lmao.clone()],
            Regex::one_space(),
        );

        // [{(hello)*}{(test)*}], with arbitrary spaces between all words and
        // delimiters (and at least one space between each word).
        fn bracket_list(r: Regex) -> Regex {
            r.separated_list(Regex::one_space())
                .delimited(Regex::lbracket(), Regex::rbracket())
        }
        let regex2 = bracket_list(hello.clone())
            .separated(Regex::spaces(), bracket_list(test.clone()))
            .delimited(Regex::lsqbracket(), Regex::rsqbracket());

        let accepted1: Vec<&str> = vec!["hello test lmao!", "hello    test    lmao!"];
        let rejected1: Vec<&str> = vec![
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
        let accepted2: Vec<&str> = vec![
            "[ { hello hello hello } { test test test test } ]",
            "[ { } { test test test test } ]",
            "[ { hello hello hello } { } ]",
            "[ { hello      hello   hello } {  test    test test  test   } ]",
            "[ { hello } { test } ]",
            "[ { hello}{}]",
            "[{}{}]",
            "[{hello hello hello}{test test test test}]",
        ];
        let rejected2: Vec<&str> = vec![
            "[ { hello hellohello } { test test test } ]",
            "[ { hello hello hello } { test testtest test } ]",
            "[ { hell hello hello } { test test test test } ]",
            "[ { hello } { teste test } ]",
            "[ { { hello hello hello } } { test test test test } ]",
        ];

        regex_one_test(0, &regex1, &accepted1, &rejected1);
        regex_one_test(1, &regex2, &accepted2, &rejected2);
    }
}
