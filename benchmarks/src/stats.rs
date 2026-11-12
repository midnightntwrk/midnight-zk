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

//! Summary statistics over timing samples.

/// The summary of a set of samples, in the unit of the samples.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stats {
    /// The median.
    pub median: u64,
    /// The smallest sample.
    pub min: u64,
    /// The largest sample.
    pub max: u64,
    /// The median absolute deviation from the median.
    pub mad: u64,
}

impl Stats {
    /// Summarizes `samples`, or returns `None` if there are none.
    pub fn of(samples: &[u64]) -> Option<Self> {
        let median = median(samples)?;
        let deviations: Vec<u64> = samples.iter().map(|s| s.abs_diff(median)).collect();
        Some(Stats {
            median,
            min: *samples.iter().min()?,
            max: *samples.iter().max()?,
            mad: self::median(&deviations)?,
        })
    }

    /// The median absolute deviation as a percentage of the median.
    pub fn mad_percent(&self) -> f64 {
        if self.median == 0 {
            return 0.0;
        }
        100.0 * self.mad as f64 / self.median as f64
    }
}

/// The median of `samples`, or `None` if there are none. With an even number
/// of samples it is the mean of the two middle ones, rounded down.
pub fn median(samples: &[u64]) -> Option<u64> {
    let mut sorted = samples.to_vec();
    sorted.sort_unstable();
    let mid = sorted.len() / 2;
    match sorted.len() {
        0 => None,
        n if n % 2 == 1 => Some(sorted[mid]),
        _ => {
            let (lo, hi) = (sorted[mid - 1], sorted[mid]);
            Some(lo + (hi - lo) / 2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stats(median: u64, min: u64, max: u64, mad: u64) -> Stats {
        Stats {
            median,
            min,
            max,
            mad,
        }
    }

    #[test]
    fn no_samples() {
        assert_eq!(median(&[]), None);
        assert_eq!(Stats::of(&[]), None);
    }

    #[test]
    fn single_sample() {
        let s = Stats::of(&[42]).unwrap();
        assert_eq!(s, stats(42, 42, 42, 0));
        assert_eq!(s.mad_percent(), 0.0);
    }

    #[test]
    fn odd_number_of_samples() {
        // The deviations from the median 40 are [10, 10, 20, 60, 0].
        let s = Stats::of(&[50, 30, 20, 100, 40]).unwrap();
        assert_eq!(s, stats(40, 20, 100, 10));
        assert_eq!(s.mad_percent(), 25.0);
    }

    #[test]
    fn even_number_of_samples() {
        // The median is (20 + 40) / 2 and the deviations are [20, 10, 10, 70].
        let s = Stats::of(&[10, 40, 20, 100]).unwrap();
        assert_eq!(s, stats(30, 10, 100, 15));
        assert_eq!(s.mad_percent(), 50.0);
    }

    #[test]
    fn median_does_not_overflow() {
        assert_eq!(median(&[u64::MAX, u64::MAX - 2]), Some(u64::MAX - 1));
    }

    #[test]
    fn zero_median_has_no_relative_deviation() {
        assert_eq!(Stats::of(&[0, 0, 5]).unwrap().mad_percent(), 0.0);
    }
}
