/// Structure corresponding to [u64; N]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct U64Words<const N: usize>([u64; N]);

/// Structure corresponding to [u64; 2*N]
/// If nightly features were allowed, we could use the following alias:
///     pub(crate) struct U64Double<const N: usize>([u64; 2*N]);
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct U64Double<const N: usize> {
    low: U64Words<N>,
    high: U64Words<N>,
}

/// Function taking as input three u64 numbers and returning the sum of them as
/// u64, as well as the carry encoded as u64.
const fn add64_with_carry(a: u64, b: u64, carry_in: u64) -> (u64, u64) {
    let (sum1, overflow1) = a.overflowing_add(b);
    let (sum2, overflow2) = sum1.overflowing_add(carry_in);
    let carry_out = (overflow1 as u64) + (overflow2 as u64);
    (sum2, carry_out)
}

/// Function taking as input three u64 numbers and returning the difference of
/// them as u64, as well as the any borrowed value if needed encoded as u64.
const fn sub64_with_overflow(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let (diff1, overflow1) = a.overflowing_sub(b);
    let (diff2, overflow2) = diff1.overflowing_sub(borrow);
    let borrow_out = (overflow1 as u64) + (overflow2 as u64);
    (diff2, borrow_out)
}

impl<const N: usize> U64Double<N> {
    /// Takes as input a u64 slice and returns a U64Double<N>.
    #[allow(dead_code)]
    pub(crate) const fn from(val: &[u64]) -> Self {
        assert!(val.len() == 2 * N);
        let mut low = [0; N];
        let mut high = [0; N];
        let mut i = 0;
        while i < N {
            low[i] = val[i];
            high[i] = val[N + i];
            i += 1;
        }
        Self {
            low: U64Words::<N>::from(low),
            high: U64Words::<N>::from(high),
        }
    }

    /// Takes as input a U64Words<N> and returns a U64Double<N>.
    pub(crate) const fn from_u64words(low: &U64Words<N>) -> Self {
        let high = U64Words::<N>::zero();
        let mut buffer_low = U64Words::<N>::zero();
        let mut i = 0;
        while i < N {
            buffer_low.0[i] = low.0[i];
            i += 1;
        }
        Self {
            low: buffer_low,
            high,
        }
    }

    /// Return a copy of a U64Double<N>.
    pub(crate) const fn copy(&self) -> Self {
        let mut buffer_low = U64Words::<N>::zero();
        let mut buffer_high = U64Words::<N>::zero();
        let mut i = 0;
        while i < N {
            buffer_low.0[i] = self.low.0[i];
            buffer_high.0[i] = self.high.0[i];
            i += 1;
        }
        Self {
            low: buffer_low,
            high: buffer_high,
        }
    }

    /// Return the zero value of U64Double<N> type.
    pub(crate) const fn zero() -> Self {
        Self {
            low: U64Words::<N>::zero(),
            high: U64Words::<N>::zero(),
        }
    }

    /// Return the maximum value of U64Double<N> type.
    #[allow(dead_code)]
    pub(crate) const fn max() -> Self {
        Self {
            low: U64Words::<N>::max(),
            high: U64Words::<N>::max(),
        }
    }

    /// Return the size in bits of a U64Double<N> as usize.
    pub(crate) const fn size_in_bits(&self) -> usize {
        let mut i = N;
        while i > 0 {
            if self.high.0[i - 1] != 0 {
                return 64 * (N + i) - self.high.0[i - 1].leading_zeros() as usize;
            }
            i -= 1;
        }
        i = N;
        while i > 0 {
            if self.low.0[i - 1] != 0 {
                return 64 * i - self.low.0[i - 1].leading_zeros() as usize;
            }
            i -= 1;
        }
        0
    }

    /// Return the u64 value stored at index `index` of a U64Double<N>
    /// when represented as a [u64, 2*N].
    pub(crate) const fn get(&self, index: usize) -> u64 {
        assert!(index < 2 * N);
        if index < N {
            return self.low.0[index];
        }
        self.high.0[index - N]
    }

    /// Modifying the u64 value stored at index `index` of a U64Double<N>
    /// when represented as a [u64, 2*N].
    pub(crate) const fn modify(&mut self, value: u64, index: usize) {
        assert!(index < 2 * N);
        if index < N {
            self.low.0[index] = value;
        } else {
            self.high.0[index - N] = value;
        }
    }

    /// Return self * 2^shift
    pub(crate) const fn pow2(&self, shift: usize) -> Self {
        let mut result = Self::zero();
        let shift_word = shift / 64;
        let shift_bit = shift % 64;

        let mut i = 0;
        while i < 2 * N {
            // Shift within bounds
            if i + shift_word < 2 * N {
                let value = result.get(shift_word + i) | (self.get(i) << shift_bit);
                result.modify(value, shift_word + i);
            }
            // Shift to carry to the next word
            if shift_bit != 0 && shift_word + i + 1 < 2 * N {
                let value = result.get(shift_word + i + 1) | (self.get(i) >> (64 - shift_bit));
                result.modify(value, shift_word + i + 1);
            }
            i += 1;
        }
        result
    }

    /// Return:
    /// - the value -1 when self < b
    /// - the value 0 when self == b
    /// - the value 1 when self > b
    pub(crate) const fn cmp(&self, b: &Self) -> i32 {
        let cmp_high = self.high.cmp(&b.high);
        if cmp_high == 0 {
            return self.low.cmp(&b.low);
        }
        cmp_high
    }

    /// Return the addition of two U64Double<N> as well as the carry
    /// If carry > 0, this means the addition overflowed
    #[allow(dead_code)]
    pub(crate) const fn add(&self, b: &Self) -> (Self, u64) {
        let (sum_low, carry_low) = self.low.add(&b.low);
        let (sum_high, carry) = self.high.add_with_carry(&b.high, carry_low);
        (
            Self {
                low: sum_low,
                high: sum_high,
            },
            carry,
        )
    }

    /// Return the difference of two U64Double<N> as well as the borrow
    /// If borrow > 0, this means that |a - b| > 2^(2*N)
    pub(crate) const fn sub(&self, b: &Self) -> (Self, u64) {
        let (diff_low, borrow_low) = self.low.sub(&b.low);
        let (diff_high, borrow) = self.high.sub_with_borrow(&b.high, borrow_low);
        (
            Self {
                low: diff_low,
                high: diff_high,
            },
            borrow,
        )
    }

    /// Return the output of n % d as a U64Words<N> when d is a U64Words<N> and
    /// n is a U64Double<N>.
    /// This function is useful when doing the modulo operation on the
    /// the multiplication of two numbers.
    pub(crate) const fn modulo_half(&self, d: &U64Words<N>) -> U64Words<N> {
        let mut result = self.copy();
        let mut size_result = result.size_in_bits();

        let size_modulus = d.size_in_bits();
        let modulus_double = Self::from_u64words(d);

        let size_words = 64 * N;
        while size_result > size_words {
            let diff_size = size_result - size_modulus;

            // If result is i bit longer than modulus, with i > 0,
            // we attempt to remove modulus*2**i to result, othewise modulus.
            // If result already is smaller than modulus, return modulus.
            let mut shifted_modulus = modulus_double.pow2(diff_size);
            // If modulus*2**i > result, we remove instead modulus * 2**{i-1} or modulus
            if shifted_modulus.cmp(&result) == 1 {
                if diff_size > 1 {
                    shifted_modulus = modulus_double.pow2(diff_size - 1);
                } else {
                    shifted_modulus = modulus_double.copy();
                }
            }
            let (diff, _) = result.sub(&shifted_modulus);
            result = diff;
            size_result = result.size_in_bits();
        }

        // As `result` fits in a U64Words::<N>, we finish the modulo using `modulo`
        result.low.modulo(d)
    }
}

impl<const N: usize> U64Words<N> {
    /// Cast a [u64; N] as a U64Words<N>
    pub(crate) const fn from(val: [u64; N]) -> Self {
        Self(val)
    }

    /// Cast a u64 as a U64Words<N>
    #[allow(dead_code)]
    pub(crate) const fn from_u64(val: u64) -> Self {
        let mut buffer = [0; N];
        buffer[0] = val;
        Self(buffer)
    }

    /// Return a copy of a U64Words<N>
    pub(crate) const fn copy(&self) -> Self {
        let mut buffer = Self::zero();
        let mut i = 0;
        while i < N {
            buffer.0[i] = self.0[i];
            i += 1;
        }
        buffer
    }

    /// Return the zero value of U64Words<N> type
    pub(crate) const fn zero() -> Self {
        Self([0; N])
    }

    /// Return the max value of U64Words<N> type
    pub(crate) const fn max() -> Self {
        Self([u64::MAX; N])
    }

    /// Return a U64Words<N> as a slice
    #[allow(dead_code)]
    pub(crate) const fn as_slice(&self) -> &[u64] {
        &self.0
    }

    /// Return the value stored in a U64Words<N>
    pub(crate) const fn value(&self) -> [u64; N] {
        self.0
    }

    /// Return the size in bits of a U64Words<N> as usize.
    pub(crate) const fn size_in_bits(&self) -> usize {
        let mut i = N;
        while i > 0 {
            if self.0[i - 1] != 0 {
                return 64 * i - self.0[i - 1].leading_zeros() as usize;
            }
            i -= 1;
        }
        0
    }

    /// Return self * 2^shift
    pub(crate) const fn pow2(&self, shift: usize) -> Self {
        let mut result = Self::zero();
        let shift_word = shift / 64;
        let shift_bit = shift % 64;

        let mut i = 0;
        while i < N {
            // Shift within bounds
            if i + shift_word < N {
                result.0[shift_word + i] |= self.0[i] << shift_bit;
            }
            // Shift to carry to the next word
            if shift_bit != 0 && shift_word + i + 1 < N {
                result.0[shift_word + i + 1] |= self.0[i] >> (64 - shift_bit);
            }
            i += 1;
        }
        result
    }

    /// Return:
    /// - the value -1 when self < b
    /// - the value 0 when self == b
    /// - the value 1 when self > b
    pub(crate) const fn cmp(&self, b: &Self) -> i32 {
        let mut i = N;
        while i > 0 {
            i -= 1;
            if self.0[i] < b.0[i] {
                return -1;
            }
            if self.0[i] > b.0[i] {
                return 1;
            }
        }
        0
    }

    // Return the addition of two U64Double<N> and a u64 as well as the carry
    /// If carry > 0, this means the addition overflowed
    pub(crate) const fn add_with_carry(&self, b: &Self, carry_in: u64) -> (Self, u64) {
        let mut result = Self::zero();
        let mut carry: u64 = carry_in;

        let mut i = 0;
        while i < N {
            let (sum, carry_out) = add64_with_carry(self.0[i], b.0[i], carry);
            result.0[i] = sum;
            carry = carry_out;
            i += 1;
        }

        (result, carry)
    }

    /// Return the addition of two U64Double<N> as well as the carry
    /// If carry > 0, this means the addition overflowed
    pub(crate) const fn add(&self, b: &Self) -> (Self, u64) {
        self.add_with_carry(b, 0u64)
    }

    /// Return the difference of two U64Double<N> and a u64 as well as the
    /// borrow If borrow > 0, this means that |a - b| > 2^(2*N)
    pub(crate) const fn sub_with_borrow(&self, b: &Self, borrow_in: u64) -> (Self, u64) {
        let mut res = Self::zero();
        let mut borrow = borrow_in;

        let mut i = 0;
        while i < N {
            let (diff, overflow) = sub64_with_overflow(self.0[i], b.0[i], borrow);
            res.0[i] = diff;
            borrow = overflow;
            i += 1;
        }
        (res, borrow)
    }

    /// Return the difference of two U64Double<N> as well as the borrow
    /// If borrow > 0, this means that |a - b| > 2^(2*N)
    pub(crate) const fn sub(&self, b: &Self) -> (Self, u64) {
        self.sub_with_borrow(b, 0u64)
    }

    /// Return the multiplication of two U64Double<N> as a U64Double<N>
    pub(crate) const fn mul(&self, b: &Self) -> U64Double<N> {
        let mut result = U64Double::<N>::zero();

        let mut i = 0;
        while i < N {
            let mut j = 0;
            while j < N {
                let rij = (self.0[i] as u128) * (b.0[j] as u128);
                let lo = (rij & 0xFFFFFFFFFFFFFFFF) as u64;
                let hi = (rij >> 64) as u64;

                // Add lo to tmp[i+j]
                let (sum, mut carry) = add64_with_carry(result.get(i + j), lo, 0);
                result.modify(sum, i + j);

                // Add hi + carry to next word and propagate
                let mut k = i + j + 1;
                let mut value = hi;
                while value != 0 || carry != 0 {
                    let (s, c) = add64_with_carry(result.get(k), value, carry);
                    result.modify(s, k);
                    carry = c;
                    value = 0; // hi only added once
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        result
    }

    /// Return the modulo of a U64Double<N> with a U64Double<N>
    pub(crate) const fn modulo(&self, modulus: &Self) -> Self {
        let mut result = self.copy();
        // If n < modulus, return n
        if self.cmp(modulus) == -1 {
            return result;
        }
        let mut size_result = result.size_in_bits() as i32;

        let size_modulus = modulus.size_in_bits() as i32;
        let mut diff_size = size_result - size_modulus;

        while diff_size > -1 {
            let mut shifted_modulus;

            // If result is i bit longer than modulus, with i > 0,
            // we attempt to remove modulus*2**i to result, othewise modulus.
            // If result already is smaller than modulus, return modulus.
            if diff_size != 0 {
                shifted_modulus = modulus.pow2(diff_size as usize);

                // If modulus*2**i > result, we remove instead modulus * 2**{i-1} or modulus
                if shifted_modulus.cmp(&result) == 1 {
                    if diff_size > 1 {
                        shifted_modulus = modulus.pow2(diff_size as usize - 1);
                    } else {
                        shifted_modulus = modulus.copy();
                    }
                }
            } else if modulus.cmp(&result) == 1 {
                return result;
            } else {
                let (difference, _) = result.sub(modulus);
                return difference;
            };

            let (difference, _) = result.sub(&shifted_modulus);
            result = difference;
            size_result = result.size_in_bits() as i32;
            diff_size = size_result - size_modulus;
        }
        result
    }
}
