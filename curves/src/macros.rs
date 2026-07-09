#[macro_export]
macro_rules! impl_binops_calls {
    ($field:ident) => {
        impl ::core::ops::Neg for $field {
            type Output = $field;

            #[inline]
            fn neg(self) -> $field {
                -&self
            }
        }

        impl<'a> ::core::ops::Neg for &'a $field {
            type Output = $field;

            #[inline]
            fn neg(self) -> $field {
                self.neg()
            }
        }

        impl<'a, 'b> ::core::ops::Sub<&'b $field> for &'a $field {
            type Output = $field;

            #[inline]
            fn sub(self, rhs: &'b $field) -> $field {
                self.sub(rhs)
            }
        }

        impl<'a, 'b> ::core::ops::Add<&'b $field> for &'a $field {
            type Output = $field;

            #[inline]
            fn add(self, rhs: &'b $field) -> $field {
                self.add(rhs)
            }
        }

        impl<'a, 'b> ::core::ops::Mul<&'b $field> for &'a $field {
            type Output = $field;

            #[inline]
            fn mul(self, rhs: &'b $field) -> $field {
                self.mul(rhs)
            }
        }
    };
}

#[macro_export]
macro_rules! impl_add_binop_specify_output {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl<'b> ::core::ops::Add<&'b $rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: &'b $rhs) -> $output {
                &self + rhs
            }
        }

        impl<'a> ::core::ops::Add<$rhs> for &'a $lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: $rhs) -> $output {
                self + &rhs
            }
        }

        impl ::core::ops::Add<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: $rhs) -> $output {
                &self + &rhs
            }
        }
    };
}

#[macro_export]
macro_rules! impl_sub_binop_specify_output {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl<'b> ::core::ops::Sub<&'b $rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: &'b $rhs) -> $output {
                &self - rhs
            }
        }

        impl<'a> ::core::ops::Sub<$rhs> for &'a $lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: $rhs) -> $output {
                self - &rhs
            }
        }

        impl ::core::ops::Sub<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: $rhs) -> $output {
                &self - &rhs
            }
        }
    };
}

#[macro_export]
macro_rules! impl_binops_additive_specify_output {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        $crate::impl_add_binop_specify_output!($lhs, $rhs, $output);
        $crate::impl_sub_binop_specify_output!($lhs, $rhs, $output);
    };
}

#[macro_export]
macro_rules! impl_binops_multiplicative_mixed {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl<'b> ::core::ops::Mul<&'b $rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: &'b $rhs) -> $output {
                &self * rhs
            }
        }

        impl<'a> ::core::ops::Mul<$rhs> for &'a $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                self * &rhs
            }
        }

        impl ::core::ops::Mul<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                &self * &rhs
            }
        }
    };
}

#[macro_export]
macro_rules! impl_binops_additive {
    ($lhs:ident, $rhs:ident) => {
        $crate::impl_binops_additive_specify_output!($lhs, $rhs, $lhs);

        impl ::core::ops::SubAssign<$rhs> for $lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: $rhs) {
                *self = &*self - &rhs;
            }
        }

        impl ::core::ops::AddAssign<$rhs> for $lhs {
            #[inline]
            fn add_assign(&mut self, rhs: $rhs) {
                *self = &*self + &rhs;
            }
        }

        impl<'b> ::core::ops::SubAssign<&'b $rhs> for $lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self - rhs;
            }
        }

        impl<'b> ::core::ops::AddAssign<&'b $rhs> for $lhs {
            #[inline]
            fn add_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self + rhs;
            }
        }
    };
}

#[macro_export]
macro_rules! impl_binops_multiplicative {
    ($lhs:ident, $rhs:ident) => {
        $crate::impl_binops_multiplicative_mixed!($lhs, $rhs, $lhs);

        impl ::core::ops::MulAssign<$rhs> for $lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: $rhs) {
                *self = &*self * &rhs;
            }
        }

        impl<'b> ::core::ops::MulAssign<&'b $rhs> for $lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self * rhs;
            }
        }
    };
}

#[macro_export]
macro_rules! impl_sum_prod {
    ($f:ident) => {
        impl<T: ::core::borrow::Borrow<$f>> ::core::iter::Sum<T> for $f {
            fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
                iter.fold(Self::zero(), |acc, item| acc + item.borrow())
            }
        }

        impl<T: ::core::borrow::Borrow<$f>> ::core::iter::Product<T> for $f {
            fn product<I: Iterator<Item = T>>(iter: I) -> Self {
                iter.fold(Self::one(), |acc, item| acc * item.borrow())
            }
        }
    };
}

#[macro_export]
macro_rules! field_bits {
    ($field:ident) => {
        impl ff::PrimeFieldBits for $field {
            #[cfg(target_pointer_width = "64")]
            type ReprBits = [u64; Self::NUM_LIMBS];
            #[cfg(not(target_pointer_width = "64"))]
            type ReprBits = [u32; Self::NUM_LIMBS * 2];

            fn to_le_bits(&self) -> ff::FieldBits<Self::ReprBits> {
                use ff::PrimeField;
                let bytes: [u8; Self::SIZE] = self.to_repr().into();

                #[cfg(target_pointer_width = "64")]
                const STEP: usize = 8;
                #[cfg(not(target_pointer_width = "64"))]
                const STEP: usize = 4;

                let limbs = (0..Self::NUM_LIMBS * 8 / STEP)
                    .map(|off| {
                        #[cfg(target_pointer_width = "64")]
                        let limb = u64::from_le_bytes(
                            bytes[off * STEP..(off + 1) * STEP].try_into().unwrap(),
                        );
                        #[cfg(not(target_pointer_width = "64"))]
                        let limb = u32::from_le_bytes(
                            bytes[off * STEP..(off + 1) * STEP].try_into().unwrap(),
                        );

                        limb
                    })
                    .collect::<Vec<_>>();

                ff::FieldBits::new(limbs.try_into().unwrap())
            }

            fn char_le_bits() -> ff::FieldBits<Self::ReprBits> {
                #[cfg(target_pointer_width = "64")]
                let bits = ff::FieldBits::new(Self::MODULUS_LIMBS);
                #[cfg(not(target_pointer_width = "64"))]
                let bits = ff::FieldBits::new(Self::MODULUS_LIMBS_32);

                bits
            }
        }
    };
}

#[macro_export]
macro_rules! impl_from_u64 {
    ($field:ident) => {
        impl From<u64> for $field {
            fn from(val: u64) -> $field {
                let limbs = std::iter::once(val)
                    .chain(std::iter::repeat(0))
                    .take(Self::NUM_LIMBS)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                $field(limbs) * Self::R2
            }
        }
    };
}

#[macro_export]
macro_rules! impl_from_bool {
    ($field:ident) => {
        impl From<bool> for $field {
            fn from(val: bool) -> $field {
                let limbs = std::iter::once(u64::from(val))
                    .chain(std::iter::repeat(0))
                    .take(Self::NUM_LIMBS)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                $field(limbs) * Self::R2
            }
        }
    };
}
