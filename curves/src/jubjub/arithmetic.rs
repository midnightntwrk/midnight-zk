//! Macros for binary operations in the JubJub curve and its scalar field.

pub(crate) mod add {
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
    macro_rules! impl_binops_additive {
        ($lhs:ident) => {
            $crate::impl_binops_additive!($lhs, $lhs);
        };
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
}

pub(crate) mod mul {
    #[macro_export]
    macro_rules! impl_binops_multiplicative {
        ($lhs:ident) => {
            $crate::impl_binops_multiplicative!($lhs, $lhs);
        };
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
}
