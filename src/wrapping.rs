// Copyright © 2018–2019 Trevor Spiteri

// This library is free software: you can redistribute it and/or
// modify it under the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT
// License along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

use crate::{
    sealed::Fixed,
    traits::ToFixed,
    types::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    cmp::Ordering,
    default::Default,
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    iter::{Product, Sum},
    num::Wrapping as CoreWrapping,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
};

/// Provides intentionally wrapped arithmetic on fixed-point numbers.
///
/// The underlying value can be retrieved through the `.0` index.
///
/// # Examples
///
/// ```rust
/// use fixed::Wrapping;
/// type Fix = fixed::types::I16F16;
/// let max = Wrapping(Fix::max_value());
/// let delta = Wrapping(Fix::from_bits(1));
/// assert_eq!(Fix::min_value(), (max + delta).0);
/// ```
#[repr(transparent)]
pub struct Wrapping<F: Fixed>(pub F);

impl<F: Fixed> Wrapping<F> {
    /// Wrapping ceil. Rounds to the next integer towards +∞, wrapping
    /// on overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::Wrapping;
    /// type Fix = fixed::types::I16F16;
    /// let two_half = Wrapping(Fix::from_int(5) / 2);
    /// assert_eq!(two_half.ceil(), Wrapping(Fix::from_int(3)));
    /// assert_eq!(Wrapping(Fix::max_value()).ceil(), Wrapping(Fix::min_value()));
    /// ```
    pub fn ceil(self) -> Wrapping<F> {
        Wrapping((self.0).wrapping_ceil())
    }

    /// Wrapping floor. Rounds to the next integer towards −∞,
    /// wrapping on overflow.
    ///
    /// Overflow can only occur for signed numbers with zero integer
    /// bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::Wrapping;
    /// type Fix = fixed::types::I16F16;
    /// let two_half = Wrapping(Fix::from_int(5) / 2);
    /// assert_eq!(two_half.floor(), Wrapping(Fix::from_int(2)));
    /// type AllFrac = fixed::types::I0F32;
    /// assert_eq!(Wrapping(AllFrac::min_value()).floor(), Wrapping(AllFrac::from_int(0)));
    /// ```
    pub fn floor(self) -> Wrapping<F> {
        Wrapping((self.0).wrapping_floor())
    }

    /// Wrapping round. Rounds to the next integer to the nearest,
    /// with ties rounded away from zero, and wrapping on overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::Wrapping;
    /// type Fix = fixed::types::I16F16;
    /// let two_half = Wrapping(Fix::from_int(5) / 2);
    /// assert_eq!(two_half.round(), Wrapping(Fix::from_int(3)));
    /// assert_eq!((-two_half).round(), Wrapping(Fix::from_int(-3)));
    /// assert_eq!(Wrapping(Fix::max_value()).round(), Wrapping(Fix::min_value()));
    /// ```
    pub fn round(self) -> Wrapping<F> {
        Wrapping((self.0).wrapping_round())
    }

    /// Wrapping absolute value. Returns the absolute value, wrapping
    /// on overflow.
    ///
    /// Overflow can only occur for signed numbers when trying to find
    /// the absolute value of the minimum value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::Wrapping;
    /// type Fix = fixed::types::I16F16;
    /// assert_eq!(Wrapping(Fix::from_int(-5)).abs(), Wrapping(Fix::from_int(5)));
    /// assert_eq!(Wrapping(Fix::min_value()).abs(), Wrapping(Fix::min_value()));
    /// ```
    pub fn abs(self) -> Wrapping<F> {
        Wrapping((self.0).wrapping_abs())
    }
}

impl<F: Fixed> Clone for Wrapping<F> {
    #[inline]
    fn clone(&self) -> Wrapping<F> {
        Wrapping(self.0)
    }
}

impl<F: Fixed> Copy for Wrapping<F> {}

impl<F: Fixed> Default for Wrapping<F> {
    #[inline]
    fn default() -> Wrapping<F> {
        Wrapping(F::Traits::default().into())
    }
}

impl<F: Fixed> Hash for Wrapping<F> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.traits().hash(state);
    }
}

impl<F: Fixed> Debug for Wrapping<F> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        <F::Traits as Debug>::fmt(&self.0.traits(), f)
    }
}

impl<F: Fixed> Display for Wrapping<F> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        <F::Traits as Display>::fmt(&self.0.traits(), f)
    }
}

impl<F: Fixed> From<F> for Wrapping<F> {
    #[inline]
    fn from(src: F) -> Wrapping<F> {
        Wrapping(src)
    }
}

impl<F: Fixed> Eq for Wrapping<F> {}
impl<F: Fixed> PartialEq<Wrapping<F>> for Wrapping<F> {
    #[inline]
    fn eq(&self, other: &Wrapping<F>) -> bool {
        self.0.traits().eq(&other.0.traits())
    }
}
impl<F: Fixed> Ord for Wrapping<F> {
    #[inline]
    fn cmp(&self, other: &Wrapping<F>) -> Ordering {
        self.0.traits().cmp(&other.0.traits())
    }
}
impl<F: Fixed> PartialOrd<Wrapping<F>> for Wrapping<F> {
    #[inline]
    fn partial_cmp(&self, other: &Wrapping<F>) -> Option<Ordering> {
        self.0.traits().partial_cmp(&other.0.traits())
    }
    #[inline]
    fn lt(&self, other: &Wrapping<F>) -> bool {
        self.0.traits().lt(&other.0.traits())
    }
    #[inline]
    fn le(&self, other: &Wrapping<F>) -> bool {
        self.0.traits().le(&other.0.traits())
    }
    #[inline]
    fn gt(&self, other: &Wrapping<F>) -> bool {
        self.0.traits().gt(&other.0.traits())
    }
    #[inline]
    fn ge(&self, other: &Wrapping<F>) -> bool {
        self.0.traits().ge(&other.0.traits())
    }
}

macro_rules! op {
    (
        $Fixed:ident($LeEqU:ident)::$wrapping:ident,
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac: $LeEqU> $Op<Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: Wrapping<$Fixed<Frac>>) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, Frac: $LeEqU> $Op<Wrapping<$Fixed<Frac>>> for &'a Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: Wrapping<$Fixed<Frac>>) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, Frac: $LeEqU> $Op<&'a Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &Wrapping<$Fixed<Frac>>) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, 'b, Frac: $LeEqU> $Op<&'a Wrapping<$Fixed<Frac>>> for &'b Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &Wrapping<$Fixed<Frac>>) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<Frac: $LeEqU> $OpAssign<Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: Wrapping<$Fixed<Frac>>) {
                self.0 = (self.0).$wrapping(other.0);
            }
        }
        impl<'a, Frac: $LeEqU> $OpAssign<&'a Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: &Wrapping<$Fixed<Frac>>) {
                self.0 = (self.0).$wrapping(other.0);
            }
        }
    };
}

macro_rules! op_bits {
    (
        $Fixed:ident($LeEqU:ident)::$wrapping:ident,
        $Bits:ident,
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac: $LeEqU> $Op<$Bits> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, Frac: $LeEqU> $Op<$Bits> for &'a Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, Frac: $LeEqU> $Op<&'a $Bits> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<'a, 'b, Frac: $LeEqU> $Op<&'a $Bits> for &'b Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<Frac: $LeEqU> $OpAssign<$Bits> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: $Bits) {
                self.0 = (self.0).$wrapping(other);
            }
        }
        impl<'a, Frac: $LeEqU> $OpAssign<&'a $Bits> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: &$Bits) {
                self.0 = (self.0).$wrapping(*other);
            }
        }
    };
}

macro_rules! op_sh {
    (
        $Fixed:ident($LeEqU:ident),
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac: $LeEqU> $Op<usize> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: usize) -> Wrapping<$Fixed<Frac>> {
                Wrapping($Fixed::from_bits(
                    CoreWrapping((self.0).to_bits()).$op(other).0,
                ))
            }
        }
        impl<Frac: $LeEqU> $OpAssign<usize> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: usize) {
                self.0 = (self.0).$op(other);
            }
        }
        impl<'a, Frac: $LeEqU> $OpAssign<&'a usize> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: &usize) {
                self.0 = (self.0).$op(*other);
            }
        }
    };
}

macro_rules! ops {
    ($Fixed:ident($LeEqU:ident, $Bits:ident)) => {
        impl<Frac: $LeEqU> Neg for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn neg(self) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).wrapping_neg())
            }
        }
        impl<'a, Frac: $LeEqU> Neg for &'a Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn neg(self) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).wrapping_neg())
            }
        }
        op! { $Fixed($LeEqU)::wrapping_add, Add add, AddAssign add_assign }
        op! { $Fixed($LeEqU)::wrapping_sub, Sub sub, SubAssign sub_assign }
        op! { $Fixed($LeEqU)::wrapping_mul, Mul mul, MulAssign mul_assign }
        op! { $Fixed($LeEqU)::wrapping_div, Div div, DivAssign div_assign }
        op_bits! { $Fixed($LeEqU)::wrapping_mul_int, $Bits, Mul mul, MulAssign mul_assign }
        op_bits! { $Fixed($LeEqU)::wrapping_div_int, $Bits, Div div, DivAssign div_assign }
        op_bits! { $Fixed($LeEqU)::wrapping_rem_int, $Bits, Rem rem, RemAssign rem_assign }

        impl<Frac: $LeEqU> Not for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn not(self) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).not())
            }
        }
        impl<'a, Frac: $LeEqU> Not for &'a Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn not(self) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).not())
            }
        }
        op! { $Fixed($LeEqU)::bitand, BitAnd bitand, BitAndAssign bitand_assign }
        op! { $Fixed($LeEqU)::bitor, BitOr bitor, BitOrAssign bitor_assign }
        op! { $Fixed($LeEqU)::bitxor, BitXor bitxor, BitXorAssign bitxor_assign }

        op_sh! { $Fixed($LeEqU), Shl shl, ShlAssign shl_assign }
        op_sh! { $Fixed($LeEqU), Shr shr, ShrAssign shr_assign }

        impl<Frac: $LeEqU> Sum<Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>> {
            fn sum<I>(iter: I) -> Wrapping<$Fixed<Frac>>
            where
                I: Iterator<Item = Wrapping<$Fixed<Frac>>>,
            {
                iter.fold(Wrapping($Fixed::from_bits(0)), Add::add)
            }
        }

        impl<'a, Frac: 'a + $LeEqU> Sum<&'a Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>> {
            fn sum<I>(iter: I) -> Wrapping<$Fixed<Frac>>
            where
                I: Iterator<Item = &'a Wrapping<$Fixed<Frac>>>,
            {
                iter.fold(Wrapping($Fixed::from_bits(0)), Add::add)
            }
        }

        impl<Frac: $LeEqU> Product<Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>> {
            fn product<I>(mut iter: I) -> Wrapping<$Fixed<Frac>>
            where
                I: Iterator<Item = Wrapping<$Fixed<Frac>>>,
            {
                match iter.next() {
                    None => Wrapping(1.wrapping_to_fixed()),
                    Some(first) => iter.fold(first, Mul::mul),
                }
            }
        }

        impl<'a, Frac: 'a + $LeEqU> Product<&'a Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>> {
            fn product<I>(mut iter: I) -> Wrapping<$Fixed<Frac>>
            where
                I: Iterator<Item = &'a Wrapping<$Fixed<Frac>>>,
            {
                match iter.next() {
                    None => Wrapping(1.wrapping_to_fixed()),
                    Some(first) => iter.fold(*first, Mul::mul),
                }
            }
        }
    };
}

ops! { FixedI8(LeEqU8, i8) }
ops! { FixedI16(LeEqU16, i16) }
ops! { FixedI32(LeEqU32, i32) }
ops! { FixedI64(LeEqU64, i64) }
ops! { FixedI128(LeEqU128, i128) }
ops! { FixedU8(LeEqU8, u8) }
ops! { FixedU16(LeEqU16, u16) }
ops! { FixedU32(LeEqU32, u32) }
ops! { FixedU64(LeEqU64, u64) }
ops! { FixedU128(LeEqU128, u128) }
