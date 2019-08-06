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
    frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8},
    sealed::Fixed,
    traits::ToFixed,
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
pub struct Wrapping<F>(pub F)
where
    F: Fixed;

impl<F> Wrapping<F>
where
    F: Fixed,
{
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

impl<F> Clone for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn clone(&self) -> Wrapping<F> {
        Wrapping(self.0)
    }
}

impl<F> Copy for Wrapping<F> where F: Fixed {}

impl<F> Default for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn default() -> Wrapping<F> {
        Wrapping(F::default())
    }
}

impl<F> Hash for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        (self.0).hash(state);
    }
}

impl<F> Debug for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        <F as Debug>::fmt(&self.0, f)
    }
}

impl<F> Display for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        <F as Display>::fmt(&self.0, f)
    }
}

impl<F> From<F> for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn from(src: F) -> Wrapping<F> {
        Wrapping(src)
    }
}

impl<F> Eq for Wrapping<F> where F: Fixed {}
impl<F> PartialEq<Wrapping<F>> for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn eq(&self, other: &Wrapping<F>) -> bool {
        (self.0).eq(&other.0)
    }
}
impl<F> Ord for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn cmp(&self, other: &Wrapping<F>) -> Ordering {
        (self.0).cmp(&other.0)
    }
}
impl<F> PartialOrd<Wrapping<F>> for Wrapping<F>
where
    F: Fixed,
{
    #[inline]
    fn partial_cmp(&self, other: &Wrapping<F>) -> Option<Ordering> {
        (self.0).partial_cmp(&other.0)
    }
    #[inline]
    fn lt(&self, other: &Wrapping<F>) -> bool {
        (self.0).lt(&other.0)
    }
    #[inline]
    fn le(&self, other: &Wrapping<F>) -> bool {
        (self.0).le(&other.0)
    }
    #[inline]
    fn gt(&self, other: &Wrapping<F>) -> bool {
        (self.0).gt(&other.0)
    }
    #[inline]
    fn ge(&self, other: &Wrapping<F>) -> bool {
        (self.0).ge(&other.0)
    }
}

macro_rules! op {
    (
        $Fixed:ident($Len:ident)::$wrapping:ident,
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac> $Op<Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: Wrapping<$Fixed<Frac>>) -> Wrapping<$Fixed<Frac>>
            where
                Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
            {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, Frac> $Op<Wrapping<$Fixed<Frac>>> for &'a Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: Wrapping<$Fixed<Frac>>) -> Wrapping<$Fixed<Frac>>
            where
                Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
            {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, Frac> $Op<&'a Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &Wrapping<$Fixed<Frac>>) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, 'b, Frac> $Op<&'a Wrapping<$Fixed<Frac>>> for &'b Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &Wrapping<$Fixed<Frac>>) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<Frac> $OpAssign<Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn $op_assign(&mut self, other: Wrapping<$Fixed<Frac>>) {
                self.0 = (self.0).$wrapping(other.0);
            }
        }
        impl<'a, Frac> $OpAssign<&'a Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn $op_assign(&mut self, other: &Wrapping<$Fixed<Frac>>) {
                self.0 = (self.0).$wrapping(other.0);
            }
        }
    };
}

macro_rules! op_bits {
    (
        $Fixed:ident($Len:ident)::$wrapping:ident,
        $Bits:ident,
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac> $Op<$Bits> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, Frac> $Op<$Bits> for &'a Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, Frac> $Op<&'a $Bits> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<'a, 'b, Frac> $Op<&'a $Bits> for &'b Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<Frac> $OpAssign<$Bits> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn $op_assign(&mut self, other: $Bits) {
                self.0 = (self.0).$wrapping(other);
            }
        }
        impl<'a, Frac> $OpAssign<&'a $Bits> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn $op_assign(&mut self, other: &$Bits) {
                self.0 = (self.0).$wrapping(*other);
            }
        }
    };
}

macro_rules! op_sh {
    (
        $Fixed:ident($Len:ident),
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac> $Op<usize> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: usize) -> Wrapping<$Fixed<Frac>>
            where
                Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
            {
                Wrapping($Fixed::from_bits(
                    CoreWrapping((self.0).to_bits()).$op(other).0,
                ))
            }
        }
        impl<Frac> $OpAssign<usize> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn $op_assign(&mut self, other: usize) {
                self.0 = (self.0).$op(other);
            }
        }
        impl<'a, Frac> $OpAssign<&'a usize> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn $op_assign(&mut self, other: &usize) {
                self.0 = (self.0).$op(*other);
            }
        }
    };
}

macro_rules! ops {
    ($Fixed:ident($Len:ident, $Bits:ident)) => {
        impl<Frac> Neg for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn neg(self) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).wrapping_neg())
            }
        }
        impl<'a, Frac> Neg for &'a Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn neg(self) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).wrapping_neg())
            }
        }
        op! { $Fixed($Len)::wrapping_add, Add add, AddAssign add_assign }
        op! { $Fixed($Len)::wrapping_sub, Sub sub, SubAssign sub_assign }
        op! { $Fixed($Len)::wrapping_mul, Mul mul, MulAssign mul_assign }
        op! { $Fixed($Len)::wrapping_div, Div div, DivAssign div_assign }
        op_bits! { $Fixed($Len)::wrapping_mul_int, $Bits, Mul mul, MulAssign mul_assign }
        op_bits! { $Fixed($Len)::wrapping_div_int, $Bits, Div div, DivAssign div_assign }
        op_bits! { $Fixed($Len)::wrapping_rem_int, $Bits, Rem rem, RemAssign rem_assign }

        impl<Frac> Not for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn not(self) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).not())
            }
        }
        impl<'a, Frac> Not for &'a Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn not(self) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).not())
            }
        }
        op! { $Fixed($Len)::bitand, BitAnd bitand, BitAndAssign bitand_assign }
        op! { $Fixed($Len)::bitor, BitOr bitor, BitOrAssign bitor_assign }
        op! { $Fixed($Len)::bitxor, BitXor bitxor, BitXorAssign bitxor_assign }

        op_sh! { $Fixed($Len), Shl shl, ShlAssign shl_assign }
        op_sh! { $Fixed($Len), Shr shr, ShrAssign shr_assign }

        impl<Frac> Sum<Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            fn sum<I>(iter: I) -> Wrapping<$Fixed<Frac>>
            where
                I: Iterator<Item = Wrapping<$Fixed<Frac>>>,
            {
                iter.fold(Wrapping($Fixed::from_bits(0)), Add::add)
            }
        }

        impl<'a, Frac> Sum<&'a Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>>
        where
            Frac: 'a + Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            fn sum<I>(iter: I) -> Wrapping<$Fixed<Frac>>
            where
                I: Iterator<Item = &'a Wrapping<$Fixed<Frac>>>,
            {
                iter.fold(Wrapping($Fixed::from_bits(0)), Add::add)
            }
        }

        impl<Frac> Product<Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
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

        impl<'a, Frac> Product<&'a Wrapping<$Fixed<Frac>>> for Wrapping<$Fixed<Frac>>
        where
            Frac: 'a + Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
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

ops! { FixedI8(U8, i8) }
ops! { FixedI16(U16, i16) }
ops! { FixedI32(U32, i32) }
ops! { FixedI64(U64, i64) }
ops! { FixedI128(U128, i128) }
ops! { FixedU8(U8, u8) }
ops! { FixedU16(U16, u16) }
ops! { FixedU32(U32, u32) }
ops! { FixedU64(U64, u64) }
ops! { FixedU128(U128, u128) }
