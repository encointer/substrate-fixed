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

/*!
This module contains traits.
*/

use crate::{
    frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8},
    sealed::{self, SealedFixed, SealedFloat, SealedInt},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex},
    hash::Hash,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};
#[cfg(feature = "f16")]
use half::f16;

/// This trait provides common methods to all fixed-point numbers.
pub trait Fixed
where
    Self: Copy + Default + Hash + Ord,
    Self: Debug + Display + Binary + Octal + LowerHex + UpperHex,
    Self: FromFixed + ToFixed + sealed::Fixed,
    Self: Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Div<Output = Self>,
    Self: BitAnd<Output = Self> + BitOr<Output = Self> + BitXor<Output = Self>,
    Self: Not<Output = Self> + Shl<u32, Output = Self> + Shr<u32, Output = Self>,
    Self: AddAssign + SubAssign + MulAssign + DivAssign,
    Self: BitAndAssign + BitOrAssign + BitXorAssign + ShlAssign<u32> + ShrAssign<u32>,
    Self: PartialOrd<i8> + PartialOrd<i16> + PartialOrd<i32>,
    Self: PartialOrd<i64> + PartialOrd<i128> + PartialOrd<isize>,
    Self: PartialOrd<u8> + PartialOrd<u16> + PartialOrd<u32>,
    Self: PartialOrd<u64> + PartialOrd<u128> + PartialOrd<usize>,
    Self: PartialOrd<f32> + PartialOrd<f64>,
{
    /// The primitive integer underlying type.
    type Bits;

    /// Returns the smallest value that can be represented.
    fn min_value() -> Self;

    /// Returns the largest value that can be represented.
    fn max_value() -> Self;

    /// Returns the number of integer bits.
    fn int_nbits() -> u32;

    /// Returns the number of fractional bits.
    fn frac_nbits() -> u32;

    /// Creates a fixed-point number that has a bitwise representation
    /// identical to the given integer.
    fn from_bits(bits: Self::Bits) -> Self;

    /// Creates an integer that has a bitwise representation identical
    /// to the given fixed-point number.
    fn to_bits(self) -> Self::Bits;

    /// Returns the integer part.
    fn int(self) -> Self;

    /// Returns the fractional part.
    fn frac(self) -> Self;

    /// Rounds to the next integer towards +∞.
    fn ceil(self) -> Self;

    /// Rounds to the next integer towards −∞.
    fn floor(self) -> Self;

    /// Rounds to the nearest integer, with ties rounded away from zero.
    fn round(self) -> Self;

    /// Checked ceil. Rounds to the next integer towards +∞, returning
    /// [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_ceil(self) -> Option<Self>;

    /// Checked floor. Rounds to the next integer towards −∞, returning
    /// [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_floor(self) -> Option<Self>;

    /// Checked round. Rounds to the nearest integer, with ties
    /// rounded away from zero, returning [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_round(self) -> Option<Self>;

    /// Saturating ceil. Rounds to the next integer towards +∞,
    /// saturating on overflow.
    fn saturating_ceil(self) -> Self;

    /// Saturating floor. Rounds to the next integer towards −∞,
    /// saturating on overflow.
    fn saturating_floor(self) -> Self;

    /// Saturating round. Rounds to the nearest integer, with ties
    /// rounded away from zero, and saturating on overflow.
    fn saturating_round(self) -> Self;

    /// Wrapping ceil. Rounds to the next integer towards +∞, wrapping
    /// on overflow.
    fn wrapping_ceil(self) -> Self;

    /// Wrapping floor. Rounds to the next integer towards −∞,
    /// wrapping on overflow.
    fn wrapping_floor(self) -> Self;

    /// Wrapping round. Rounds to the next integer to the nearest,
    /// with ties rounded away from zero, and wrapping on overflow.
    fn wrapping_round(self) -> Self;

    /// Overflowing ceil. Rounds to the next integer towards +∞.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_ceil(self) -> (Self, bool);

    /// Overflowing floor. Rounds to the next integer towards −∞.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_floor(self) -> (Self, bool);

    /// Overflowing round. Rounds to the next integer to the nearest,
    /// with ties rounded away from zero.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_round(self) -> (Self, bool);

    /// Returns the number of ones in the binary representation.
    fn count_ones(self) -> u32;

    /// Returns the number of zeros in the binary representation.
    fn count_zeros(self) -> u32;

    /// Returns the number of leading zeros in the binary representation.
    fn leading_zeros(self) -> u32;

    /// Returns the number of trailing zeros in the binary representation.
    fn trailing_zeros(self) -> u32;

    /// Shifts to the left by *n* bits, wrapping the truncated bits to the right end.
    fn rotate_left(self, n: u32) -> Self;

    /// Shifts to the right by *n* bits, wrapping the truncated bits to the left end.
    fn rotate_right(self, n: u32) -> Self;

    /// Multiplication by an integer.
    fn mul_int(self, rhs: Self::Bits) -> Self;

    /// Division by an integer.
    fn div_int(self, rhs: Self::Bits) -> Self;

    /// Remainder for division by an integer.
    fn rem_int(self, rhs: Self::Bits) -> Self;

    /// Checked negation. Returns the negated value, or [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_neg(self) -> Option<Self>;

    /// Checked addition. Returns the sum, or [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_add(self, rhs: Self) -> Option<Self>;

    /// Checked subtraction. Returns the difference, or [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_sub(self, rhs: Self) -> Option<Self>;

    /// Checked multiplication. Returns the product, or [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_mul(self, rhs: Self) -> Option<Self>;

    /// Checked division. Returns the quotient, or [`None`] if the
    /// divisor is zero or on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_div(self, rhs: Self) -> Option<Self>;

    /// Checked multiplication by an integer. Returns the product, or
    /// [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_mul_int(self, rhs: Self::Bits) -> Option<Self>;

    /// Checked division by an integer. Returns the quotient, or
    /// [`None`] if the divisor is zero or if the division results in
    /// overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_div_int(self, rhs: Self::Bits) -> Option<Self>;

    /// Checked fixed-point remainder for division by an integer.
    /// Returns the remainder, or [`None`] if the divisor is zero or
    /// if the division results in overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_rem_int(self, rhs: Self::Bits) -> Option<Self>;

    /// Checked shift left. Returns the shifted number, or [`None`] if
    /// `rhs` ≥ the number of bits.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_shl(self, rhs: u32) -> Option<Self>;

    /// Checked shift right. Returns the shifted number, or [`None`]
    /// if `rhs` ≥ the number of bits.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_shr(self, rhs: u32) -> Option<Self>;

    /// Saturated negation. Returns the negated value, saturating on overflow.
    fn saturating_neg(self) -> Self;

    /// Saturating addition. Returns the sum, saturating on overflow.
    fn saturating_add(self, rhs: Self) -> Self;

    /// Saturating subtraction. Returns the difference, saturating on overflow.
    fn saturating_sub(self, rhs: Self) -> Self;

    /// Saturating multiplication. Returns the product, saturating on overflow.
    fn saturating_mul(self, rhs: Self) -> Self;

    /// Saturating division. Returns the quotient, saturating on overflow.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn saturating_div(self, rhs: Self) -> Self;

    /// Saturating multiplication by an integer. Returns the product, saturating on overflow.
    fn saturating_mul_int(self, rhs: Self::Bits) -> Self;

    /// Wrapping negation. Returns the negated value, wrapping on overflow.
    fn wrapping_neg(self) -> Self;

    /// Wrapping addition. Returns the sum, wrapping on overflow.
    fn wrapping_add(self, rhs: Self) -> Self;

    /// Wrapping subtraction. Returns the difference, wrapping on overflow.
    fn wrapping_sub(self, rhs: Self) -> Self;

    /// Wrapping multiplication. Returns the product, wrapping on overflow.
    fn wrapping_mul(self, rhs: Self) -> Self;

    /// Wrapping division. Returns the quotient, wrapping on overflow.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn wrapping_div(self, rhs: Self) -> Self;

    /// Wrapping multiplication by an integer. Returns the product, wrapping on overflow.
    fn wrapping_mul_int(self, rhs: Self::Bits) -> Self;

    /// Wrapping division by an integer. Returns the quotient, wrapping on overflow.
    ///
    /// Overflow can only occur when dividing the minimum value by −1.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn wrapping_div_int(self, rhs: Self::Bits) -> Self;

    /// Wrapping fixed-point remainder for division by an integer.
    /// Returns the remainder, wrapping on overflow.
    ///
    /// Overflow can only occur when dividing the minimum value by −1.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn wrapping_rem_int(self, rhs: Self::Bits) -> Self;

    /// Wrapping shift left. Wraps `rhs` if `rhs` ≥ the number of
    /// bits, then shifts and returns the number.
    fn wrapping_shl(self, rhs: u32) -> Self;

    /// Wrapping shift right. Wraps `rhs` if `rhs` ≥ the number of
    /// bits, then shifts and returns the number.
    fn wrapping_shr(self, rhs: u32) -> Self;

    /// Overflowing negation.
    ///
    /// Returns a [tuple] of the negated value and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_neg(self) -> (Self, bool);

    /// Overflowing addition.
    ///
    /// Returns a [tuple] of the sum and a [`bool`], indicating whether
    /// an overflow has occurred. On overflow, the wrapped value is
    /// returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_add(self, rhs: Self) -> (Self, bool);

    /// Overflowing subtraction.
    ///
    /// Returns a [tuple] of the difference and a [`bool`], indicating
    /// whether an overflow has occurred. On overflow, the wrapped
    /// value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);

    /// Overflowing multiplication.
    ///
    /// Returns a [tuple] of the product and a [`bool`], indicating
    /// whether an overflow has occurred. On overflow, the wrapped
    /// value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);

    /// Overflowing division.
    ///
    /// Returns a [tuple] of the quotient and a [`bool`], indicating
    /// whether an overflow has occurred. On overflow, the wrapped
    /// value is returned.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_div(self, rhs: Self) -> (Self, bool);

    /// Overflowing multiplication by an integer.
    ///
    /// Returns a [tuple] of the product and a [`bool`], indicating
    /// whether an overflow has occurred. On overflow, the wrapped
    /// value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_mul_int(self, rhs: Self::Bits) -> (Self, bool);

    /// Overflowing division by an integer.
    ///
    /// Returns a [tuple] of the quotient and a [`bool`], indicating
    /// whether an overflow has occurred. On overflow, the wrapped
    /// value is returned.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_div_int(self, rhs: Self::Bits) -> (Self, bool);

    /// Overflowing fixed-point remainder for division by an integer.
    ///
    /// Returns a [tuple] of the remainder and a [`bool`], indicating
    /// whether an overflow has occurred. On overflow, the wrapped
    /// value is returned. Overflow can only occur when dividing the
    /// minimum value by −1.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_rem_int(self, rhs: Self::Bits) -> (Self, bool);

    /// Overflowing shift left.
    ///
    /// Returns a [tuple] of the shifted value and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);

    /// Overflowing shift right.
    ///
    /// Returns a [tuple] of the shifted value and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);
}

/// This trait provides common methods to all signed fixed-point numbers.
pub trait FixedSigned: Fixed + Neg<Output = Self> {
    /// Returns the absolute value.
    fn abs(self) -> Self;

    /// Returns a number representing the sign of `self`.
    ///
    /// # Panics
    ///
    /// When debug assertions are enabled, this method panics
    ///   * if the value is positive and the fixed-point number has
    ///     zero or one integer bits such that it cannot hold the
    ///     value 1.
    ///   * if the value is negative and the fixed-point number has
    ///     zero integer bits, such that it cannot hold the value −1.
    ///
    /// When debug assertions are not enabled, the wrapped value can
    /// be returned in those cases, but it is not considered a
    /// breaking change if in the future it panics; using this method
    /// when 1 and −1 cannot be represented is almost certainly a bug.
    fn signum(self) -> Self;

    /// Checked absolute value. Returns the absolute value, or [`None`] on overflow.
    ///
    /// Overflow can only occur when trying to find the absolute value of the minimum value.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_abs(self) -> Option<Self>;

    /// Saturating absolute value. Returns the absolute value, saturating on overflow.
    ///
    /// Overflow can only occur when trying to find the absolute value of the minimum value.
    fn saturating_abs(self) -> Self;

    /// Wrapping absolute value. Returns the absolute value, wrapping on overflow.
    ///
    /// Overflow can only occur when trying to find the absolute value of the minimum value.
    fn wrapping_abs(self) -> Self;

    /// Overflowing absolute value.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_abs(self) -> (Self, bool);

    /// Returns [`true`][`bool`] if the number is > 0.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn is_positive(self) -> bool;

    /// Returns [`true`][`bool`] if the number is < 0.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn is_negative(self) -> bool;
}

/// This trait provides common methods to all unsigned fixed-point numbers.
pub trait FixedUnsigned: Fixed {
    /// Returns [`true`][`bool`] if the fixed-point number is
    /// 2<sup><i>k</i></sup> for some integer <i>k</i>.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn is_power_of_two(self) -> bool;

    /// Returns the smallest power of two ≥ `self`.
    fn next_power_of_two(self) -> Self;

    /// Returns the smallest power of two ≥ `self`, or [`None`] if the
    /// next power of two is too large to represent.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_next_power_of_two(self) -> Option<Self>;
}

/// This trait provides infallible conversions that might be lossy.
///
/// This trait is implemented for conversions between integer
/// primitives, floating-point primitives and fixed-point numbers.
///
/// # Examples
///
/// ```rust
/// use fixed::traits::LossyFrom;
/// use fixed::types::{I12F4, I4F60};
/// // original is 0x1.234
/// let original = I4F60::from_bits(0x1234i64 << (60 - 12));
/// let lossy = I12F4::lossy_from(original);
/// assert_eq!(lossy, I12F4::from_bits(0x0012));
/// ```
pub trait LossyFrom<Src> {
    /// Performs the conversion.
    fn lossy_from(src: Src) -> Self;
}

/// This trait provides infallible conversions that might be lossy.
/// This is the reciprocal of [`LossyFrom`].
///
/// Usually [`LossyFrom`] should be implemented instead of this trait;
/// there is a blanket implementation which provides this trait when
/// [`LossyFrom`] is implemented (similar to [`Into`] and [`From`]).
///
/// # Examples
///
/// ```rust
/// use fixed::traits::LossyInto;
/// use fixed::types::{I12F4, I4F12};
/// // original is 0x1.234
/// let original = I4F12::from_bits(0x1234);
/// let lossy: I12F4 = original.lossy_into();
/// assert_eq!(lossy, I12F4::from_bits(0x0012));
/// ```
///
/// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
/// [`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
/// [`LossyFrom`]: trait.LossyFrom.html
pub trait LossyInto<Dst> {
    /// Performs the conversion.
    fn lossy_into(self) -> Dst;
}

impl<Src, Dst> LossyInto<Dst> for Src
where
    Dst: LossyFrom<Src>,
{
    fn lossy_into(self) -> Dst {
        Dst::lossy_from(self)
    }
}

/// This trait provides checked conversions from fixed-point numbers.
///
/// This trait is implemented for conversions between integer
/// primitives, floating-point primitives and fixed-point numbers.
///
/// # Examples
///
/// ```rust
/// use fixed::traits::FromFixed;
/// use fixed::types::U8F8;
/// // 0x87.65
/// let f = U8F8::from_bits(0x8765);
/// assert_eq!(f32::from_fixed(f), f32::from(0x8765u16) / 256.0);
/// assert_eq!(i32::checked_from_fixed(f), Some(0x87));
/// assert_eq!(u8::saturating_from_fixed(f), 0x87);
/// // no fit
/// assert_eq!(i8::checked_from_fixed(f), None);
/// assert_eq!(i8::saturating_from_fixed(f), i8::max_value());
/// assert_eq!(i8::wrapping_from_fixed(f), 0x87u8 as i8);
/// assert_eq!(i8::overflowing_from_fixed(f), (0x87u8 as i8, true));
/// ```
pub trait FromFixed {
    /// Converts from a fixed-point number.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Panics
    ///
    /// When debug assertions are enabled, panics if the value does
    /// not fit. When debug assertions are not enabled, the wrapped
    /// value can be returned, but it is not considered a breaking
    /// change if in the future it panics; if wrapping is required use
    /// [`wrapping_from_fixed`] instead.
    ///
    /// [`wrapping_from_fixed`]: #method.wrapping_from_fixed
    fn from_fixed<F>(val: F) -> Self
    where
        F: sealed::Fixed;

    /// Converts from a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_from_fixed<F>(val: F) -> Option<Self>
    where
        F: sealed::Fixed,
        Self: Sized;

    /// Converts from a fixed-point number, saturating if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn saturating_from_fixed<F>(val: F) -> Self
    where
        F: sealed::Fixed;

    /// Converts from a fixed-point number, wrapping if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn wrapping_from_fixed<F>(val: F) -> Self
    where
        F: sealed::Fixed;

    /// Converts from a fixed-point number.
    ///
    /// Returns a [tuple] of the value and a [`bool`] indicating whether
    /// an overflow has occurred. On overflow, the wrapped value is
    /// returned.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
    where
        F: sealed::Fixed,
        Self: Sized;
}

/// This trait provides checked conversions to fixed-point numbers.
///
/// This trait is implemented for conversions between integer
/// primitives, floating-point primitives and fixed-point numbers.
///
/// # Examples
///
/// ```rust
/// use fixed::traits::ToFixed;
/// use fixed::types::{U8F8, U16F16};
/// let f: U8F8 = 13.5f32.to_fixed();
/// assert_eq!(f, U8F8::from_bits((13 << 8) | (1 << 7)));
/// // 0x1234.5678 is too large and can be wrapped to 0x34.56
/// let too_large = U16F16::from_bits(0x1234_5678);
/// let checked: Option<U8F8> = too_large.checked_to_fixed();
/// assert_eq!(checked, None);
/// let saturating: U8F8 = too_large.saturating_to_fixed();
/// assert_eq!(saturating, U8F8::max_value());
/// let wrapping: U8F8 = too_large.wrapping_to_fixed();
/// assert_eq!(wrapping, U8F8::from_bits(0x3456));
/// let overflowing: (U8F8, bool) = too_large.overflowing_to_fixed();
/// assert_eq!(overflowing, (U8F8::from_bits(0x3456), true));
/// ```
pub trait ToFixed {
    /// Converts to a fixed-point number.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Panics
    ///
    /// When debug assertions are enabled, panics if the value does
    /// not fit. When debug assertions are not enabled, the wrapped
    /// value can be returned, but it is not considered a breaking
    /// change if in the future it panics; if wrapping is required use
    /// [`wrapping_to_fixed`] instead.
    ///
    /// [`wrapping_to_fixed`]: #method.wrapping_to_fixed
    fn to_fixed<F>(self) -> F
    where
        F: sealed::Fixed;

    /// Converts to a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_to_fixed<F>(self) -> Option<F>
    where
        F: sealed::Fixed;

    /// Converts to a fixed-point number, saturating if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn saturating_to_fixed<F>(self) -> F
    where
        F: sealed::Fixed;

    /// Converts to a fixed-point number, wrapping if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn wrapping_to_fixed<F>(self) -> F
    where
        F: sealed::Fixed;

    /// Converts from a fixed-point number.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: sealed::Fixed;
}

impl ToFixed for bool {
    #[inline]
    fn to_fixed<F>(self) -> F
    where
        F: sealed::Fixed,
    {
        ToFixed::to_fixed(u8::from(self))
    }
    #[inline]
    fn checked_to_fixed<F>(self) -> Option<F>
    where
        F: sealed::Fixed,
    {
        ToFixed::checked_to_fixed(u8::from(self))
    }
    #[inline]
    fn saturating_to_fixed<F>(self) -> F
    where
        F: sealed::Fixed,
    {
        ToFixed::saturating_to_fixed(u8::from(self))
    }
    #[inline]
    fn wrapping_to_fixed<F>(self) -> F
    where
        F: sealed::Fixed,
    {
        ToFixed::wrapping_to_fixed(u8::from(self))
    }
    #[inline]
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: sealed::Fixed,
    {
        ToFixed::overflowing_to_fixed(u8::from(self))
    }
}

macro_rules! impl_int {
    ($Int:ident) => {
        impl FromFixed for $Int {
            #[inline]
            fn from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                SealedInt::from_fixed(val)
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: sealed::Fixed,
            {
                SealedInt::checked_from_fixed(val)
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                SealedInt::saturating_from_fixed(val)
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                SealedInt::wrapping_from_fixed(val)
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: sealed::Fixed,
            {
                SealedInt::overflowing_from_fixed(val)
            }
        }

        impl ToFixed for $Int {
            #[inline]
            fn to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedInt::to_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: sealed::Fixed,
            {
                SealedInt::checked_to_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedInt::saturating_to_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedInt::wrapping_to_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: sealed::Fixed,
            {
                SealedInt::overflowing_to_fixed(self)
            }
        }
    };
}

impl_int! { i8 }
impl_int! { i16 }
impl_int! { i32 }
impl_int! { i64 }
impl_int! { i128 }
impl_int! { isize }
impl_int! { u8 }
impl_int! { u16 }
impl_int! { u32 }
impl_int! { u64 }
impl_int! { u128 }
impl_int! { usize }

macro_rules! impl_float {
    ($Float:ty) => {
        impl FromFixed for $Float {
            #[inline]
            fn from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                val.to_float()
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: sealed::Fixed,
            {
                Some(val.to_float())
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                val.to_float()
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                val.to_float()
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: sealed::Fixed,
            {
                (val.to_float(), false)
            }
        }

        impl ToFixed for $Float {
            #[inline]
            fn to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedFloat::to_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: sealed::Fixed,
            {
                SealedFloat::checked_to_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedFloat::saturating_to_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedFloat::wrapping_to_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: sealed::Fixed,
            {
                SealedFloat::overflowing_to_fixed(self)
            }
        }
    };
}

#[cfg(feature = "f16")]
impl_float! { f16 }
impl_float! { f32 }
impl_float! { f64 }

macro_rules! trait_delegate {
    (fn $method:ident() -> $Ret:ty) => {
        #[inline]
        fn $method() -> $Ret {
            Self::$method()
        }
    };
    (fn $method:ident(self $(, $param:ident: $Param:ty)*) -> $Ret:ty) => {
        #[inline]
        fn $method(self $(, $param: $Param)*) -> $Ret {
            self.$method($($param),*)
        }
    };
}

macro_rules! impl_fixed {
    ($Fixed:ident, $NBits:ident, $Bits:ident) => {
        impl<Frac> Fixed for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            type Bits = $Bits;
            trait_delegate! { fn min_value() -> Self }
            trait_delegate! { fn max_value() -> Self }
            trait_delegate! { fn int_nbits() -> u32 }
            trait_delegate! { fn frac_nbits() -> u32 }
            #[inline]
            fn from_bits(bits: Self::Bits) -> Self {
                Self::from_bits(bits)
            }
            trait_delegate! { fn to_bits(self) -> Self::Bits }
            trait_delegate! { fn int(self) -> Self }
            trait_delegate! { fn frac(self) -> Self }
            trait_delegate! { fn ceil(self) -> Self }
            trait_delegate! { fn floor(self) -> Self }
            trait_delegate! { fn round(self) -> Self }
            trait_delegate! { fn checked_ceil(self) -> Option<Self> }
            trait_delegate! { fn checked_floor(self) -> Option<Self> }
            trait_delegate! { fn checked_round(self) -> Option<Self> }
            trait_delegate! { fn saturating_ceil(self) -> Self }
            trait_delegate! { fn saturating_floor(self) -> Self }
            trait_delegate! { fn saturating_round(self) -> Self }
            trait_delegate! { fn wrapping_ceil(self) -> Self }
            trait_delegate! { fn wrapping_floor(self) -> Self }
            trait_delegate! { fn wrapping_round(self) -> Self }
            trait_delegate! { fn overflowing_ceil(self) -> (Self, bool) }
            trait_delegate! { fn overflowing_floor(self) -> (Self, bool) }
            trait_delegate! { fn overflowing_round(self) -> (Self, bool) }
            trait_delegate! { fn count_ones(self) -> u32 }
            trait_delegate! { fn count_zeros(self) -> u32 }
            trait_delegate! { fn leading_zeros(self) -> u32 }
            trait_delegate! { fn trailing_zeros(self) -> u32 }
            trait_delegate! { fn rotate_left(self, n: u32) -> Self }
            trait_delegate! { fn rotate_right(self, n: u32) -> Self }
            #[inline]
            fn mul_int(self, rhs: Self::Bits) -> Self {
                self * rhs
            }
            #[inline]
            fn div_int(self, rhs: Self::Bits) -> Self {
                self / rhs
            }
            #[inline]
            fn rem_int(self, rhs: Self::Bits) -> Self {
                self % rhs
            }
            trait_delegate! { fn checked_neg(self) -> Option<Self> }
            trait_delegate! { fn checked_add(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_sub(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_mul(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_div(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_mul_int(self, rhs: Self::Bits) -> Option<Self> }
            trait_delegate! { fn checked_div_int(self, rhs: Self::Bits) -> Option<Self> }
            trait_delegate! { fn checked_rem_int(self, rhs: Self::Bits) -> Option<Self> }
            trait_delegate! { fn checked_shl(self, rhs: u32) -> Option<Self> }
            trait_delegate! { fn checked_shr(self, rhs: u32) -> Option<Self> }
            trait_delegate! { fn saturating_neg(self) -> Self }
            trait_delegate! { fn saturating_add(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_sub(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_mul(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_div(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_mul_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_neg(self) -> Self }
            trait_delegate! { fn wrapping_add(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_sub(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_mul(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_div(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_mul_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_div_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_rem_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_shl(self, rhs: u32) -> Self }
            trait_delegate! { fn wrapping_shr(self, rhs: u32) -> Self }
            trait_delegate! { fn overflowing_neg(self) -> (Self, bool) }
            trait_delegate! { fn overflowing_add(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_sub(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_mul(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_div(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_mul_int(self, rhs: Self::Bits) -> (Self, bool) }
            trait_delegate! { fn overflowing_div_int(self, rhs: Self::Bits) -> (Self, bool) }
            trait_delegate! { fn overflowing_rem_int(self, rhs: Self::Bits) -> (Self, bool) }
            trait_delegate! { fn overflowing_shl(self, rhs: u32) -> (Self, bool) }
            trait_delegate! { fn overflowing_shr(self, rhs: u32) -> (Self, bool) }
        }

        impl<Frac> FromFixed for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                SealedFixed::from_fixed(val)
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: sealed::Fixed,
            {
                SealedFixed::checked_from_fixed(val)
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                SealedFixed::saturating_from_fixed(val)
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: sealed::Fixed,
            {
                SealedFixed::wrapping_from_fixed(val)
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: sealed::Fixed,
            {
                SealedFixed::overflowing_from_fixed(val)
            }
        }

        impl<Frac> ToFixed for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedFixed::from_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: sealed::Fixed,
            {
                SealedFixed::checked_from_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedFixed::saturating_from_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: sealed::Fixed,
            {
                SealedFixed::wrapping_from_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: sealed::Fixed,
            {
                SealedFixed::overflowing_from_fixed(self)
            }
        }
    };
}

macro_rules! impl_fixed_signed {
    ($Fixed:ident, $NBits:ident, $Bits:ident) => {
        impl_fixed! { $Fixed, $NBits, $Bits }

        impl<Frac> FixedSigned for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            trait_delegate! { fn abs(self) -> Self }
            trait_delegate! { fn signum(self) -> Self }
            trait_delegate! { fn checked_abs(self) -> Option<Self> }
            trait_delegate! { fn saturating_abs(self) -> Self }
            trait_delegate! { fn wrapping_abs(self) -> Self }
            trait_delegate! { fn overflowing_abs(self) -> (Self, bool) }
            trait_delegate! { fn is_positive(self) -> bool }
            trait_delegate! { fn is_negative(self) -> bool }
        }
    };
}

macro_rules! impl_fixed_unsigned {
    ($Fixed:ident, $NBits:ident, $Bits:ident) => {
        impl_fixed! { $Fixed, $NBits, $Bits }

        impl<Frac> FixedUnsigned for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            trait_delegate! { fn is_power_of_two(self) -> bool }
            trait_delegate! { fn next_power_of_two(self) -> Self }
            trait_delegate! { fn checked_next_power_of_two(self) -> Option<Self> }
        }
    };
}

impl_fixed_signed! { FixedI8, U8, i8 }
impl_fixed_signed! { FixedI16, U16, i16 }
impl_fixed_signed! { FixedI32, U32, i32 }
impl_fixed_signed! { FixedI64, U64, i64 }
impl_fixed_signed! { FixedI128, U128, i128 }
impl_fixed_unsigned! { FixedU8, U8, u8 }
impl_fixed_unsigned! { FixedU16, U16, u16 }
impl_fixed_unsigned! { FixedU32, U32, u32 }
impl_fixed_unsigned! { FixedU64, U64, u64 }
impl_fixed_unsigned! { FixedU128, U128, u128 }
