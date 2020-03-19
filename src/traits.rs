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
    helpers::{FloatHelper, FloatKind, FromFloatHelper, IntHelper, Sealed, Widest},
    types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8, Unsigned},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8, ParseFixedError,
};
use core::{
    fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex},
    hash::Hash,
    mem,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};
#[cfg(feature = "f16")]
use half::{bf16, f16};
#[cfg(feature = "serde")]
use serde::{de::Deserialize, ser::Serialize};

macro_rules! comment_features {
    ($comment:expr) => {
        #[cfg(all(not(feature = "f16"), not(feature = "serde")))]
        doc_comment! {
            $comment;
            pub trait FixedOptionalFeatures {}
        }
        #[cfg(all(feature = "f16", not(feature = "serde")))]
        doc_comment! {
            $comment;
            pub trait FixedOptionalFeatures: PartialOrd<f16> + PartialOrd<bf16> {}
        }
        #[cfg(all(not(feature = "f16"), feature = "serde"))]
        doc_comment! {
            $comment;
            pub trait FixedOptionalFeatures: Serialize + for<'de> Deserialize<'de> {}
        }
        #[cfg(all(feature = "f16", feature = "serde"))]
        doc_comment! {
            $comment;
            pub trait FixedOptionalFeatures
            where
                Self: PartialOrd<f16> + PartialOrd<bf16>,
                Self: Serialize + for<'de> Deserialize<'de>,
            {
            }
        }
    };
}

comment_features! {
    "This trait is used to provide supertraits to the [`Fixed`] trait
depending on the crate’s [optional features].

 1. If the `f16` feature is enabled,
    <code>[PartialOrd][`PartialOrd`]&lt;[f16][`f16`]&gt;</code> and
    <code>[PartialOrd][`PartialOrd`]&lt;[bf16][`bf16`]&gt;</code> are
    supertraits of [`Fixed`].
 2. If the `serde` feature is enabled, [`Serialize`] and
    [`Deserialize`] are supertraits of [`Fixed`].

[`Deserialize`]: https://docs.rs/serde/^1/serde/de/trait.Deserialize.html
[`Fixed`]: trait.Fixed.html
[`PartialOrd`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html
[`Serialize`]: https://docs.rs/serde/^1/serde/ser/trait.Serialize.html
[`bf16`]: https://docs.rs/half/^1/half/struct.bf16.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[optional features]: ../index.html#optional-features
"
}

/// This trait provides methods common to all fixed-point numbers.
///
/// It can be helpful when writing generic code that makes use of
/// fixed-point numbers. For methods only available on signed
/// fixed-point numbers, use the [`FixedSigned`] trait instead, and
/// for methods only available on unsigned fixed-point numbers, use
/// [`FixedUnsigned`].
///
/// This trait is sealed and cannot be implemented for more types; it
/// is implemented for [`FixedI8`], [`FixedI16`], [`FixedI32`],
/// [`FixedI64`], [`FixedI128`], [`FixedU8`], [`FixedU16`],
/// [`FixedU32`], [`FixedU64`], and [`FixedU128`].
///
/// # Examples
///
/// ```rust
/// use substrate_fixed::{
///     traits::Fixed,
///     types::{I8F8, I16F16},
/// };
///
/// fn checked_add_twice<F: Fixed>(lhs: F, rhs: F) -> Option<F> {
///     lhs.checked_add(rhs)?.checked_add(rhs)
/// }
///
/// let val1 = checked_add_twice(I8F8::from_num(5), Fixed::from_num(1.75));
/// assert_eq!(val1, Some(Fixed::from_num(8.5)));
/// // can use with different fixed-point type
/// let val2 = checked_add_twice(I16F16::from_num(5), Fixed::from_num(1.75));
/// assert_eq!(val2, Some(Fixed::from_num(8.5)));
/// ```
///
/// The following example fails to compile, since the compiler cannot
/// infer that 500 in the `checked_mul_int` call is of type `F::Bits`.
///
/// ```compile_fail
/// use substrate_fixed::traits::Fixed;
///
/// fn checked_add_times_500<F: Fixed>(lhs: F, rhs: F) -> Option<F> {
///     rhs.checked_mul_int(500)?.checked_add(lhs)
/// }
/// ```
///
/// One way to fix this is to add a trait bound indicating that any
/// [`u16`] (which can represent 500) can be converted into `F::Bits`.
///
/// ```rust
/// use substrate_fixed::{traits::Fixed, types::U12F4};
///
/// fn checked_add_times_500<F: Fixed>(lhs: F, rhs: F) -> Option<F>
/// where
///     u16: Into<F::Bits>,
/// {
///     rhs.checked_mul_int(500.into())?.checked_add(lhs)
/// }
///
/// let val = checked_add_times_500(U12F4::from_num(0.25), Fixed::from_num(1.5));
/// assert_eq!(val, Some(Fixed::from_num(750.25)));
/// ```
///
/// While this works in most cases, [`u16`] cannot be converted to
/// [`i16`], even if the value 500 does fit in [`i16`], so that the
/// following example would fail to compile.
///
/// ```compile_fail
/// use substrate_fixed::{traits::Fixed, types::I12F4};
///
/// fn checked_add_times_500<F: Fixed>(lhs: F, rhs: F) -> Option<F>
/// where
///     u16: Into<F::Bits>,
/// {
///     rhs.checked_mul_int(500.into())?.checked_add(lhs)
/// }
///
/// // I12F4::Bits is i16, and u16 does not implement Into<i16>
/// let val = checked_add_times_500(I12F4::from_num(0.25), Fixed::from_num(1.5));
/// # let _ = val;
/// ```
///
/// We can use [`TryFrom`] to fix this, as we know that
/// `F::Bits::try_from(500_u16)` will work for both [`u16`] and
/// [`i16`]. (The function will always return [`None`] when `F::Bits`
/// is [`u8`] or [`i8`].)
///
/// ```rust
/// use substrate_fixed::{traits::Fixed, types::I12F4};
/// use core::convert::TryInto;
///
/// fn checked_add_times_500<F: Fixed>(lhs: F, rhs: F) -> Option<F>
/// where
///     u16: TryInto<F::Bits>,
/// {
///     rhs.checked_mul_int(500.try_into().ok()?)?.checked_add(lhs)
/// }
///
/// let val = checked_add_times_500(I12F4::from_num(0.25), Fixed::from_num(1.5));
/// assert_eq!(val, Some(Fixed::from_num(750.25)));
/// ```
///
/// [`FixedI128`]: ../struct.FixedI128.html
/// [`FixedI16`]: ../struct.FixedI16.html
/// [`FixedI32`]: ../struct.FixedI32.html
/// [`FixedI64`]: ../struct.FixedI64.html
/// [`FixedI8`]: ../struct.FixedI8.html
/// [`FixedSigned`]: trait.FixedSigned.html
/// [`FixedU128`]: ../struct.FixedU128.html
/// [`FixedU16`]: ../struct.FixedU16.html
/// [`FixedU32`]: ../struct.FixedU32.html
/// [`FixedU64`]: ../struct.FixedU64.html
/// [`FixedU8`]: ../struct.FixedU8.html
/// [`FixedUnsigned`]: trait.FixedUnsigned.html
/// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
/// [`TryFrom`]: https://doc.rust-lang.org/nightly/core/convert/trait.TryFrom.html
/// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
/// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
/// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
/// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
pub trait Fixed
where
    Self: Copy + Default + Hash + Ord,
    Self: Debug + Display + Binary + Octal + LowerHex + UpperHex,
    Self: FromStr<Err = ParseFixedError>,
    Self: FromFixed + ToFixed,
    Self: Add<Output = Self> + AddAssign + Sub<Output = Self> + SubAssign,
    Self: Mul<Output = Self> + MulAssign + Div<Output = Self> + DivAssign,
    Self: Rem<Output = Self> + RemAssign,
    Self: Mul<<Self as Fixed>::Bits, Output = Self> + MulAssign<<Self as Fixed>::Bits>,
    Self: Div<<Self as Fixed>::Bits, Output = Self> + DivAssign<<Self as Fixed>::Bits>,
    Self: Rem<<Self as Fixed>::Bits, Output = Self> + RemAssign<<Self as Fixed>::Bits>,
    Self: Not<Output = Self> + BitAnd<Output = Self> + BitAndAssign,
    Self: BitOr<Output = Self> + BitOrAssign + BitXor<Output = Self> + BitXorAssign,
    Self: Shl<u32, Output = Self> + ShlAssign<u32> + Shr<u32, Output = Self> + ShrAssign<u32>,
    Self: PartialOrd<i8> + PartialOrd<i16> + PartialOrd<i32>,
    Self: PartialOrd<i64> + PartialOrd<i128> + PartialOrd<isize>,
    Self: PartialOrd<u8> + PartialOrd<u16> + PartialOrd<u32>,
    Self: PartialOrd<u64> + PartialOrd<u128> + PartialOrd<usize>,
    Self: PartialOrd<f32> + PartialOrd<f64>,
    Self: FixedOptionalFeatures,
    Self: Sealed,
{
    /// The primitive integer underlying type.
    type Bits;

    /// A byte array with the same size as the type.
    type Bytes;

    /// The number of fractional bits.
    ///
    /// <code>&lt;F as [Fixed]&gt;::Frac::[U32]</code> is equivalent to
    /// <code>&lt;F as [Fixed]&gt;::[frac_nbits][`frac_nbits`]()</code>.
    ///
    /// [Fixed]: trait.Fixed.html
    /// [U32]: ../types/extra/trait.Unsigned.html#associatedconstant.U32
    /// [`frac_nbits`]: #tymethod.frac_nbits
    type Frac: Unsigned;

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

    /// Creates a fixed-point number from its representation as a byte
    /// array in big endian.
    fn from_be_bytes(bytes: Self::Bytes) -> Self;

    /// Creates a fixed-point number from its representation as a byte
    /// array in little endian.
    fn from_le_bytes(bytes: Self::Bytes) -> Self;

    /// Creates a fixed-point number from its representation as a byte
    /// array in native endian.
    fn from_ne_bytes(bytes: Self::Bytes) -> Self;

    /// Returns the memory representation of this fixed-point number
    /// as a byte array in big-endian byte order.
    fn to_be_bytes(self) -> Self::Bytes;

    /// Returns the memory representation of this fixed-point number
    /// as a byte array in little-endian byte order.
    fn to_le_bytes(self) -> Self::Bytes;

    /// Returns the memory representation of this fixed-point number
    /// as a byte array in native byte order.
    fn to_ne_bytes(self) -> Self::Bytes;

    /// Creates a fixed-point number from another number.
    ///
    /// Returns the same value as [`src.to_fixed()`][`to_fixed`].
    ///
    /// [`to_fixed`]: trait.ToFixed.html#tymethod.to_fixed
    fn from_num<Src: ToFixed>(src: Src) -> Self;

    /// Converts a fixed-point number to another number.
    ///
    /// Returns the same value as [`Dst::from_fixed(self)`][`from_fixed`].
    ///
    /// [`from_fixed`]: trait.FromFixed.html#tymethod.from_fixed
    fn to_num<Dst: FromFixed>(self) -> Dst;

    /// Creates a fixed-point number from another number if it fits,
    /// otherwise returns [`None`].
    ///
    /// Returns the same value as [`src.checked_to_fixed()`][`checked_to_fixed`].
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    /// [`checked_to_fixed`]: trait.ToFixed.html#tymethod.checked_to_fixed
    fn checked_from_num<Src: ToFixed>(src: Src) -> Option<Self>;

    /// Converts a fixed-point number to another number if it fits,
    /// otherwise returns [`None`].
    ///
    /// Returns the same value as [`Dst::checked_from_fixed(self)`][`checked_from_fixed`].
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    /// [`checked_from_fixed`]: trait.FromFixed.html#tymethod.checked_from_fixed
    fn checked_to_num<Dst: FromFixed>(self) -> Option<Dst>;

    /// Creates a fixed-point number from another number, saturating the
    /// value if it does not fit.
    ///
    /// Returns the same value as [`src.saturating_to_fixed()`][`saturating_to_fixed`].
    ///
    /// [`saturating_to_fixed`]: trait.ToFixed.html#tymethod.saturating_to_fixed
    fn saturating_from_num<Src: ToFixed>(src: Src) -> Self;

    /// Converts a fixed-point number to another number, saturating the
    /// value if it does not fit.
    ///
    /// Returns the same value as [`Dst::saturating_from_fixed(self)`][`saturating_from_fixed`].
    ///
    /// [`saturating_from_fixed`]: trait.FromFixed.html#tymethod.saturating_from_fixed
    fn saturating_to_num<Dst: FromFixed>(self) -> Dst;

    /// Creates a fixed-point number from another number, wrapping the
    /// value on overflow.
    ///
    /// Returns the same value as [`src.wrapping_to_fixed()`][`wrapping_to_fixed`].
    ///
    /// [`wrapping_to_fixed`]: trait.ToFixed.html#tymethod.wrapping_to_fixed
    fn wrapping_from_num<Src: ToFixed>(src: Src) -> Self;

    /// Converts a fixed-point number to another number, wrapping the
    /// value on overflow.
    ///
    /// Returns the same value as [`Src::wrapping_from_fixed(self)`][`wrapping_from_fixed`].
    ///
    /// [`wrapping_from_fixed`]: trait.FromFixed.html#tymethod.wrapping_from_fixed
    fn wrapping_to_num<Dst: FromFixed>(self) -> Dst;

    /// Creates a fixed-point number from another number.
    ///
    /// Returns the same value as [`src.overflowing_to_fixed()`][`overflowing_to_fixed`].
    ///
    /// [`overflowing_to_fixed`]: trait.ToFixed.html#tymethod.overflowing_to_fixed
    fn overflowing_from_num<Src: ToFixed>(src: Src) -> (Self, bool);

    /// Converts a fixed-point number to another number.
    ///
    /// Returns the same value as [`Dst::overflowing_from_fixed(self)`][`overflowing_from_fixed`].
    ///
    /// [`overflowing_from_fixed`]: trait.FromFixed.html#tymethod.overflowing_from_fixed
    fn overflowing_to_num<Dst: FromFixed>(self) -> (Dst, bool);

    /// Parses a string slice containing binary digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn from_str_binary(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing octal digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn from_str_octal(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing hexadecimal digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn from_str_hex(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing decimal digits to return a
    /// fixed-point number, saturating on overflow.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn saturating_from_str(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing binary digits to return a
    /// fixed-point number, saturating on overflow.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn saturating_from_str_binary(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing octal digits to return a
    /// fixed-point number, saturating on overflow.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn saturating_from_str_octal(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing hexadecimal digits to return a
    /// fixed-point number, saturating on overflow.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn saturating_from_str_hex(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing decimal digits to return a
    /// fixed-point number, wrapping on overflow.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn wrapping_from_str(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing binary digits to return a
    /// fixed-point number, wrapping on overflow.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn wrapping_from_str_binary(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing octal digits to return a
    /// fixed-point number, wrapping on overflow.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn wrapping_from_str_octal(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing hexadecimal digits to return a
    /// fixed-point number, wrapping on overflow.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    fn wrapping_from_str_hex(src: &str) -> Result<Self, ParseFixedError>;

    /// Parses a string slice containing decimal digits to return a
    /// fixed-point number.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_from_str(src: &str) -> Result<(Self, bool), ParseFixedError>;

    /// Parses a string slice containing binary digits to return a
    /// fixed-point number.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_from_str_binary(src: &str) -> Result<(Self, bool), ParseFixedError>;

    /// Parses a string slice containing octal digits to return a
    /// fixed-point number.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_from_str_octal(src: &str) -> Result<(Self, bool), ParseFixedError>;

    /// Parses a string slice containing hexadecimal digits to return a
    /// fixed-point number.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_from_str_hex(src: &str) -> Result<(Self, bool), ParseFixedError>;

    /// Returns the integer part.
    fn int(self) -> Self;

    /// Returns the fractional part.
    fn frac(self) -> Self;

    /// Rounds to the next integer towards 0.
    fn round_to_zero(self) -> Self;

    /// Rounds to the next integer towards +∞.
    fn ceil(self) -> Self;

    /// Rounds to the next integer towards −∞.
    fn floor(self) -> Self;

    /// Rounds to the nearest integer, with ties rounded away from zero.
    fn round(self) -> Self;

    /// Rounds to the nearest integer, with ties rounded to even.
    fn round_ties_to_even(self) -> Self;

    /// Checked ceil. Rounds to the next integer towards +∞, returning
    /// [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_ceil(self) -> Option<Self>;

    /// Checked floor. Rounds to the next integer towards −∞, returning
    /// [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_floor(self) -> Option<Self>;

    /// Checked round. Rounds to the nearest integer, with ties
    /// rounded away from zero, returning [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_round(self) -> Option<Self>;

    /// Checked round. Rounds to the nearest integer, with ties
    /// rounded to even, returning [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_round_ties_to_even(self) -> Option<Self>;

    /// Saturating ceil. Rounds to the next integer towards +∞,
    /// saturating on overflow.
    fn saturating_ceil(self) -> Self;

    /// Saturating floor. Rounds to the next integer towards −∞,
    /// saturating on overflow.
    fn saturating_floor(self) -> Self;

    /// Saturating round. Rounds to the nearest integer, with ties
    /// rounded away from zero, and saturating on overflow.
    fn saturating_round(self) -> Self;

    /// Saturating round. Rounds to the nearest integer, with ties
    /// rounded to_even, and saturating on overflow.
    fn saturating_round_ties_to_even(self) -> Self;

    /// Wrapping ceil. Rounds to the next integer towards +∞, wrapping
    /// on overflow.
    fn wrapping_ceil(self) -> Self;

    /// Wrapping floor. Rounds to the next integer towards −∞,
    /// wrapping on overflow.
    fn wrapping_floor(self) -> Self;

    /// Wrapping round. Rounds to the next integer to the nearest,
    /// with ties rounded away from zero, and wrapping on overflow.
    fn wrapping_round(self) -> Self;

    /// Wrapping round. Rounds to the next integer to the nearest,
    /// with ties rounded to even, and wrapping on overflow.
    fn wrapping_round_ties_to_even(self) -> Self;

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

    /// Overflowing round. Rounds to the next integer to the nearest,
    /// with ties rounded to even.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`],
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_round_ties_to_even(self) -> (Self, bool);

    /// Returns the number of ones in the binary representation.
    fn count_ones(self) -> u32;

    /// Returns the number of zeros in the binary representation.
    fn count_zeros(self) -> u32;

    /// Returns the number of leading zeros in the binary representation.
    fn leading_zeros(self) -> u32;

    /// Returns the number of trailing zeros in the binary representation.
    fn trailing_zeros(self) -> u32;

    /// Shifts to the left by `n` bits, wrapping the truncated bits to the right end.
    fn rotate_left(self, n: u32) -> Self;

    /// Shifts to the right by `n` bits, wrapping the truncated bits to the left end.
    fn rotate_right(self, n: u32) -> Self;

    /// Euclidean division by an integer.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero or if the division results in overflow.
    fn div_euclid(self, rhs: Self) -> Self;

    /// Remainder for Euclidean division.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn rem_euclid(self, rhs: Self) -> Self;

    /// Euclidean division by an integer.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero or if the division results in overflow.
    fn div_euclid_int(self, rhs: Self::Bits) -> Self;

    /// Remainder for Euclidean division by an integer.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero or if the division results in overflow.
    fn rem_euclid_int(self, rhs: Self::Bits) -> Self;

    /// Checked negation. Returns the negated value, or [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_neg(self) -> Option<Self>;

    /// Checked addition. Returns the sum, or [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_add(self, rhs: Self) -> Option<Self>;

    /// Checked subtraction. Returns the difference, or [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_sub(self, rhs: Self) -> Option<Self>;

    /// Checked multiplication. Returns the product, or [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_mul(self, rhs: Self) -> Option<Self>;

    /// Checked division. Returns the quotient, or [`None`] if the
    /// divisor is zero or on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_div(self, rhs: Self) -> Option<Self>;

    /// Checked remainder. Returns the remainder, or [`None`] if the
    /// divisor is zero.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_rem(self, rhs: Self) -> Option<Self>;

    /// Checked remainder for Euclidean division. Returns the
    /// remainder, or [`None`] if the divisor is zero or the division
    /// results in overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_div_euclid(self, rhs: Self) -> Option<Self>;

    /// Checked remainder for Euclidean division. Returns the
    /// remainder, or [`None`] if the divisor is zero.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_rem_euclid(self, rhs: Self) -> Option<Self>;

    /// Checked multiplication by an integer. Returns the product, or
    /// [`None`] on overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_mul_int(self, rhs: Self::Bits) -> Option<Self>;

    /// Checked division by an integer. Returns the quotient, or
    /// [`None`] if the divisor is zero or if the division results in
    /// overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_div_int(self, rhs: Self::Bits) -> Option<Self>;

    /// Checked fixed-point remainder for division by an integer.
    /// Returns the remainder, or [`None`] if the divisor is zero or
    /// if the division results in overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_rem_int(self, rhs: Self::Bits) -> Option<Self>;

    /// Checked Euclidean division by an integer. Returns the
    /// quotient, or [`None`] if the divisor is zero or if the
    /// division results in overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_div_euclid_int(self, rhs: Self::Bits) -> Option<Self>;

    /// Checked remainder for Euclidean division by an integer.
    /// Returns the remainder, or [`None`] if the divisor is zero or
    /// if the remainder results in overflow.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_rem_euclid_int(self, rhs: Self::Bits) -> Option<Self>;

    /// Checked shift left. Returns the shifted number, or [`None`] if
    /// `rhs` ≥ the number of bits.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_shl(self, rhs: u32) -> Option<Self>;

    /// Checked shift right. Returns the shifted number, or [`None`]
    /// if `rhs` ≥ the number of bits.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
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

    /// Saturating Euclidean division. Returns the quotient, saturating on overflow.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn saturating_div_euclid(self, rhs: Self) -> Self;

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

    /// Wrapping Euclidean division. Returns the quotient, wrapping on overflow.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn wrapping_div_euclid(self, rhs: Self) -> Self;

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

    /// Wrapping Euclidean division by an integer. Returns the
    /// quotient, wrapping on overflow.
    ///
    /// Overflow can only occur when dividing the minimum value by −1.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn wrapping_div_euclid_int(self, rhs: Self::Bits) -> Self;

    /// Wrapping remainder for Euclidean division by an integer.
    /// Returns the remainder, wrapping on overflow.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    fn wrapping_rem_euclid_int(self, rhs: Self::Bits) -> Self;

    /// Wrapping shift left. Wraps `rhs` if `rhs` ≥ the number of
    /// bits, then shifts and returns the number.
    fn wrapping_shl(self, rhs: u32) -> Self;

    /// Wrapping shift right. Wraps `rhs` if `rhs` ≥ the number of
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

    /// Overflowing Euclidean division.
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
    fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool);

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

    /// Overflowing Euclidean division by an integer.
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
    fn overflowing_div_euclid_int(self, rhs: Self::Bits) -> (Self, bool);

    /// Overflowing remainder for Euclidean division by an integer.
    ///
    /// Returns a [tuple] of the remainder and a [`bool`], indicating
    /// whether an overflow has occurred. On overflow, the wrapped
    /// value is returned.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_rem_euclid_int(self, rhs: Self::Bits) -> (Self, bool);

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

    /// Remainder for division by an integer.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    #[deprecated(
        since = "0.5.3",
        note = "cannot overflow, use `%` or `Rem::rem` instead"
    )]
    fn wrapping_rem_int(self, rhs: Self::Bits) -> Self {
        self % rhs
    }

    /// Remainder for division by an integer.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    #[deprecated(
        since = "0.5.3",
        note = "cannot overflow, use `%` or `Rem::rem` instead"
    )]
    fn overflowing_rem_int(self, rhs: Self::Bits) -> (Self, bool) {
        (self % rhs, false)
    }
}

/// This trait provides methods common to all signed fixed-point numbers.
///
/// Methods common to all fixed-point numbers including unsigned
/// fixed-point numbers are provided by the [`Fixed`] supertrait.
///
/// This trait is sealed and cannot be implemented for more types; it
/// is implemented for [`FixedI8`], [`FixedI16`], [`FixedI32`],
/// [`FixedI64`], and [`FixedI128`].
///
/// [`FixedI128`]: ../struct.FixedI128.html
/// [`FixedI16`]: ../struct.FixedI16.html
/// [`FixedI32`]: ../struct.FixedI32.html
/// [`FixedI64`]: ../struct.FixedI64.html
/// [`FixedI8`]: ../struct.FixedI8.html
/// [`Fixed`]: trait.Fixed.html
pub trait FixedSigned: Fixed + Neg<Output = Self> {
    /// Returns [`true`][`bool`] if the number is > 0.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    fn is_positive(self) -> bool;

    /// Returns [`true`][`bool`] if the number is < 0.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    fn is_negative(self) -> bool;

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
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
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
}

/// This trait provides methods common to all unsigned fixed-point numbers.
///
/// Methods common to all fixed-point numbers including signed
/// fixed-point numbers are provided by the [`Fixed`] supertrait.
///
/// This trait is sealed and cannot be implemented for more types; it
/// is implemented for [`FixedU8`], [`FixedU16`], [`FixedU32`],
/// [`FixedU64`], and [`FixedU128`].
///
/// [`FixedU128`]: ../struct.FixedU128.html
/// [`FixedU16`]: ../struct.FixedU16.html
/// [`FixedU32`]: ../struct.FixedU32.html
/// [`FixedU64`]: ../struct.FixedU64.html
/// [`FixedU8`]: ../struct.FixedU8.html
/// [`Fixed`]: trait.Fixed.html
pub trait FixedUnsigned: Fixed {
    /// Returns [`true`][`bool`] if the fixed-point number is
    /// 2<sup><i>k</i></sup> for some integer <i>k</i>.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    fn is_power_of_two(self) -> bool;

    /// Returns the smallest power of two that is ≥ `self`.
    fn next_power_of_two(self) -> Self;

    /// Returns the smallest power of two that is ≥ `self`, or [`None`] if the
    /// next power of two is too large to represent.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
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
/// use substrate_fixed::traits::LossyFrom;
/// use substrate_fixed::types::{I12F4, I4F60};
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
/// use substrate_fixed::traits::LossyInto;
/// use substrate_fixed::types::{I12F4, I4F12};
/// // original is 0x1.234
/// let original = I4F12::from_bits(0x1234);
/// let lossy: I12F4 = original.lossy_into();
/// assert_eq!(lossy, I12F4::from_bits(0x0012));
/// ```
///
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
/// [`Into`]: https://doc.rust-lang.org/nightly/core/convert/trait.Into.html
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
/// use substrate_fixed::traits::FromFixed;
/// use substrate_fixed::types::U8F8;
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
    fn from_fixed<F: Fixed>(src: F) -> Self;

    /// Converts from a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_from_fixed<F: Fixed>(src: F) -> Option<Self>
    where
        Self: Sized;

    /// Converts from a fixed-point number, saturating if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn saturating_from_fixed<F: Fixed>(src: F) -> Self;

    /// Converts from a fixed-point number, wrapping if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn wrapping_from_fixed<F: Fixed>(src: F) -> Self;

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
    fn overflowing_from_fixed<F: Fixed>(src: F) -> (Self, bool)
    where
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
/// use substrate_fixed::traits::ToFixed;
/// use substrate_fixed::types::{U8F8, U16F16};
/// let f: U8F8 = 13.5f32.to_fixed();
/// assert_eq!(f, U8F8::from_bits((13 << 8) | (1 << 7)));
/// // 0x1234.5678 is too large and can be wrapped to 0x34.56
/// let too_large = U16F16::from_bits(0x1234_5678);
/// let checked: Option<U8F8> = too_large.checked_to_num();
/// assert_eq!(checked, None);
/// let saturating: U8F8 = too_large.saturating_to_num();
/// assert_eq!(saturating, U8F8::max_value());
/// let wrapping: U8F8 = too_large.wrapping_to_num();
/// assert_eq!(wrapping, U8F8::from_bits(0x3456));
/// let overflowing: (U8F8, bool) = too_large.overflowing_to_num();
/// assert_eq!(overflowing, (U8F8::from_bits(0x3456), true));
/// ```
pub trait ToFixed {
    /// Converts to a fixed-point number.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Panics
    ///
    /// Panics if `self` is a floating-point number that is not [finite].
    ///
    /// When debug assertions are enabled, also panics if the value
    /// does not fit. When debug assertions are not enabled, the
    /// wrapped value can be returned, but it is not considered a
    /// breaking change if in the future it panics; if wrapping is
    /// required use [`wrapping_to_fixed`] instead.
    ///
    /// [`wrapping_to_fixed`]: #method.wrapping_to_fixed
    /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    fn to_fixed<F: Fixed>(self) -> F;

    /// Converts to a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    fn checked_to_fixed<F: Fixed>(self) -> Option<F>;

    /// Converts to a fixed-point number, saturating if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Panics
    ///
    /// Panics if `self` is a floating-point number that is [NaN].
    ///
    /// [NaN]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_nan
    fn saturating_to_fixed<F: Fixed>(self) -> F;

    /// Converts to a fixed-point number, wrapping if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Panics
    ///
    /// Panics if `self` is a floating-point number that is not [finite].
    ///
    /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    fn wrapping_to_fixed<F: Fixed>(self) -> F;

    /// Converts to a fixed-point number.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Panics
    ///
    /// Panics if `self` is a floating-point number that is not [finite].
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool);
}

impl ToFixed for bool {
    /// Converts a [`bool`] to a fixed-point number.
    ///
    /// # Panics
    ///
    /// When debug assertions are enabled, panics if the value does
    /// not fit. When debug assertions are not enabled, the wrapped
    /// value can be returned, but it is not considered a breaking
    /// change if in the future it panics; if wrapping is required use
    /// [`wrapping_to_fixed`] instead.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [`wrapping_to_fixed`]: #method.wrapping_to_fixed
    #[inline]
    fn to_fixed<F: Fixed>(self) -> F {
        ToFixed::to_fixed(self as u8)
    }

    /// Converts a [`bool`] to a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    fn checked_to_fixed<F: Fixed>(self) -> Option<F> {
        ToFixed::checked_to_fixed(self as u8)
    }

    /// Convert a [`bool`] to a fixed-point number, saturating if it does not fit.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    fn saturating_to_fixed<F: Fixed>(self) -> F {
        ToFixed::saturating_to_fixed(self as u8)
    }

    /// Converts a [`bool`] to a fixed-point number, wrapping if it does not fit.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    fn wrapping_to_fixed<F: Fixed>(self) -> F {
        ToFixed::wrapping_to_fixed(self as u8)
    }

    /// Converts a [`bool`] to a fixed-point number.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
    #[inline]
    fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool) {
        ToFixed::overflowing_to_fixed(self as u8)
    }
}

macro_rules! impl_int {
    ($Int:ident) => {
        impl FromFixed for $Int {
            /// Converts a fixed-point number to an integer.
            ///
            /// Any fractional bits are truncated.
            ///
            /// # Panics
            ///
            /// When debug assertions are enabled, panics if the value
            /// does not fit. When debug assertions are not enabled,
            /// the wrapped value can be returned, but it is not
            /// considered a breaking change if in the future it
            /// panics; if wrapping is required use
            /// [`wrapping_from_fixed`] instead.
            ///
            /// [`wrapping_from_fixed`]: #method.wrapping_from_fixed
            #[inline]
            fn from_fixed<F: Fixed>(src: F) -> Self {
                $Int::from_repr_fixed(FromFixed::from_fixed(src))
            }

            /// Converts a fixed-point number to an integer if it fits, otherwise returns [`None`].
            ///
            /// Any fractional bits are truncated.
            ///
            /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
            #[inline]
            fn checked_from_fixed<F: Fixed>(src: F) -> Option<Self> {
                FromFixed::checked_from_fixed(src).map($Int::from_repr_fixed)
            }

            /// Converts a fixed-point number to an integer, saturating if it does not fit.
            ///
            /// Any fractional bits are truncated.
            #[inline]
            fn saturating_from_fixed<F: Fixed>(src: F) -> Self {
                $Int::from_repr_fixed(FromFixed::saturating_from_fixed(src))
            }

            /// Converts a fixed-point number to an integer, wrapping if it does not fit.
            ///
            /// Any fractional bits are truncated.
            #[inline]
            fn wrapping_from_fixed<F: Fixed>(src: F) -> Self {
                $Int::from_repr_fixed(FromFixed::wrapping_from_fixed(src))
            }

            /// Converts a fixed-point number to an integer.
            ///
            /// Returns a [tuple] of the value and a [`bool`] indicating whether
            /// an overflow has occurred. On overflow, the wrapped value is
            /// returned.
            ///
            /// Any fractional bits are truncated.
            ///
            /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
            /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
            #[inline]
            fn overflowing_from_fixed<F: Fixed>(src: F) -> (Self, bool) {
                let (repr_fixed, overflow) = FromFixed::overflowing_from_fixed(src);
                ($Int::from_repr_fixed(repr_fixed), overflow)
            }
        }

        impl ToFixed for $Int {
            /// Converts an integer to a fixed-point number.
            ///
            /// # Panics
            ///
            /// When debug assertions are enabled, panics if the value
            /// does not fit. When debug assertions are not enabled,
            /// the wrapped value can be returned, but it is not
            /// considered a breaking change if in the future it
            /// panics; if wrapping is required use
            /// [`wrapping_to_fixed`] instead.
            ///
            /// [`wrapping_to_fixed`]: #method.wrapping_to_fixed
            #[inline]
            fn to_fixed<F: Fixed>(self) -> F {
                ToFixed::to_fixed(self.to_repr_fixed())
            }

            /// Converts an integer to a fixed-point number if it fits, otherwise returns [`None`].
            ///
            /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
            #[inline]
            fn checked_to_fixed<F: Fixed>(self) -> Option<F> {
                ToFixed::checked_to_fixed(self.to_repr_fixed())
            }

            /// Converts an integer to a fixed-point number, saturating if it does not fit.
            #[inline]
            fn saturating_to_fixed<F: Fixed>(self) -> F {
                ToFixed::saturating_to_fixed(self.to_repr_fixed())
            }

            /// Converts an integer to a fixed-point number, wrapping if it does not fit.
            #[inline]
            fn wrapping_to_fixed<F: Fixed>(self) -> F {
                ToFixed::wrapping_to_fixed(self.to_repr_fixed())
            }

            /// Converts an integer to a fixed-point number.
            ///
            /// Returns a [tuple] of the fixed-point number and a [`bool`]
            /// indicating whether an overflow has occurred. On overflow, the
            /// wrapped value is returned.
            ///
            /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
            /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
            #[inline]
            fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool) {
                ToFixed::overflowing_to_fixed(self.to_repr_fixed())
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
            /// Converts a fixed-point number to a floating-point number.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// # Panics
            ///
            /// When debug assertions are enabled, panics if the value
            /// does not fit. When debug assertions are not enabled,
            /// the wrapped value can be returned, but it is not
            /// considered a breaking change if in the future it
            /// panics; if wrapping is required use
            /// [`wrapping_from_fixed`] instead.
            ///
            /// [`wrapping_from_fixed`]: #method.wrapping_from_fixed
            #[inline]
            fn from_fixed<F: Fixed>(src: F) -> Self {
                let helper = src.private_to_float_helper();
                FloatHelper::from_to_float_helper(helper, F::frac_nbits(), F::int_nbits())
            }

            /// Converts a fixed-point number to a floating-point
            /// number if it fits, otherwise returns [`None`].
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
            #[inline]
            fn checked_from_fixed<F: Fixed>(src: F) -> Option<Self> {
                Some(FromFixed::from_fixed(src))
            }

            /// Converts a fixed-point number to a floating-point
            /// number, saturating if it does not fit.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            #[inline]
            fn saturating_from_fixed<F: Fixed>(src: F) -> Self {
                FromFixed::from_fixed(src)
            }

            /// Converts a fixed-point number to a floating-point
            /// number, wrapping if it does not fit.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            #[inline]
            fn wrapping_from_fixed<F: Fixed>(src: F) -> Self {
                FromFixed::from_fixed(src)
            }

            /// Converts a fixed-point number to a floating-point number.
            ///
            /// Returns a [tuple] of the value and a [`bool`]
            /// indicating whether an overflow has occurred. On
            /// overflow, the wrapped value is returned.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
            /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
            #[inline]
            fn overflowing_from_fixed<F: Fixed>(src: F) -> (Self, bool) {
                (FromFixed::from_fixed(src), false)
            }
        }

        impl ToFixed for $Float {
            /// Converts a floating-point number to a fixed-point number.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// # Panics
            ///
            /// Panics if `self` is not [finite].
            ///
            /// When debug assertions are enabled, also panics if the
            /// value does not fit. When debug assertions are not
            /// enabled, the wrapped value can be returned, but it is
            /// not considered a breaking change if in the future it
            /// panics; if wrapping is required use
            /// [`wrapping_to_fixed`] instead.
            ///
            /// [`wrapping_to_fixed`]: #method.wrapping_to_fixed
            /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
            #[inline]
            fn to_fixed<F: Fixed>(self) -> F {
                let (wrapped, overflow) = ToFixed::overflowing_to_fixed(self);
                debug_assert!(!overflow, "{} overflows", self);
                let _ = overflow;
                wrapped
            }

            /// Converts a floating-point number to a fixed-point
            /// number if it fits, otherwise returns [`None`].
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
            #[inline]
            fn checked_to_fixed<F: Fixed>(self) -> Option<F> {
                let kind = self.to_float_kind(F::frac_nbits(), F::int_nbits());
                match kind {
                    FloatKind::Finite { .. } => {
                        let helper = FromFloatHelper { kind };
                        match F::private_overflowing_from_float_helper(helper) {
                            (_, true) => None,
                            (wrapped, false) => Some(wrapped),
                        }
                    }
                    _ => None,
                }
            }

            /// Converts a floating-point number to a fixed-point
            /// number, saturating if it does not fit.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// # Panics
            ///
            /// Panics if `self` is [NaN].
            ///
            /// [NaN]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_nan
            #[inline]
            fn saturating_to_fixed<F: Fixed>(self) -> F {
                let kind = self.to_float_kind(F::frac_nbits(), F::int_nbits());
                let helper = FromFloatHelper { kind };
                F::private_saturating_from_float_helper(helper)
            }

            /// Converts a floating-point number to a fixed-point
            /// number, wrapping if it does not fit.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// # Panics
            ///
            /// Panics if `self` is not [finite].
            ///
            /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
            #[inline]
            fn wrapping_to_fixed<F: Fixed>(self) -> F {
                let (wrapped, _) = ToFixed::overflowing_to_fixed(self);
                wrapped
            }

            /// Converts a floating-point number to a fixed-point number.
            ///
            /// Returns a [tuple] of the fixed-point number and a [`bool`]
            /// indicating whether an overflow has occurred. On overflow, the
            /// wrapped value is returned.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// # Panics
            ///
            /// Panics if `self` is not [finite].
            ///
            /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
            /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
            /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
            #[inline]
            fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool) {
                let kind = self.to_float_kind(F::frac_nbits(), F::int_nbits());
                let helper = FromFloatHelper { kind };
                F::private_overflowing_from_float_helper(helper)
            }
        }
    };
}

#[cfg(feature = "f16")]
impl_float! { f16 }
#[cfg(feature = "f16")]
impl_float! { bf16 }
impl_float! { f32 }
impl_float! { f64 }

macro_rules! trait_delegate {
    (fn $method:ident($($param:ident: $Param:ty),*) -> $Ret:ty) => {
        #[inline]
        fn $method($($param: $Param),*) -> $Ret {
            Self::$method($($param),*)
        }
    };
    (fn $method:ident(self $(, $param:ident: $Param:ty)*) -> $Ret:ty) => {
        #[inline]
        fn $method(self $(, $param: $Param)*) -> $Ret {
            self.$method($($param),*)
        }
    };
    (fn $method:ident<$Gen:ident: $Trait:ident>($($param:ident: $Param:ty),*) -> $Ret:ty) => {
        #[inline]
        fn $method<$Gen: $Trait>($($param: $Param),*) -> $Ret {
            Self::$method($($param),*)
        }
    };
    (fn $method:ident<$Gen:ident: $Trait:ident>(self $(, $param:ident: $Param:ty)*) -> $Ret:ty) => {
        #[inline]
        fn $method<$Gen: $Trait>(self $(, $param: $Param)*) -> $Ret {
            self.$method($($param),*)
        }
    };
}

macro_rules! impl_fixed {
    ($Fixed:ident, $LeEqU:ident, $Bits:ident, $Signedness:tt) => {
        impl<Frac: $LeEqU> FixedOptionalFeatures for $Fixed<Frac> {}

        impl<Frac: $LeEqU> Fixed for $Fixed<Frac> {
            type Bits = $Bits;
            type Bytes = [u8; mem::size_of::<$Bits>()];
            type Frac = Frac;
            trait_delegate! { fn min_value() -> Self }
            trait_delegate! { fn max_value() -> Self }
            trait_delegate! { fn int_nbits() -> u32 }
            trait_delegate! { fn frac_nbits() -> u32 }
            trait_delegate! { fn from_bits(bits: Self::Bits) -> Self }
            trait_delegate! { fn to_bits(self) -> Self::Bits }
            trait_delegate! { fn from_be_bytes(bits: Self::Bytes) -> Self }
            trait_delegate! { fn from_le_bytes(bits: Self::Bytes) -> Self }
            trait_delegate! { fn from_ne_bytes(bits: Self::Bytes) -> Self }
            trait_delegate! { fn to_be_bytes(self) -> Self::Bytes }
            trait_delegate! { fn to_le_bytes(self) -> Self::Bytes }
            trait_delegate! { fn to_ne_bytes(self) -> Self::Bytes }
            trait_delegate! { fn from_num<Src: ToFixed>(src: Src) -> Self }
            trait_delegate! { fn to_num<Dst: FromFixed>(self) -> Dst }
            trait_delegate! { fn checked_from_num<Src: ToFixed>(val: Src) -> Option<Self> }
            trait_delegate! { fn checked_to_num<Dst: FromFixed>(self) -> Option<Dst> }
            trait_delegate! { fn saturating_from_num<Src: ToFixed>(val: Src) -> Self }
            trait_delegate! { fn saturating_to_num<Dst: FromFixed>(self) -> Dst }
            trait_delegate! { fn wrapping_from_num<Src: ToFixed>(val: Src) -> Self }
            trait_delegate! { fn wrapping_to_num<Dst: FromFixed>(self) -> Dst }
            trait_delegate! { fn overflowing_from_num<Src: ToFixed>(val: Src) -> (Self, bool) }
            trait_delegate! { fn overflowing_to_num<Dst: FromFixed>(self) -> (Dst, bool) }
            trait_delegate! { fn from_str_binary(src: &str) -> Result<Self, ParseFixedError> }
            trait_delegate! { fn from_str_octal(src: &str) -> Result<Self, ParseFixedError> }
            trait_delegate! { fn from_str_hex(src: &str) -> Result<Self, ParseFixedError> }
            trait_delegate! {
                fn saturating_from_str(src: &str) -> Result<Self, ParseFixedError>
            }
            trait_delegate! {
                fn saturating_from_str_binary(src: &str) -> Result<Self, ParseFixedError>
            }
            trait_delegate! {
                fn saturating_from_str_octal(src: &str) -> Result<Self, ParseFixedError>
            }
            trait_delegate! {
                fn saturating_from_str_hex(src: &str) -> Result<Self, ParseFixedError>
            }
            trait_delegate! {
                fn wrapping_from_str(src: &str) -> Result<Self, ParseFixedError>
            }
            trait_delegate! {
                fn wrapping_from_str_binary(src: &str) -> Result<Self, ParseFixedError>
            }
            trait_delegate! {
                fn wrapping_from_str_octal(src: &str) -> Result<Self, ParseFixedError>
            }
            trait_delegate! {
                fn wrapping_from_str_hex(src: &str) -> Result<Self, ParseFixedError>
            }
            trait_delegate! {
                fn overflowing_from_str(src: &str) -> Result<(Self, bool), ParseFixedError>
            }
            trait_delegate! {
                fn overflowing_from_str_binary(src: &str) -> Result<(Self, bool), ParseFixedError>
            }
            trait_delegate! {
                fn overflowing_from_str_octal(src: &str) -> Result<(Self, bool), ParseFixedError>
            }
            trait_delegate! {
                fn overflowing_from_str_hex(src: &str) -> Result<(Self, bool), ParseFixedError>
            }
            trait_delegate! { fn int(self) -> Self }
            trait_delegate! { fn frac(self) -> Self }
            trait_delegate! { fn ceil(self) -> Self }
            trait_delegate! { fn floor(self) -> Self }
            trait_delegate! { fn round_to_zero(self) -> Self }
            trait_delegate! { fn round(self) -> Self }
            trait_delegate! { fn round_ties_to_even(self) -> Self }
            trait_delegate! { fn checked_ceil(self) -> Option<Self> }
            trait_delegate! { fn checked_floor(self) -> Option<Self> }
            trait_delegate! { fn checked_round(self) -> Option<Self> }
            trait_delegate! { fn checked_round_ties_to_even(self) -> Option<Self> }
            trait_delegate! { fn saturating_ceil(self) -> Self }
            trait_delegate! { fn saturating_floor(self) -> Self }
            trait_delegate! { fn saturating_round(self) -> Self }
            trait_delegate! { fn saturating_round_ties_to_even(self) -> Self }
            trait_delegate! { fn wrapping_ceil(self) -> Self }
            trait_delegate! { fn wrapping_floor(self) -> Self }
            trait_delegate! { fn wrapping_round(self) -> Self }
            trait_delegate! { fn wrapping_round_ties_to_even(self) -> Self }
            trait_delegate! { fn overflowing_ceil(self) -> (Self, bool) }
            trait_delegate! { fn overflowing_floor(self) -> (Self, bool) }
            trait_delegate! { fn overflowing_round(self) -> (Self, bool) }
            trait_delegate! { fn overflowing_round_ties_to_even(self) -> (Self, bool) }
            trait_delegate! { fn count_ones(self) -> u32 }
            trait_delegate! { fn count_zeros(self) -> u32 }
            trait_delegate! { fn leading_zeros(self) -> u32 }
            trait_delegate! { fn trailing_zeros(self) -> u32 }
            trait_delegate! { fn rotate_left(self, n: u32) -> Self }
            trait_delegate! { fn rotate_right(self, n: u32) -> Self }
            trait_delegate! { fn div_euclid(self, rhs: Self) -> Self }
            trait_delegate! { fn rem_euclid(self, rhs: Self) -> Self }
            trait_delegate! { fn div_euclid_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn rem_euclid_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn checked_neg(self) -> Option<Self> }
            trait_delegate! { fn checked_add(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_sub(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_mul(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_div(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_rem(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_div_euclid(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_rem_euclid(self, rhs: Self) -> Option<Self> }
            trait_delegate! { fn checked_mul_int(self, rhs: Self::Bits) -> Option<Self> }
            trait_delegate! { fn checked_div_int(self, rhs: Self::Bits) -> Option<Self> }
            trait_delegate! { fn checked_rem_int(self, rhs: Self::Bits) -> Option<Self> }
            trait_delegate! { fn checked_div_euclid_int(self, rhs: Self::Bits) -> Option<Self> }
            trait_delegate! { fn checked_rem_euclid_int(self, rhs: Self::Bits) -> Option<Self> }
            trait_delegate! { fn checked_shl(self, rhs: u32) -> Option<Self> }
            trait_delegate! { fn checked_shr(self, rhs: u32) -> Option<Self> }
            trait_delegate! { fn saturating_neg(self) -> Self }
            trait_delegate! { fn saturating_add(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_sub(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_mul(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_div(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_div_euclid(self, rhs: Self) -> Self }
            trait_delegate! { fn saturating_mul_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_neg(self) -> Self }
            trait_delegate! { fn wrapping_add(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_sub(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_mul(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_div(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_div_euclid(self, rhs: Self) -> Self }
            trait_delegate! { fn wrapping_mul_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_div_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_div_euclid_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_rem_euclid_int(self, rhs: Self::Bits) -> Self }
            trait_delegate! { fn wrapping_shl(self, rhs: u32) -> Self }
            trait_delegate! { fn wrapping_shr(self, rhs: u32) -> Self }
            trait_delegate! { fn overflowing_neg(self) -> (Self, bool) }
            trait_delegate! { fn overflowing_add(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_sub(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_mul(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_div(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) }
            trait_delegate! { fn overflowing_mul_int(self, rhs: Self::Bits) -> (Self, bool) }
            trait_delegate! { fn overflowing_div_int(self, rhs: Self::Bits) -> (Self, bool) }
            trait_delegate! { fn overflowing_div_euclid_int(self, rhs: Self::Bits) -> (Self, bool) }
            trait_delegate! { fn overflowing_rem_euclid_int(self, rhs: Self::Bits) -> (Self, bool) }
            trait_delegate! { fn overflowing_shl(self, rhs: u32) -> (Self, bool) }
            trait_delegate! { fn overflowing_shr(self, rhs: u32) -> (Self, bool) }
        }

        impl<Frac: $LeEqU> FromFixed for $Fixed<Frac> {
            /// Converts a fixed-point number.
            ///
            /// Any extra fractional bits are truncated.
            #[inline]
            fn from_fixed<F: Fixed>(src: F) -> Self {
                let (wrapped, overflow) = FromFixed::overflowing_from_fixed(src);
                debug_assert!(!overflow, "{} overflows", src);
                let _ = overflow;
                wrapped
            }

            /// Converts a fixed-point number if it fits, otherwise returns [`None`].
            ///
            /// Any extra fractional bits are truncated.
            ///
            /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
            #[inline]
            fn checked_from_fixed<F: Fixed>(src: F) -> Option<Self> {
                match FromFixed::overflowing_from_fixed(src) {
                    (_, true) => None,
                    (wrapped, false) => Some(wrapped),
                }
            }

            /// Converts a fixed-point number, saturating if it does not fit.
            ///
            /// Any extra fractional bits are truncated.
            #[inline]
            fn saturating_from_fixed<F: Fixed>(src: F) -> Self {
                let conv = src.private_to_fixed_helper(Self::FRAC_NBITS, Self::INT_NBITS);
                if conv.overflow {
                    return if src < 0 {
                        Self::min_value()
                    } else {
                        Self::max_value()
                    };
                }
                let bits = if_signed_unsigned! {
                    $Signedness,
                    match conv.bits {
                        Widest::Unsigned(bits) => {
                            if (bits as $Bits) < 0 {
                                return Self::max_value();
                            }
                            bits as $Bits
                        }
                        Widest::Negative(bits) => bits as $Bits,
                    },
                    match conv.bits {
                        Widest::Unsigned(bits) => bits as $Bits,
                        Widest::Negative(_) => {
                            return Self::min_value();
                        }
                    },
                };
                Self::from_bits(bits)
            }

            /// Converts a fixed-point number, wrapping if it does not fit.
            ///
            /// Any extra fractional bits are truncated.
            #[inline]
            fn wrapping_from_fixed<F: Fixed>(src: F) -> Self {
                let (wrapped, _) = FromFixed::overflowing_from_fixed(src);
                wrapped
            }

            /// Converts a fixed-point number.
            ///
            /// Returns a [tuple] of the value and a [`bool`]
            /// indicating whether an overflow has occurred. On
            /// overflow, the wrapped value is returned.
            ///
            /// Any extra fractional bits are truncated.
            ///
            /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
            /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
            #[inline]
            fn overflowing_from_fixed<F: Fixed>(src: F) -> (Self, bool) {
                let conv = src.private_to_fixed_helper(Self::FRAC_NBITS, Self::INT_NBITS);
                let mut new_overflow = false;
                let bits = if_signed_unsigned! {
                    $Signedness,
                    match conv.bits {
                        Widest::Unsigned(bits) => {
                            if (bits as $Bits) < 0 {
                                new_overflow = true;
                            }
                            bits as $Bits
                        }
                        Widest::Negative(bits) => bits as $Bits,
                    },
                    match conv.bits {
                        Widest::Unsigned(bits) => bits as $Bits,
                        Widest::Negative(bits) => {
                            new_overflow = true;
                            bits as $Bits
                        }
                    },
                };
                (Self::from_bits(bits), conv.overflow || new_overflow)
            }
        }

        impl<Frac: $LeEqU> ToFixed for $Fixed<Frac> {
            /// Converts a fixed-point number.
            ///
            /// Any extra fractional bits are truncated.
            #[inline]
            fn to_fixed<F: Fixed>(self) -> F {
                FromFixed::from_fixed(self)
            }

            /// Converts a fixed-point number if it fits, otherwise returns [`None`].
            ///
            /// Any extra fractional bits are truncated.
            ///
            /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
            #[inline]
            fn checked_to_fixed<F: Fixed>(self) -> Option<F> {
                FromFixed::checked_from_fixed(self)
            }

            /// Converts a fixed-point number, saturating if it does not fit.
            ///
            /// Any extra fractional bits are truncated.
            #[inline]
            fn saturating_to_fixed<F: Fixed>(self) -> F {
                FromFixed::saturating_from_fixed(self)
            }

            /// Converts a fixed-point number, wrapping if it does not fit.
            ///
            /// Any extra fractional bits are truncated.
            #[inline]
            fn wrapping_to_fixed<F: Fixed>(self) -> F {
                FromFixed::wrapping_from_fixed(self)
            }

            /// Converts a fixed-point number.
            ///
            /// Returns a [tuple] of the value and a [`bool`]
            /// indicating whether an overflow has occurred. On
            /// overflow, the wrapped value is returned.
            ///
            /// Any extra fractional bits are truncated.
            ///
            /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
            /// [tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
            #[inline]
            fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool) {
                FromFixed::overflowing_from_fixed(self)
            }
        }

        if_signed! {
            $Signedness;
            impl<Frac: $LeEqU> FixedSigned for $Fixed<Frac> {
                trait_delegate! { fn abs(self) -> Self }
                trait_delegate! { fn signum(self) -> Self }
                trait_delegate! { fn checked_abs(self) -> Option<Self> }
                trait_delegate! { fn saturating_abs(self) -> Self }
                trait_delegate! { fn wrapping_abs(self) -> Self }
                trait_delegate! { fn overflowing_abs(self) -> (Self, bool) }
                trait_delegate! { fn is_positive(self) -> bool }
                trait_delegate! { fn is_negative(self) -> bool }
            }
        }

        if_unsigned! {
            $Signedness;
            impl<Frac: $LeEqU> FixedUnsigned for $Fixed<Frac> {
                trait_delegate! { fn is_power_of_two(self) -> bool }
                trait_delegate! { fn next_power_of_two(self) -> Self }
                trait_delegate! { fn checked_next_power_of_two(self) -> Option<Self> }
            }
        }
    };
}

impl_fixed! { FixedI8, LeEqU8, i8, Signed }
impl_fixed! { FixedI16, LeEqU16, i16, Signed }
impl_fixed! { FixedI32, LeEqU32, i32, Signed }
impl_fixed! { FixedI64, LeEqU64, i64, Signed }
impl_fixed! { FixedI128, LeEqU128, i128, Signed }
impl_fixed! { FixedU8, LeEqU8, u8, Unsigned }
impl_fixed! { FixedU16, LeEqU16, u16, Unsigned }
impl_fixed! { FixedU32, LeEqU32, u32, Unsigned }
impl_fixed! { FixedU64, LeEqU64, u64, Unsigned }
impl_fixed! { FixedU128, LeEqU128, u128, Unsigned }
