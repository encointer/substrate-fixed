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

use crate::sealed::Fixed;

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
        F: Fixed;

    /// Converts from a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_from_fixed<F>(val: F) -> Option<Self>
    where
        F: Fixed,
        Self: Sized;

    /// Converts from a fixed-point number, saturating if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn saturating_from_fixed<F>(val: F) -> Self
    where
        F: Fixed;

    /// Converts from a fixed-point number, wrapping if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn wrapping_from_fixed<F>(val: F) -> Self
    where
        F: Fixed;

    /// Converts from a fixed-point number.
    ///
    /// Returns a tuple of the value and a [`bool`] indicating whether
    /// an overflow has occurred. On overflow, the wrapped value is
    /// returned.
    ///
    /// Any extra fractional bits are truncated.
    ///
    ///[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
    where
        F: Fixed,
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
        F: Fixed;

    /// Converts to a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    fn checked_to_fixed<F>(self) -> Option<F>
    where
        F: Fixed;

    /// Converts to a fixed-point number, saturating if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn saturating_to_fixed<F>(self) -> F
    where
        F: Fixed;

    /// Converts to a fixed-point number, wrapping if it does not fit.
    ///
    /// Any extra fractional bits are truncated.
    fn wrapping_to_fixed<F>(self) -> F
    where
        F: Fixed;

    /// Converts from a fixed-point number.
    ///
    /// Returns a tuple of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// Any extra fractional bits are truncated.
    ///
    ///[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: Fixed;
}
