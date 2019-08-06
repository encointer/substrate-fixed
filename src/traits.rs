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
#[cfg(feature = "f16")]
use half::f16;

/// This trait provides common methods to all fixed-point numbers.
pub trait Fixed: Copy {
    /// The primitive integer underlying type.
    type Bits;

    /// Create with a given bit representation.
    fn from_bits(bits: Self::Bits) -> Self;

    /// Convert to a bit representation.
    fn to_bits(self) -> Self::Bits;
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
    /// Returns a tuple of the value and a [`bool`] indicating whether
    /// an overflow has occurred. On overflow, the wrapped value is
    /// returned.
    ///
    /// Any extra fractional bits are truncated.
    ///
    ///[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
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
    /// Returns a tuple of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// Any extra fractional bits are truncated.
    ///
    ///[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
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

macro_rules! impl_fixed {
    ($Fixed:ident, $NBits:ident, $Bits:ident) => {
        impl<Frac> Fixed for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            type Bits = $Bits;
            #[inline]
            fn from_bits(bits: Self::Bits) -> Self {
                $Fixed::from_bits(bits)
            }
            #[inline]
            fn to_bits(self) -> Self::Bits {
                self.to_bits()
            }
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

impl_fixed! { FixedI8, U8, i8 }
impl_fixed! { FixedI16, U16, i16 }
impl_fixed! { FixedI32, U32, i32 }
impl_fixed! { FixedI64, U64, i64 }
impl_fixed! { FixedI128, U128, i128 }
impl_fixed! { FixedU8, U8, u8 }
impl_fixed! { FixedU16, U16, u16 }
impl_fixed! { FixedU32, U32, u32 }
impl_fixed! { FixedU64, U64, u64 }
impl_fixed! { FixedU128, U128, u128 }
