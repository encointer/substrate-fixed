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
This module contains sealed traits.
*/

use frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8};
#[cfg(feature = "f16")]
use half::f16;
pub(crate) use sealed_fixed::{SealedFixed, Widest};
pub(crate) use sealed_float::SealedFloat;
pub(crate) use sealed_int::SealedInt;
use traits::{CheckedFromFixed, CheckedToFixed};
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

/// This trait is implemented for all the primitive integer types.
///
/// This trait is sealed and cannot be implemented for more types; it
/// is implemented for [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
/// [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
/// [`usize`].
///
/// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
/// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
/// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
/// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
/// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
/// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
/// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
/// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
/// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
/// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
/// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
/// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
pub trait Int: SealedInt + CheckedFromFixed + CheckedToFixed {
    /// Converts from a fixed-point number.
    ///
    /// Any fractional bits are truncated.
    ///
    /// # Panics
    ///
    /// When debug assertions are enabled, panics if the value does
    /// not fit. When debug assertions are not enabled, the wrapped
    /// value can be returned, but it is not considered a breaking
    /// change if in the future it panics; if wrapping is required use
    /// [`wrapping_from_fixed`] instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// let fix = Fix::from_bits(-3 << 8 | 5);
    /// assert_eq!(i32::from_fixed(fix), -3);
    /// ```
    ///
    /// [`wrapping_from_fixed`]: #method.wrapping_from_fixed
    #[inline]
    fn from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        let (wrapped, overflow) = <Self as SealedInt>::overflowing_from_fixed(val);
        debug_assert!(!overflow, "{} overflows", val);
        let _ = overflow;
        wrapped
    }

    /// Converts to a fixed-point number.
    ///
    /// # Panics
    ///
    /// When debug assertions are enabled, panics if the value does
    /// not fit. When debug assertions are not enabled, the wrapped
    /// value can be returned, but it is not considered a breaking
    /// change if in the future it panics; if wrapping is required use
    /// [`wrapping_to_fixed`] instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// let fix: Fix = 3.to_fixed();
    /// assert_eq!(fix, Fix::from_bits(3 << 8));
    /// ```
    ///
    /// [`wrapping_to_fixed`]: #method.wrapping_to_fixed
    #[inline]
    fn to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        let (wrapped, overflow) = <Self as SealedInt>::overflowing_to_fixed(self);
        debug_assert!(!overflow, "{} overflows", self);
        let _ = overflow;
        wrapped
    }

    /// Converts from a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// let fix = Fix::from_bits(-3 << 8 | 5);
    /// assert_eq!(i32::checked_from_fixed(fix), Some(-3));
    /// assert!(u32::checked_from_fixed(fix).is_none());
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    #[inline]
    fn checked_from_fixed<F>(val: F) -> Option<Self>
    where
        F: Fixed,
    {
        match <Self as SealedInt>::overflowing_from_fixed(val) {
            (wrapped, false) => Some(wrapped),
            (_, true) => None,
        }
    }

    /// Converts to a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// assert_eq!(3.checked_to_fixed::<Fix>(), Some(Fix::from_bits(3 << 8)));
    /// assert!(i32::max_value().checked_to_fixed::<Fix>().is_none());
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    #[inline]
    fn checked_to_fixed<F>(self) -> Option<F>
    where
        F: Fixed,
    {
        match <Self as SealedInt>::overflowing_to_fixed(self) {
            (wrapped, false) => Some(wrapped),
            (_, true) => None,
        }
    }

    /// Converts from a fixed-point number, saturating if it does not
    /// fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// let fix = Fix::from_bits(-3 << 8 | 5);
    /// assert_eq!(i32::saturating_from_fixed(fix), -3);
    /// assert_eq!(u32::saturating_from_fixed(fix), 0);
    /// ```
    #[inline]
    fn saturating_from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        match <Self as SealedInt>::overflowing_from_fixed(val) {
            (wrapped, false) => wrapped,
            (_, true) => {
                if val.to_bits().is_negative() {
                    Self::min_value()
                } else {
                    Self::max_value()
                }
            }
        }
    }

    /// Converts to a fixed-point number, saturating if it does not
    /// fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedU16<fixed::frac::U8>;
    /// assert_eq!(3i64.saturating_to_fixed::<Fix>(), Fix::from_bits(3 << 8));
    /// assert_eq!((-1i8).saturating_to_fixed::<Fix>(), Fix::min_value());
    /// ```
    #[inline]
    fn saturating_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        match <Self as SealedInt>::overflowing_to_fixed(self) {
            (wrapped, false) => wrapped,
            (_, true) => {
                if self.is_negative() {
                    F::from_bits(<F as SealedFixed>::Bits::min_value())
                } else {
                    F::from_bits(<F as SealedFixed>::Bits::max_value())
                }
            }
        }
    }

    /// Converts from a fixed-point number, wrapping if it does not
    /// fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// let fix = Fix::from_bits(-3 << 8 | 5);
    /// assert_eq!(i32::wrapping_from_fixed(fix), -3);
    /// assert_eq!(u32::wrapping_from_fixed(fix), 3u32.wrapping_neg());
    /// ```
    #[inline]
    fn wrapping_from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        let (wrapped, _) = <Self as SealedInt>::overflowing_from_fixed(val);
        wrapped
    }

    /// Converts to a fixed-point number, wrapping if it does not fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedU16<fixed::frac::U8>;
    /// assert_eq!(3i64.wrapping_to_fixed::<Fix>(), Fix::from_bits(3 << 8));
    /// assert_eq!((-1i8).wrapping_to_fixed::<Fix>(), Fix::from_bits(0xff00));
    /// ```
    #[inline]
    fn wrapping_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        let (wrapped, _) = <Self as SealedInt>::overflowing_to_fixed(self);
        wrapped
    }

    /// Converts from a fixed-point number.
    ///
    /// Returns a tuple of the integer and a [`bool`] indicating
    /// whether an overflow has occurred. On overflow, the wrapped
    /// value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// let fix = Fix::from_bits(-3 << 8 | 5);
    /// assert_eq!(i32::overflowing_from_fixed(fix), (-3, false));
    /// assert_eq!(u32::overflowing_from_fixed(fix), (3u32.wrapping_neg(), true));
    /// ```
    ///
    ///[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
    where
        F: Fixed,
    {
        <Self as SealedInt>::overflowing_from_fixed(val)
    }

    /// Converts to a fixed-point number.
    ///
    /// Returns a tuple of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Int;
    /// type Fix = fixed::FixedU16<fixed::frac::U8>;
    /// assert_eq!(3i64.overflowing_to_fixed::<Fix>(), (Fix::from_bits(3 << 8), false));
    /// assert_eq!((-1i8).overflowing_to_fixed::<Fix>(), (Fix::from_bits(0xff00), true));
    /// ```
    ///
    ///[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: Fixed,
    {
        <Self as SealedInt>::overflowing_to_fixed(self)
    }
}

/// This trait is implemented for the primitive floating-point types,
/// and for [`f16`] if the [`f16` feature] is enabled.
///
/// This trait is sealed and cannot be implemented for more types; it
/// is implemented for [`f32`] and [`f64`], and for [`f16`] if the
/// [`f16` feature] is enabled.
///
/// [`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
/// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
/// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
/// [`f16` feature]: ../index.html#optional-features
pub trait Float: SealedFloat + CheckedToFixed {
    /// Converts from a fixed-point number.
    ///
    /// This method rounds to the nearest, with ties rounding to even.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Float;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// // 1.625 is 1.101 in binary
    /// let fix = Fix::from_bits(0b1101 << (8 - 3));
    /// assert_eq!(f32::from_fixed(fix), 1.625);
    /// ```
    #[inline]
    fn from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        val.to_float()
    }

    /// Converts to a fixed-point number.
    ///
    /// This method rounds to the nearest, with ties rounding to even.
    ///
    /// # Panics
    ///
    /// Panics if the value is not [finite].
    ///
    /// When debug assertions are enabled, also panics if the value
    /// does not fit. When debug assertions are not enabled, the
    /// wrapped value can be returned, but it is not considered a
    /// breaking change if in the future it panics; if wrapping is
    /// required use [`wrapping_to_fixed`] instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Float;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// // 1.625 is 1.101 in binary
    /// let fix: Fix = 1.625.to_fixed();
    /// assert_eq!(fix, Fix::from_bits(0b1101 << (8 - 3)));
    /// ```
    ///
    /// [`wrapping_to_fixed`]: #method.wrapping_to_fixed
    /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    #[inline]
    fn to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        let (wrapped, overflow) = <Self as SealedFloat>::overflowing_to_fixed(self);
        debug_assert!(!overflow, "{} overflows", self);
        let _ = overflow;
        wrapped
    }

    /// Converts to a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Float;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// // 1.625 is 1.101 in binary
    /// let checked_fix: Option<Fix> = 1.625f32.checked_to_fixed();
    /// let one_point_625 = Fix::from_bits(0b1101 << (8 - 3));
    /// assert_eq!(checked_fix, Some(one_point_625));
    /// assert!(1000f32.checked_to_fixed::<Fix>().is_none());
    /// assert!(std::f64::NAN.checked_to_fixed::<Fix>().is_none());
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    #[inline]
    fn checked_to_fixed<F>(self) -> Option<F>
    where
        F: Fixed,
    {
        if !self.is_finite() {
            return None;
        }
        match <Self as SealedFloat>::overflowing_to_fixed(self) {
            (wrapped, false) => Some(wrapped),
            (_, true) => None,
        }
    }

    /// Converts to a fixed-point number, saturating if it does not
    /// fit.
    ///
    /// # Panics
    ///
    /// This method panics if the value is [NaN].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Float;
    /// type Fix = fixed::FixedI16<fixed::frac::U8>;
    /// // 1.625 is 1.101 in binary
    /// let fix: Fix = 1.625f32.saturating_to_fixed();
    /// assert_eq!(fix, Fix::from_bits(0b1101 << (8 - 3)));
    /// let neg_inf_to_fixed: Fix = std::f64::NEG_INFINITY.saturating_to_fixed();
    /// assert_eq!(neg_inf_to_fixed, Fix::min_value());
    /// ```
    ///
    /// [NaN]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_nan
    #[inline]
    fn saturating_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        assert!(!self.is_nan(), "NaN");
        let saturated = if self.is_sign_negative() {
            F::from_bits(<F as SealedFixed>::Bits::min_value())
        } else {
            F::from_bits(<F as SealedFixed>::Bits::max_value())
        };
        if !self.is_finite() {
            return saturated;
        }
        match <Self as SealedFloat>::overflowing_to_fixed(self) {
            (wrapped, false) => wrapped,
            (_, true) => saturated,
        }
    }

    /// Converts to a fixed-point number, wrapping if it does not fit.
    ///
    /// # Panics
    ///
    /// This method panics if the value is not [finite].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Float;
    /// type Fix = fixed::FixedU16<fixed::frac::U8>;
    /// // 6.5 is 110.1 in binary
    /// let six_point_5 = Fix::from_bits(0b1101 << (8 - 1));
    /// assert_eq!(6.5f32.wrapping_to_fixed::<Fix>(), six_point_5);
    /// // 1030.5 = 1024 + 6.5, 1024 is a power of 2 that will be wrapped
    /// assert_eq!(1030.5f64.wrapping_to_fixed::<Fix>(), six_point_5);
    /// ```
    ///
    /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    #[inline]
    fn wrapping_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        let (wrapped, _) = <Self as SealedFloat>::overflowing_to_fixed(self);
        wrapped
    }

    /// Converts to a fixed-point number.
    ///
    /// Returns a tuple of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// # Panics
    ///
    /// This method panics if the value is not [finite].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Float;
    /// type Fix = fixed::FixedU16<fixed::frac::U8>;
    /// // 6.5 is 110.1 in binary
    /// let six_point_5 = Fix::from_bits(0b1101 << (8 - 1));
    /// assert_eq!(6.5f32.overflowing_to_fixed::<Fix>(), (six_point_5, false));
    /// // 1030.5 = 1024 + 6.5, 1024 is a power of 2 that will be wrapped
    /// assert_eq!(1030.5f64.overflowing_to_fixed::<Fix>(), (six_point_5, true));
    /// ```
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    #[inline]
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: Fixed,
    {
        <Self as SealedFloat>::overflowing_to_fixed(self)
    }
}

/// This trait is implemented for all the fixed-point types.
///
/// This trait is sealed and cannot be implemented for more types; it
/// is implemented for [`FixedI8`], [`FixedI16`], [`FixedI32`],
/// [`FixedI64`], [`FixedI128`], [`FixedU8`], [`FixedU16`],
/// [`FixedU32`], [`FixedU64`], and [`FixedU128`].
///
/// [`FixedI128`]: ../struct.FixedI128.html
/// [`FixedI16`]: ../struct.FixedI16.html
/// [`FixedI32`]: ../struct.FixedI32.html
/// [`FixedI64`]: ../struct.FixedI64.html
/// [`FixedI8`]: ../struct.FixedI8.html
/// [`FixedU128`]: ../struct.FixedU128.html
/// [`FixedU16`]: ../struct.FixedU16.html
/// [`FixedU32`]: ../struct.FixedU32.html
/// [`FixedU64`]: ../struct.FixedU64.html
/// [`FixedU8`]: ../struct.FixedU8.html
pub trait Fixed: SealedFixed + CheckedFromFixed + CheckedToFixed {
    /// Converts from another fixed-point number which can have a
    /// different type.
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
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = Src::from_bits(0b111 << (16 - 2));
    /// let dst: Dst = Fixed::from_fixed(src);
    /// assert_eq!(dst, Dst::from_bits(0b111 << (4 - 2)));
    /// // src >> 4 is 0.000111, which for Dst is truncated to 0.0001
    /// let trunc: Dst = Fixed::from_fixed(src >> 4);
    /// assert_eq!(trunc, Dst::from_bits(1));
    /// ```
    ///
    /// [`wrapping_from_fixed`]: #method.wrapping_from_fixed
    #[inline]
    fn from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        let (wrapped, overflow) = <Self as SealedFixed>::overflowing_from_fixed(val);
        debug_assert!(!overflow, "{} overflows", val);
        let _ = overflow;
        wrapped
    }

    /// Converts to another fixed-point number which can have a
    /// different type.
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
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// fn erase_type(a: impl Fixed) -> impl Fixed { a }
    ///
    /// type Src = fixed::FixedI16<fixed::frac::U6>;
    /// type Dst = fixed::FixedI32<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = erase_type(Src::from_bits(0b111 << (6 - 2)));
    /// let dst: Dst = src.to_fixed();
    /// assert_eq!(dst, Dst::from_bits(0b111 << (4 - 2)));
    /// // src >> 4 is 0.000111, which for Dst is truncated to 0.0001
    /// let shifted = erase_type(Src::from_bits(0b111 << (6 - 2)) >> 4);
    /// let trunc: Dst = shifted.to_fixed();
    /// assert_eq!(trunc, Dst::from_bits(1));
    /// ```
    ///
    /// [`wrapping_to_fixed`]: #method.wrapping_to_fixed
    #[inline]
    fn to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        let (wrapped, overflow) = <F as SealedFixed>::overflowing_from_fixed(self);
        debug_assert!(!overflow, "{} overflows", self);
        let _ = overflow;
        wrapped
    }

    /// Converts from a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = Src::from_bits(0b111 << (16 - 2));
    /// let dst: Option<Dst> = Fixed::checked_from_fixed(src);
    /// assert_eq!(dst, Some(Dst::from_bits(0b111 << (4 - 2))));
    /// let too_large = Src::max_value();
    /// let no_fit: Option<Dst> = Fixed::checked_from_fixed(too_large);
    /// assert!(no_fit.is_none());
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    #[inline]
    fn checked_from_fixed<F>(val: F) -> Option<Self>
    where
        F: Fixed,
    {
        let (wrapped, overflow) = <Self as SealedFixed>::overflowing_from_fixed(val);
        if overflow {
            None
        } else {
            Some(wrapped)
        }
    }

    /// Converts to a fixed-point number if it fits, otherwise returns [`None`].
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// fn erase_type(a: impl Fixed) -> impl Fixed { a }
    ///
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = erase_type(Src::from_bits(0b111 << (16 - 2)));
    /// let dst: Option<Dst> = src.checked_to_fixed();
    /// assert_eq!(dst, Some(Dst::from_bits(0b111 << (4 - 2))));
    /// let too_large = erase_type(Src::max_value());
    /// let no_fit: Option<Dst> = too_large.checked_to_fixed();
    /// assert!(no_fit.is_none());
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    #[inline]
    fn checked_to_fixed<F>(self) -> Option<F>
    where
        F: Fixed,
    {
        match <F as SealedFixed>::overflowing_from_fixed(self) {
            (wrapped, false) => Some(wrapped),
            (_, true) => None,
        }
    }

    /// Converts from a fixed-point number, saturating if it does not
    /// fit.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = Src::from_bits(0b111 << (16 - 2));
    /// let dst: Dst = Fixed::saturating_from_fixed(src);
    /// assert_eq!(dst, Dst::from_bits(0b111 << (4 - 2)));
    /// let too_large = Src::max_value();
    /// let sat_max: Dst = Fixed::saturating_from_fixed(too_large);
    /// assert_eq!(sat_max, Dst::max_value());
    /// let too_small = Src::min_value();
    /// let sat_min: Dst = Fixed::saturating_from_fixed(too_small);
    /// assert_eq!(sat_min, Dst::min_value());
    /// ```
    #[inline]
    fn saturating_from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        <Self as SealedFixed>::saturating_from_fixed(val)
    }

    /// Converts to a fixed-point number, saturating if it does not
    /// fit.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// fn erase_type(a: impl Fixed) -> impl Fixed { a }
    ///
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = erase_type(Src::from_bits(0b111 << (16 - 2)));
    /// let dst: Dst = src.saturating_to_fixed();
    /// assert_eq!(dst, Dst::from_bits(0b111 << (4 - 2)));
    /// let too_large = erase_type(Src::max_value());
    /// let sat_max: Dst = too_large.saturating_to_fixed();
    /// assert_eq!(sat_max, Dst::max_value());
    /// let too_small = erase_type(Src::min_value());
    /// let sat_min: Dst = too_small.saturating_to_fixed();
    /// assert_eq!(sat_min, Dst::min_value());
    /// ```
    #[inline]
    fn saturating_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        <F as SealedFixed>::saturating_from_fixed(self)
    }

    /// Converts from a fixed-point number, wrapping if it does not
    /// fit.
    ///
    /// Any extra fractional bits are truncated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = Src::from_bits(0b111 << (16 - 2));
    /// let dst: Dst = Fixed::wrapping_from_fixed(src);
    /// assert_eq!(dst, Dst::from_bits(0b111 << (4 - 2)));
    /// // 0x1234.5678 is wrapped and truncated to 0x234.5
    /// let too_large = Src::from_bits(0x1234_5678);
    /// let wrapped: Dst = Fixed::wrapping_from_fixed(too_large);
    /// assert_eq!(wrapped, Dst::from_bits(0x2345));
    /// ```
    #[inline]
    fn wrapping_from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        let (wrapped, _) = <Self as SealedFixed>::overflowing_from_fixed(val);
        wrapped
    }

    /// Converts to a fixed-point number, wrapping if it does not fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// fn erase_type(a: impl Fixed) -> impl Fixed { a }
    ///
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = erase_type(Src::from_bits(0b111 << (16 - 2)));
    /// let dst: Dst = src.wrapping_to_fixed();
    /// assert_eq!(dst, Dst::from_bits(0b111 << (4 - 2)));
    /// // 0x1234.5678 is wrapped and truncated to 0x234.5
    /// let too_large = erase_type(Src::from_bits(0x1234_5678));
    /// let wrapped: Dst = too_large.wrapping_to_fixed();
    /// assert_eq!(wrapped, Dst::from_bits(0x2345));
    /// ```
    #[inline]
    fn wrapping_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        let (wrapped, _) = <F as SealedFixed>::overflowing_from_fixed(self);
        wrapped
    }

    /// Converts from a fixed-point number.
    ///
    /// Returns a tuple of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = Src::from_bits(0b111 << (16 - 2));
    /// let dst: (Dst, bool) = Fixed::overflowing_from_fixed(src);
    /// assert_eq!(dst, (Dst::from_bits(0b111 << (4 - 2)), false));
    /// // 0x1234.5678 is wrapped and truncated to 0x234.5
    /// let too_large = Src::from_bits(0x1234_5678);
    /// let wrapped: (Dst, bool) = Fixed::overflowing_from_fixed(too_large);
    /// assert_eq!(wrapped, (Dst::from_bits(0x2345), true));
    /// ```
    ///
    ///[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
    where
        F: Fixed,
    {
        <Self as SealedFixed>::overflowing_from_fixed(val)
    }

    /// Converts to a fixed-point number.
    ///
    /// Returns a tuple of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::sealed::Fixed;
    /// fn erase_type(a: impl Fixed) -> impl Fixed { a }
    ///
    /// type Src = fixed::FixedI32<fixed::frac::U16>;
    /// type Dst = fixed::FixedI16<fixed::frac::U4>;
    /// // 1.75 is 1.11 in binary
    /// let src = erase_type(Src::from_bits(0b111 << (16 - 2)));
    /// let dst: (Dst, bool) = src.overflowing_to_fixed();
    /// assert_eq!(dst, (Dst::from_bits(0b111 << (4 - 2)), false));
    /// // 0x1234.5678 is wrapped and truncated to 0x234.5
    /// let too_large = erase_type(Src::from_bits(0x1234_5678));
    /// let wrapped: (Dst, bool) = too_large.overflowing_to_fixed();
    /// assert_eq!(wrapped, (Dst::from_bits(0x2345), true));
    /// ```
    ///
    ///[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: Fixed,
    {
        <F as SealedFixed>::overflowing_from_fixed(self)
    }
}

impl Int for i8 {}
impl Int for i16 {}
impl Int for i32 {}
impl Int for i64 {}
impl Int for i128 {}
impl Int for isize {}
impl Int for u8 {}
impl Int for u16 {}
impl Int for u32 {}
impl Int for u64 {}
impl Int for u128 {}
impl Int for usize {}

#[cfg(feature = "f16")]
impl Float for f16 {}
impl Float for f32 {}
impl Float for f64 {}

impl<Frac> Fixed for FixedI8<Frac> where Frac: Unsigned + IsLessOrEqual<U8, Output = True> {}
impl<Frac> Fixed for FixedI16<Frac> where Frac: Unsigned + IsLessOrEqual<U16, Output = True> {}
impl<Frac> Fixed for FixedI32<Frac> where Frac: Unsigned + IsLessOrEqual<U32, Output = True> {}
impl<Frac> Fixed for FixedI64<Frac> where Frac: Unsigned + IsLessOrEqual<U64, Output = True> {}
impl<Frac> Fixed for FixedI128<Frac> where Frac: Unsigned + IsLessOrEqual<U128, Output = True> {}
impl<Frac> Fixed for FixedU8<Frac> where Frac: Unsigned + IsLessOrEqual<U8, Output = True> {}
impl<Frac> Fixed for FixedU16<Frac> where Frac: Unsigned + IsLessOrEqual<U16, Output = True> {}
impl<Frac> Fixed for FixedU32<Frac> where Frac: Unsigned + IsLessOrEqual<U32, Output = True> {}
impl<Frac> Fixed for FixedU64<Frac> where Frac: Unsigned + IsLessOrEqual<U64, Output = True> {}
impl<Frac> Fixed for FixedU128<Frac> where Frac: Unsigned + IsLessOrEqual<U128, Output = True> {}

impl CheckedToFixed for bool {
    #[inline]
    fn to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        Int::to_fixed(self as u8)
    }
    #[inline]
    fn checked_to_fixed<F>(self) -> Option<F>
    where
        F: Fixed,
    {
        Int::checked_to_fixed(self as u8)
    }
    #[inline]
    fn saturating_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        Int::saturating_to_fixed(self as u8)
    }
    #[inline]
    fn wrapping_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        Int::wrapping_to_fixed(self as u8)
    }
    #[inline]
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: Fixed,
    {
        Int::overflowing_to_fixed(self as u8)
    }
}

macro_rules! checked_int {
    ($Int:ty) => {
        impl CheckedFromFixed for $Int {
            #[inline]
            fn from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Int::from_fixed(val)
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: Fixed,
            {
                Int::checked_from_fixed(val)
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Int::saturating_from_fixed(val)
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Int::wrapping_from_fixed(val)
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: Fixed,
            {
                Int::overflowing_from_fixed(val)
            }
        }

        impl CheckedToFixed for $Int {
            #[inline]
            fn to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Int::to_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: Fixed,
            {
                Int::checked_to_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Int::saturating_to_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Int::wrapping_to_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed,
            {
                Int::overflowing_to_fixed(self)
            }
        }
    };
}

checked_int! { i8 }
checked_int! { i16 }
checked_int! { i32 }
checked_int! { i64 }
checked_int! { i128 }
checked_int! { isize }
checked_int! { u8 }
checked_int! { u16 }
checked_int! { u32 }
checked_int! { u64 }
checked_int! { u128 }
checked_int! { usize }

macro_rules! checked_fixed {
    ($Fixed:ident, $NBits:ident) => {
        impl<Frac> CheckedFromFixed for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Fixed::from_fixed(val)
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: Fixed,
            {
                Fixed::checked_from_fixed(val)
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Fixed::saturating_from_fixed(val)
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Fixed::wrapping_from_fixed(val)
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: Fixed,
            {
                Fixed::overflowing_from_fixed(val)
            }
        }

        impl<Frac> CheckedToFixed for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Fixed::to_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: Fixed,
            {
                Fixed::checked_to_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Fixed::saturating_to_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Fixed::wrapping_to_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed,
            {
                Fixed::overflowing_to_fixed(self)
            }
        }
    };
}

checked_fixed! { FixedI8, U8 }
checked_fixed! { FixedI16, U16 }
checked_fixed! { FixedI32, U32 }
checked_fixed! { FixedI64, U64 }
checked_fixed! { FixedI128, U128 }
checked_fixed! { FixedU8, U8 }
checked_fixed! { FixedU16, U16 }
checked_fixed! { FixedU32, U32 }
checked_fixed! { FixedU64, U64 }
checked_fixed! { FixedU128, U128 }

macro_rules! checked_float {
    ($Float:ty) => {
        impl CheckedFromFixed for $Float {
            #[inline]
            fn from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Float::from_fixed(val)
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: Fixed,
            {
                Some(Float::from_fixed(val))
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Float::from_fixed(val)
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                Float::from_fixed(val)
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: Fixed,
            {
                (Float::from_fixed(val), false)
            }
        }

        impl CheckedToFixed for $Float {
            #[inline]
            fn to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Float::to_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: Fixed,
            {
                Float::checked_to_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Float::saturating_to_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                Float::wrapping_to_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed,
            {
                Float::overflowing_to_fixed(self)
            }
        }
    };
}

#[cfg(feature = "f16")]
checked_float! { f16 }
checked_float! { f32 }
checked_float! { f64 }
