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

use crate::{
    frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8},
    traits::{FromFixed, ToFixed},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
pub(crate) use crate::{
    sealed_fixed::{SealedFixed, Widest},
    sealed_float::SealedFloat,
    sealed_int::SealedInt,
};
#[cfg(feature = "f16")]
use half::f16;

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
pub trait Int: SealedInt + FromFixed + ToFixed + Copy {}

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
pub trait Float: SealedFloat + FromFixed + ToFixed + Copy {}

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
pub trait Fixed: SealedFixed + FromFixed + ToFixed + Copy {
    /// The primitive integer underlying type.
    type Bits: Int;

    /// Create with a given bit representation.
    fn from_bits(bits: Self::Bits) -> Self;

    /// Convert to a bit representation.
    fn to_bits(self) -> Self::Bits;
}

impl ToFixed for bool {
    #[inline]
    fn to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        ToFixed::to_fixed(u8::from(self))
    }
    #[inline]
    fn checked_to_fixed<F>(self) -> Option<F>
    where
        F: Fixed,
    {
        ToFixed::checked_to_fixed(u8::from(self))
    }
    #[inline]
    fn saturating_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        ToFixed::saturating_to_fixed(u8::from(self))
    }
    #[inline]
    fn wrapping_to_fixed<F>(self) -> F
    where
        F: Fixed,
    {
        ToFixed::wrapping_to_fixed(u8::from(self))
    }
    #[inline]
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: Fixed,
    {
        ToFixed::overflowing_to_fixed(u8::from(self))
    }
}

macro_rules! impl_int {
    ($Int:ident) => {
        impl Int for $Int {}

        impl FromFixed for $Int {
            #[inline]
            fn from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                SealedInt::from_fixed(val)
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: Fixed,
            {
                SealedInt::checked_from_fixed(val)
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                SealedInt::saturating_from_fixed(val)
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                SealedInt::wrapping_from_fixed(val)
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: Fixed,
            {
                SealedInt::overflowing_from_fixed(val)
            }
        }

        impl ToFixed for $Int {
            #[inline]
            fn to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedInt::to_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: Fixed,
            {
                SealedInt::checked_to_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedInt::saturating_to_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedInt::wrapping_to_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed,
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
        impl Float for $Float {}

        impl FromFixed for $Float {
            #[inline]
            fn from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                val.to_float()
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: Fixed,
            {
                Some(val.to_float())
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                val.to_float()
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                val.to_float()
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: Fixed,
            {
                (val.to_float(), false)
            }
        }

        impl ToFixed for $Float {
            #[inline]
            fn to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedFloat::to_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: Fixed,
            {
                SealedFloat::checked_to_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedFloat::saturating_to_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedFloat::wrapping_to_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed,
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
                F: Fixed,
            {
                SealedFixed::from_fixed(val)
            }
            #[inline]
            fn checked_from_fixed<F>(val: F) -> Option<Self>
            where
                F: Fixed,
            {
                SealedFixed::checked_from_fixed(val)
            }
            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                SealedFixed::saturating_from_fixed(val)
            }
            #[inline]
            fn wrapping_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                SealedFixed::wrapping_from_fixed(val)
            }
            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: Fixed,
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
                F: Fixed,
            {
                SealedFixed::from_fixed(self)
            }
            #[inline]
            fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: Fixed,
            {
                SealedFixed::checked_from_fixed(self)
            }
            #[inline]
            fn saturating_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedFixed::saturating_from_fixed(self)
            }
            #[inline]
            fn wrapping_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedFixed::wrapping_from_fixed(self)
            }
            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed,
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
