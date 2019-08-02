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
pub trait Int: SealedInt + FromFixed + ToFixed {}

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
pub trait Float: SealedFloat + FromFixed + ToFixed {}

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
pub trait Fixed: SealedFixed + FromFixed + ToFixed {}

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

macro_rules! checked_int {
    ($Int:ty) => {
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

macro_rules! checked_float {
    ($Float:ty) => {
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
checked_float! { f16 }
checked_float! { f32 }
checked_float! { f64 }

macro_rules! checked_fixed {
    ($Fixed:ident, $NBits:ident) => {
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
