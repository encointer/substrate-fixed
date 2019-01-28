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
pub(crate) use sealed_fixed::SealedFixed;
pub(crate) use sealed_float::SealedFloat;
pub(crate) use sealed_int::SealedInt;
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

/// This trait is implemented for all the primitive integer types and
/// [`bool`].
///
/// This trait is sealed and cannot be implemented for more types; it
/// is implemented for [`bool`], [`i8`], [`i16`], [`i32`],
/// [`i64`], [`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].
///
/// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
/// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
/// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
/// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
/// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
/// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
/// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
/// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
/// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
/// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
/// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
pub trait Int: SealedInt {}

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
pub trait Float: SealedFloat {}

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
pub trait Fixed: SealedFixed {}

impl Int for bool {}
impl Int for i8 {}
impl Int for i16 {}
impl Int for i32 {}
impl Int for i64 {}
impl Int for i128 {}
impl Int for u8 {}
impl Int for u16 {}
impl Int for u32 {}
impl Int for u64 {}
impl Int for u128 {}

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
