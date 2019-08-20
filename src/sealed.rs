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
#![deprecated(since = "0.4.2")]
#![allow(deprecated)]

use crate::{
    traits::Fixed as TraitsFixed,
    types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
#[cfg(feature = "f16")]
use half::f16;

/// This trait is implemented for all the primitive integer types.
#[deprecated(since = "0.4.2", note = "do not use")]
pub trait Int: Copy {}

/// This trait is implemented for the primitive floating-point types,
/// and for [`f16`] if the [`f16` feature] is enabled.
///
/// [`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
/// [`f16` feature]: ../index.html#optional-features
#[deprecated(since = "0.4.2", note = "do not use")]
pub trait Float: Copy {}

/// This trait is implemented for all the fixed-point types.
#[deprecated(since = "0.4.2", note = "use `traits::Fixed` instead")]
pub trait Fixed: TraitsFixed {}

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

impl<Frac: LeEqU8> Fixed for FixedI8<Frac> {}
impl<Frac: LeEqU16> Fixed for FixedI16<Frac> {}
impl<Frac: LeEqU32> Fixed for FixedI32<Frac> {}
impl<Frac: LeEqU64> Fixed for FixedI64<Frac> {}
impl<Frac: LeEqU128> Fixed for FixedI128<Frac> {}
impl<Frac: LeEqU8> Fixed for FixedU8<Frac> {}
impl<Frac: LeEqU16> Fixed for FixedU16<Frac> {}
impl<Frac: LeEqU32> Fixed for FixedU32<Frac> {}
impl<Frac: LeEqU64> Fixed for FixedU64<Frac> {}
impl<Frac: LeEqU128> Fixed for FixedU128<Frac> {}
