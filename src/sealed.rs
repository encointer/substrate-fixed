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
    helpers::IntHelper,
    traits::Fixed as TraitsFixed,
    types::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

mod hide {
    use core::cmp::Ordering;

    // Unsigned can have 0 ≤ x < 2↑128, that is its msb can be 0 or 1.
    // Negative can have −2↑127 ≤ x < 0, that is its msb must be 1.
    pub enum Widest {
        Unsigned(u128),
        Negative(i128),
    }

    pub struct ToFixedHelper {
        pub(crate) bits: Widest,
        pub(crate) dir: Ordering,
        pub(crate) overflow: bool,
    }

    pub struct ToFloatHelper {
        pub(crate) neg: bool,
        pub(crate) abs: u128,
    }

    pub struct FromFloatHelper {
        pub(crate) kind: FloatKind,
    }
    pub enum FloatKind {
        NaN,
        Infinite { neg: bool },
        Finite { neg: bool, conv: ToFixedHelper },
    }

    pub trait Sealed: Copy {
        fn private_to_fixed_helper(self, dst_frac_nbits: u32, dst_int_nbits: u32) -> ToFixedHelper;
        fn private_to_float_helper(self) -> ToFloatHelper;
        fn private_saturating_from_float_helper(src: FromFloatHelper) -> Self;
        fn private_overflowing_from_float_helper(src: FromFloatHelper) -> (Self, bool);
    }
}

pub(crate) use self::hide::*;

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
#[deprecated(since = "0.4.2", note = "use traits::Fixed instead")]
pub trait Fixed: TraitsFixed {}

#[allow(deprecated)]
mod impl_deprecated {
    use crate::{
        sealed::{Fixed, Float, Int},
        types::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
        FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
        FixedU8,
    };
    #[cfg(feature = "f16")]
    use half::f16;

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
}

macro_rules! impl_sealed {
    ($Fixed:ident($LeEqU:ident, $Signedness:tt)) => {
        impl<Frac: $LeEqU> Sealed for $Fixed<Frac> {
            #[inline]
            fn private_to_fixed_helper(
                self,
                dst_frac_nbits: u32,
                dst_int_nbits: u32,
            ) -> ToFixedHelper {
                self.to_bits().to_fixed_helper(
                    Self::frac_nbits() as i32,
                    dst_frac_nbits,
                    dst_int_nbits,
                )
            }
            #[inline]
            fn private_to_float_helper(self) -> ToFloatHelper {
                let (neg, abs) = self.to_bits().neg_abs();
                let abs = abs.into();
                ToFloatHelper { neg, abs }
            }
            #[inline]
            fn private_saturating_from_float_helper(src: FromFloatHelper) -> Self {
                let neg = match src.kind {
                    FloatKind::NaN => panic!("NaN"),
                    FloatKind::Infinite { neg } => neg,
                    FloatKind::Finite { neg, .. } => neg,
                };
                let saturated = if neg {
                    Self::min_value()
                } else {
                    Self::max_value()
                };
                let conv = match src.kind {
                    FloatKind::Finite { conv, .. } => conv,
                    _ => return saturated,
                };
                if conv.overflow {
                    return saturated;
                }
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match conv.bits {
                        Widest::Unsigned(bits) => {
                            let bits = bits as _;
                            if bits < 0 {
                                return Self::max_value();
                            }
                            bits
                        }
                        Widest::Negative(bits) => bits as _,
                    },
                    match conv.bits {
                        Widest::Unsigned(bits) => bits as _,
                        Widest::Negative(_) => return Self::min_value(),
                    },
                );
                Self::from_bits(bits)
            }
            #[inline]
            fn private_overflowing_from_float_helper(src: FromFloatHelper) -> (Self, bool) {
                let conv = match src.kind {
                    FloatKind::NaN => panic!("NaN"),
                    FloatKind::Infinite { .. } => panic!("infinite"),
                    FloatKind::Finite { conv, .. } => conv,
                };
                let mut new_overflow = false;
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match conv.bits {
                        Widest::Unsigned(bits) => {
                            let bits = bits as _;
                            if bits < 0 {
                                new_overflow = true;
                            }
                            bits
                        }
                        Widest::Negative(bits) => bits as _,
                    },
                    match conv.bits {
                        Widest::Unsigned(bits) => bits as _,
                        Widest::Negative(bits) => {
                            new_overflow = true;
                            bits as _
                        }
                    },
                );
                (Self::from_bits(bits), conv.overflow || new_overflow)
            }
        }
    };
}

impl_sealed! { FixedI8(LeEqU8, Signed) }
impl_sealed! { FixedI16(LeEqU16, Signed) }
impl_sealed! { FixedI32(LeEqU32, Signed) }
impl_sealed! { FixedI64(LeEqU64, Signed) }
impl_sealed! { FixedI128(LeEqU128, Signed) }
impl_sealed! { FixedU8(LeEqU8, Unsigned) }
impl_sealed! { FixedU16(LeEqU16, Unsigned) }
impl_sealed! { FixedU32(LeEqU32, Unsigned) }
impl_sealed! { FixedU64(LeEqU64, Unsigned) }
impl_sealed! { FixedU128(LeEqU128, Unsigned) }
