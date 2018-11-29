// Copyright © 2018 Trevor Spiteri

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

use core::mem;
use frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8};
#[cfg(feature = "f16")]
use half::f16;
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

pub(crate) trait FloatHelper {
    type Bits;

    fn prec() -> u32;
    fn exp_bias() -> i32;
    fn exp_min() -> i32;
    fn exp_max() -> i32;

    fn zero(neg: bool) -> Self;
    fn infinity(neg: bool) -> Self;
    fn from_parts(neg: bool, exp: i32, mant: Self::Bits) -> Self;
    fn parts(self) -> (bool, i32, Self::Bits);
}

macro_rules! float_helper {
    ($Float:ident($Bits:ty, $prec:expr)) => {
        impl FloatHelper for $Float {
            type Bits = $Bits;

            #[inline]
            fn prec() -> u32 {
                $prec
            }

            #[inline]
            fn exp_bias() -> i32 {
                let nbits = mem::size_of::<$Bits>() * 8;
                let exp_bits = nbits - $prec;
                (1 << (exp_bits - 1)) - 1
            }

            #[inline]
            fn exp_min() -> i32 {
                1 - <$Float as FloatHelper>::exp_bias()
            }

            #[inline]
            fn exp_max() -> i32 {
                <$Float as FloatHelper>::exp_bias()
            }

            #[inline]
            fn zero(neg: bool) -> $Float {
                let nbits = mem::size_of::<$Bits>() * 8;
                let neg_mask = !0 << (nbits - 1);
                let neg_bits = if neg { neg_mask } else { 0 };
                <$Float>::from_bits(neg_bits)
            }

            #[inline]
            fn infinity(neg: bool) -> $Float {
                let nbits = mem::size_of::<$Bits>() * 8;
                let neg_mask = !0 << (nbits - 1);
                let mant_mask = !(!0 << ($prec - 1));
                let exp_mask = !(neg_mask | mant_mask);

                let neg_bits = if neg { neg_mask } else { 0 };
                <$Float>::from_bits(neg_bits | exp_mask)
            }

            #[inline]
            fn from_parts(neg: bool, exp: i32, mant: Self::Bits) -> $Float {
                let nbits = mem::size_of::<$Bits>() * 8;
                let neg_mask = !0 << (nbits - 1);

                let neg_bits = if neg { neg_mask } else { 0 };
                let biased_exp = (exp + <$Float as FloatHelper>::exp_bias()) as Self::Bits;
                let exp_bits = biased_exp << ($prec - 1);
                <$Float>::from_bits(neg_bits | exp_bits | mant)
            }

            #[inline]
            fn parts(self) -> (bool, i32, $Bits) {
                let nbits = mem::size_of::<$Bits>() * 8;
                let neg_mask = !0 << (nbits - 1);
                let mant_mask = !(!0 << ($prec - 1));
                let exp_mask = !(neg_mask | mant_mask);

                let bits = self.to_bits();
                let neg = bits & neg_mask != 0;
                let biased_exp = (bits & exp_mask) >> ($prec - 1);
                let exp = ({
                    #[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
                    {
                        biased_exp as i32
                    }
                }) - <$Float as FloatHelper>::exp_bias();
                let mant = bits & mant_mask;

                (neg, exp, mant)
            }
        }
    };
}

#[cfg(feature = "f16")]
float_helper! { f16(u16, 11) }
float_helper! { f32(u32, 24) }
float_helper! { f64(u64, 53) }

pub(crate) trait FixedHelper<Frac>: Sized
where
    Frac: Unsigned,
{
    type UInner;

    #[inline]
    fn int_frac_bits() -> u32 {
        mem::size_of::<Self::UInner>() as u32 * 8
    }

    fn is_signed() -> bool;
    fn one() -> Option<Self>;
    fn minus_one() -> Option<Self>;
    fn from_parts(neg: bool, int_abs: Self::UInner, frac_abs: Self::UInner) -> Self;
    fn parts(self) -> (bool, Self::UInner, Self::UInner);
}

macro_rules! fixed_num_unsigned {
    ($Fixed:ident($UInner:ty, $Len:ty)) => {
        impl<Frac> FixedHelper<Frac> for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type UInner = $UInner;

            #[inline]
            fn is_signed() -> bool {
                false
            }

            #[inline]
            fn one() -> Option<Self> {
                let int_bits = <$Fixed<Frac>>::int_bits();
                let frac_bits = <$Fixed<Frac>>::frac_bits();
                if int_bits < 1 {
                    None
                } else {
                    Some($Fixed::from_bits(1 << frac_bits))
                }
            }

            #[inline]
            fn minus_one() -> Option<Self> {
                None
            }

            #[inline]
            fn from_parts(
                neg: bool,
                int_abs: Self::UInner,
                frac_abs: Self::UInner,
            ) -> $Fixed<Frac> {
                let int_bits = <$Fixed<Frac>>::int_bits();
                let frac_bits = <$Fixed<Frac>>::frac_bits();

                let _ = neg;
                debug_assert!(!neg);

                let int_frac = if int_bits == 0 {
                    frac_abs
                } else if frac_bits == 0 {
                    int_abs
                } else {
                    (int_abs << frac_bits) | (frac_abs >> int_bits)
                };
                $Fixed::from_bits(int_frac)
            }

            #[inline]
            fn parts(self) -> (bool, $UInner, $UInner) {
                let int_bits = <$Fixed<Frac>>::int_bits();
                let frac_bits = <$Fixed<Frac>>::frac_bits();

                let bits = self.to_bits();
                let int_part = if int_bits == 0 { 0 } else { bits >> frac_bits };
                let frac_part = if frac_bits == 0 { 0 } else { bits << int_bits };
                (false, int_part, frac_part)
            }
        }
    };
}

macro_rules! fixed_num_signed {
    ($Fixed:ident($UInner:ty, $Len:ty)) => {
        impl<Frac> FixedHelper<Frac> for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type UInner = $UInner;

            #[inline]
            fn is_signed() -> bool {
                true
            }

            #[inline]
            fn one() -> Option<Self> {
                let int_bits = <$Fixed<Frac>>::int_bits();
                let frac_bits = <$Fixed<Frac>>::frac_bits();
                if int_bits < 2 {
                    None
                } else {
                    Some($Fixed::from_bits(1 << frac_bits))
                }
            }

            #[inline]
            fn minus_one() -> Option<Self> {
                let int_bits = <$Fixed<Frac>>::int_bits();
                let frac_bits = <$Fixed<Frac>>::frac_bits();
                if int_bits < 1 {
                    None
                } else {
                    Some($Fixed::from_bits(!0 << frac_bits))
                }
            }

            #[inline]
            fn from_parts(
                neg: bool,
                int_abs: Self::UInner,
                frac_abs: Self::UInner,
            ) -> $Fixed<Frac> {
                let int_bits = <$Fixed<Frac>>::int_bits();
                let frac_bits = <$Fixed<Frac>>::frac_bits();

                let int_frac_abs = if int_bits == 0 {
                    frac_abs
                } else if frac_bits == 0 {
                    int_abs
                } else {
                    (int_abs << frac_bits) | (frac_abs >> int_bits)
                };
                let int_frac = if neg {
                    int_frac_abs.wrapping_neg()
                } else {
                    int_frac_abs
                };
                $Fixed::from_bits(int_frac as _)
            }

            #[inline]
            fn parts(self) -> (bool, $UInner, $UInner) {
                let int_bits = <$Fixed<Frac>>::int_bits();
                let frac_bits = <$Fixed<Frac>>::frac_bits();

                let (neg, abs) = if self.to_bits() < 0 {
                    (true, self.to_bits().wrapping_neg() as $UInner)
                } else {
                    (false, self.to_bits() as $UInner)
                };
                let (int_abs, frac_abs) = if int_bits == 0 {
                    (0, abs)
                } else if frac_bits == 0 {
                    (abs, 0)
                } else {
                    ((abs >> frac_bits), (abs << int_bits))
                };
                (neg, int_abs, frac_abs)
            }
        }
    };
}

fixed_num_unsigned! { FixedU8(u8, U8) }
fixed_num_unsigned! { FixedU16(u16, U16) }
fixed_num_unsigned! { FixedU32(u32, U32) }
fixed_num_unsigned! { FixedU64(u64, U64) }
fixed_num_unsigned! { FixedU128(u128, U128) }
fixed_num_signed! { FixedI8(u8, U8) }
fixed_num_signed! { FixedI16(u16, U16) }
fixed_num_signed! { FixedI32(u32, U32) }
fixed_num_signed! { FixedI64(u64, U64) }
fixed_num_signed! { FixedI128(u128, U128) }
