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
use frac::Unsigned;
use helper::FloatHelper;
use {FixedI16, FixedI32, FixedI8, FixedU16, FixedU32, FixedU8};

macro_rules! from_float {
    (fn $method:ident($Float:ty) -> $Uns:ty) => {
        fn $method(val: $Float, frac_bits: u32) -> Option<($Uns, bool)> {
            let _ = (val, frac_bits);
            unimplemented!()
        }
    };
}

macro_rules! to_float {
    (fn $method:ident($Uns:ty) -> $Float:ty) => {
        fn $method(self, neg: bool, frac_bits: u32) -> $Float {
            type FloatBits = <$Float as FloatHelper>::Bits;
            let prec = <$Float as FloatHelper>::prec();
            let exp_min = <$Float as FloatHelper>::exp_min();
            let exp_max = <$Float as FloatHelper>::exp_max();
            let fix_bits = mem::size_of::<$Uns>() as u32 * 8;
            let int_bits = fix_bits - frac_bits;

            let leading_zeros = self.leading_zeros();
            let signif_bits = int_bits + frac_bits - leading_zeros;
            if signif_bits == 0 {
                return <$Float as FloatHelper>::zero(neg);
            }
            // remove leading zeros and implicit one
            let mut mantissa = self << leading_zeros << 1;
            let exponent = int_bits as i32 - 1 - leading_zeros as i32;
            let biased_exponent = if exponent > exp_max {
                return <$Float as FloatHelper>::infinity(neg);
            } else if exponent < exp_min {
                let lost_prec = exp_min - exponent;
                if lost_prec as u32 >= (int_bits + frac_bits) {
                    mantissa = 0;
                } else {
                    // reinsert implicit one
                    mantissa = (mantissa >> 1) | !(!0 >> 1);
                    mantissa >>= lost_prec - 1;
                }
                0
            } else {
                (exponent + exp_max) as FloatBits
            };
            // check for rounding
            let round_up = (int_bits + frac_bits >= prec) && {
                let shift = prec - 1;
                let mid_bit = !(!0 >> 1) >> shift;
                let lower_bits = mid_bit - 1;
                if mantissa & mid_bit == 0 {
                    false
                } else if mantissa & lower_bits != 0 {
                    true
                } else {
                    // round to even
                    mantissa & (mid_bit << 1) != 0
                }
            };
            let bits_sign = if neg { !(!0 >> 1) } else { 0 };
            let bits_exp = biased_exponent << (prec - 1);
            let bits_mantissa = (if int_bits + frac_bits >= prec - 1 {
                #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
                {
                    (mantissa >> (int_bits + frac_bits - (prec - 1))) as FloatBits
                }
            } else {
                #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
                {
                    (mantissa as FloatBits) << (prec - 1 - (int_bits + frac_bits))
                }
            }) & !(!0 << (prec - 1));
            let mut bits_exp_mantissa = bits_exp | bits_mantissa;
            if round_up {
                bits_exp_mantissa += 1;
            }
            <$Float>::from_bits(bits_sign | bits_exp_mantissa)
        }
    };
}

pub(crate) trait FloatConv: Sized {
    fn from_f32(val: f32, frac_bits: u32) -> Option<(Self, bool)>;
    fn from_f64(val: f64, frac_bits: u32) -> Option<(Self, bool)>;
    fn to_f32(self, neg: bool, frac_bits: u32) -> f32;
    fn to_f64(self, neg: bool, frac_bits: u32) -> f64;
}

macro_rules! float_conv {
    ($($Uns:ty)*) => { $(
        impl FloatConv for $Uns {
            from_float! { fn from_f32(f32) -> $Uns }
            from_float! { fn from_f64(f64) -> $Uns }
            to_float! { fn to_f32($Uns) -> f32 }
            to_float! { fn to_f64($Uns) -> f64 }
        }
    )* };
}
float_conv! { u8 u16 u32 u64 u128 }

macro_rules! lossless_from_fixed {
    ($Fixed:ident:: $method:ident -> $Float:ident) => {
        impl<Frac: Unsigned> From<$Fixed<Frac>> for $Float {
            #[inline]
            fn from(src: $Fixed<Frac>) -> $Float {
                src.$method()
            }
        }
    };
}

lossless_from_fixed! { FixedI8::to_f32 -> f32 }
lossless_from_fixed! { FixedI16::to_f32 -> f32 }
lossless_from_fixed! { FixedU8::to_f32 -> f32 }
lossless_from_fixed! { FixedU16::to_f32 -> f32 }
lossless_from_fixed! { FixedI8::to_f64 -> f64 }
lossless_from_fixed! { FixedI16::to_f64 -> f64 }
lossless_from_fixed! { FixedI32::to_f64 -> f64 }
lossless_from_fixed! { FixedU8::to_f64 -> f64 }
lossless_from_fixed! { FixedU16::to_f64 -> f64 }
lossless_from_fixed! { FixedU32::to_f64 -> f64 }
