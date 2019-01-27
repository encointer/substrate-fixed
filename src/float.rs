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

use core::mem;
#[cfg(feature = "f16")]
use half::f16;
use sealed::SealedFloat;

macro_rules! from_float {
    (fn $method:ident($Float:ty) -> $Uns:ty) => {
        fn $method(val: $Float, frac_bits: u32) -> Option<($Uns, bool)> {
            let float_bits = mem::size_of::<$Float>() as i32 * 8;
            let prec = <$Float as SealedFloat>::prec() as i32;
            let exp_min = <$Float as SealedFloat>::exp_min();
            let exp_max = <$Float as SealedFloat>::exp_max();
            let fix_bits = mem::size_of::<$Uns>() as i32 * 8;

            let (neg, exp, mut mantissa) = <$Float as SealedFloat>::parts(val);
            if exp > exp_max {
                return None;
            }
            // if not subnormal, add implicit bit
            if exp >= exp_min {
                mantissa |= 1 << (prec - 1);
            }
            if mantissa == 0 {
                return Some((0, neg));
            }
            let leading_zeros = mantissa.leading_zeros();
            mantissa <<= leading_zeros;
            let mut need_to_shr = -exp + leading_zeros as i32 + prec - 1 - frac_bits as i32;
            let rounding_bit = need_to_shr - 1;
            if 0 <= rounding_bit && rounding_bit < float_bits && mantissa & (1 << rounding_bit) != 0
            {
                // Rounding bit is one.
                // If any lower bit is one, round up.
                // If bit exactly above rounding is one, round up (tie to even).
                let round_up = (rounding_bit > 0 && mantissa & ((1 << rounding_bit) - 1) != 0)
                    || (rounding_bit + 1 < float_bits && mantissa & (1 << (rounding_bit + 1)) != 0);
                if round_up {
                    mantissa = match mantissa.overflowing_add(1 << rounding_bit) {
                        (m, false) => m,
                        (m, true) => {
                            need_to_shr -= 1;
                            (m >> 1) | (1 << (float_bits - 1))
                        }
                    };
                }
            }
            // now rounding is done, we can truncate extra right bits
            if float_bits - need_to_shr > fix_bits {
                return None;
            }
            #[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
            {
                if need_to_shr == 0 {
                    Some(((mantissa as $Uns), neg))
                } else if need_to_shr < 0 {
                    Some(((mantissa as $Uns) << -need_to_shr, neg))
                } else if need_to_shr < float_bits {
                    Some(((mantissa >> need_to_shr) as $Uns, neg))
                } else {
                    Some((0, neg))
                }
            }
        }
    };
}

macro_rules! to_float {
    (fn $method:ident($Uns:ty) -> $Float:ty) => {
        fn $method(self, neg: bool, frac_bits: u32) -> $Float {
            type FloatBits = <$Float as SealedFloat>::Bits;
            let prec = <$Float as SealedFloat>::prec();
            let exp_min = <$Float as SealedFloat>::exp_min();
            let exp_max = <$Float as SealedFloat>::exp_max();
            let fix_bits = mem::size_of::<$Uns>() as u32 * 8;
            let int_bits = fix_bits - frac_bits;

            let leading_zeros = self.leading_zeros();
            let signif_bits = int_bits + frac_bits - leading_zeros;
            if signif_bits == 0 {
                return <$Float as SealedFloat>::zero(neg);
            }
            // remove leading zeros and implicit one
            let mut mantissa = self << leading_zeros << 1;
            let exponent = int_bits as i32 - 1 - leading_zeros as i32;
            let biased_exponent = if exponent > exp_max {
                return <$Float as SealedFloat>::infinity(neg);
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
                #[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
                {
                    (mantissa >> (int_bits + frac_bits - (prec - 1))) as FloatBits
                }
            } else {
                #[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
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
    #[cfg(feature = "f16")]
    fn from_f16(val: f16, frac_bits: u32) -> Option<(Self, bool)>;
    fn from_f32(val: f32, frac_bits: u32) -> Option<(Self, bool)>;
    fn from_f64(val: f64, frac_bits: u32) -> Option<(Self, bool)>;
    #[cfg(feature = "f16")]
    fn to_f16(self, neg: bool, frac_bits: u32) -> f16;
    fn to_f32(self, neg: bool, frac_bits: u32) -> f32;
    fn to_f64(self, neg: bool, frac_bits: u32) -> f64;
}

macro_rules! float_conv {
    ($($Uns:ty)*) => { $(
        impl FloatConv for $Uns {
            #[cfg(feature = "f16")]
            from_float! { fn from_f16(f16) -> $Uns }
            from_float! { fn from_f32(f32) -> $Uns }
            from_float! { fn from_f64(f64) -> $Uns }
            #[cfg(feature = "f16")]
            to_float! { fn to_f16($Uns) -> f16 }
            to_float! { fn to_f32($Uns) -> f32 }
            to_float! { fn to_f64($Uns) -> f64 }
        }
    )* };
}
float_conv! { u8 u16 u32 u64 u128 }
