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
use helper::FloatHelper;

macro_rules! to_f {
    (fn $method:ident($Uns:ty) -> $Flt:ty) => {
        fn $method(self, neg: bool, frac_bits: u32) -> $Flt {
            type Bits = <$Flt as FloatHelper>::Bits;
            let prec = <$Flt as FloatHelper>::prec();
            let exp_min = <$Flt as FloatHelper>::exp_min();
            let exp_max = <$Flt as FloatHelper>::exp_max();
            let fix_bits = mem::size_of::<$Uns>() as u32 * 8;
            let int_bits = fix_bits - frac_bits;

            let leading_zeros = self.leading_zeros();
            let signif_bits = int_bits + frac_bits - leading_zeros;
            if signif_bits == 0 {
                return <$Flt as FloatHelper>::zero(neg);
            }
            // remove leading zeros and implicit one
            let mut mantissa = self << leading_zeros << 1;
            let exponent = int_bits as i32 - 1 - leading_zeros as i32;
            let biased_exponent = if exponent > exp_max {
                return <$Flt as FloatHelper>::infinity(neg);
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
                (exponent + exp_max) as Bits
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
                    (mantissa >> (int_bits + frac_bits - (prec - 1))) as Bits
                }
            } else {
                #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
                {
                    (mantissa as Bits) << (prec - 1 - (int_bits + frac_bits))
                }
            }) & !(!0 << (prec - 1));
            let mut bits_exp_mantissa = bits_exp | bits_mantissa;
            if round_up {
                bits_exp_mantissa += 1;
            }
            <$Flt>::from_bits(bits_sign | bits_exp_mantissa)
        }
    };
}

pub(crate) trait FltConv: Sized {
    fn to_f32(self, neg: bool, frac_bits: u32) -> f32;
    fn to_f64(self, neg: bool, frac_bits: u32) -> f64;
}

macro_rules! flt_conv {
    ($($Uns:ty)*) => { $(
        impl FltConv for $Uns {
            to_f! { fn to_f32($Uns) -> f32 }
            to_f! { fn to_f64($Uns) -> f64 }
        }
    )* };
}
flt_conv! { u8 u16 u32 u64 u128 }
