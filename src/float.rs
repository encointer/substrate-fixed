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
use frac::{IsLessOrEqual, True, Unsigned, U16, U32, U8};
#[cfg(feature = "f16")]
use half::f16;
use helper::FloatHelper;
use {FixedI16, FixedI32, FixedI8, FixedU16, FixedU32, FixedU8};

macro_rules! from_float {
    (fn $method:ident($Float:ty) -> $Uns:ty) => {
        fn $method(val: $Float, frac_bits: u32) -> Option<($Uns, bool)> {
            let float_bits = mem::size_of::<$Float>() as i32 * 8;
            let prec = <$Float as FloatHelper>::prec() as i32;
            let exp_min = <$Float as FloatHelper>::exp_min();
            let exp_max = <$Float as FloatHelper>::exp_max();
            let fix_bits = mem::size_of::<$Uns>() as i32 * 8;

            let (neg, exp, mut mantissa) = <$Float as FloatHelper>::parts(val);
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

macro_rules! lossless_from_fixed {
    ($Fixed:ident($Len:ty):: $method:ident -> $Float:ident) => {
        impl<Frac> From<$Fixed<Frac>> for $Float
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn from(src: $Fixed<Frac>) -> $Float {
                src.$method()
            }
        }
    };
}

#[cfg(feature = "f16")]
lossless_from_fixed! { FixedI8(U8)::to_f16 -> f16 }
#[cfg(feature = "f16")]
lossless_from_fixed! { FixedU8(U8)::to_f16 -> f16 }
lossless_from_fixed! { FixedI8(U8)::to_f32 -> f32 }
lossless_from_fixed! { FixedI16(U16)::to_f32 -> f32 }
lossless_from_fixed! { FixedU8(U8)::to_f32 -> f32 }
lossless_from_fixed! { FixedU16(U16)::to_f32 -> f32 }
lossless_from_fixed! { FixedI8(U8)::to_f64 -> f64 }
lossless_from_fixed! { FixedI16(U16)::to_f64 -> f64 }
lossless_from_fixed! { FixedI32(U32)::to_f64 -> f64 }
lossless_from_fixed! { FixedU8(U8)::to_f64 -> f64 }
lossless_from_fixed! { FixedU16(U16)::to_f64 -> f64 }
lossless_from_fixed! { FixedU32(U32)::to_f64 -> f64 }

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn signed_from_f32() {
        type Fix = FixedI8<frac::U4>;
        // 1.1 -> 0001.1000
        assert_eq!(Fix::from_f32(3.0 / 2.0).unwrap(), Fix::from_bits(24));
        // 0.11 -> 0000.1100
        assert_eq!(Fix::from_f32(3.0 / 4.0).unwrap(), Fix::from_bits(12));
        // 0.011 -> 0000.0110
        assert_eq!(Fix::from_f32(3.0 / 8.0).unwrap(), Fix::from_bits(6));
        // 0.0011 -> 0000.0011
        assert_eq!(Fix::from_f32(3.0 / 16.0).unwrap(), Fix::from_bits(3));
        // 0.00011 -> 0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(3.0 / 32.0).unwrap(), Fix::from_bits(2));
        // 0.00101 -> 0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(5.0 / 32.0).unwrap(), Fix::from_bits(2));
        // 0.000011 -> 0000.0001 (nearest)
        assert_eq!(Fix::from_f32(3.0 / 64.0).unwrap(), Fix::from_bits(1));
        // 0.00001 -> 0000.0000 (tie to even)
        assert_eq!(Fix::from_f32(1.0 / 32.0).unwrap(), Fix::from_bits(0));

        // -1.1 -> -0001.1000
        assert_eq!(Fix::from_f32(-3.0 / 2.0).unwrap(), Fix::from_bits(-24));
        // -0.11 -> -0000.1100
        assert_eq!(Fix::from_f32(-3.0 / 4.0).unwrap(), Fix::from_bits(-12));
        // -0.011 -> -0000.0110
        assert_eq!(Fix::from_f32(-3.0 / 8.0).unwrap(), Fix::from_bits(-6));
        // -0.0011 -> -0000.0011
        assert_eq!(Fix::from_f32(-3.0 / 16.0).unwrap(), Fix::from_bits(-3));
        // -0.00011 -> -0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(-3.0 / 32.0).unwrap(), Fix::from_bits(-2));
        // -0.00101 -> -0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(-5.0 / 32.0).unwrap(), Fix::from_bits(-2));
        // -0.000011 -> -0000.0001 (nearest)
        assert_eq!(Fix::from_f32(-3.0 / 64.0).unwrap(), Fix::from_bits(-1));
        // -0.00001 -> 0000.0000 (tie to even)
        assert_eq!(Fix::from_f32(-1.0 / 32.0).unwrap(), Fix::from_bits(0));

        // 111.1111 -> 111.1111
        assert_eq!(Fix::from_f32(127.0 / 16.0).unwrap(), Fix::from_bits(127));
        // 111.11111 -> too large (tie to even)
        assert!(Fix::from_f32(255.0 / 32.0).is_none());

        // -111.1111 -> -111.1111
        assert_eq!(Fix::from_f32(-127.0 / 16.0).unwrap(), Fix::from_bits(-127));
        // -111.11111 -> -1000.0000 (tie to even)
        assert_eq!(Fix::from_f32(-255.0 / 32.0).unwrap(), Fix::from_bits(-128));
        // -1000.00001 -> -1000.0000 (tie to even)
        assert_eq!(Fix::from_f32(-257.0 / 32.0).unwrap(), Fix::from_bits(-128));
        // -1000.0001 -> too small
        assert!(Fix::from_f32(-129.0 / 16.0).is_none());
    }

    #[test]
    fn unsigned_from_f32() {
        type Fix = FixedU8<frac::U4>;
        // 1.1 -> 0001.1000
        assert_eq!(Fix::from_f32(3.0 / 2.0).unwrap(), Fix::from_bits(24));
        // 0.11 -> 0000.1100
        assert_eq!(Fix::from_f32(3.0 / 4.0).unwrap(), Fix::from_bits(12));
        // 0.011 -> 0000.0110
        assert_eq!(Fix::from_f32(3.0 / 8.0).unwrap(), Fix::from_bits(6));
        // 0.0011 -> 0000.0011
        assert_eq!(Fix::from_f32(3.0 / 16.0).unwrap(), Fix::from_bits(3));
        // 0.00011 -> 0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(3.0 / 32.0).unwrap(), Fix::from_bits(2));
        // 0.00101 -> 0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(5.0 / 32.0).unwrap(), Fix::from_bits(2));
        // 0.000011 -> 0000.0001 (nearest)
        assert_eq!(Fix::from_f32(3.0 / 64.0).unwrap(), Fix::from_bits(1));
        // 0.00001 -> 0000.0000 (tie to even)
        assert_eq!(Fix::from_f32(1.0 / 32.0).unwrap(), Fix::from_bits(0));
        // -0.00001 -> 0000.0000 (tie to even)
        assert_eq!(Fix::from_f32(-1.0 / 32.0).unwrap(), Fix::from_bits(0));
        // -0.0001 -> too small
        assert!(Fix::from_f32(-1.0 / 16.0).is_none());

        // 1111.1111 -> 1111.1111
        assert_eq!(Fix::from_f32(255.0 / 16.0).unwrap(), Fix::from_bits(255));
        // 1111.11111 -> too large (tie to even)
        assert!(Fix::from_f32(511.0 / 32.0).is_none());
    }

    #[cfg(feature = "f16")]
    #[test]
    fn to_f16() {
        use half::f16;
        for u in 0x00..=0xff {
            let fu = FixedU8::<frac::U7>::from_bits(u);
            assert_eq!(fu.to_f16(), f16::from_f32(u as f32 / 128.0));
            let i = u as i8;
            let fi = FixedI8::<frac::U7>::from_bits(i);
            assert_eq!(fi.to_f16(), f16::from_f32(i as f32 / 128.0));

            for hi in &[
                0u32,
                0x0000_0100,
                0x7fff_ff00,
                0x8000_0000,
                0x8100_0000,
                0xffff_fe00,
                0xffff_ff00,
            ] {
                let uu = *hi | u as u32;
                let fuu = FixedU32::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f16(), f16::from_f32(uu as f32 / 128.0));
                let ii = uu as i32;
                let fii = FixedI32::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f16(), f16::from_f32(ii as f32 / 128.0));
            }

            for hi in &[
                0u128,
                0x0000_0000_0000_0000_0000_0000_0000_0100,
                0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
                0x8000_0000_0000_0000_0000_0000_0000_0000,
                0x8100_0000_0000_0000_0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u as u128;
                let fuu = FixedU128::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f16(), f16::from_f64(uu as f64 / 128.0));
                let ii = uu as i128;
                let fii = FixedI128::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f16(), f16::from_f64(ii as f64 / 128.0));
            }
        }
    }

    #[test]
    fn to_f32() {
        for u in 0x00..=0xff {
            let fu = FixedU8::<frac::U7>::from_bits(u);
            assert_eq!(fu.to_f32(), u as f32 / 128.0);
            let i = u as i8;
            let fi = FixedI8::<frac::U7>::from_bits(i);
            assert_eq!(fi.to_f32(), i as f32 / 128.0);

            for hi in &[
                0u32,
                0x0000_0100,
                0x7fff_ff00,
                0x8000_0000,
                0x8100_0000,
                0xffff_fe00,
                0xffff_ff00,
            ] {
                let uu = *hi | u as u32;
                let fuu = FixedU32::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f32(), uu as f32 / 128.0);
                let ii = uu as i32;
                let fii = FixedI32::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f32(), ii as f32 / 128.0);
            }

            for hi in &[
                0u128,
                0x0000_0000_0000_0000_0000_0000_0000_0100,
                0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
                0x8000_0000_0000_0000_0000_0000_0000_0000,
                0x8100_0000_0000_0000_0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u as u128;
                let fuu = FixedU128::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f32(), (uu as f64 / 128.0) as f32);
                let ii = uu as i128;
                let fii = FixedI128::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f32(), (ii as f64 / 128.0) as f32);
            }
        }
    }

    #[test]
    fn to_infinite_f32() {
        // too_large is 1.ffff_ffff_ffff... << 127,
        // which will be rounded to 1.0 << 128.
        let too_large = FixedU128::<frac::U0>::max_value();
        assert_eq!(too_large.count_ones(), 128);
        assert!(too_large.to_f32().is_infinite());

        // still_too_large is 1.ffff_ff << 127,
        // which is exactly midway between 1.0 << 128 (even)
        // and the largest normal f32 that is 1.ffff_fe << 127 (odd).
        // The tie will be rounded to even, which is to 1.0 << 128.
        let still_too_large = too_large << 103u32;
        assert_eq!(still_too_large.count_ones(), 25);
        assert!(still_too_large.to_f32().is_infinite());

        // not_too_large is 1.ffff_feff_ffff... << 127,
        // which will be rounded to 1.ffff_fe << 127.
        let not_too_large = still_too_large - FixedU128::from_bits(1);
        assert_eq!(not_too_large.count_ones(), 127);
        assert!(!not_too_large.to_f32().is_infinite());

        // min_128 is -1.0 << 127.
        let min_i128 = FixedI128::<frac::U0>::min_value();
        assert_eq!(min_i128.count_ones(), 1);
        assert_eq!(min_i128.to_f32(), -127f32.exp2());
    }

    #[test]
    fn to_f64() {
        for u in 0x00..=0xff {
            let fu = FixedU8::<frac::U7>::from_bits(u);
            assert_eq!(fu.to_f32(), u as f32 / 128.0);
            let i = u as i8;
            let fi = FixedI8::<frac::U7>::from_bits(i);
            assert_eq!(fi.to_f32(), i as f32 / 128.0);

            for hi in &[
                0u64,
                0x0000_0000_0000_0100,
                0x7fff_ffff_ffff_ff00,
                0x8000_0000_0000_0000,
                0x8100_0000_0000_0000,
                0xffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u as u64;
                let fuu = FixedU64::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f64(), uu as f64 / 128.0);
                let ii = uu as i64;
                let fii = FixedI64::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f64(), ii as f64 / 128.0);
            }

            for hi in &[
                0u128,
                0x0000_0000_0000_0000_0000_0000_0000_0100,
                0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
                0x8000_0000_0000_0000_0000_0000_0000_0000,
                0x8100_0000_0000_0000_0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u as u128;
                let fuu = FixedU128::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f64(), uu as f64 / 128.0);
                let ii = uu as i128;
                let fii = FixedI128::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f64(), ii as f64 / 128.0);
            }
        }
    }
}
