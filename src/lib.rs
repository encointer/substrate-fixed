/*!
# Fixed-point numbers

Coming soon (waiting on [const generics]).

[const generics]: https://github.com/rust-lang/rust/issues/44580
*/
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/rug/0.0.0")]
#![doc(test(attr(deny(warnings))))]

mod display;
mod traits;

use std::f32;
use std::f64;
use std::mem;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Sub, SubAssign,
};
use traits::FixedNum;

const F: u32 = 7;

macro_rules! refs {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<'a> $Imp<$Fixed> for &'a $Fixed {
            type Output = $Fixed;
            #[inline]
            fn $method(self, rhs: $Fixed) -> $Fixed {
                <$Fixed as $Imp>::$method(*self, rhs)
            }
        }

        impl<'a> $Imp<&'a $Fixed> for $Fixed {
            type Output = $Fixed;
            #[inline]
            fn $method(self, rhs: &$Fixed) -> $Fixed {
                <$Fixed as $Imp>::$method(self, *rhs)
            }
        }

        impl<'a, 'b> $Imp<&'a $Fixed> for &'b $Fixed {
            type Output = $Fixed;
            #[inline]
            fn $method(self, rhs: &$Fixed) -> $Fixed {
                <$Fixed as $Imp>::$method(*self, *rhs)
            }
        }
    };
}

macro_rules! refs_assign {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<'a> $Imp<&'a $Fixed> for $Fixed {
            #[inline]
            fn $method(&mut self, rhs: &$Fixed) {
                <$Fixed as $Imp>::$method(self, *rhs);
            }
        }
    };
}

macro_rules! pass {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl $Imp<$Fixed> for $Fixed {
            type Output = $Fixed;
            #[inline]
            fn $method(self, rhs: $Fixed) -> $Fixed {
                $Fixed(<$Inner as $Imp>::$method(self.0, rhs.0))
            }
        }

        refs! { impl $Imp for $Fixed($Inner) { $method } }
    };
}

macro_rules! pass_assign {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl $Imp<$Fixed> for $Fixed {
            #[inline]
            fn $method(&mut self, rhs: $Fixed) {
                <$Inner as $Imp>::$method(&mut self.0, rhs.0);
            }
        }

        refs_assign! { impl $Imp for $Fixed($Inner) { $method } }
    };
}

macro_rules! pass_one {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl $Imp for $Fixed {
            type Output = $Fixed;
            #[inline]
            fn $method(self) -> $Fixed {
                $Fixed(<$Inner as $Imp>::$method(self.0))
            }
        }

        impl<'a> $Imp for &'a $Fixed {
            type Output = $Fixed;
            #[inline]
            fn $method(self) -> $Fixed {
                <$Fixed as $Imp>::$method(*self)
            }
        }
    };
}

macro_rules! doc_comment {
    ($x:expr, $($tt:tt)*) => {
        #[doc = $x]
        $($tt)*
    };
}

macro_rules! to_f {
    ($method:ident -> $f:ident($u:ident), $exp_bits:expr, $prec:expr) => {
        doc_comment! {
            concat!(
                "Converts the fixed-point number to `",
                stringify!($f),
                "`."
            ),
            pub fn $method(self) -> $f {
                // exponent is IEEE754 style (1 <= significand < 2)
                let exp_max = (1 << ($exp_bits - 1)) - 1;
                let exp_min = 1 - exp_max;
                let (int_bits, frac_bits) = (Self::int_bits(), Self::frac_bits());

                let (neg, int, frac) = self.parts();
                let int_frac = (int << frac_bits) | (frac >> int_bits);
                let leading_zeros = int_frac.leading_zeros();
                let signif_bits = int_bits + frac_bits - leading_zeros;
                if signif_bits == 0 {
                    debug_assert!(!neg);
                    return 0.0;
                }
                // remove leading zeros and implicit one
                let mut mantissa = int_frac << leading_zeros << 1;
                let exponent = int_bits as i32 - 1 - leading_zeros as i32;
                let biased_exponent = if exponent > exp_max {
                    return if neg { $f::NEG_INFINITY } else { $f::INFINITY };
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
                    (exponent + exp_max) as $u
                };
                // check for rounding
                let round_up = (int_bits + frac_bits >= $prec) && {
                    let shift = $prec - 1;
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
                let bits_exp = biased_exponent << ($prec - 1);
                let bits_mantissa = (if int_bits + frac_bits >= $prec - 1 {
                    (mantissa >> (int_bits + frac_bits - $prec + 1)) as $u
                } else {
                    (mantissa as $u) << ($prec - 1 - int_bits - frac_bits)
                }) & !(!0 << ($prec - 1));
                let mut bits_exp_mantissa = bits_exp | bits_mantissa;
                if round_up {
                    // cannot be infinite already
                    debug_assert!(bits_exp_mantissa != !0 >> 1);
                    bits_exp_mantissa += 1;
                }
                $f::from_bits(bits_sign | bits_exp_mantissa)
            }
        }
    };
}

macro_rules! fixed_unsigned {
    ($(#[$attr:meta])* $Fixed:ident($Inner:ty)) => {
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        $(#[$attr])*
        pub struct $Fixed($Inner);

        impl $Fixed {
            doc_comment! {
                concat!(
                    "Creates a fixed-point number of type `",
                    stringify!($Fixed),
                    "` that has a bitwise representation identical to the `",
                    stringify!($Inner),
                    "` value."
                ),
                #[inline]
                pub fn from_bits(v: $Inner) -> $Fixed {
                    $Fixed(v)
                }
            }

            doc_comment! {
                concat!(
                    "Creates an integer of type `",
                    stringify!($Inner),
                    "` that has a bitwise representation identical to the `",
                    stringify!($Fixed),
                    "` value."
                ),
                #[inline]
                pub fn to_bits(self) -> $Inner {
                    self.0
                }
            }

            to_f! { to_f32 -> f32(u32), 8, 24 }
            to_f! { to_f64 -> f64(u64), 11, 53 }
        }

        pass! { impl Add for $Fixed($Inner) { add } }
        pass_assign! { impl AddAssign for $Fixed($Inner) { add_assign } }
        pass! { impl Sub for $Fixed($Inner) { sub } }
        pass_assign! { impl SubAssign for $Fixed($Inner) { sub_assign } }

        impl Mul<$Fixed> for $Fixed {
            type Output = $Fixed;
            #[inline]
            fn mul(self, rhs: $Fixed) -> $Fixed {
                $Fixed(<$Inner as MulDiv>::mul(self.0, rhs.0))
            }
        }

        refs! { impl Mul for $Fixed($Inner) { mul } }

        impl MulAssign<$Fixed> for $Fixed {
            #[inline]
            fn mul_assign(&mut self, rhs: $Fixed) {
                self.0 = <$Inner as MulDiv>::mul(self.0, rhs.0)
            }
        }

        refs_assign! { impl MulAssign for $Fixed($Inner) { mul_assign } }

        impl Div<$Fixed> for $Fixed {
            type Output = $Fixed;
            #[inline]
            fn div(self, rhs: $Fixed) -> $Fixed {
                $Fixed(<$Inner as MulDiv>::div(self.0, rhs.0))
            }
        }

        refs! { impl Div for $Fixed($Inner) { div } }

        impl DivAssign<$Fixed> for $Fixed {
            #[inline]
            fn div_assign(&mut self, rhs: $Fixed) {
                self.0 = <$Inner as MulDiv>::div(self.0, rhs.0)
            }
        }

        refs_assign! { impl DivAssign for $Fixed($Inner) { div_assign } }

        pass_one! { impl Not for $Fixed($Inner) { not } }
        pass! { impl BitAnd for $Fixed($Inner) { bitand } }
        pass_assign! { impl BitAndAssign for $Fixed($Inner) { bitand_assign } }
        pass! { impl BitOr for $Fixed($Inner) { bitor } }
        pass_assign! { impl BitOrAssign for $Fixed($Inner) { bitor_assign } }
        pass! { impl BitXor for $Fixed($Inner) { bitxor } }
        pass_assign! { impl BitXorAssign for $Fixed($Inner) { bitxor_assign } }
    };
}

macro_rules! fixed_signed {
    ($(#[$attr:meta])* $Fixed:ident($Inner:ty)) => {
        fixed_unsigned! { $(#[$attr])* $Fixed($Inner) }

        pass_one! { impl Neg for $Fixed($Inner) { neg } }
    };
}

fixed_unsigned! {
    /// An eight-bit fixed-point unsigned integer with `F` fractional bits.
    FixedU8(u8)
}
fixed_unsigned! {
    /// A 16-bit fixed-point unsigned integer with `F` fractional bits.
    FixedU16(u16)
}
fixed_unsigned! {
    /// A 32-bit fixed-point unsigned integer with `F` fractional bits.
    FixedU32(u32)
}
fixed_unsigned! {
    /// A 64-bit fixed-point unsigned integer with `F` fractional bits.
    FixedU64(u64)
}
fixed_unsigned! {
    /// A 128-bit fixed-point unsigned integer with `F` fractional bits.
    FixedU128(u128)
}
fixed_signed! {
    /// An eight-bit fixed-point signed integer with `F` fractional bits.
    FixedI8(i8)
}
fixed_signed! {
    /// A 16-bit fixed-point signed integer with `F` fractional bits.
    FixedI16(i16)
}
fixed_signed! {
    /// A 32-bit fixed-point signed integer with `F` fractional bits.
    FixedI32(i32)
}
fixed_signed! {
    /// A 64-bit fixed-point signed integer with `F` fractional bits.
    FixedI64(i64)
}
fixed_signed! {
    /// A 128-bit fixed-point signed integer with `F` fractional bits.
    FixedI128(i128)
}

trait MulDiv {
    fn mul(self, rhs: Self) -> Self;
    fn div(self, rhs: Self) -> Self;
}

macro_rules! mul_div_widen {
    ($Single:ty, $Double:ty) => {
        impl MulDiv for $Single {
            #[inline]
            fn mul(self, rhs: $Single) -> $Single {
                const BITS: u32 = mem::size_of::<$Single>() as u32 * 8;
                const I: u32 = BITS - F;
                let lhs2 = self as $Double;
                let rhs2 = rhs as $Double << I;
                let prod2 = lhs2 * rhs2;
                (prod2 >> BITS) as $Single
            }

            #[inline]
            fn div(self, rhs: $Single) -> $Single {
                let lhs2 = self as $Double << F;
                let rhs2 = rhs as $Double;
                let quot2 = lhs2 / rhs2;
                let quot = quot2 as $Single;
                debug_assert!(quot as $Double == quot2, "overflow");
                quot
            }
        }
    };
}

macro_rules! mul_div_fallback {
    ($Single:ty) => {
        impl MulDiv for $Single {
            #[inline]
            fn mul(self, rhs: $Single) -> $Single {
                if F == 0 {
                    self * rhs
                } else {
                    unimplemented!()
                }
            }

            #[inline]
            fn div(self, rhs: $Single) -> $Single {
                if F == 0 {
                    self / rhs
                } else {
                    unimplemented!()
                }
            }
        }
    };
}

mul_div_widen! { u8, u16 }
mul_div_widen! { u16, u32 }
mul_div_widen! { u32, u64 }
mul_div_widen! { u64, u128 }
mul_div_fallback! { u128 }
mul_div_widen! { i8, i16 }
mul_div_widen! { i16, i32 }
mul_div_widen! { i32, i64 }
mul_div_widen! { i64, i128 }
mul_div_fallback! { i128 }

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn fixed_u16() {
        let a = 12;
        let b = 4;
        let af = FixedU16::from_bits(a << F);
        let bf = FixedU16::from_bits(b << F);
        assert_eq!((af + bf).to_bits(), (a << F) + (b << F));
        assert_eq!((af - bf).to_bits(), (a << F) - (b << F));
        assert_eq!((af * bf).to_bits(), (a << F) * b);
        assert_eq!((af / bf).to_bits(), (a << F) / b);
        assert_eq!((af & bf).to_bits(), (a << F) & (b << F));
        assert_eq!((af | bf).to_bits(), (a << F) | (b << F));
        assert_eq!((af ^ bf).to_bits(), (a << F) ^ (b << F));
        assert_eq!((!af).to_bits(), !(a << F));
    }

    #[test]
    fn fixed_i16() {
        let a = 12;
        let b = -4;
        let af = FixedI16::from_bits(a << F);
        let bf = FixedI16::from_bits(b << F);
        assert_eq!((af + bf).to_bits(), (a << F) + (b << F));
        assert_eq!((af - bf).to_bits(), (a << F) - (b << F));
        assert_eq!((af * bf).to_bits(), (a << F) * b);
        assert_eq!((af / bf).to_bits(), (a << F) / b);
        assert_eq!((af & bf).to_bits(), (a << F) & (b << F));
        assert_eq!((af | bf).to_bits(), (a << F) | (b << F));
        assert_eq!((af ^ bf).to_bits(), (a << F) ^ (b << F));
        assert_eq!((-af).to_bits(), -(a << F));
        assert_eq!((!af).to_bits(), !(a << F));
    }

    #[test]
    fn to_f32() {
        for u in 0x00..=0xff {
            let fu = FixedU8::from_bits(u);
            assert_eq!(fu.to_f32(), u as f32 / 128.0);
            let i = u as i8;
            let fi = FixedI8::from_bits(i);
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
                let fuu = FixedU32::from_bits(uu);
                assert_eq!(fuu.to_f32(), uu as f32 / 128.0);
                let ii = uu as i32;
                let fii = FixedI32::from_bits(ii);
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
                let fuu = FixedU128::from_bits(uu);
                assert_eq!(fuu.to_f32(), (uu as f64 / 128.0) as f32);
                let ii = uu as i128;
                let fii = FixedI128::from_bits(ii);
                assert_eq!(fii.to_f32(), (ii as f64 / 128.0) as f32);
            }
        }
    }

    #[test]
    fn to_f64() {
        for u in 0x00..=0xff {
            let fu = FixedU8::from_bits(u);
            assert_eq!(fu.to_f32(), u as f32 / 128.0);
            let i = u as i8;
            let fi = FixedI8::from_bits(i);
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
                let fuu = FixedU64::from_bits(uu);
                assert_eq!(fuu.to_f64(), uu as f64 / 128.0);
                let ii = uu as i64;
                let fii = FixedI64::from_bits(ii);
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
                let fuu = FixedU128::from_bits(uu);
                assert_eq!(fuu.to_f64(), uu as f64 / 128.0);
                let ii = uu as i128;
                let fii = FixedI128::from_bits(ii);
                assert_eq!(fii.to_f64(), ii as f64 / 128.0);
            }
        }
    }
}
