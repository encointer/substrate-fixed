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

use core::cmp::Ordering;
use core::fmt::{Debug, Display};
#[cfg(feature = "f16")]
use half::f16;
use sealed::{Fixed, SealedInt, Widest};

pub trait SealedFloat: Copy + Debug + Display {
    type Bits: SealedInt;

    const PREC: u32;
    const EXP_BIAS: i32 = (1 << (Self::Bits::NBITS - Self::PREC - 1)) - 1;
    const EXP_MIN: i32 = 1 - Self::EXP_BIAS;
    const EXP_MAX: i32 = Self::EXP_BIAS;
    const SIGN_MASK: Self::Bits;
    const EXP_MASK: Self::Bits;
    const MANT_MASK: Self::Bits;

    fn zero(neg: bool) -> Self;
    fn infinity(neg: bool) -> Self;
    fn is_nan(self) -> bool;
    fn is_finite(self) -> bool;
    fn is_zero(self) -> bool;
    fn is_sign_negative(self) -> bool;

    fn parts(self) -> (bool, i32, Self::Bits);
    fn from_parts(sign: bool, exp: i32, mant: Self::Bits) -> Self;

    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: Fixed;

    fn from_neg_abs(neg: bool, abs: u128, frac_bits: u32, int_bits: u32) -> Self;
    // self must be finite, otherwise meaningless results are returned
    fn to_fixed_dir_overflow(self, frac_bits: u32, int_bits: u32) -> (Widest, Ordering, bool);
}

macro_rules! sealed_float {
    ($Float:ident($Bits:ty, $IBits:ty, $prec:expr)) => {
        impl SealedFloat for $Float {
            type Bits = $Bits;

            const PREC: u32 = $prec;
            const SIGN_MASK: Self::Bits = Self::Bits::MSB;
            const EXP_MASK: Self::Bits = Self::SIGN_MASK - (1 << (Self::PREC - 1));
            const MANT_MASK: Self::Bits = (1 << (Self::PREC - 1)) - 1;

            #[inline]
            fn zero(neg: bool) -> $Float {
                Self::from_bits(if neg { Self::SIGN_MASK } else { 0 })
            }

            #[inline]
            fn infinity(neg: bool) -> $Float {
                Self::from_bits(Self::EXP_MASK | if neg { Self::SIGN_MASK } else { 0 })
            }

            #[inline]
            fn is_nan(self) -> bool {
                (self.to_bits() & !Self::SIGN_MASK) > Self::EXP_MASK
            }

            #[inline]
            fn is_finite(self) -> bool {
                (self.to_bits() & !Self::SIGN_MASK) < Self::EXP_MASK
            }

            #[inline]
            fn is_zero(self) -> bool {
                (self.to_bits() & !Self::SIGN_MASK) == 0
            }

            #[inline]
            fn is_sign_negative(self) -> bool {
                (self.to_bits() & Self::SIGN_MASK) != 0
            }

            #[inline]
            #[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
            fn parts(self) -> (bool, i32, $Bits) {
                let bits = self.to_bits();
                let neg = bits & Self::SIGN_MASK != 0;
                let biased_exp = (bits & Self::EXP_MASK) >> (Self::PREC - 1);
                let exp = biased_exp as i32 - Self::EXP_BIAS;
                let mant = bits & Self::MANT_MASK;

                (neg, exp, mant)
            }

            #[inline]
            #[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
            fn from_parts(sign: bool, exp: i32, mant: $Bits) -> Self {
                let sign_bits = if sign { Self::SIGN_MASK } else { 0 };
                let biased_exp = (exp + Self::EXP_BIAS) as Self::Bits;
                let exp_bits = biased_exp << (Self::PREC - 1);
                let bits = sign_bits | exp_bits | mant;
                Self::from_bits(bits)
            }

            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed,
            {
                F::overflowing_from_float(self)
            }

            fn from_neg_abs(neg: bool, abs: u128, frac_bits: u32, int_bits: u32) -> $Float {
                let fix_bits = frac_bits + int_bits;

                let extra_zeros = 128 - fix_bits;
                let leading_zeros = abs.leading_zeros() - extra_zeros;
                let signif_bits = fix_bits - leading_zeros;
                if signif_bits == 0 {
                    return Self::zero(neg);
                }
                // remove leading zeros and implicit one
                let mut mantissa = abs << leading_zeros << 1;
                let exponent = int_bits as i32 - 1 - leading_zeros as i32;
                let biased_exponent = if exponent > Self::EXP_MAX {
                    return Self::infinity(neg);
                } else if exponent < Self::EXP_MIN {
                    let lost_prec = Self::EXP_MIN - exponent;
                    if lost_prec as u32 >= (int_bits + frac_bits) {
                        mantissa = 0;
                    } else {
                        // reinsert implicit one
                        mantissa = (mantissa >> 1) | !(!0 >> 1);
                        mantissa >>= lost_prec - 1;
                    }
                    0
                } else {
                    (exponent + Self::EXP_MAX) as Self::Bits
                };
                // check for rounding
                let round_up = (fix_bits >= Self::PREC) && {
                    let shift = Self::PREC - 1;
                    let mid_bit = !(!0 >> 1) >> (shift + extra_zeros);
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
                let bits_exp = biased_exponent << (Self::PREC - 1);
                let bits_mantissa = (if fix_bits >= Self::PREC - 1 {
                    (mantissa >> (fix_bits - (Self::PREC - 1))) as Self::Bits
                } else {
                    (mantissa as Self::Bits) << (Self::PREC - 1 - fix_bits)
                }) & !(!0 << (Self::PREC - 1));
                let mut bits_exp_mantissa = bits_exp | bits_mantissa;
                if round_up {
                    bits_exp_mantissa += 1;
                }
                Self::from_bits(bits_sign | bits_exp_mantissa)
            }

            fn to_fixed_dir_overflow(
                self,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> (Widest, Ordering, bool) {
                let prec = Self::PREC as i32;

                let (neg, exp, mut mantissa) = self.parts();
                debug_assert!(exp <= Self::EXP_MAX, "not finite");
                // if not subnormal, add implicit bit
                if exp >= Self::EXP_MIN {
                    mantissa |= 1 << (prec - 1);
                }
                if mantissa == 0 {
                    return (Widest::Unsigned(0), Ordering::Equal, false);
                }

                let mut src_frac_bits = prec - 1 - exp;
                let need_to_shr = src_frac_bits - dst_frac_bits as i32;
                if need_to_shr > prec {
                    let dir = if neg {
                        Ordering::Greater
                    } else {
                        Ordering::Less
                    };
                    return (Widest::Unsigned(0), dir, false);
                }
                let mut dir = Ordering::Equal;
                if need_to_shr > 0 {
                    let removed_bits = mantissa & !(!0 << need_to_shr);
                    let will_be_lsb = 1 << need_to_shr;
                    let tie = will_be_lsb >> 1;
                    if removed_bits == 0 {
                        // removed nothing
                    } else if removed_bits < tie {
                        dir = Ordering::Less;
                    } else if removed_bits > tie || mantissa & will_be_lsb != 0 {
                        mantissa += will_be_lsb;
                        dir = Ordering::Greater;
                    } else {
                        dir = Ordering::Less;
                    };
                    mantissa >>= need_to_shr;
                    src_frac_bits -= need_to_shr;
                }
                let mut mantissa = mantissa as $IBits;
                if neg {
                    mantissa = -mantissa;
                    dir = dir.reverse();
                }
                let (fixed, _, overflow) =
                    mantissa.to_fixed_dir_overflow(src_frac_bits, dst_frac_bits, dst_int_bits);
                (fixed, dir, overflow)
            }
        }
    };
}

#[cfg(feature = "f16")]
sealed_float! { f16(u16, i16, 11) }
sealed_float! { f32(u32, i32, 24) }
sealed_float! { f64(u64, i64, 53) }
