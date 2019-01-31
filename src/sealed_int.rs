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

use core::fmt::{Debug, Display};
use frac::{Bit, False, True, Unsigned, U1, U128, U16, U32, U64, U8};
use sealed_fixed::Widest;

pub trait SealedInt: Copy + Ord + Debug + Display {
    type NBits: Unsigned;
    type IsSigned: Bit;
    type Unsigned: SealedInt;

    const NBITS: u32 = Self::NBits::U32;
    const IS_SIGNED: bool = Self::IsSigned::BOOL;
    const MSB: Self;

    fn one_shl(shift: u32) -> Self;
    fn all_ones_shl(shift: u32) -> Self;
    fn is_zero(self) -> bool;
    fn is_positive(self) -> bool;
    fn is_negative(self) -> bool;

    fn to_fixed_overflow(
        self,
        src_frac_bits: u32,
        dst_frac_bits: u32,
        dst_int_bits: u32,
    ) -> (Widest, bool);

    fn neg_abs(self) -> (bool, Self::Unsigned);
    fn from_neg_abs(neg: bool, abs: Self::Unsigned) -> Self;
}

macro_rules! sealed_int {
    ($Int:ident($NBits:ident, $IsSigned:ident, $Unsigned:ty); $($rest:tt)*) => {
        impl SealedInt for $Int {
            type NBits = $NBits;
            type IsSigned = $IsSigned;
            type Unsigned = $Unsigned;

            const MSB: $Int = 1 << (Self::NBITS - 1);

            #[inline]
            fn one_shl(shift: u32) -> $Int {
                1 << shift
            }

            #[inline]
            fn all_ones_shl(shift: u32) -> $Int {
                !0 << shift
            }

            #[inline]
            fn is_zero(self) -> bool {
                self == 0
            }

            #[inline]
            fn is_positive(self) -> bool {
                self > 0
            }

            $($rest)*
        }
    };
    ($Unsigned:ident($NBits:ident)) => {
        sealed_int! {
            $Unsigned($NBits, False, $Unsigned);

            #[inline]
            fn is_negative(self) -> bool {
                false
            }

            #[inline]
            fn neg_abs(self) -> (bool, Self::Unsigned) {
                (false, self)
            }

            #[inline]
            fn from_neg_abs(neg: bool, abs: Self::Unsigned) -> Self {
                debug_assert!(!neg || abs == 0);
                let _ = neg;
                abs
            }

            #[inline]
            fn to_fixed_overflow(
                self,
                src_frac_bits: u32,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> (Widest, bool) {
                let src_bits = Self::NBITS as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if self == 0 {
                    return (Widest::Unsigned(0), false);
                }

                let leading_zeros = self.leading_zeros();
                let bits = self << leading_zeros;
                let need_to_shr =
                    leading_zeros as i32 + src_frac_bits as i32 - dst_frac_bits as i32;
                let overflow = src_bits - need_to_shr > dst_bits;
                let bits = if need_to_shr == 0 {
                    u128::from(bits)
                } else if need_to_shr < 0 && -need_to_shr < 128 {
                    u128::from(bits) << -need_to_shr
                } else if need_to_shr > 0 && need_to_shr < 128 {
                    u128::from(bits) >> need_to_shr
                } else {
                    0
                };
                (Widest::Unsigned(bits), overflow)
            }
        }
    };
    ($Signed:ident($NBits:ident, $Unsigned:ty)) => {
        sealed_int! {
            $Signed($NBits, True, $Unsigned);

            #[inline]
            fn is_negative(self) -> bool {
                self < 0
            }

            #[inline]
            fn neg_abs(self) -> (bool, Self::Unsigned) {
                if self < 0 {
                    (true, self.wrapping_neg() as $Unsigned)
                } else {
                    (false, self as $Unsigned)
                }
            }

            #[inline]
            fn from_neg_abs(neg: bool, abs: Self::Unsigned) -> Self {
                debug_assert!(abs <= Self::Unsigned::MSB);
                if neg {
                    abs.wrapping_neg() as Self
                } else {
                    abs as Self
                }
            }

            #[inline]
            fn to_fixed_overflow(
                self,
                src_frac_bits: u32,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> (Widest, bool) {
                let src_bits = Self::NBITS as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if self >= 0 {
                    return SealedInt::to_fixed_overflow(
                        self as $Unsigned,
                        src_frac_bits,
                        dst_frac_bits,
                        dst_int_bits,
                    );
                }

                let leading_ones = (!self).leading_zeros();
                let bits = self << (leading_ones - 1);
                let need_to_shr =
                    leading_ones as i32 - 1 + src_frac_bits as i32 - dst_frac_bits as i32;
                let overflow = src_bits - need_to_shr > dst_bits;
                let bits = if need_to_shr == 0 {
                    i128::from(bits)
                } else if need_to_shr < 0 && -need_to_shr < 128 {
                    i128::from(bits) << -need_to_shr
                } else if need_to_shr > 0 && need_to_shr < 128 {
                    i128::from(bits) >> need_to_shr
                } else {
                    0
                };
                (Widest::Negative(bits), overflow)
            }
        }
    };
}

impl SealedInt for bool {
    type NBits = U1;
    type IsSigned = False;
    type Unsigned = bool;

    const MSB: bool = true;

    #[inline]
    fn one_shl(shift: u32) -> bool {
        let _ = shift;
        debug_assert_eq!(shift, 0);
        true
    }

    #[inline]
    fn all_ones_shl(shift: u32) -> bool {
        let _ = shift;
        debug_assert_eq!(shift, 0);
        true
    }

    #[inline]
    fn is_zero(self) -> bool {
        !self
    }

    #[inline]
    fn is_positive(self) -> bool {
        self
    }

    #[inline]
    fn is_negative(self) -> bool {
        false
    }

    #[inline]
    fn to_fixed_overflow(
        self,
        src_frac_bits: u32,
        dst_frac_bits: u32,
        dst_int_bits: u32,
    ) -> (Widest, bool) {
        debug_assert_eq!(src_frac_bits, 0);
        let _ = src_frac_bits;
        if !self {
            return (Widest::Unsigned(0), false);
        }
        let overflow = dst_int_bits == 0;
        let bits = if dst_frac_bits == 0 {
            1u128
        } else if dst_frac_bits < 128 {
            1u128 << dst_frac_bits
        } else {
            0
        };
        (Widest::Unsigned(bits), overflow)
    }

    #[inline]
    fn neg_abs(self) -> (bool, bool) {
        (false, self)
    }

    #[inline]
    fn from_neg_abs(neg: bool, abs: bool) -> bool {
        debug_assert!(!neg || !abs);
        let _ = neg;
        abs
    }
}

sealed_int! { i8(U8, u8) }
sealed_int! { i16(U16, u16) }
sealed_int! { i32(U32, u32) }
sealed_int! { i64(U64, u64) }
sealed_int! { i128(U128, u128) }
sealed_int! { u8(U8) }
sealed_int! { u16(U16) }
sealed_int! { u32(U32) }
sealed_int! { u64(U64) }
sealed_int! { u128(U128) }
