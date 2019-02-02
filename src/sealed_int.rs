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
use frac::{Bit, False, True, Unsigned, U0, U128, U16, U32, U64, U8};
use sealed::{Fixed, Widest};
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

pub trait SealedInt: Copy + Ord + Debug + Display {
    type NBits: Unsigned;
    type IsSigned: Bit;
    type Unsigned: SealedInt;
    type ReprFixed: Fixed;

    const NBITS: u32 = Self::NBits::U32;
    const IS_SIGNED: bool = Self::IsSigned::BOOL;
    const MSB: Self;

    fn overflowing_from_fixed<F>(fixed: F) -> (Self, bool)
    where
        F: Fixed;
    fn overflowing_to_fixed<F>(self) -> (F, bool)
    where
        F: Fixed;

    fn min_value() -> Self;
    fn max_value() -> Self;

    fn one_shl(shift: u32) -> Self;
    fn all_ones_shl(shift: u32) -> Self;
    fn is_zero(self) -> bool;
    fn is_negative(self) -> bool;

    fn to_fixed_dir_overflow(
        self,
        src_frac_bits: i32,
        dst_frac_bits: u32,
        dst_int_bits: u32,
    ) -> (Widest, Ordering, bool);

    fn to_repr_fixed(self) -> Self::ReprFixed;

    fn neg_abs(self) -> (bool, Self::Unsigned);
    fn from_neg_abs(neg: bool, abs: Self::Unsigned) -> Self;
}

macro_rules! sealed_int {
    ($Int:ident($NBits:ident, $IsSigned:ident, $Unsigned:ty, $ReprFixed:ident); $($rest:tt)*) => {
        impl SealedInt for $Int {
            type NBits = $NBits;
            type IsSigned = $IsSigned;
            type Unsigned = $Unsigned;
            type ReprFixed = $ReprFixed<U0>;

            const MSB: $Int = 1 << (Self::NBITS - 1);

            #[inline]
            fn min_value() -> $Int {
                $Int::min_value()
            }

            #[inline]
            fn max_value() -> $Int {
                $Int::max_value()
            }

            #[inline]
            fn overflowing_from_fixed<F>(fixed: F) -> (Self, bool)
            where
                F: Fixed,
            {
                let (wrapped, overflow) = Self::ReprFixed::overflowing_from_fixed(fixed);
                (wrapped.to_bits(), overflow)
            }

            #[inline]
            fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed
            {
                F::overflowing_from_fixed(Self::ReprFixed::from_bits(self))
            }

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
            fn to_repr_fixed(self) -> Self::ReprFixed {
                Self::ReprFixed::from_bits(self)
            }

            $($rest)*
        }
    };
    ($Unsigned:ident($NBits:ident, $ReprFixed:ident)) => {
        sealed_int! {
            $Unsigned($NBits, False, $Unsigned, $ReprFixed);

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
            fn to_fixed_dir_overflow(
                self,
                src_frac_bits: i32,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> (Widest, Ordering, bool) {
                let src_bits = Self::NBITS as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if self == 0 {
                    return (Widest::Unsigned(0), Ordering::Equal, false);
                }

                let leading_zeros = self.leading_zeros();
                let need_to_shr = src_frac_bits - dst_frac_bits as i32;
                let overflow = src_bits - dst_bits > need_to_shr + leading_zeros as i32;
                let bits_128 = u128::from(self);
                let (bits, lost_bits) = match need_to_shr {
                    -0x7fff_ffff..=-128 => (0, false),
                    -127..=-1 => (bits_128 << -need_to_shr, false),
                    0 => (bits_128, false),
                    1..=127 => {
                        let shifted = bits_128 >> need_to_shr;
                        (shifted, shifted << need_to_shr != bits_128)
                    }
                    128..=0x7fff_ffff => (0, true),
                    _ => unreachable!(),
                };
                let dir = if lost_bits { Ordering::Less } else { Ordering::Equal };
                (Widest::Unsigned(bits), dir, overflow)
            }
        }
    };
    ($Signed:ident($NBits:ident, $Unsigned:ty, $ReprFixed:ident)) => {
        sealed_int! {
            $Signed($NBits, True, $Unsigned, $ReprFixed);

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
            fn to_fixed_dir_overflow(
                self,
                src_frac_bits: i32,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> (Widest, Ordering, bool) {
                let src_bits = Self::NBITS as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if self == 0 {
                    return (Widest::Unsigned(0), Ordering::Equal, false);
                }

                let need_to_shr = src_frac_bits - dst_frac_bits as i32;
                let leading = if self >= 0 {
                    self.leading_zeros()
                } else {
                    (!self).leading_zeros() - 1
                };
                let overflow = src_bits - dst_bits > need_to_shr + leading as i32;
                let bits_128 = i128::from(self);
                let (bits, lost_bits) = match need_to_shr {
                    -0x7fff_ffff..=-128 => (0, false),
                    -127..=-1 => (bits_128 << -need_to_shr, false),
                    0 => (bits_128, false),
                    1..=127 => {
                        let shifted = bits_128 >> need_to_shr;
                        (shifted, shifted << need_to_shr != bits_128)
                    }
                    128..=0x7fff_ffff => (bits_128 >> 127, true),
                    _ => unreachable!(),
                };
                let dir = if lost_bits { Ordering::Less } else { Ordering::Equal };
                if self >= 0 {
                    (Widest::Unsigned(bits as u128), dir, overflow)
                } else {
                    (Widest::Negative(bits), dir, overflow)
                }
            }
        }
    };
}

sealed_int! { i8(U8, u8, FixedI8) }
sealed_int! { i16(U16, u16, FixedI16) }
sealed_int! { i32(U32, u32, FixedI32) }
sealed_int! { i64(U64, u64, FixedI64) }
sealed_int! { i128(U128, u128, FixedI128) }
sealed_int! { u8(U8, FixedU8) }
sealed_int! { u16(U16, FixedU16) }
sealed_int! { u32(U32, FixedU32) }
sealed_int! { u64(U64, FixedU64) }
sealed_int! { u128(U128, FixedU128) }
