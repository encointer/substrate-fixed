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

use crate::{
    frac::{Bit, False, True, Unsigned, U0, U128, U16, U32, U64, U8},
    sealed::{Fixed, SealedFixed, Widest},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    cmp::Ordering,
    fmt::{Debug, Display},
};

pub trait SealedInt: Copy {
    type NBits: Unsigned;
    type IsSigned: Bit;
    type Unsigned: SealedInt;
    type ReprFixed: Fixed;
    type Traits: Copy + Ord + Debug + Display;

    const NBITS: u32 = Self::NBits::U32;
    const IS_SIGNED: bool = Self::IsSigned::BOOL;
    const MSB: Self;
    const ZERO: Self;

    fn traits(self) -> Self::Traits;

    #[inline]
    fn from_fixed<F: Fixed>(val: F) -> Self {
        let (wrapped, overflow) = Self::overflowing_from_fixed(val);
        debug_assert!(!overflow, "{} overflows", val.traits());
        let _ = overflow;
        wrapped
    }
    #[inline]
    fn checked_from_fixed<F: Fixed>(val: F) -> Option<Self> {
        match Self::overflowing_from_fixed(val) {
            (_, true) => None,
            (wrapped, false) => Some(wrapped),
        }
    }
    fn saturating_from_fixed<F: Fixed>(val: F) -> Self;
    #[inline]
    fn wrapping_from_fixed<F: Fixed>(val: F) -> Self {
        let (wrapped, _) = Self::overflowing_from_fixed(val);
        wrapped
    }
    fn overflowing_from_fixed<F: Fixed>(val: F) -> (Self, bool);

    #[inline]
    fn to_fixed<F: Fixed>(self) -> F {
        let (wrapped, overflow) = Self::overflowing_to_fixed(self);
        debug_assert!(!overflow, "{} overflows", self.traits());
        let _ = overflow;
        wrapped
    }
    #[inline]
    fn checked_to_fixed<F: Fixed>(self) -> Option<F> {
        match Self::overflowing_to_fixed(self) {
            (_, true) => None,
            (wrapped, false) => Some(wrapped),
        }
    }
    fn saturating_to_fixed<F: Fixed>(self) -> F;
    #[inline]
    fn wrapping_to_fixed<F: Fixed>(self) -> F {
        let (wrapped, _) = Self::overflowing_to_fixed(self);
        wrapped
    }
    fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool);

    fn min_value() -> Self;
    fn max_value() -> Self;

    fn one_shl(shift: u32) -> Self;
    fn all_ones_shl(shift: u32) -> Self;
    fn is_zero(self) -> bool;
    fn is_negative(self) -> bool;
    fn checked_add(self, val: Self) -> Option<Self>;
    fn overflowing_add(self, val: Self) -> (Self, bool);
    fn leading_zeros(self) -> u32;

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
            type Traits = $Int;

            const MSB: $Int = 1 << (Self::NBITS - 1);
            const ZERO: $Int = 0;

            #[inline]
            fn traits(self) -> Self::Traits {
                self
            }

            #[inline]
            fn min_value() -> $Int {
                $Int::min_value()
            }

            #[inline]
            fn max_value() -> $Int {
                $Int::max_value()
            }

            #[inline]
            fn saturating_from_fixed<F: Fixed>(val: F) -> Self {
                let saturated = Self::ReprFixed::saturating_from_fixed(val);
                IntRepr::from_int_repr(saturated.to_bits())
            }
            #[inline]
            fn overflowing_from_fixed<F: Fixed>(val: F) -> (Self, bool) {
                let (wrapped, overflow) = Self::ReprFixed::overflowing_from_fixed(val);
                (IntRepr::from_int_repr(wrapped.to_bits()), overflow)
            }

            #[inline]
            fn saturating_to_fixed<F: Fixed>(self) -> F {
                SealedFixed::saturating_from_fixed(self.to_repr_fixed())
            }
            #[inline]
            fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool) {
                SealedFixed::overflowing_from_fixed(self.to_repr_fixed())
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
            fn checked_add(self, val: $Int) -> Option<$Int> {
                <$Int>::checked_add(self, val)
            }

            #[inline]
            fn overflowing_add(self, val: $Int) -> ($Int, bool) {
                <$Int>::overflowing_add(self, val)
            }

            #[inline]
            fn leading_zeros(self) -> u32 {
                <$Int>::leading_zeros(self)
            }

            #[inline]
            fn to_repr_fixed(self) -> Self::ReprFixed {
                Self::ReprFixed::from_bits(self.int_repr())
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
                let bits_128 = u128::from(self.int_repr());
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
                let bits_128 = i128::from(self.int_repr());
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
#[cfg(target_pointer_width = "32")]
sealed_int! { isize(U32, usize, FixedI32) }
#[cfg(target_pointer_width = "64")]
sealed_int! { isize(U64, usize, FixedI64) }
sealed_int! { u8(U8, FixedU8) }
sealed_int! { u16(U16, FixedU16) }
sealed_int! { u32(U32, FixedU32) }
sealed_int! { u64(U64, FixedU64) }
sealed_int! { u128(U128, FixedU128) }
#[cfg(target_pointer_width = "32")]
sealed_int! { usize(U32, FixedU32) }
#[cfg(target_pointer_width = "64")]
sealed_int! { usize(U64, FixedU64) }

trait IntRepr: Copy {
    type Int;
    fn int_repr(self) -> Self::Int;
    fn from_int_repr(i: Self::Int) -> Self;
}

macro_rules! int_repr {
    ($T:ident) => {
        impl IntRepr for $T {
            type Int = $T;
            #[inline]
            fn int_repr(self) -> $T {
                self
            }
            #[inline]
            fn from_int_repr(i: $T) -> $T {
                i
            }
        }
    };
    ($T:ident($Int:ident)) => {
        impl IntRepr for $T {
            type Int = $Int;
            #[inline]
            fn int_repr(self) -> $Int {
                self as $Int
            }
            #[inline]
            fn from_int_repr(i: $Int) -> $T {
                i as $T
            }
        }
    };
}

int_repr! { i8 }
int_repr! { i16 }
int_repr! { i32 }
int_repr! { i64 }
int_repr! { i128 }
#[cfg(target_pointer_width = "16")]
int_repr! { isize(i16) }
#[cfg(target_pointer_width = "32")]
int_repr! { isize(i32) }
#[cfg(target_pointer_width = "64")]
int_repr! { isize(i64) }
int_repr! { u8 }
int_repr! { u16 }
int_repr! { u32 }
int_repr! { u64 }
int_repr! { u128 }
#[cfg(target_pointer_width = "16")]
int_repr! { usize(u16) }
#[cfg(target_pointer_width = "32")]
int_repr! { usize(u32) }
#[cfg(target_pointer_width = "64")]
int_repr! { usize(u64) }
