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

pub trait SealedInt: Copy + Ord {
    type Unsigned: SealedInt;

    fn is_signed() -> bool;
    fn nbits() -> u32;
    fn one_shl(shift: u32) -> Self;
    fn all_ones_shl(shift: u32) -> Self;
    fn is_zero(self) -> bool;
    fn neg_abs(self) -> (bool, Self::Unsigned);
    fn from_neg_abs(neg: bool, abs: Self::Unsigned) -> Self;

    #[inline]
    fn msb() -> Self {
        Self::one_shl(Self::nbits() - 1)
    }
}

macro_rules! sealed_int {
    ($Int:ident($Unsigned:ty, $is_signed:ident, $nbits:expr); $($rest:tt)*) => {
        impl SealedInt for $Int {
            type Unsigned = $Unsigned;

            #[inline]
            fn is_signed() -> bool {
                $is_signed
            }

            #[inline]
            fn nbits() -> u32 {
                $nbits
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

            $($rest)*
        }
    };
    ($Int:ident($Unsigned:ty, false, $nbits:expr)) => {
        sealed_int! {
            $Int($Unsigned, false, $nbits);

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
        }
    };
    ($Int:ident($Unsigned:ty, true, $nbits:expr)) => {
        sealed_int! {
            $Int($Unsigned, true, $nbits);

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
                debug_assert!(abs <= Self::Unsigned::msb());
                if neg {
                    abs.wrapping_neg() as Self
                } else {
                    abs as Self
                }
            }
        }
    };
}

impl SealedInt for bool {
    type Unsigned = bool;

    #[inline]
    fn is_signed() -> bool {
        false
    }

    #[inline]
    fn nbits() -> u32 {
        1
    }

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

sealed_int! { i8(u8, true, 8) }
sealed_int! { i16(u16, true, 16) }
sealed_int! { i32(u32, true, 32) }
sealed_int! { i64(u64, true, 64) }
sealed_int! { i128(u128, true, 128) }
sealed_int! { u8(u8, false, 8) }
sealed_int! { u16(u16, false, 16) }
sealed_int! { u32(u32, false, 32) }
sealed_int! { u64(u64, false, 64) }
sealed_int! { u128(u128, false, 128) }
