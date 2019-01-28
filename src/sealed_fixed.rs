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
use frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8};
use sealed::SealedInt;
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

pub trait SealedFixed: Copy + Debug + Display {
    type Bits: SealedInt;
    type Frac: Unsigned;

    fn frac_bits() -> u32;
    fn int_bits() -> u32 {
        Self::Bits::nbits() - Self::frac_bits()
    }

    #[inline]
    fn one() -> Option<Self> {
        let min_int_bits = if Self::Bits::is_signed() { 2 } else { 1 };
        if Self::int_bits() < min_int_bits {
            None
        } else {
            Some(Self::from_bits(Self::Bits::one_shl(Self::frac_bits())))
        }
    }

    #[inline]
    fn minus_one() -> Option<Self> {
        if !Self::Bits::is_signed() || Self::int_bits() < 1 {
            None
        } else {
            Some(Self::from_bits(Self::Bits::all_ones_shl(Self::frac_bits())))
        }
    }

    fn from_bits(bits: Self::Bits) -> Self;
    fn to_bits(self) -> Self::Bits;
    fn parts(
        self,
    ) -> (
        bool,
        <Self::Bits as SealedInt>::Unsigned,
        <Self::Bits as SealedInt>::Unsigned,
    );

    fn to_neg_abs_overflow(self, frac_bits: u32, int_bits: u32) -> (bool, u128, bool);
}

macro_rules! sealed_fixed {
    ($Fixed:ident($Bits:ty, $Len:ty)) => {
        impl<Frac> SealedFixed for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type Bits = $Bits;
            type Frac = Frac;

            #[inline]
            fn frac_bits() -> u32 {
                Frac::to_u32()
            }

            #[inline]
            fn from_bits(bits: Self::Bits) -> Self {
                $Fixed::from_bits(bits)
            }

            #[inline]
            fn to_bits(self) -> Self::Bits {
                $Fixed::to_bits(self)
            }

            #[inline]
            fn parts(
                self,
            ) -> (
                bool,
                <Self::Bits as SealedInt>::Unsigned,
                <Self::Bits as SealedInt>::Unsigned,
            ) {
                let frac_bits = <Self as SealedFixed>::frac_bits();
                let int_bits = <Self as SealedFixed>::int_bits();

                let (neg, abs) = SealedInt::neg_abs(self.to_bits());
                let (int_abs, frac_abs) = if int_bits == 0 {
                    (0, abs)
                } else if frac_bits == 0 {
                    (abs, 0)
                } else {
                    ((abs >> frac_bits), (abs << int_bits))
                };
                (neg, int_abs, frac_abs)
            }

            #[inline]
            fn to_neg_abs_overflow(
                self,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> (bool, u128, bool) {
                let src_frac_bits = <Self as SealedFixed>::frac_bits();
                let src_bits = Self::Bits::nbits() as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if SealedInt::is_zero(self.to_bits()) {
                    return (false, 0, false);
                }

                let (neg, mut abs) = SealedInt::neg_abs(self.to_bits());
                let leading_zeros = abs.leading_zeros();
                abs <<= leading_zeros;
                let need_to_shr =
                    leading_zeros as i32 + src_frac_bits as i32 - dst_frac_bits as i32;
                let overflow = src_bits - need_to_shr > dst_bits;
                let abs = if need_to_shr == 0 {
                    u128::from(abs)
                } else if need_to_shr < 0 && -need_to_shr < 128 {
                    u128::from(abs) << -need_to_shr
                } else if need_to_shr > 0 && need_to_shr < 128 {
                    u128::from(abs) >> need_to_shr
                } else {
                    0
                };
                (neg, abs, overflow)
            }
        }
    };
}

sealed_fixed! { FixedI8(i8, U8) }
sealed_fixed! { FixedI16(i16, U16) }
sealed_fixed! { FixedI32(i32, U32) }
sealed_fixed! { FixedI64(i64, U64) }
sealed_fixed! { FixedI128(i128, U128) }
sealed_fixed! { FixedU8(u8, U8) }
sealed_fixed! { FixedU16(u16, U16) }
sealed_fixed! { FixedU32(u32, U32) }
sealed_fixed! { FixedU64(u64, U64) }
sealed_fixed! { FixedU128(u128, U128) }
