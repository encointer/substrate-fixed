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
    helpers::IntHelper,
    traits::ToFixed,
    types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    wide_div::WideDivRem,
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    cmp::Ordering,
    iter::{Product, Sum},
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
};

macro_rules! refs {
    (impl $Imp:ident for $Fixed:ident($Inner:ty, $LeEqU:ident) { $method:ident }) => {
        impl<'a, Frac: $LeEqU> $Imp<$Fixed<Frac>> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                (*self).$method(rhs)
            }
        }

        impl<'a, Frac: $LeEqU> $Imp<&'a $Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                self.$method(*rhs)
            }
        }

        impl<'a, 'b, Frac: $LeEqU> $Imp<&'a $Fixed<Frac>> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                (*self).$method(*rhs)
            }
        }
    };
}

macro_rules! refs_assign {
    (impl $Imp:ident for $Fixed:ident($Inner:ty, $LeEqU:ident) { $method:ident }) => {
        impl<'a, Frac: $LeEqU> $Imp<&'a $Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Fixed<Frac>) {
                self.$method(*rhs);
            }
        }
    };
}

macro_rules! pass {
    (impl $Imp:ident for $Fixed:ident($Inner:ty, $LeEqU:ident) { $method:ident }) => {
        impl<Frac: $LeEqU> $Imp<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().$method(rhs.to_bits()))
            }
        }

        refs! { impl $Imp for $Fixed($Inner, $LeEqU) { $method } }
    };
}

macro_rules! pass_assign {
    (impl $Imp:ident for $Fixed:ident($Inner:ty, $LeEqU:ident) { $method:ident }) => {
        impl<Frac: $LeEqU> $Imp<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: $Fixed<Frac>) {
                self.bits.$method(rhs.to_bits())
            }
        }

        refs_assign! { impl $Imp for $Fixed($Inner, $LeEqU) { $method } }
    };
}

macro_rules! pass_one {
    (impl $Imp:ident for $Fixed:ident($Inner:ty, $LeEqU:ident) { $method:ident }) => {
        impl<Frac: $LeEqU> $Imp for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().$method())
            }
        }

        impl<'a, Frac: $LeEqU> $Imp for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self) -> $Fixed<Frac> {
                (*self).$method()
            }
        }
    };
}

macro_rules! shift {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident($Inner:ty, $LeEqU:ident) { $method:ident }) => {
        impl<Frac: $LeEqU> $Imp<$Rhs> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits().$method(rhs))
            }
        }

        impl<'a, Frac: $LeEqU> $Imp<$Rhs> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<Frac> {
                (*self).$method(rhs)
            }
        }

        impl<'a, Frac: $LeEqU> $Imp<&'a $Rhs> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<Frac> {
                self.$method(*rhs)
            }
        }

        impl<'a, 'b, Frac: $LeEqU> $Imp<&'a $Rhs> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<Frac> {
                (*self).$method(*rhs)
            }
        }
    };
}

macro_rules! shift_assign {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident($Inner:ty, $LeEqU:ident) { $method:ident }) => {
        impl<Frac: $LeEqU> $Imp<$Rhs> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: $Rhs) {
                self.bits.$method(rhs)
            }
        }

        impl<'a, Frac: $LeEqU> $Imp<&'a $Rhs> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Rhs) {
                self.$method(*rhs)
            }
        }
    };
}

macro_rules! shift_all {
    (
        impl {$Imp:ident, $ImpAssign:ident}<{$($Rhs:ty),*}>
            for $Fixed:ident($Inner:ty, $LeEqU:ident)
        { $method:ident, $method_assign:ident }
    ) => { $(
        shift! { impl $Imp<$Rhs> for $Fixed($Inner, $LeEqU) { $method } }
        shift_assign! { impl $ImpAssign<$Rhs> for $Fixed($Inner, $LeEqU) { $method_assign } }
    )* };
}

macro_rules! fixed_arith {
    ($Fixed:ident($Inner:ty, $LeEqU:ident, $bits_count:expr), $Signedness:tt) => {
        if_signed! {
            $Signedness; pass_one! { impl Neg for $Fixed($Inner, $LeEqU) { neg } }
        }

        pass! { impl Add for $Fixed($Inner, $LeEqU) { add } }
        pass_assign! { impl AddAssign for $Fixed($Inner, $LeEqU) { add_assign } }
        pass! { impl Sub for $Fixed($Inner, $LeEqU) { sub } }
        pass_assign! { impl SubAssign for $Fixed($Inner, $LeEqU) { sub_assign } }

        impl<Frac: $LeEqU> Mul<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                debug_assert!(dir == Ordering::Equal, "overflow");
                Self::from_bits(ans)
            }
        }

        refs! { impl Mul for $Fixed($Inner, $LeEqU) { mul } }

        impl<Frac: $LeEqU> MulAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = (*self).mul(rhs)
            }
        }

        refs_assign! { impl MulAssign for $Fixed($Inner, $LeEqU) { mul_assign } }

        impl<Frac: $LeEqU> Div<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                debug_assert!(dir == Ordering::Equal, "overflow");
                Self::from_bits(ans)
            }
        }

        refs! { impl Div for $Fixed($Inner, $LeEqU) { div } }

        impl<Frac: $LeEqU> DivAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = (*self).div(rhs)
            }
        }

        refs_assign! { impl DivAssign for $Fixed($Inner, $LeEqU) { div_assign } }

        pass_one! { impl Not for $Fixed($Inner, $LeEqU) { not } }
        pass! { impl BitAnd for $Fixed($Inner, $LeEqU) { bitand } }
        pass_assign! { impl BitAndAssign for $Fixed($Inner, $LeEqU) { bitand_assign } }
        pass! { impl BitOr for $Fixed($Inner, $LeEqU) { bitor } }
        pass_assign! { impl BitOrAssign for $Fixed($Inner, $LeEqU) { bitor_assign } }
        pass! { impl BitXor for $Fixed($Inner, $LeEqU) { bitxor } }
        pass_assign! { impl BitXorAssign for $Fixed($Inner, $LeEqU) { bitxor_assign } }

        impl<Frac: $LeEqU> Mul<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().mul(rhs))
            }
        }

        impl<Frac: $LeEqU> Mul<$Fixed<Frac>> for $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                rhs.mul(self)
            }
        }

        impl<'a, Frac: $LeEqU> Mul<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Inner) -> $Fixed<Frac> {
                (*self).mul(rhs)
            }
        }

        impl<'a, Frac: $LeEqU> Mul<&'a $Fixed<Frac>> for $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                (*rhs).mul(self)
            }
        }

        impl<'a, Frac: $LeEqU> Mul<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Inner) -> $Fixed<Frac> {
                self.mul(*rhs)
            }
        }

        impl<'a, Frac: $LeEqU> Mul<$Fixed<Frac>> for &'a $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                rhs.mul(*self)
            }
        }

        impl<'a, 'b, Frac: $LeEqU> Mul<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Inner) -> $Fixed<Frac> {
                (*self).mul(*rhs)
            }
        }

        impl<'a, 'b, Frac: $LeEqU> Mul<&'a $Fixed<Frac>> for &'b $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                (*rhs).mul(*self)
            }
        }

        impl<Frac: $LeEqU> MulAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Inner) {
                *self = (*self).mul(rhs);
            }
        }

        impl<'a, Frac: $LeEqU> MulAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: &$Inner) {
                *self = (*self).mul(*rhs);
            }
        }

        impl<Frac: $LeEqU> Div<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().div(rhs))
            }
        }

        impl<'a, Frac: $LeEqU> Div<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Inner) -> $Fixed<Frac> {
                (*self).div(rhs)
            }
        }

        impl<'a, Frac: $LeEqU> Div<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: &$Inner) -> $Fixed<Frac> {
                self.div(*rhs)
            }
        }
        impl<'a, 'b, Frac: $LeEqU> Div<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: &$Inner) -> $Fixed<Frac> {
                (*self).div(*rhs)
            }
        }

        impl<Frac: $LeEqU> DivAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: $Inner) {
                *self = (*self).div(rhs);
            }
        }

        impl<'a, Frac: $LeEqU> DivAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: &$Inner) {
                *self = (*self).div(*rhs);
            }
        }

        impl<Frac: $LeEqU> Rem<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().rem(rhs))
            }
        }

        impl<'a, Frac: $LeEqU> Rem<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: $Inner) -> $Fixed<Frac> {
                (*self).rem(rhs)
            }
        }

        impl<'a, Frac: $LeEqU> Rem<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: &$Inner) -> $Fixed<Frac> {
                self.rem(*rhs)
            }
        }

        impl<'a, 'b, Frac: $LeEqU> Rem<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: &$Inner) -> $Fixed<Frac> {
                (*self).rem(*rhs)
            }
        }

        impl<Frac: $LeEqU> RemAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn rem_assign(&mut self, rhs: $Inner) {
                *self = (*self).rem(rhs);
            }
        }

        impl<'a, Frac: $LeEqU> RemAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn rem_assign(&mut self, rhs: &$Inner) {
                *self = (*self).rem(*rhs);
            }
        }

        shift_all! {
            impl {Shl, ShlAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed($Inner, $LeEqU) {
                shl, shl_assign
            }
        }
        shift_all! {
            impl {Shr, ShrAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed($Inner, $LeEqU) {
                shr, shr_assign
            }
        }

        impl<Frac: $LeEqU> Sum<$Fixed<Frac>> for $Fixed<Frac> {
            fn sum<I>(iter: I) -> $Fixed<Frac>
            where
                I: Iterator<Item = $Fixed<Frac>>,
            {
                iter.fold(Self::from_bits(0), Add::add)
            }
        }

        impl<'a, Frac: 'a + $LeEqU> Sum<&'a $Fixed<Frac>> for $Fixed<Frac> {
            fn sum<I>(iter: I) -> $Fixed<Frac>
            where
                I: Iterator<Item = &'a $Fixed<Frac>>,
            {
                iter.fold(Self::from_bits(0), Add::add)
            }
        }

        impl<Frac: $LeEqU> Product<$Fixed<Frac>> for $Fixed<Frac> {
            fn product<I>(mut iter: I) -> $Fixed<Frac>
            where
                I: Iterator<Item = $Fixed<Frac>>,
            {
                match iter.next() {
                    None => 1.to_fixed(),
                    Some(first) => iter.fold(first, Mul::mul),
                }
            }
        }

        impl<'a, Frac: 'a + $LeEqU> Product<&'a $Fixed<Frac>> for $Fixed<Frac> {
            fn product<I>(mut iter: I) -> $Fixed<Frac>
            where
                I: Iterator<Item = &'a $Fixed<Frac>>,
            {
                match iter.next() {
                    None => 1.to_fixed(),
                    Some(first) => iter.fold(*first, Mul::mul),
                }
            }
        }
    };
}

fixed_arith! { FixedU8(u8, LeEqU8, 8), Unsigned }
fixed_arith! { FixedU16(u16, LeEqU16, 16), Unsigned }
fixed_arith! { FixedU32(u32, LeEqU32, 32), Unsigned }
fixed_arith! { FixedU64(u64, LeEqU64, 64), Unsigned }
fixed_arith! { FixedU128(u128, LeEqU128, 128), Unsigned }
fixed_arith! { FixedI8(i8, LeEqU8, 8), Signed }
fixed_arith! { FixedI16(i16, LeEqU16, 16), Signed }
fixed_arith! { FixedI32(i32, LeEqU32, 32), Signed }
fixed_arith! { FixedI64(i64, LeEqU64, 64), Signed }
fixed_arith! { FixedI128(i128, LeEqU128, 128), Signed }

pub(crate) trait MulDivDir: Sized {
    fn mul_dir(self, rhs: Self, frac_nbits: u32) -> (Self, Ordering);
    fn div_dir(self, rhs: Self, frac_nbits: u32) -> (Self, Ordering);
}

macro_rules! mul_div_widen {
    ($Single:ty, $Double:ty, $Signedness:tt) => {
        impl MulDivDir for $Single {
            #[inline]
            fn mul_dir(self, rhs: $Single, frac_nbits: u32) -> ($Single, Ordering) {
                const NBITS: u32 = <$Single>::NBITS;
                let int_nbits: u32 = NBITS - frac_nbits;
                let lhs2 = <$Double>::from(self);
                let rhs2 = <$Double>::from(rhs) << int_nbits;
                let (prod2, overflow) = lhs2.overflowing_mul(rhs2);
                let dir;
                if_unsigned! {
                    $Signedness;
                    dir = if !overflow {
                        Ordering::Equal
                    } else {
                        Ordering::Less
                    };
                }
                if_signed! {
                    $Signedness;
                    dir = if !overflow {
                        Ordering::Equal
                    } else if (self < 0) == (rhs < 0) {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    };
                }
                ((prod2 >> NBITS) as $Single, dir)
            }

            #[inline]
            fn div_dir(self, rhs: $Single, frac_nbits: u32) -> ($Single, Ordering) {
                let lhs2 = <$Double>::from(self) << frac_nbits;
                let rhs2 = <$Double>::from(rhs);
                let quot2 = lhs2 / rhs2;
                let quot = quot2 as $Single;
                let dir = <$Double>::from(quot).cmp(&quot2);
                (quot, dir)
            }
        }
    };
}

trait FallbackHelper: Sized {
    type Unsigned;
    fn hi_lo(self) -> (Self, Self);
    fn shift_lo_up(self) -> Self;
    fn shift_lo_up_unsigned(self) -> Self::Unsigned;
    fn combine_lo_then_shl(self, lo: Self::Unsigned, shift: u32) -> (Self, Ordering);
    fn carrying_add(self, other: Self) -> (Self, Self);
}

impl FallbackHelper for u128 {
    type Unsigned = u128;
    #[inline]
    fn hi_lo(self) -> (u128, u128) {
        (self >> 64, self & !(!0 << 64))
    }

    #[inline]
    fn shift_lo_up(self) -> u128 {
        debug_assert!(self >> 64 == 0);
        self << 64
    }

    #[inline]
    fn shift_lo_up_unsigned(self) -> u128 {
        debug_assert!(self >> 64 == 0);
        self << 64
    }

    #[inline]
    fn combine_lo_then_shl(self, lo: u128, shift: u32) -> (u128, Ordering) {
        if shift == 128 {
            (self, Ordering::Equal)
        } else if shift == 0 {
            (lo, 0.cmp(&self))
        } else {
            let lo = lo >> shift;
            let hi = self << (128 - shift);
            (lo | hi, 0.cmp(&(self >> shift)))
        }
    }

    #[inline]
    fn carrying_add(self, rhs: u128) -> (u128, u128) {
        let (sum, overflow) = self.overflowing_add(rhs);
        let carry = if overflow { 1 } else { 0 };
        (sum, carry)
    }
}

impl FallbackHelper for i128 {
    type Unsigned = u128;
    #[inline]
    fn hi_lo(self) -> (i128, i128) {
        (self >> 64, self & !(!0 << 64))
    }

    #[inline]
    fn shift_lo_up(self) -> i128 {
        debug_assert!(self >> 64 == 0);
        self << 64
    }

    #[inline]
    fn shift_lo_up_unsigned(self) -> u128 {
        debug_assert!(self >> 64 == 0);
        (self << 64) as u128
    }

    #[inline]
    fn combine_lo_then_shl(self, lo: u128, shift: u32) -> (i128, Ordering) {
        if shift == 128 {
            (self, Ordering::Equal)
        } else if shift == 0 {
            let ans = lo as i128;
            (ans, (ans >> 64 >> 64).cmp(&self))
        } else {
            let lo = (lo >> shift) as i128;
            let hi = self << (128 - shift);
            let ans = lo | hi;
            (ans, (ans >> 64 >> 64).cmp(&(self >> shift)))
        }
    }

    #[inline]
    fn carrying_add(self, rhs: i128) -> (i128, i128) {
        let (sum, overflow) = self.overflowing_add(rhs);
        let carry = if overflow {
            if sum < 0 {
                1
            } else {
                -1
            }
        } else {
            0
        };
        (sum, carry)
    }
}

macro_rules! mul_div_fallback {
    ($Single:ty, $Uns:ty, $Signedness:tt) => {
        impl MulDivDir for $Single {
            #[inline]
            fn mul_dir(self, rhs: $Single, frac_nbits: u32) -> ($Single, Ordering) {
                if frac_nbits == 0 {
                    let (ans, overflow) = self.overflowing_mul(rhs);
                    let dir = if !overflow {
                        Ordering::Equal
                    } else {
                        if_signed_unsigned! {
                            $Signedness,
                            if (self < 0) == (rhs < 0) {
                                Ordering::Less
                            } else {
                                Ordering::Greater
                            },
                            Ordering::Less,
                        }
                    };
                    (ans, dir)
                } else {
                    let (lh, ll) = self.hi_lo();
                    let (rh, rl) = rhs.hi_lo();
                    let ll_rl = ll.wrapping_mul(rl);
                    let lh_rl = lh.wrapping_mul(rl);
                    let ll_rh = ll.wrapping_mul(rh);
                    let lh_rh = lh.wrapping_mul(rh);

                    let col01 = ll_rl as <$Single as FallbackHelper>::Unsigned;
                    let (col01_hi, col01_lo) = col01.hi_lo();
                    let partial_col12 = lh_rl + col01_hi as $Single;
                    let (col12, carry_col3) = partial_col12.carrying_add(ll_rh);
                    let (col12_hi, col12_lo) = col12.hi_lo();
                    let ans01 = col12_lo.shift_lo_up_unsigned() + col01_lo;
                    let ans23 = lh_rh + col12_hi + carry_col3.shift_lo_up();
                    ans23.combine_lo_then_shl(ans01, frac_nbits)
                }
            }

            #[inline]
            fn div_dir(self, rhs: $Single, frac_nbits: u32) -> ($Single, Ordering) {
                if frac_nbits == 0 {
                    let (ans, overflow) = self.overflowing_div(rhs);
                    let dir = if !overflow {
                        Ordering::Equal
                    } else {
                        if_signed_unsigned! {
                            $Signedness,
                            if (self < 0) == (rhs < 0) {
                                Ordering::Less
                            } else {
                                Ordering::Greater
                            },
                            Ordering::Less,
                        }
                    };
                    (ans, dir)
                } else {
                    const NBITS: u32 = <$Single>::NBITS;
                    let lhs2 = (self >> (NBITS - frac_nbits), (self << frac_nbits) as $Uns);
                    let (quot2, _) = rhs.div_rem_from(lhs2);
                    let quot = quot2.1 as $Single;
                    let quot2_ret = (quot >> (NBITS / 2) >> (NBITS - NBITS / 2), quot2.1);
                    let dir = (quot2_ret.0)
                        .cmp(&quot2.0)
                        .then((quot2_ret.1).cmp(&quot2.1));
                    (quot, dir)
                }
            }
        }
    };
}

mul_div_widen! { u8, u16, Unsigned }
mul_div_widen! { u16, u32, Unsigned }
mul_div_widen! { u32, u64, Unsigned }
mul_div_widen! { u64, u128, Unsigned }
mul_div_fallback! { u128, u128, Unsigned }
mul_div_widen! { i8, i16, Signed }
mul_div_widen! { i16, i32, Signed }
mul_div_widen! { i32, i64, Signed }
mul_div_widen! { i64, i128, Signed }
mul_div_fallback! { i128, u128, Signed }

#[cfg(test)]
mod tests {
    use crate::{types::extra::Unsigned, *};

    #[test]
    fn fixed_u16() {
        use crate::types::extra::U7 as Frac;
        let frac = Frac::U32;
        let a = 12;
        let b = 4;
        let af = FixedU16::<Frac>::from_bits(a << Frac::U32);
        let bf = FixedU16::<Frac>::from_bits(b << Frac::U32);
        assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
        assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
        assert_eq!((af * bf).to_bits(), (a << frac) * b);
        assert_eq!((af / bf).to_bits(), (a << frac) / b);
        assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
        assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
        assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
        assert_eq!((!af).to_bits(), !(a << frac));
        assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
        assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
    }

    #[test]
    fn fixed_i16() {
        use crate::types::extra::U7 as Frac;
        let frac = Frac::U32;
        let a = 12;
        let b = 4;
        for &pair in &[(a, b), (a, -b), (-a, b), (-a, -b)] {
            let (a, b) = pair;
            let af = FixedI16::<Frac>::from_bits(a << frac);
            let bf = FixedI16::<Frac>::from_bits(b << frac);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((-af).to_bits(), -(a << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
        }
    }

    #[test]
    fn fixed_u128() {
        use crate::types::extra::U7 as Frac;
        let frac = Frac::U32;
        let a = 0x0003_4567_89ab_cdef_0123_4567_89ab_cdef_u128;
        let b = 5;
        for &(a, b) in &[(a, b), (b, a)] {
            let af = FixedU128::<Frac>::from_bits(a << frac);
            let bf = FixedU128::<Frac>::from_bits(b << frac);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            if a > b {
                assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            }
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
        }
    }

    #[test]
    fn fixed_i128() {
        use crate::types::extra::U7 as Frac;
        let frac = Frac::U32;
        let a = 0x0003_4567_89ab_cdef_0123_4567_89ab_cdef_i128;
        let b = 5;
        for &(a, b) in &[
            (a, b),
            (a, -b),
            (-a, b),
            (-a, -b),
            (b, a),
            (b, -a),
            (-b, a),
            (-b, -a),
        ] {
            let af = FixedI128::<Frac>::from_bits(a << frac);
            let bf = FixedI128::<Frac>::from_bits(b << frac);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
        }
    }
}
