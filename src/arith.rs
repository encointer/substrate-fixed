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

use frac::Unsigned;
use std::cmp::Ordering;
use std::iter::{Product, Sum};
use std::mem;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use {
    FixedHelper, FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32,
    FixedU64, FixedU8,
};

macro_rules! refs {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<'a, Frac: Unsigned> $Imp<$Fixed<Frac>> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Fixed<Frac>>>::$method(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> $Imp<&'a $Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Fixed<Frac>>>::$method(self, *rhs)
            }
        }

        impl<'a, 'b, Frac: Unsigned> $Imp<&'a $Fixed<Frac>> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Fixed<Frac>>>::$method(*self, *rhs)
            }
        }
    };
}

macro_rules! refs_assign {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<'a, Frac: Unsigned> $Imp<&'a $Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Fixed<Frac>) {
                <$Fixed<Frac> as $Imp<$Fixed<Frac>>>::$method(self, *rhs);
            }
        }
    };
}

macro_rules! pass {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner as $Imp<$Inner>>::$method(
                    self.to_bits(),
                    rhs.to_bits(),
                ))
            }
        }

        refs! { impl $Imp for $Fixed($Inner) { $method } }
    };
}

macro_rules! pass_assign {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: $Fixed<Frac>) {
                <$Inner as $Imp<$Inner>>::$method(&mut (self.0).0, rhs.to_bits());
            }
        }

        refs_assign! { impl $Imp for $Fixed($Inner) { $method } }
    };
}

macro_rules! pass_one {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner as $Imp>::$method(self.to_bits()))
            }
        }

        impl<'a, Frac: Unsigned> $Imp for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp>::$method(*self)
            }
        }
    };
}

macro_rules! shift {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp<$Rhs> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner as $Imp<$Rhs>>::$method(self.to_bits(), rhs))
            }
        }

        impl<'a, Frac: Unsigned> $Imp<$Rhs> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Rhs>>::$method(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> $Imp<&'a $Rhs> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Rhs>>::$method(self, *rhs)
            }
        }

        impl<'a, 'b, Frac: Unsigned> $Imp<&'a $Rhs> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Rhs>>::$method(*self, *rhs)
            }
        }
    };
}

macro_rules! shift_assign {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp<$Rhs> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: $Rhs) {
                <$Inner as $Imp<$Rhs>>::$method(&mut (self.0).0, rhs);
            }
        }

        impl<'a, Frac: Unsigned> $Imp<&'a $Rhs> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Rhs) {
                <$Fixed<Frac> as $Imp<$Rhs>>::$method(self, *rhs);
            }
        }
    };
}

macro_rules! shift_all {
    (
        impl {$Imp:ident, $ImpAssign:ident}<{$($Rhs:ty),*}>
            for $Fixed:ident($Inner:ty)
        { $method:ident, $method_assign:ident }
    ) => { $(
        shift! { impl $Imp<$Rhs> for $Fixed($Inner) { $method } }
        shift_assign! { impl $ImpAssign<$Rhs> for $Fixed($Inner) { $method_assign } }
    )* };
}

macro_rules! fixed_arith {
    ($Fixed:ident($Inner:ty, $bits_count:expr), $Signedness:tt) => {
        if_signed! {
            $Signedness => pass_one! { impl Neg for $Fixed($Inner) { neg } }
        }

        pass! { impl Add for $Fixed($Inner) { add } }
        pass_assign! { impl AddAssign for $Fixed($Inner) { add_assign } }
        pass! { impl Sub for $Fixed($Inner) { sub } }
        pass_assign! { impl SubAssign for $Fixed($Inner) { sub_assign } }

        impl<Frac: Unsigned> Mul<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                debug_assert!(dir == Ordering::Equal, "overflow");
                $Fixed::from_bits(ans)
            }
        }

        refs! { impl Mul for $Fixed($Inner) { mul } }

        impl<Frac: Unsigned> MulAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = <$Fixed<Frac> as Mul<$Fixed<Frac>>>::mul(*self, rhs)
            }
        }

        refs_assign! { impl MulAssign for $Fixed($Inner) { mul_assign } }

        impl<Frac: Unsigned> Div<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                debug_assert!(dir == Ordering::Equal, "overflow");
                $Fixed::from_bits(ans)
            }
        }

        refs! { impl Div for $Fixed($Inner) { div } }

        impl<Frac: Unsigned> DivAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = <$Fixed<Frac> as Div<$Fixed<Frac>>>::div(*self, rhs)
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

        impl<Frac: Unsigned> Mul<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits() * rhs)
            }
        }

        impl<Frac: Unsigned> Mul<$Fixed<Frac>> for $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(rhs, self)
            }
        }

        impl<'a, Frac: Unsigned> Mul<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> Mul<&'a $Fixed<Frac>> for $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(*rhs, self)
            }
        }

        impl<'a, Frac: Unsigned> Mul<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(self, *rhs)
            }
        }

        impl<'a, Frac: Unsigned> Mul<$Fixed<Frac>> for &'a $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(rhs, *self)
            }
        }

        impl<'a, 'b, Frac: Unsigned> Mul<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(*self, *rhs)
            }
        }

        impl<'a, 'b, Frac: Unsigned> Mul<&'a $Fixed<Frac>> for &'b $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(*rhs, *self)
            }
        }

        impl<Frac: Unsigned> MulAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Inner) {
                *self = <$Fixed<Frac> as Mul<$Inner>>::mul(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> MulAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: &$Inner) {
                *self = <$Fixed<Frac> as Mul<$Inner>>::mul(*self, *rhs)
            }
        }

        impl<Frac: Unsigned> Div<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits() / rhs)
            }
        }

        impl<'a, Frac: Unsigned> Div<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Div<$Inner>>::div(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> Div<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Div<$Inner>>::div(self, *rhs)
            }
        }
        impl<'a, 'b, Frac: Unsigned> Div<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Div<$Inner>>::div(*self, *rhs)
            }
        }

        impl<Frac: Unsigned> DivAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: $Inner) {
                *self = <$Fixed<Frac> as Div<$Inner>>::div(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> DivAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: &$Inner) {
                *self = <$Fixed<Frac> as Div<$Inner>>::div(*self, *rhs)
            }
        }

        impl<Frac: Unsigned> Rem<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits() % rhs)
            }
        }

        impl<'a, Frac: Unsigned> Rem<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: $Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Rem<$Inner>>::rem(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> Rem<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Rem<$Inner>>::rem(self, *rhs)
            }
        }
        impl<'a, 'b, Frac: Unsigned> Rem<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Rem<$Inner>>::rem(*self, *rhs)
            }
        }

        impl<Frac: Unsigned> RemAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn rem_assign(&mut self, rhs: $Inner) {
                *self = <$Fixed<Frac> as Rem<$Inner>>::rem(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> RemAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn rem_assign(&mut self, rhs: &$Inner) {
                *self = <$Fixed<Frac> as Rem<$Inner>>::rem(*self, *rhs)
            }
        }

        shift_all! {
            impl {Shl, ShlAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed($Inner) {
                shl, shl_assign
            }
        }
        shift_all! {
            impl {Shr, ShrAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed($Inner) {
                shr, shr_assign
            }
        }

        impl<Frac: Unsigned> Sum<$Fixed<Frac>> for $Fixed<Frac> {
            fn sum<I: Iterator<Item = $Fixed<Frac>>>(iter: I) -> $Fixed<Frac> {
                iter.fold($Fixed::from_bits(0), Add::add)
            }
        }

        impl<'a, Frac: Unsigned + 'a> Sum<&'a $Fixed<Frac>> for $Fixed<Frac> {
            fn sum<I: Iterator<Item = &'a $Fixed<Frac>>>(iter: I) -> $Fixed<Frac> {
                iter.fold($Fixed::from_bits(0), Add::add)
            }
        }

        impl<Frac: Unsigned> Product<$Fixed<Frac>> for $Fixed<Frac> {
            fn product<I: Iterator<Item = $Fixed<Frac>>>(mut iter: I) -> $Fixed<Frac> {
                match iter.next() {
                    None => <$Fixed<Frac> as FixedHelper<Frac>>::one().expect("overflow"),
                    Some(first) => iter.fold(first, Mul::mul),
                }
            }
        }

        impl<'a, Frac: Unsigned + 'a> Product<&'a $Fixed<Frac>> for $Fixed<Frac> {
            fn product<I: Iterator<Item = &'a $Fixed<Frac>>>(mut iter: I) -> $Fixed<Frac> {
                match iter.next() {
                    None => <$Fixed<Frac> as FixedHelper<Frac>>::one().expect("overflow"),
                    Some(first) => iter.fold(*first, Mul::mul),
                }
            }
        }
    };
}

fixed_arith! { FixedU8(u8, 8), Unsigned }
fixed_arith! { FixedU16(u16, 16), Unsigned }
fixed_arith! { FixedU32(u32, 32), Unsigned }
fixed_arith! { FixedU64(u64, 64), Unsigned }
fixed_arith! { FixedU128(u128, 128), Unsigned }
fixed_arith! { FixedI8(i8, 8), Signed }
fixed_arith! { FixedI16(i16, 16), Signed }
fixed_arith! { FixedI32(i32, 32), Signed }
fixed_arith! { FixedI64(i64, 64), Signed }
fixed_arith! { FixedI128(i128, 128), Signed }

pub(crate) trait MulDivDir: Sized {
    fn mul_dir(self, rhs: Self, frac_bits: u32) -> (Self, Ordering);
    fn div_dir(self, rhs: Self, frac_bits: u32) -> (Self, Ordering);
}

macro_rules! mul_div_widen {
    ($Single:ty, $Double:ty, $Signedness:tt) => {
        impl MulDivDir for $Single {
            #[inline]
            fn mul_dir(self, rhs: $Single, frac_bits: u32) -> ($Single, Ordering) {
                const BITS: u32 = mem::size_of::<$Single>() as u32 * 8;
                let int_bits: u32 = BITS - frac_bits;
                let lhs2 = self as $Double;
                let rhs2 = rhs as $Double << int_bits;
                let (prod2, overflow) = lhs2.overflowing_mul(rhs2);
                let dir;
                if_unsigned! { $Signedness => {
                    dir = if !overflow {
                        Ordering::Equal
                    } else {
                        Ordering::Less
                    };
                } }
                if_signed! { $Signedness => {
                    dir = if !overflow {
                        Ordering::Equal
                    } else if (self < 0) == (rhs < 0) {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    };
                } }
                ((prod2 >> BITS) as $Single, dir)
            }

            #[inline]
            fn div_dir(self, rhs: $Single, frac_bits: u32) -> ($Single, Ordering) {
                let lhs2 = self as $Double << frac_bits;
                let rhs2 = rhs as $Double;
                let quot2 = lhs2 / rhs2;
                let quot = quot2 as $Single;
                let dir = (quot as $Double).cmp(&quot2);
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
            return (self, Ordering::Equal);
        }
        if shift == 0 {
            return (lo, 0.cmp(&self));
        }
        let lo = lo >> shift;
        let hi = self << (128 - shift);
        (lo | hi, 0.cmp(&(self >> shift)))
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
            return (self, Ordering::Equal);
        }
        if shift == 0 {
            let ans = lo as i128;
            return (ans, (ans >> 64 >> 64).cmp(&self));
        }
        let lo = (lo >> shift) as i128;
        let hi = self << (128 - shift);
        let ans = lo | hi;
        (ans, (ans >> 64 >> 64).cmp(&(self >> shift)))
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
    ($Single:ty, $Signedness:tt) => {
        impl MulDivDir for $Single {
            fn mul_dir(self, rhs: $Single, frac_bits: u32) -> ($Single, Ordering) {
                if frac_bits == 0 {
                    let (ans, overflow) = self.overflowing_mul(rhs);
                    let dir;
                    if_unsigned! { $Signedness => {
                        dir = if !overflow {
                            Ordering::Equal
                        } else {
                            Ordering::Less
                        };
                    } }
                    if_signed! { $Signedness => {
                        dir = if !overflow {
                            Ordering::Equal
                        } else if (self < 0) == (rhs < 0) {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        };
                    } }
                    (ans, dir)
                } else {
                    let (lh, ll) = self.hi_lo();
                    let (rh, rl) = rhs.hi_lo();
                    let ll_rl = ll.wrapping_mul(rl);
                    let lh_rl = lh.wrapping_mul(rl);
                    let ll_rh = ll.wrapping_mul(rh);
                    let lh_rh = lh.wrapping_mul(rh);
                    let col01 = ll_rl as <$Single as FallbackHelper>::Unsigned;
                    let (col12, carry_col3) = lh_rl.carrying_add(ll_rh);
                    let col23 = lh_rh;
                    let (col12_hi, col12_lo) = col12.hi_lo();
                    let col12_lo_up = col12_lo.shift_lo_up_unsigned();
                    let (ans01, carry_col2) = col01.carrying_add(col12_lo_up);
                    let carries = carry_col2 as $Single + carry_col3.shift_lo_up();
                    let ans23 = col23.wrapping_add(carries).wrapping_add(col12_hi);

                    ans23.combine_lo_then_shl(ans01, frac_bits)
                }
            }

            fn div_dir(self, rhs: $Single, frac_bits: u32) -> ($Single, Ordering) {
                if frac_bits == 0 {
                    let (ans, overflow) = self.overflowing_div(rhs);
                    let dir;
                    if_unsigned! { $Signedness => {
                        dir = if !overflow {
                            Ordering::Equal
                        } else {
                            Ordering::Less
                        };
                    } }
                    if_signed! { $Signedness => {
                        dir = if !overflow {
                            Ordering::Equal
                        } else if (self < 0) == (rhs < 0) {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        };
                    } }
                    (ans, dir)
                } else {
                    unimplemented!()
                }
            }
        }
    };
}

mul_div_widen! { u8, u16, Unsigned }
mul_div_widen! { u16, u32, Unsigned }
mul_div_widen! { u32, u64, Unsigned }
mul_div_widen! { u64, u128, Unsigned }
mul_div_fallback! { u128, Unsigned }
mul_div_widen! { i8, i16, Signed }
mul_div_widen! { i16, i32, Signed }
mul_div_widen! { i32, i64, Signed }
mul_div_widen! { i64, i128, Signed }
mul_div_fallback! { i128, Signed }

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn fixed_u16() {
        use frac::U7 as Frac;
        let frac = Frac::to_u32();
        let a = 12;
        let b = 4;
        let af = FixedU16::<Frac>::from_bits(a << Frac::to_u32());
        let bf = FixedU16::<Frac>::from_bits(b << Frac::to_u32());
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
        use frac::U7 as Frac;
        let frac = Frac::to_u32();
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
        use frac::U7 as Frac;
        let frac = Frac::to_u32();
        let a = 0x0003456789abcdef_0123456789abcdef_u128;
        let b = 5;
        let af = FixedU128::<Frac>::from_bits(a << frac);
        let bf = FixedU128::<Frac>::from_bits(b << frac);
        assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
        assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
        assert_eq!((af * bf).to_bits(), (a << frac) * b);
        // assert_eq!((af / bf).to_bits(), (a << frac) / b);
        assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
        assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
        assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
        assert_eq!((!af).to_bits(), !(a << frac));
    }

    #[test]
    fn fixed_i128() {
        use frac::U7 as Frac;
        let frac = Frac::to_u32();
        let a = 0x0003456789abcdef_0123456789abcdef_i128;
        let b = 5;
        for &pair in &[(a, b), (a, -b), (-a, b), (-a, -b)] {
            let (a, b) = pair;
            let af = FixedI128::<Frac>::from_bits(a << frac);
            let bf = FixedI128::<Frac>::from_bits(b << frac);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            // assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
        }
    }
}
