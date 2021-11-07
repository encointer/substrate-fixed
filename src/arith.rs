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
    iter::{Product, Sum},
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
};

macro_rules! refs {
    (impl $Imp:ident for $Fixed:ident$(($LeEqU:ident))* { $method:ident }) => {
        impl<'a, Frac $(: $LeEqU)*> $Imp<$Fixed<Frac>> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                (*self).$method(rhs)
            }
        }

        impl<'a, Frac $(: $LeEqU)*> $Imp<&'a $Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                self.$method(*rhs)
            }
        }

        impl<'a, 'b, Frac $(: $LeEqU)*> $Imp<&'a $Fixed<Frac>> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                (*self).$method(*rhs)
            }
        }
    };

    (impl $Imp:ident<$Inner:ty> for $Fixed:ident$(($LeEqU:ident))* { $method:ident }) => {
        impl<'a, Frac $(: $LeEqU)*> $Imp<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Inner) -> $Fixed<Frac> {
                (*self).$method(rhs)
            }
        }

        impl<'a, Frac $(: $LeEqU)*> $Imp<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Inner) -> $Fixed<Frac> {
                self.$method(*rhs)
            }
        }

        impl<'a, 'b, Frac $(: $LeEqU)*> $Imp<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Inner) -> $Fixed<Frac> {
                (*self).$method(*rhs)
            }
        }
    };
}

macro_rules! refs_assign {
    (impl $Imp:ident for $Fixed:ident$(($LeEqU:ident))* { $method:ident }) => {
        impl<'a, Frac $(: $LeEqU)*> $Imp<&'a $Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Fixed<Frac>) {
                self.$method(*rhs);
            }
        }
    };

    (impl $Imp:ident<$Inner:ty> for $Fixed:ident$(($LeEqU:ident))* { $method:ident }) => {
        impl<'a, Frac $(: $LeEqU)*> $Imp<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Inner) {
                self.$method(*rhs);
            }
        }
    };
}

macro_rules! pass {
    (impl $Imp:ident for $Fixed:ident { $method:ident }) => {
        impl<Frac> $Imp<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().$method(rhs.to_bits()))
            }
        }

        refs! { impl $Imp for $Fixed { $method } }
    };
}

macro_rules! pass_assign {
    (impl $Imp:ident for $Fixed:ident { $method:ident }) => {
        impl<Frac> $Imp<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: $Fixed<Frac>) {
                self.bits.$method(rhs.to_bits())
            }
        }

        refs_assign! { impl $Imp for $Fixed { $method } }
    };
}

macro_rules! pass_one {
    (impl $Imp:ident for $Fixed:ident { $method:ident }) => {
        impl<Frac> $Imp for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().$method())
            }
        }

        impl<'a, Frac> $Imp for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self) -> $Fixed<Frac> {
                (*self).$method()
            }
        }
    };
}

macro_rules! shift {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident { $method:ident }) => {
        impl<Frac> $Imp<$Rhs> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits().$method(rhs))
            }
        }

        impl<'a, Frac> $Imp<$Rhs> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<Frac> {
                (*self).$method(rhs)
            }
        }

        impl<'a, Frac> $Imp<&'a $Rhs> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<Frac> {
                self.$method(*rhs)
            }
        }

        impl<'a, 'b, Frac> $Imp<&'a $Rhs> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<Frac> {
                (*self).$method(*rhs)
            }
        }
    };
}

macro_rules! shift_assign {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident { $method:ident }) => {
        impl<Frac> $Imp<$Rhs> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: $Rhs) {
                self.bits.$method(rhs)
            }
        }

        impl<'a, Frac> $Imp<&'a $Rhs> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Rhs) {
                self.$method(*rhs)
            }
        }
    };
}

macro_rules! shift_all {
    (
        impl {$Imp:ident, $ImpAssign:ident}<{$($Rhs:ty),*}> for $Fixed:ident
        { $method:ident, $method_assign:ident }
    ) => { $(
        shift! { impl $Imp<$Rhs> for $Fixed { $method } }
        shift_assign! { impl $ImpAssign<$Rhs> for $Fixed { $method_assign } }
    )* };
}

macro_rules! fixed_arith {
    ($Fixed:ident($Inner:ty, $LeEqU:ident, $bits_count:expr), $Signedness:tt) => {
        if_signed! {
            $Signedness; pass_one! { impl Neg for $Fixed { neg } }
        }

        pass! { impl Add for $Fixed { add } }
        pass_assign! { impl AddAssign for $Fixed { add_assign } }
        pass! { impl Sub for $Fixed { sub } }
        pass_assign! { impl SubAssign for $Fixed { sub_assign } }

        impl<Frac: $LeEqU> Mul<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, overflow) = self.to_bits().mul_overflow(rhs.to_bits(), Frac::U32);
                debug_assert!(!overflow, "overflow");
                Self::from_bits(ans)
            }
        }

        refs! { impl Mul for $Fixed($LeEqU) { mul } }

        impl<Frac: $LeEqU> MulAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = (*self).mul(rhs)
            }
        }

        refs_assign! { impl MulAssign for $Fixed($LeEqU) { mul_assign } }

        impl<Frac: $LeEqU> Div<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, overflow) = self.to_bits().div_overflow(rhs.to_bits(), Frac::U32);
                debug_assert!(!overflow, "overflow");
                Self::from_bits(ans)
            }
        }

        refs! { impl Div for $Fixed($LeEqU) { div } }

        impl<Frac: $LeEqU> DivAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = (*self).div(rhs)
            }
        }

        refs_assign! { impl DivAssign for $Fixed($LeEqU) { div_assign } }

        // do not pass! { Rem }, as I::min_value() % I::from(-1) should return 0, not panic
        impl<Frac> Rem<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                self.checked_rem(rhs).expect("division by zero")
            }
        }

        refs! { impl Rem for $Fixed { rem } }

        impl<Frac> RemAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn rem_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = (*self).rem(rhs)
            }
        }

        refs_assign! { impl RemAssign for $Fixed { rem_assign } }

        pass_one! { impl Not for $Fixed { not } }
        pass! { impl BitAnd for $Fixed { bitand } }
        pass_assign! { impl BitAndAssign for $Fixed { bitand_assign } }
        pass! { impl BitOr for $Fixed { bitor } }
        pass_assign! { impl BitOrAssign for $Fixed { bitor_assign } }
        pass! { impl BitXor for $Fixed { bitxor } }
        pass_assign! { impl BitXorAssign for $Fixed { bitxor_assign } }

        impl<Frac: $LeEqU> Mul<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().mul(rhs))
            }
        }

        refs! { impl Mul<$Inner> for $Fixed($LeEqU) { mul } }

        impl<Frac: $LeEqU> MulAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Inner) {
                *self = (*self).mul(rhs);
            }
        }

        refs_assign! { impl MulAssign<$Inner> for $Fixed($LeEqU) { mul_assign } }

        impl<Frac: $LeEqU> Mul<$Fixed<Frac>> for $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                rhs.mul(self)
            }
        }

        impl<'a, Frac: $LeEqU> Mul<&'a $Fixed<Frac>> for $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                (*rhs).mul(self)
            }
        }

        impl<'a, Frac: $LeEqU> Mul<$Fixed<Frac>> for &'a $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                rhs.mul(*self)
            }
        }

        impl<'a, 'b, Frac: $LeEqU> Mul<&'a $Fixed<Frac>> for &'b $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                (*rhs).mul(*self)
            }
        }

        impl<Frac: $LeEqU> Div<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().div(rhs))
            }
        }

        refs! { impl Div<$Inner> for $Fixed($LeEqU) { div } }

        impl<Frac: $LeEqU> DivAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: $Inner) {
                *self = (*self).div(rhs);
            }
        }

        refs_assign! { impl DivAssign<$Inner> for $Fixed($LeEqU) { div_assign } }

        impl<Frac: $LeEqU> Rem<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: $Inner) -> $Fixed<Frac> {
                self.checked_rem_int(rhs).expect("division by zero")
            }
        }

        refs! { impl Rem<$Inner> for $Fixed($LeEqU) { rem } }

        impl<Frac: $LeEqU> RemAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn rem_assign(&mut self, rhs: $Inner) {
                *self = (*self).rem(rhs);
            }
        }

        refs_assign! { impl RemAssign<$Inner> for $Fixed($LeEqU) { rem_assign } }

        shift_all! {
            impl {Shl, ShlAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed {
                shl, shl_assign
            }
        }
        shift_all! {
            impl {Shr, ShrAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed {
                shr, shr_assign
            }
        }

        impl<Frac> Sum<$Fixed<Frac>> for $Fixed<Frac> {
            fn sum<I>(iter: I) -> $Fixed<Frac>
            where
                I: Iterator<Item = $Fixed<Frac>>,
            {
                iter.fold(Self::from_bits(0), Add::add)
            }
        }

        impl<'a, Frac: 'a> Sum<&'a $Fixed<Frac>> for $Fixed<Frac> {
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

pub(crate) trait MulDivOverflow: Sized {
    fn mul_overflow(self, rhs: Self, frac_nbits: u32) -> (Self, bool);
    fn div_overflow(self, rhs: Self, frac_nbits: u32) -> (Self, bool);
}

macro_rules! mul_div_widen {
    ($Single:ty, $Double:ty, $Signedness:tt) => {
        impl MulDivOverflow for $Single {
            #[inline]
            fn mul_overflow(self, rhs: $Single, frac_nbits: u32) -> ($Single, bool) {
                const NBITS: u32 = <$Single>::NBITS;
                let int_nbits: u32 = NBITS - frac_nbits;
                let lhs2 = <$Double>::from(self);
                let rhs2 = <$Double>::from(rhs) << int_nbits;
                let (prod2, overflow) = lhs2.overflowing_mul(rhs2);
                ((prod2 >> NBITS) as $Single, overflow)
            }

            #[inline]
            fn div_overflow(self, rhs: $Single, frac_nbits: u32) -> ($Single, bool) {
                const NBITS: u32 = <$Single>::NBITS;
                let lhs2 = <$Double>::from(self) << frac_nbits;
                let rhs2 = <$Double>::from(rhs);
                let quot2 = lhs2 / rhs2;
                let quot = quot2 as $Single;
                let overflow = if_signed_unsigned! {
                    $Signedness,
                    quot2 >> NBITS != if quot < 0 { -1 } else { 0 },
                    quot2 >> NBITS != 0
                };
                (quot, overflow)
            }
        }
    };
}

trait FallbackHelper: Sized {
    type Unsigned;
    fn hi_lo(self) -> (Self, Self);
    fn shift_lo_up(self) -> Self;
    fn shift_lo_up_unsigned(self) -> Self::Unsigned;
    fn combine_lo_then_shl(self, lo: Self::Unsigned, shift: u32) -> (Self, bool);
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
    fn combine_lo_then_shl(self, lo: u128, shift: u32) -> (u128, bool) {
        if shift == 128 {
            (self, false)
        } else if shift == 0 {
            (lo, self != 0)
        } else {
            let lo = lo >> shift;
            let hi = self << (128 - shift);
            (lo | hi, self >> shift != 0)
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
    fn combine_lo_then_shl(self, lo: u128, shift: u32) -> (i128, bool) {
        if shift == 128 {
            (self, false)
        } else if shift == 0 {
            let ans = lo as i128;
            (ans, self != if ans < 0 { -1 } else { 0 })
        } else {
            let lo = (lo >> shift) as i128;
            let hi = self << (128 - shift);
            let ans = lo | hi;
            (ans, self >> shift != if ans < 0 { -1 } else { 0 })
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
        impl MulDivOverflow for $Single {
            #[inline]
            fn mul_overflow(self, rhs: $Single, frac_nbits: u32) -> ($Single, bool) {
                if frac_nbits == 0 {
                    self.overflowing_mul(rhs)
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
                    let (col12, carry_col3) = <$Single as FallbackHelper>::carrying_add(partial_col12, ll_rh);
                    let (col12_hi, col12_lo) = col12.hi_lo();
                    let ans01 = col12_lo.shift_lo_up_unsigned() + col01_lo;
                    let ans23 = lh_rh + col12_hi + carry_col3.shift_lo_up();
                    ans23.combine_lo_then_shl(ans01, frac_nbits)
                }
            }

            #[inline]
            fn div_overflow(self, rhs: $Single, frac_nbits: u32) -> ($Single, bool) {
                if frac_nbits == 0 {
                    self.overflowing_div(rhs)
                } else {
                    const NBITS: u32 = <$Single>::NBITS;
                    let lhs2 = (self >> (NBITS - frac_nbits), (self << frac_nbits) as $Uns);
                    let (quot2, _) = rhs.div_rem_from(lhs2);
                    let quot = quot2.1 as $Single;
                    let overflow = if_signed_unsigned! {
                        $Signedness,
                        quot2.0 != if quot < 0 { -1 } else { 0 },
                        quot2.0 != 0
                    };
                    (quot, overflow)
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
#[allow(clippy::cognitive_complexity)]
mod tests {
    use crate::{types::extra::Unsigned, *};

    #[test]
    fn fixed_u16() {
        use crate::types::extra::U7 as Frac;
        let frac = Frac::U32;
        let a = 12;
        let b = 5;
        for &(a, b) in &[(a, b), (b, a)] {
            let af = FixedU16::<Frac>::from_num(a);
            let bf = FixedU16::<Frac>::from_num(b);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            if a > b {
                assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            }
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af % bf).to_bits(), (a << frac) % (b << frac));
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
            assert_eq!((af * b).to_bits(), (a << frac) * b);
            assert_eq!((b * af).to_bits(), (a << frac) * b);
            assert_eq!((af / b).to_bits(), (a << frac) / b);
            assert_eq!((af % b).to_bits(), (a << frac) % (b << frac));
        }
    }

    #[test]
    fn fixed_i16() {
        use crate::types::extra::U7 as Frac;
        let frac = Frac::U32;
        let a = 12;
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
            let af = FixedI16::<Frac>::from_num(a);
            let bf = FixedI16::<Frac>::from_num(b);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af % bf).to_bits(), (a << frac) % (b << frac));
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((-af).to_bits(), -(a << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
            assert_eq!((af * b).to_bits(), (a << frac) * b);
            assert_eq!((b * af).to_bits(), (a << frac) * b);
            assert_eq!((af / b).to_bits(), (a << frac) / b);
            assert_eq!((af % b).to_bits(), (a << frac) % (b << frac));
        }
    }

    #[test]
    fn fixed_u128() {
        use crate::types::extra::U7 as Frac;
        let frac = Frac::U32;
        let a = 0x0003_4567_89ab_cdef_0123_4567_89ab_cdef_u128;
        let b = 5;
        for &(a, b) in &[(a, b), (b, a)] {
            let af = FixedU128::<Frac>::from_num(a);
            let bf = FixedU128::<Frac>::from_num(b);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            if a > b {
                assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            }
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af % bf).to_bits(), (a << frac) % (b << frac));
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
            assert_eq!((af * b).to_bits(), (a << frac) * b);
            assert_eq!((b * af).to_bits(), (a << frac) * b);
            assert_eq!((af / b).to_bits(), (a << frac) / b);
            assert_eq!((af % b).to_bits(), (a << frac) % (b << frac));
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
            let af = FixedI128::<Frac>::from_num(a);
            let bf = FixedI128::<Frac>::from_num(b);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af % bf).to_bits(), (a << frac) % (b << frac));
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((-af).to_bits(), -(a << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
            assert_eq!((af * b).to_bits(), (a << frac) * b);
            assert_eq!((b * af).to_bits(), (a << frac) * b);
            assert_eq!((af / b).to_bits(), (a << frac) / b);
            assert_eq!((af % b).to_bits(), (a << frac) % (b << frac));
        }
    }

    fn check_rem_int(a: i32, b: i32) {
        use crate::types::I16F16;
        assert_eq!(I16F16::from_num(a) % b, a % b);
        assert_eq!(I16F16::from_num(a).rem_euclid_int(b), a.rem_euclid(b));
        match (I16F16::from_num(a).checked_rem_int(b), a.checked_rem(b)) {
            (Some(a), Some(b)) => assert_eq!(a, b),
            (None, None) => {}
            (a, b) => panic!("mismatch {:?}, {:?}", a, b),
        }
        match (
            I16F16::from_num(a).checked_rem_euclid_int(b),
            a.checked_rem_euclid(b),
        ) {
            (Some(a), Some(b)) => assert_eq!(a, b),
            (None, None) => {}
            (a, b) => panic!("mismatch {:?}, {:?}", a, b),
        }
    }

    #[test]
    #[allow(clippy::modulo_one)]
    fn rem_int() {
        use crate::types::{I0F32, I16F16, I1F31};
        check_rem_int(-0x8000, -0x8000);
        check_rem_int(-0x8000, -0x7fff);
        check_rem_int(-0x8000, 0x7fff);
        check_rem_int(-0x8000, 0x8000);
        check_rem_int(-0x7fff, -0x8000);
        check_rem_int(-0x7fff, -0x7fff);
        check_rem_int(-0x7fff, 0x7fff);
        check_rem_int(-0x7fff, 0x8000);
        check_rem_int(0x7fff, -0x8000);
        check_rem_int(0x7fff, -0x7fff);
        check_rem_int(0x7fff, 0x7fff);
        check_rem_int(0x7fff, 0x8000);

        fn i1(f: f32) -> I1F31 {
            I1F31::from_num(f)
        }
        fn i0(f: f32) -> I0F32 {
            I0F32::from_num(f)
        }

        assert_eq!(I16F16::min_value() % -1, 0);
        assert_eq!(I16F16::min_value().checked_rem_int(-1).unwrap(), 0);
        assert_eq!(I16F16::min_value().rem_euclid_int(-1), 0);
        assert_eq!(I16F16::min_value().checked_rem_euclid_int(-1).unwrap(), 0);

        assert_eq!(i1(-1.0) % 1, i1(0.0));
        assert_eq!(i1(-1.0).rem_euclid_int(1), i1(0.0));

        assert_eq!(i1(-0.75) % 1, i1(-0.75));
        assert_eq!(i1(-0.75).rem_euclid_int(1), i1(0.25));

        assert_eq!(i1(-0.5) % 1, i1(-0.5));
        assert_eq!(i1(-0.5).rem_euclid_int(1), i1(0.5));

        assert_eq!(i1(-0.5) % 3, i1(-0.5));
        assert_eq!(i1(-0.5).checked_rem_euclid_int(3), None);
        assert_eq!(i1(-0.5).wrapping_rem_euclid_int(3), i1(0.5));
        assert_eq!(i1(-0.5).overflowing_rem_euclid_int(3), (i1(0.5), true));

        assert_eq!(i1(-0.25) % 1, i1(-0.25));
        assert_eq!(i1(-0.25).rem_euclid_int(1), i1(0.75));

        assert_eq!(i1(-0.25) % 3, i1(-0.25));
        assert_eq!(i1(-0.25).checked_rem_euclid_int(3), None);
        assert_eq!(i1(-0.25).wrapping_rem_euclid_int(3), i1(0.75));
        assert_eq!(i1(-0.25).overflowing_rem_euclid_int(3), (i1(0.75), true));

        assert_eq!(i1(0.0) % 1, i1(0.0));
        assert_eq!(i1(0.0).rem_euclid_int(1), i1(0.0));

        assert_eq!(i1(0.25) % 1, i1(0.25));
        assert_eq!(i1(0.25).rem_euclid_int(1), i1(0.25));

        assert_eq!(i1(0.5) % 1, i1(0.5));
        assert_eq!(i1(0.5).rem_euclid_int(1), i1(0.5));

        assert_eq!(i1(0.75) % 1, i1(0.75));
        assert_eq!(i1(0.75).rem_euclid_int(1), i1(0.75));

        assert_eq!(i0(-0.5) % 1, i0(-0.5));
        assert_eq!(i0(-0.5).checked_rem_euclid_int(1), None);
        assert_eq!(i0(-0.5).wrapping_rem_euclid_int(1), i0(-0.5));
        assert_eq!(i0(-0.5).overflowing_rem_euclid_int(1), (i0(-0.5), true));

        assert_eq!(i0(-0.375) % 1, i0(-0.375));
        assert_eq!(i0(-0.375).checked_rem_euclid_int(1), None);
        assert_eq!(i0(-0.375).wrapping_rem_euclid_int(1), i0(-0.375));
        assert_eq!(i0(-0.375).overflowing_rem_euclid_int(1), (i0(-0.375), true));

        assert_eq!(i0(-0.25) % 1, i0(-0.25));
        assert_eq!(i0(-0.25).checked_rem_euclid_int(1), None);
        assert_eq!(i0(-0.25).wrapping_rem_euclid_int(1), i0(-0.25));
        assert_eq!(i0(-0.25).overflowing_rem_euclid_int(1), (i0(-0.25), true));

        assert_eq!(i0(0.0) % 1, i0(0.0));
        assert_eq!(i0(0.0).rem_euclid_int(1), i0(0.0));

        assert_eq!(i0(0.25) % 1, i0(0.25));
        assert_eq!(i0(0.25).rem_euclid_int(1), i0(0.25));
    }
}
