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

use crate::helpers::IntHelper;

trait DivHalf: Copy {
    fn hi(self) -> Self;
    fn lo(self) -> Self;
    fn up_lo(self, lo: Self) -> Self;
    fn div_half(&mut self, d: Self, next_half: Self) -> Self;
    fn normalize(&mut self, n1: &mut Self, n0: &mut Self) -> (Self, u32);
    fn unnormalize(self, zeros: u32) -> Self;
}

macro_rules! div_half {
    ($($T:ty: $n:expr),*) => { $(
        impl DivHalf for $T {
            #[inline]
            fn hi(self) -> $T {
                self >> ($n / 2)
            }

            #[inline]
            fn lo(self) -> $T {
                self & !(!0 << ($n / 2))
            }

            #[inline]
            fn up_lo(self, lo: $T) -> $T {
                self << ($n / 2) | lo
            }

            #[inline]
            fn div_half(&mut self, d: $T, next_half: $T) -> $T {
                let dh = d.hi();
                let (mut q, rr) = (*self / dh, *self % dh);
                let m = q * d.lo();
                *self = rr.up_lo(next_half);
                if *self < m {
                    q -= 1;
                    *self = match self.overflowing_add(d) {
                        (r, false) if r < m => {
                            q -= 1;
                            r.wrapping_add(d)
                        }
                        (r, _) => r,
                    };
                }
                *self = self.wrapping_sub(m);
                q
            }

            #[inline]
            fn normalize(&mut self, n1: &mut $T, n0: &mut $T) -> ($T, u32) {
                assert!(*self != 0, "division by zero");
                let zeros = self.leading_zeros();
                if zeros == 0 {
                    (0, 0)
                } else {
                    *self <<= zeros;
                    let n2 = *n1 >> ($n - zeros);
                    *n1 = *n1 << zeros | *n0 >> ($n - zeros);
                    *n0 <<= zeros;
                    (n2, zeros)
                }
            }

            #[inline]
            fn unnormalize(self, zeros: u32) -> Self {
                self >> zeros
            }
        }
    )* };
}

div_half! { u8: 8, u16: 16, u32: 32, u64: 64, u128: 128 }

trait NegAbsHiLo {
    type Abs;
    fn neg_abs(self) -> (bool, Self::Abs);
    fn from_neg_abs(neg: bool, abs: Self::Abs) -> Self;
}

macro_rules! neg_abs_hi_lo {
    ($($S:ty: $U:ty),*) => { $(
        impl NegAbsHiLo for ($S, $U) {
            type Abs = ($U, $U);

            #[inline]
            fn neg_abs(self) -> (bool, ($U, $U)) {
                if self.0 < 0 {
                    match self.1.overflowing_neg() {
                        (n, true) => (true, (!self.0 as $U, n)),
                        (n, false) => (true, (self.0.wrapping_neg() as $U, n)),
                    }
                } else {
                    (false, (self.0 as $U, self.1))
                }
            }

            #[inline]
            fn from_neg_abs(neg: bool, abs: ($U, $U)) -> ($S, $U) {
                if neg {
                    match abs.1.overflowing_neg() {
                        (n, true) => (!abs.0 as $S, n),
                        (n, false) => (abs.0.wrapping_neg() as $S, n),
                    }
                } else {
                    (abs.0 as $S, abs.1)
                }
            }
        }
    )* };
}

neg_abs_hi_lo! { i8: u8, i16: u16, i32: u32, i64: u64, i128: u128 }

pub trait WideDivRem<U>: Sized {
    fn div_rem_from(self, dividend: (Self, U)) -> ((Self, U), Self);
}

macro_rules! unsigned_wide_div_rem {
    ($($U:ty),*) => { $(
        impl WideDivRem<$U> for $U {
            #[inline]
            fn div_rem_from(self, dividend: ($U, $U)) -> (($U, $U), $U) {
                let (mut n1, mut n0, mut d) = (dividend.0, dividend.1, self);
                let (mut r, zeros) = d.normalize(&mut n1, &mut n0);

                let q1h = r.div_half(d, n1.hi());
                let q1l = r.div_half(d, n1.lo());
                let q0h = r.div_half(d, n0.hi());
                let q0l = r.div_half(d, n0.lo());
                ((q1h.up_lo(q1l), q0h.up_lo(q0l)), r.unnormalize(zeros))
            }
        }
    )* };
}

macro_rules! signed_wide_div_rem {
    ($($S:ty: $U:ty),*) => { $(
        impl WideDivRem<$U> for $S {
            #[inline]
            fn div_rem_from(self, dividend: ($S, $U)) -> (($S, $U), $S) {
                let (n_neg, n_abs) = dividend.neg_abs();
                let (d_neg, d_abs) = self.neg_abs();
                let (q, r) = d_abs.div_rem_from(n_abs);
                (
                    NegAbsHiLo::from_neg_abs(n_neg != d_neg, q),
                    IntHelper::from_neg_abs(n_neg, r),
                )
            }
        }
    )* };
}

unsigned_wide_div_rem! { u8, u16, u32, u64, u128 }
signed_wide_div_rem! { i8: u8, i16: u16, i32: u32, i64: u64, i128: u128 }

#[cfg(test)]
mod tests {
    use super::WideDivRem;

    fn check_8((n1, n0): (u8, u8), d: u8) -> ((u8, u8), u8) {
        let n = u16::from(n1) << 8 | u16::from(n0);
        let d = u16::from(d);
        let (q, r) = (n / d, n % d);
        (((q >> 8) as u8, q as u8), r as u8)
    }

    fn check_16((n1, n0): (u16, u16), d: u16) -> ((u16, u16), u16) {
        let n = u32::from(n1) << 16 | u32::from(n0);
        let d = u32::from(d);
        let (q, r) = (n / d, n % d);
        (((q >> 16) as u16, q as u16), r as u16)
    }

    fn check_64((n1, n0): (u64, u64), d: u64) -> ((u64, u64), u64) {
        let n = u128::from(n1) << 64 | u128::from(n0);
        let d = u128::from(d);
        let (q, r) = (n / d, n % d);
        (((q >> 64) as u64, q as u64), r as u64)
    }

    fn icheck_8((n1, n0): (i8, u8), d: i8) -> ((i8, u8), i8) {
        let n = i16::from(n1) << 8 | i16::from(n0);
        let d = i16::from(d);
        let (q, r) = (n / d, n % d);
        (((q >> 8) as i8, q as u8), r as i8)
    }

    fn icheck_16((n1, n0): (i16, u16), d: i16) -> ((i16, u16), i16) {
        let n = i32::from(n1) << 16 | i32::from(n0);
        let d = i32::from(d);
        let (q, r) = (n / d, n % d);
        (((q >> 16) as i16, q as u16), r as i16)
    }

    fn icheck_64((n1, n0): (i64, u64), d: i64) -> ((i64, u64), i64) {
        let n = i128::from(n1) << 64 | i128::from(n0);
        let d = i128::from(d);
        let (q, r) = (n / d, n % d);
        (((q >> 64) as i64, q as u64), r as i64)
    }

    #[test]
    fn test_wide_div_rem() {
        for d in 1..=255 {
            for n1 in (0..=255).step_by(15) {
                for n0 in (0..=255).step_by(15) {
                    let qr = d.div_rem_from((n1, n0));
                    let check = check_8((n1, n0), d);
                    assert_eq!(qr, check);

                    let d = u16::from(d) << 8 | 1;
                    let n1 = u16::from(n1) << 8 | 1;
                    let n0 = u16::from(n0) << 8 | 1;
                    let qr = d.div_rem_from((n1, n0));
                    let check = check_16((n1, n0), d);
                    assert_eq!(qr, check);

                    let d = u64::from(d) << 48 | 1;
                    let n1 = u64::from(n1) << 48 | 1;
                    let n0 = u64::from(n0) << 48 | 1;
                    let qr = d.div_rem_from((n1, n0));
                    let check = check_64((n1, n0), d);
                    assert_eq!(qr, check);
                }
            }
        }
    }

    #[test]
    fn test_wide_idiv_rem() {
        for d in -128..=127 {
            if d == 0 {
                continue;
            }
            for n1 in (-120..=120).step_by(15) {
                for n0 in (0..=255).step_by(15) {
                    let qr = d.div_rem_from((n1, n0));
                    let check = icheck_8((n1, n0), d);
                    assert_eq!(qr, check);

                    let d = i16::from(d) << 8 | 1;
                    let n1 = i16::from(n1) << 8 | 1;
                    let n0 = u16::from(n0) << 8 | 1;
                    let qr = d.div_rem_from((n1, n0));
                    let check = icheck_16((n1, n0), d);
                    assert_eq!(qr, check);

                    let d = i64::from(d) << 48 | 1;
                    let n1 = i64::from(n1) << 48 | 1;
                    let n0 = u64::from(n0) << 48 | 1;
                    let qr = d.div_rem_from((n1, n0));
                    let check = icheck_64((n1, n0), d);
                    assert_eq!(qr, check);
                }
            }
        }
    }
}
