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

use frac::{self, Unsigned};
use std::cmp::Ordering;
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

macro_rules! fixed_cmp {
    ($Fixed:ident($Inner:ty, $bits_count:expr)) => {
        impl<Frac: Unsigned> Eq for $Fixed<Frac> {}

        impl<Frac: Unsigned, FracRhs: Unsigned> PartialEq<$Fixed<FracRhs>> for $Fixed<Frac> {
            #[inline]
            fn eq(&self, rhs: &$Fixed<FracRhs>) -> bool {
                let (fl, fr) = (Frac::to_u32(), FracRhs::to_u32());
                if fl == fr {
                    self.to_bits() == rhs.to_bits()
                } else if fl < fr {
                    rhs.eq(self)
                } else {
                    // self has more fractional bits
                    let diff = fl - fr;
                    let (aligned, extra);
                    if diff == $bits_count {
                        aligned = 0;
                        extra = self.to_bits();
                    } else {
                        aligned = self.to_bits() >> diff;
                        extra = self.to_bits() & !(!0 << diff);
                    }
                    aligned == rhs.to_bits() && extra == 0
                }
            }
        }

        impl<Frac: Unsigned> PartialEq<$Inner> for $Fixed<Frac> {
            #[inline]
            fn eq(&self, rhs: &$Inner) -> bool {
                <$Fixed<Frac> as PartialEq<$Fixed<frac::U0>>>::eq(self, &$Fixed::from_bits(*rhs))
            }
        }

        impl<Frac: Unsigned> PartialEq<$Fixed<Frac>> for $Inner {
            #[inline]
            fn eq(&self, rhs: &$Fixed<Frac>) -> bool {
                <$Fixed<frac::U0> as PartialEq<$Fixed<Frac>>>::eq(&$Fixed::from_bits(*self), rhs)
            }
        }

        impl<Frac: Unsigned> Ord for $Fixed<Frac> {
            #[inline]
            fn cmp(&self, rhs: &$Fixed<Frac>) -> Ordering {
                self.to_bits().cmp(&rhs.to_bits())
            }
        }

        impl<Frac: Unsigned, FracRhs: Unsigned> PartialOrd<$Fixed<FracRhs>> for $Fixed<Frac> {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fixed<FracRhs>) -> Option<Ordering> {
                let (fl, fr) = (Frac::to_u32(), FracRhs::to_u32());
                if fl == fr {
                    self.to_bits().partial_cmp(&rhs.to_bits())
                } else if fl < fr {
                    rhs.partial_cmp(self).map(Ordering::reverse)
                } else {
                    // self has more fractional bits
                    let diff = fl - fr;
                    let (aligned, extra);
                    if diff == $bits_count {
                        aligned = 0;
                        extra = self.to_bits();
                    } else {
                        aligned = self.to_bits() >> diff;
                        extra = self.to_bits() & !(!0 << diff);
                    }
                    match aligned.partial_cmp(&rhs.to_bits()) {
                        Some(Ordering::Equal) => extra.partial_cmp(&0),
                        other => other,
                    }
                }
            }
        }

        impl<Frac: Unsigned> PartialOrd<$Inner> for $Fixed<Frac> {
            #[inline]
            fn partial_cmp(&self, rhs: &$Inner) -> Option<Ordering> {
                <$Fixed<Frac> as PartialOrd<$Fixed<frac::U0>>>::partial_cmp(
                    self,
                    &$Fixed::from_bits(*rhs),
                )
            }
        }

        impl<Frac: Unsigned> PartialOrd<$Fixed<Frac>> for $Inner {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fixed<Frac>) -> Option<Ordering> {
                <$Fixed<frac::U0> as PartialOrd<$Fixed<Frac>>>::partial_cmp(
                    &$Fixed::from_bits(*self),
                    rhs,
                )
            }
        }
    };
}

fixed_cmp! { FixedU8(u8, 8) }
fixed_cmp! { FixedU16(u16, 16) }
fixed_cmp! { FixedU32(u32, 32) }
fixed_cmp! { FixedU64(u64, 64) }
fixed_cmp! { FixedU128(u128, 128) }
fixed_cmp! { FixedI8(i8, 8) }
fixed_cmp! { FixedI16(i16, 16) }
fixed_cmp! { FixedI32(i32, 32) }
fixed_cmp! { FixedI64(i64, 64) }
fixed_cmp! { FixedI128(i128, 128) }

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn cmp_signed() {
        use std::cmp::Ordering::*;
        let neg1_16 = FixedI32::<frac::U16>::from_int(-1).unwrap();
        let neg1_20 = FixedI32::<frac::U20>::from_int(-1).unwrap();
        let mut a = neg1_16;
        let mut b = neg1_20;
        // a = ffff.0000 = -1, b = fff.00000 = -1
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        a >>= 16;
        b >>= 16;
        // a = ffff.ffff = -2^-16, b = fff.ffff0 = -2^-16
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        a >>= 1;
        b >>= 1;
        // a = ffff.ffff = -2^-16, b = fff.ffff8 = -2^-17
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Less));
        assert_eq!(b.partial_cmp(&a), Some(Greater));
        a = neg1_16 << 11;
        b = neg1_20 << 11;
        // a = f800.0000 = -2^11, b = 800.00000 = -2^11
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        a <<= 1;
        b <<= 1;
        // a = f000.0000 = -2^-12, b = 000.00000 = 0
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Less));
        assert_eq!(b.partial_cmp(&a), Some(Greater));
    }

    #[test]
    fn cmp_unsigned() {
        use std::cmp::Ordering::*;
        let one_16 = FixedU32::<frac::U16>::from_int(1).unwrap();
        let one_20 = FixedU32::<frac::U20>::from_int(1).unwrap();
        let mut a = one_16;
        let mut b = one_20;
        // a = 0001.0000 = 1, b = 001.00000 = 1
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        a >>= 16;
        b >>= 16;
        // a = 0000.0001 = 2^-16, b = 000.00010 = 2^-16
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        a >>= 1;
        b >>= 1;
        // a = 0000.0000 = 0, b = 000.00008 = 2^-17
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Less));
        assert_eq!(b.partial_cmp(&a), Some(Greater));
        a = one_16 << 11;
        b = one_20 << 11;
        // a = 0800.0000 = 2^11, b = 800.00000 = 2^11
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        a <<= 1;
        b <<= 1;
        // a = 1000.0000 = 2^12, b = 000.00000 = 0
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Greater));
        assert_eq!(b.partial_cmp(&a), Some(Less));
    }
}
