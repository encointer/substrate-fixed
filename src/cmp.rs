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
use frac::{self, IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8};
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

macro_rules! fixed_cmp {
    ($Fixed:ident($Inner:ty, $Len:ty, $bits_count:expr)) => {
        impl<Frac> Eq for $Fixed<Frac> where Frac: Unsigned + IsLessOrEqual<$Len, Output = True> {}

        impl<Frac, FracRhs> PartialEq<$Fixed<FracRhs>> for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
            FracRhs: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
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
                    if diff == $bits_count {
                        0 == rhs.to_bits() && self.to_bits() == 0
                    } else {
                        let aligned = self.to_bits() >> diff;
                        let extra = self.to_bits() & !(!0 << diff);
                        aligned == rhs.to_bits() && extra == 0
                    }
                }
            }
        }

        impl<Frac> PartialEq<$Inner> for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn eq(&self, rhs: &$Inner) -> bool {
                <$Fixed<Frac> as PartialEq<$Fixed<frac::U0>>>::eq(self, &$Fixed::from_bits(*rhs))
            }
        }

        impl<Frac> PartialEq<$Fixed<Frac>> for $Inner
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn eq(&self, rhs: &$Fixed<Frac>) -> bool {
                <$Fixed<frac::U0> as PartialEq<$Fixed<Frac>>>::eq(&$Fixed::from_bits(*self), rhs)
            }
        }

        impl<Frac> Ord for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn cmp(&self, rhs: &$Fixed<Frac>) -> Ordering {
                self.to_bits().cmp(&rhs.to_bits())
            }
        }

        impl<Frac, FracRhs> PartialOrd<$Fixed<FracRhs>> for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
            FracRhs: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
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

            #[inline]
            fn lt(&self, rhs: &$Fixed<FracRhs>) -> bool {
                let (fl, fr) = (Frac::to_u32(), FracRhs::to_u32());
                if fl == fr {
                    self.to_bits() < rhs.to_bits()
                } else if fl < fr {
                    rhs.gt(self)
                } else {
                    // self has more fractional bits
                    let diff = fl - fr;
                    let rhs_bits = rhs.to_bits();
                    #[allow(unused_comparisons)]
                    {
                        if diff == $bits_count {
                            0 < rhs_bits || (0 == rhs_bits && self.to_bits() < 0)
                        } else {
                            (self.to_bits() >> diff) < rhs_bits
                        }
                    }
                }
            }

            #[inline]
            fn le(&self, rhs: &$Fixed<FracRhs>) -> bool {
                let (fl, fr) = (Frac::to_u32(), FracRhs::to_u32());
                if fl == fr {
                    self.to_bits() <= rhs.to_bits()
                } else if fl < fr {
                    rhs.ge(self)
                } else {
                    // self has more fractional bits
                    let diff = fl - fr;
                    let rhs_bits = rhs.to_bits();
                    if diff == $bits_count {
                        0 < rhs_bits || (0 == rhs_bits && self.to_bits() <= 0)
                    } else {
                        let aligned = self.to_bits() >> diff;
                        let extra = self.to_bits() & !(!0 << diff);
                        aligned < rhs_bits || (aligned == rhs_bits && extra == 0)
                    }
                }
            }

            #[inline]
            fn gt(&self, rhs: &$Fixed<FracRhs>) -> bool {
                !self.le(rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Fixed<FracRhs>) -> bool {
                !self.lt(rhs)
            }
        }

        impl<Frac> PartialOrd<$Inner> for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Inner) -> Option<Ordering> {
                self.partial_cmp(&$Fixed::<frac::U0>::from_bits(*rhs))
            }

            #[inline]
            fn lt(&self, rhs: &$Inner) -> bool {
                self.lt(&$Fixed::<frac::U0>::from_bits(*rhs))
            }

            #[inline]
            fn le(&self, rhs: &$Inner) -> bool {
                self.le(&$Fixed::<frac::U0>::from_bits(*rhs))
            }

            #[inline]
            fn gt(&self, rhs: &$Inner) -> bool {
                self.gt(&$Fixed::<frac::U0>::from_bits(*rhs))
            }

            #[inline]
            fn ge(&self, rhs: &$Inner) -> bool {
                self.ge(&$Fixed::<frac::U0>::from_bits(*rhs))
            }
        }

        impl<Frac> PartialOrd<$Fixed<Frac>> for $Inner
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fixed<Frac>) -> Option<Ordering> {
                $Fixed::<frac::U0>::from_bits(*self).partial_cmp(rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Fixed<Frac>) -> bool {
                $Fixed::<frac::U0>::from_bits(*self).lt(rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Fixed<Frac>) -> bool {
                $Fixed::<frac::U0>::from_bits(*self).le(rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Fixed<Frac>) -> bool {
                $Fixed::<frac::U0>::from_bits(*self).gt(rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Fixed<Frac>) -> bool {
                $Fixed::<frac::U0>::from_bits(*self).ge(rhs)
            }
        }
    };
}

fixed_cmp! { FixedU8(u8, U8, 8) }
fixed_cmp! { FixedU16(u16, U16, 16) }
fixed_cmp! { FixedU32(u32, U32, 32) }
fixed_cmp! { FixedU64(u64, U64, 64) }
fixed_cmp! { FixedU128(u128, U128, 128) }
fixed_cmp! { FixedI8(i8, U8, 8) }
fixed_cmp! { FixedI16(i16, U16, 16) }
fixed_cmp! { FixedI32(i32, U32, 32) }
fixed_cmp! { FixedI64(i64, U64, 64) }
fixed_cmp! { FixedI128(i128, U128, 128) }

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn cmp_signed() {
        use core::cmp::Ordering::*;
        let neg1_16 = FixedI32::<frac::U16>::checked_from_int(-1).unwrap();
        let neg1_20 = FixedI32::<frac::U20>::checked_from_int(-1).unwrap();
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
        use core::cmp::Ordering::*;
        let one_16 = FixedU32::<frac::U16>::checked_from_int(1).unwrap();
        let one_20 = FixedU32::<frac::U20>::checked_from_int(1).unwrap();
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
