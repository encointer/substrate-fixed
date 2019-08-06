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

#[cfg(feature = "f16")]
use half::f16;
use {
    crate::{
        frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8},
        sealed::{SealedFixed, SealedFloat, SealedInt, Widest},
        traits::Fixed,
        FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
        FixedU8,
    },
    core::cmp::Ordering,
};

macro_rules! fixed_cmp_fixed {
    ($Lhs:ident($LhsNBits:ident), $Rhs:ident($RhsNBits:ident)) => {
        impl<FracLhs, FracRhs> PartialEq<$Rhs<FracRhs>> for $Lhs<FracLhs>
        where
            FracLhs: Unsigned + IsLessOrEqual<$LhsNBits, Output = True>,
            FracRhs: Unsigned + IsLessOrEqual<$RhsNBits, Output = True>,
        {
            #[inline]
            fn eq(&self, rhs: &$Rhs<FracRhs>) -> bool {
                let (rhs_128, dir, overflow) = rhs.to_bits().to_fixed_dir_overflow(
                    <$Rhs<FracRhs>>::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                let rhs_bits = match rhs_128 {
                    Widest::Unsigned(bits) => bits as <Self as Fixed>::Bits,
                    Widest::Negative(bits) => bits as <Self as Fixed>::Bits,
                };
                dir == Ordering::Equal && !overflow && rhs_bits == self.to_bits()
            }
        }

        impl<FracLhs, FracRhs> PartialOrd<$Rhs<FracRhs>> for $Lhs<FracLhs>
        where
            FracLhs: Unsigned + IsLessOrEqual<$LhsNBits, Output = True>,
            FracRhs: Unsigned + IsLessOrEqual<$RhsNBits, Output = True>,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Rhs<FracRhs>) -> Option<Ordering> {
                match (self.to_bits().is_negative(), rhs.to_bits().is_negative()) {
                    (false, true) => return Some(Ordering::Greater),
                    (true, false) => return Some(Ordering::Less),
                    _ => {}
                }
                let (rhs_128, dir, overflow) = rhs.to_bits().to_fixed_dir_overflow(
                    <$Rhs<FracRhs>>::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                if overflow {
                    return if rhs.to_bits().is_negative() {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Less)
                    };
                }
                let rhs_bits = match rhs_128 {
                    Widest::Unsigned(bits) => bits as <Self as Fixed>::Bits,
                    Widest::Negative(bits) => bits as <Self as Fixed>::Bits,
                };
                Some(self.to_bits().cmp(&rhs_bits).then(dir))
            }

            #[inline]
            fn lt(&self, rhs: &$Rhs<FracRhs>) -> bool {
                match (self.to_bits().is_negative(), rhs.to_bits().is_negative()) {
                    (false, true) => return false,
                    (true, false) => return true,
                    _ => {}
                }
                let (rhs_128, dir, overflow) = rhs.to_bits().to_fixed_dir_overflow(
                    <$Rhs<FracRhs>>::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                if overflow {
                    return !rhs.to_bits().is_negative();
                }
                let rhs_bits = match rhs_128 {
                    Widest::Unsigned(bits) => bits as <Self as Fixed>::Bits,
                    Widest::Negative(bits) => bits as <Self as Fixed>::Bits,
                };
                self.to_bits() < rhs_bits || (self.to_bits() == rhs_bits && dir == Ordering::Less)
            }

            #[inline]
            fn le(&self, rhs: &$Rhs<FracRhs>) -> bool {
                !rhs.lt(self)
            }

            #[inline]
            fn gt(&self, rhs: &$Rhs<FracRhs>) -> bool {
                rhs.lt(self)
            }

            #[inline]
            fn ge(&self, rhs: &$Rhs<FracRhs>) -> bool {
                !self.lt(rhs)
            }
        }
    };
}

macro_rules! fixed_cmp_int {
    ($Fix:ident($NBits:ident), $Int:ident) => {
        impl<Frac> PartialEq<$Int> for $Fix<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn eq(&self, rhs: &$Int) -> bool {
                self.eq(&rhs.to_repr_fixed())
            }
        }

        impl<Frac> PartialEq<$Fix<Frac>> for $Int
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn eq(&self, rhs: &$Fix<Frac>) -> bool {
                self.to_repr_fixed().eq(rhs)
            }
        }

        impl<Frac> PartialOrd<$Int> for $Fix<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Int) -> Option<Ordering> {
                self.partial_cmp(&rhs.to_repr_fixed())
            }

            #[inline]
            fn lt(&self, rhs: &$Int) -> bool {
                self.lt(&rhs.to_repr_fixed())
            }

            #[inline]
            fn le(&self, rhs: &$Int) -> bool {
                !rhs.lt(self)
            }

            #[inline]
            fn gt(&self, rhs: &$Int) -> bool {
                rhs.lt(self)
            }

            #[inline]
            fn ge(&self, rhs: &$Int) -> bool {
                !self.lt(rhs)
            }
        }

        impl<Frac> PartialOrd<$Fix<Frac>> for $Int
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fix<Frac>) -> Option<Ordering> {
                self.to_repr_fixed().partial_cmp(rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Fix<Frac>) -> bool {
                self.to_repr_fixed().lt(rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Fix<Frac>) -> bool {
                !rhs.lt(self)
            }

            #[inline]
            fn gt(&self, rhs: &$Fix<Frac>) -> bool {
                rhs.lt(self)
            }

            #[inline]
            fn ge(&self, rhs: &$Fix<Frac>) -> bool {
                !self.lt(rhs)
            }
        }
    };
}

macro_rules! fixed_cmp_float {
    ($Fix:ident($NBits:ident), $Float:ident) => {
        impl<Frac> PartialEq<$Float> for $Fix<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn eq(&self, rhs: &$Float) -> bool {
                if !SealedFloat::is_finite(*rhs) {
                    return false;
                }
                let (rhs_128, dir, overflow) =
                    rhs.to_fixed_dir_overflow(Self::FRAC_NBITS, Self::INT_NBITS);
                let rhs_bits = match rhs_128 {
                    Widest::Unsigned(bits) => bits as <Self as Fixed>::Bits,
                    Widest::Negative(bits) => bits as <Self as Fixed>::Bits,
                };
                dir == Ordering::Equal && !overflow && rhs_bits == self.to_bits()
            }
        }

        impl<Frac> PartialEq<$Fix<Frac>> for $Float
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn eq(&self, rhs: &$Fix<Frac>) -> bool {
                rhs.eq(self)
            }
        }

        impl<Frac> PartialOrd<$Float> for $Fix<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Float) -> Option<Ordering> {
                if SealedFloat::is_nan(*rhs) {
                    return None;
                }
                let rhs_is_neg = SealedFloat::is_sign_negative(*rhs);
                if SealedFloat::is_infinite(*rhs) {
                    return if rhs_is_neg {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Less)
                    };
                }
                match (self.to_bits().is_negative(), rhs_is_neg) {
                    (false, true) => return Some(Ordering::Greater),
                    (true, false) => return Some(Ordering::Less),
                    _ => {}
                }
                let (rhs_128, dir, overflow) =
                    rhs.to_fixed_dir_overflow(Self::FRAC_NBITS, Self::INT_NBITS);
                if overflow {
                    return if rhs_is_neg {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Less)
                    };
                }
                let rhs_bits = match rhs_128 {
                    Widest::Unsigned(bits) => bits as <Self as Fixed>::Bits,
                    Widest::Negative(bits) => bits as <Self as Fixed>::Bits,
                };
                Some(self.to_bits().cmp(&rhs_bits).then(dir))
            }

            #[inline]
            fn lt(&self, rhs: &$Float) -> bool {
                if SealedFloat::is_nan(*rhs) {
                    return false;
                }
                let rhs_is_neg = SealedFloat::is_sign_negative(*rhs);
                if SealedFloat::is_infinite(*rhs) {
                    return !rhs_is_neg;
                }
                match (self.to_bits().is_negative(), rhs_is_neg) {
                    (false, true) => return false,
                    (true, false) => return true,
                    _ => {}
                }
                let (rhs_128, dir, overflow) =
                    rhs.to_fixed_dir_overflow(Self::FRAC_NBITS, Self::INT_NBITS);
                if overflow {
                    return !rhs_is_neg;
                }
                let rhs_bits = match rhs_128 {
                    Widest::Unsigned(bits) => bits as <Self as Fixed>::Bits,
                    Widest::Negative(bits) => bits as <Self as Fixed>::Bits,
                };
                let lhs_bits = self.to_bits();
                lhs_bits < rhs_bits || (lhs_bits == rhs_bits && dir == Ordering::Less)
            }

            #[inline]
            fn le(&self, rhs: &$Float) -> bool {
                !SealedFloat::is_nan(*rhs) && !rhs.lt(self)
            }

            #[inline]
            fn gt(&self, rhs: &$Float) -> bool {
                rhs.lt(self)
            }

            #[inline]
            fn ge(&self, rhs: &$Float) -> bool {
                !SealedFloat::is_nan(*rhs) && !self.lt(rhs)
            }
        }

        impl<Frac> PartialOrd<$Fix<Frac>> for $Float
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fix<Frac>) -> Option<Ordering> {
                rhs.partial_cmp(self).map(Ordering::reverse)
            }

            #[inline]
            fn lt(&self, rhs: &$Fix<Frac>) -> bool {
                if SealedFloat::is_nan(*self) {
                    return false;
                }
                let lhs_is_neg = SealedFloat::is_sign_negative(*self);
                if SealedFloat::is_infinite(*self) {
                    return lhs_is_neg;
                }
                match (lhs_is_neg, rhs.to_bits().is_negative()) {
                    (false, true) => return false,
                    (true, false) => return true,
                    _ => {}
                }
                let (lhs_128, dir, overflow) =
                    self.to_fixed_dir_overflow(<$Fix<Frac>>::FRAC_NBITS, <$Fix<Frac>>::INT_NBITS);
                if overflow {
                    return lhs_is_neg;
                }
                let lhs_bits = match lhs_128 {
                    Widest::Unsigned(bits) => bits as <$Fix<Frac> as Fixed>::Bits,
                    Widest::Negative(bits) => bits as <$Fix<Frac> as Fixed>::Bits,
                };
                let rhs_bits = rhs.to_bits();
                lhs_bits < rhs_bits || (lhs_bits == rhs_bits && dir == Ordering::Greater)
            }

            #[inline]
            fn le(&self, rhs: &$Fix<Frac>) -> bool {
                !SealedFloat::is_nan(*self) && !rhs.lt(self)
            }

            #[inline]
            fn gt(&self, rhs: &$Fix<Frac>) -> bool {
                rhs.lt(self)
            }

            #[inline]
            fn ge(&self, rhs: &$Fix<Frac>) -> bool {
                !SealedFloat::is_nan(*self) && !self.lt(rhs)
            }
        }
    };
}

macro_rules! fixed_cmp_all {
    ($Fix:ident($NBits:ident)) => {
        impl<Frac> Eq for $Fix<Frac> where Frac: Unsigned + IsLessOrEqual<$NBits, Output = True> {}

        impl<Frac> Ord for $Fix<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            #[inline]
            fn cmp(&self, rhs: &$Fix<Frac>) -> Ordering {
                self.to_bits().cmp(&rhs.to_bits())
            }
        }

        fixed_cmp_fixed! { $Fix($NBits), FixedI8(U8) }
        fixed_cmp_fixed! { $Fix($NBits), FixedI16(U16) }
        fixed_cmp_fixed! { $Fix($NBits), FixedI32(U32) }
        fixed_cmp_fixed! { $Fix($NBits), FixedI64(U64) }
        fixed_cmp_fixed! { $Fix($NBits), FixedI128(U128) }
        fixed_cmp_fixed! { $Fix($NBits), FixedU8(U8) }
        fixed_cmp_fixed! { $Fix($NBits), FixedU16(U16) }
        fixed_cmp_fixed! { $Fix($NBits), FixedU32(U32) }
        fixed_cmp_fixed! { $Fix($NBits), FixedU64(U64) }
        fixed_cmp_fixed! { $Fix($NBits), FixedU128(U128) }
        fixed_cmp_int! { $Fix($NBits), i8 }
        fixed_cmp_int! { $Fix($NBits), i16 }
        fixed_cmp_int! { $Fix($NBits), i32 }
        fixed_cmp_int! { $Fix($NBits), i64 }
        fixed_cmp_int! { $Fix($NBits), i128 }
        fixed_cmp_int! { $Fix($NBits), u8 }
        fixed_cmp_int! { $Fix($NBits), u16 }
        fixed_cmp_int! { $Fix($NBits), u32 }
        fixed_cmp_int! { $Fix($NBits), u64 }
        fixed_cmp_int! { $Fix($NBits), u128 }
        #[cfg(feature = "f16")]
        fixed_cmp_float! { $Fix($NBits), f16 }
        fixed_cmp_float! { $Fix($NBits), f32 }
        fixed_cmp_float! { $Fix($NBits), f64 }
    };
}

fixed_cmp_all! { FixedI8(U8) }
fixed_cmp_all! { FixedI16(U16) }
fixed_cmp_all! { FixedI32(U32) }
fixed_cmp_all! { FixedI64(U64) }
fixed_cmp_all! { FixedI128(U128) }
fixed_cmp_all! { FixedU8(U8) }
fixed_cmp_all! { FixedU16(U16) }
fixed_cmp_all! { FixedU32(U32) }
fixed_cmp_all! { FixedU64(U64) }
fixed_cmp_all! { FixedU128(U128) }

macro_rules! fixed_cmp {
    ($Fixed:ident($Inner:ty, $Len:ty, $bits_count:expr)) => {};
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
#[cfg_attr(feature = "cargo-clippy", allow(clippy::float_cmp))]
#[cfg_attr(feature = "cargo-clippy", allow(clippy::cognitive_complexity))]
mod tests {
    use crate::*;

    #[test]
    fn cmp_signed() {
        use core::cmp::Ordering::*;
        let neg1_16 = FixedI32::<frac::U16>::from_int(-1);
        let neg1_20 = FixedI32::<frac::U20>::from_int(-1);
        let mut a = neg1_16;
        let mut b = neg1_20;
        // a = ffff.0000 = -1, b = fff.00000 = -1
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert_eq!(a, -1i8);
        assert_eq!(b, -1i128);
        a >>= 16;
        b >>= 16;
        // a = ffff.ffff = -2^-16, b = fff.ffff0 = -2^-16
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert!(a < 0.0);
        assert_eq!(a, -(-16f32).exp2());
        assert!(a <= -(-16f32).exp2());
        assert!(a >= -(-16f32).exp2());
        assert!(a < (-16f32).exp2());
        assert_ne!(a, -0.75 * (-16f32).exp2());
        assert!(a < -0.75 * (-16f32).exp2());
        assert!(a <= -0.75 * (-16f32).exp2());
        assert!(a > -1.25 * (-16f32).exp2());
        assert!(a >= -1.25 * (-16f32).exp2());
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
        assert_eq!(a, -1i16 << 11);
        assert_eq!(b, -1i64 << 11);
        a <<= 1;
        b <<= 1;
        // a = f000.0000 = -2^-12, b = 000.00000 = 0
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Less));
        assert_eq!(b.partial_cmp(&a), Some(Greater));
        assert!(a < 1u8);
        assert_eq!(b, 0);
    }

    #[test]
    fn cmp_unsigned() {
        use core::cmp::Ordering::*;
        let one_16 = FixedU32::<frac::U16>::from_int(1);
        let one_20 = FixedU32::<frac::U20>::from_int(1);
        let mut a = one_16;
        let mut b = one_20;
        // a = 0001.0000 = 1, b = 001.00000 = 1
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert_eq!(a, 1u8);
        assert_eq!(b, 1i128);
        a >>= 16;
        b >>= 16;
        // a = 0000.0001 = 2^-16, b = 000.00010 = 2^-16
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert!(a > 0.0);
        assert_eq!(a, (-16f64).exp2());
        assert!(a <= (-16f64).exp2());
        assert!(a >= (-16f64).exp2());
        assert!(a > -(-16f64).exp2());
        assert_ne!(a, 0.75 * (-16f64).exp2());
        assert!(a > 0.75 * (-16f64).exp2());
        assert!(a >= 0.75 * (-16f64).exp2());
        assert!(a < 1.25 * (-16f64).exp2());
        assert!(a <= 1.25 * (-16f64).exp2());
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
        assert_eq!(a, 1i16 << 11);
        assert_eq!(b, 1u64 << 11);
        a <<= 1;
        b <<= 1;
        // a = 1000.0000 = 2^12, b = 000.00000 = 0
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Greater));
        assert_eq!(b.partial_cmp(&a), Some(Less));
        assert!(a > -1i8);
        assert_eq!(a, 1i32 << 12);
        assert_eq!(b, 0);
    }
}
