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

use {
    crate::{
        frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8},
        sealed::{Fixed, SealedFloat, SealedInt},
        FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
        FixedU8,
    },
    core::{
        fmt::{Debug, Display},
        hash::Hash,
    },
};

// Unsigned can have 0 ≤ x < 2↑128, that is its msb can be 0 or 1.
// Negative can have −2↑127 ≤ x < 0, that is its msb must be 1.
pub enum Widest {
    Unsigned(u128),
    Negative(i128),
}

pub trait SealedFixed: Copy + Debug + Default + Display + Eq + Hash + Ord {
    type FracNBits: Unsigned;
    type Bits: SealedInt;

    const FRAC_NBITS: u32 = Self::FracNBits::U32;
    const INT_NBITS: u32 = Self::Bits::NBITS - Self::FRAC_NBITS;

    const FRAC_MASK: u128 = !Self::INT_MASK;
    // split shift in two parts in case that FRAC_NBITS == 128
    const INT_MASK: u128 =
        !0 << (Self::FRAC_NBITS / 2) << (Self::FRAC_NBITS - Self::FRAC_NBITS / 2);
    // 0 for no frac bits
    const FRAC_MSB: u128 = Self::FRAC_MASK ^ (Self::FRAC_MASK >> 1);
    // 0 for no int bits
    const INT_LSB: u128 = Self::INT_MASK ^ (Self::INT_MASK << 1);

    #[inline]
    fn from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        let (wrapped, overflow) = SealedFixed::overflowing_from_fixed(val);
        debug_assert!(!overflow, "{} overflows", val);
        let _ = overflow;
        wrapped
    }
    #[inline]
    fn checked_from_fixed<F>(val: F) -> Option<Self>
    where
        F: Fixed,
    {
        match SealedFixed::overflowing_from_fixed(val) {
            (_, true) => None,
            (wrapped, false) => Some(wrapped),
        }
    }
    fn saturating_from_fixed<F>(fixed: F) -> Self
    where
        F: Fixed;
    #[inline]
    fn wrapping_from_fixed<F>(val: F) -> Self
    where
        F: Fixed,
    {
        let (wrapped, _) = SealedFixed::overflowing_from_fixed(val);
        wrapped
    }
    fn overflowing_from_fixed<F>(fixed: F) -> (Self, bool)
    where
        F: Fixed;

    fn saturating_from_float<F>(float: F) -> Self
    where
        F: SealedFloat;
    fn overflowing_from_float<F>(float: F) -> (Self, bool)
    where
        F: SealedFloat;
    fn to_float<F>(self) -> F
    where
        F: SealedFloat;

    #[inline]
    fn one() -> Option<Self> {
        let min_int_bits = if Self::Bits::IS_SIGNED { 2 } else { 1 };
        if Self::INT_NBITS < min_int_bits {
            None
        } else {
            Some(Self::from_bits(Self::Bits::one_shl(Self::FRAC_NBITS)))
        }
    }

    #[inline]
    fn minus_one() -> Option<Self> {
        if !Self::Bits::IS_SIGNED || Self::INT_NBITS < 1 {
            None
        } else {
            Some(Self::from_bits(Self::Bits::all_ones_shl(Self::FRAC_NBITS)))
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

    fn wrapping_ceil(self) -> Self;
    fn wrapping_floor(self) -> Self;
    fn wrapping_round(self) -> Self;
    fn wrapping_neg(self) -> Self;
    fn wrapping_abs(self) -> Self;
}

macro_rules! sealed_fixed {
    ($Fixed:ident($Bits:ty, $Len:ty, $Signedness:tt)) => {
        impl<Frac> SealedFixed for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            type FracNBits = Frac;
            type Bits = $Bits;

            #[inline]
            fn saturating_from_fixed<F>(val: F) -> Self
            where
                F: Fixed,
            {
                let (value, _, overflow) = val.to_bits().to_fixed_dir_overflow(
                    F::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                if overflow {
                    return if val.to_bits().is_negative() {
                        Self::from_bits(Self::Bits::min_value())
                    } else {
                        Self::from_bits(Self::Bits::max_value())
                    };
                }
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match value {
                        Widest::Unsigned(bits) => {
                            if (bits as Self::Bits) < 0 {
                                return Self::from_bits(Self::Bits::max_value());
                            }
                            bits as Self::Bits
                        }
                        Widest::Negative(bits) => bits as Self::Bits,
                    },
                    match value {
                        Widest::Unsigned(bits) => bits as Self::Bits,
                        Widest::Negative(_) => {
                            return Self::from_bits(Self::Bits::min_value());
                        }
                    },
                );
                SealedFixed::from_bits(bits)
            }

            #[inline]
            fn overflowing_from_fixed<F>(val: F) -> (Self, bool)
            where
                F: Fixed,
            {
                let (value, _, mut overflow) = val.to_bits().to_fixed_dir_overflow(
                    F::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match value {
                        Widest::Unsigned(bits) => {
                            if (bits as Self::Bits) < 0 {
                                overflow = true;
                            }
                            bits as Self::Bits
                        }
                        Widest::Negative(bits) => bits as Self::Bits,
                    },
                    match value {
                        Widest::Unsigned(bits) => bits as Self::Bits,
                        Widest::Negative(bits) => {
                            overflow = true;
                            bits as Self::Bits
                        }
                    },
                );
                (SealedFixed::from_bits(bits), overflow)
            }

            #[inline]
            fn saturating_from_float<F>(val: F) -> Self
            where
                F: SealedFloat,
            {
                if val.is_nan() {
                    panic!("NaN");
                }
                let saturated = if val.is_sign_negative() {
                    Self::min_value()
                } else {
                    Self::max_value()
                };
                if !val.is_finite() {
                    return saturated;
                }
                let (value, _, overflow) =
                    val.to_fixed_dir_overflow(Self::FRAC_NBITS, Self::INT_NBITS);
                if overflow {
                    return saturated;
                }
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match value {
                        Widest::Unsigned(bits) => {
                            if (bits as <Self as SealedFixed>::Bits) < 0 {
                                return Self::max_value();
                            }
                            bits as <Self as SealedFixed>::Bits
                        }
                        Widest::Negative(bits) => bits as <Self as SealedFixed>::Bits,
                    },
                    match value {
                        Widest::Unsigned(bits) => bits as <Self as SealedFixed>::Bits,
                        Widest::Negative(_) => return Self::min_value(),
                    },
                );
                SealedFixed::from_bits(bits)
            }
            #[inline]
            fn overflowing_from_float<F>(val: F) -> (Self, bool)
            where
                F: SealedFloat,
            {
                if !val.is_finite() {
                    panic!("{} is not finite", val);
                }
                let (value, _, mut overflow) =
                    val.to_fixed_dir_overflow(Self::FRAC_NBITS, Self::INT_NBITS);
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match value {
                        Widest::Unsigned(bits) => {
                            if (bits as <Self as SealedFixed>::Bits) < 0 {
                                overflow = true;
                            }
                            bits as <Self as SealedFixed>::Bits
                        }
                        Widest::Negative(bits) => bits as <Self as SealedFixed>::Bits,
                    },
                    match value {
                        Widest::Unsigned(bits) => bits as <Self as SealedFixed>::Bits,
                        Widest::Negative(bits) => {
                            overflow = true;
                            bits as <Self as SealedFixed>::Bits
                        }
                    },
                );
                (SealedFixed::from_bits(bits), overflow)
            }

            #[inline]
            fn to_float<F>(self) -> F
            where
                F: SealedFloat,
            {
                let (neg, abs) = self.to_bits().neg_abs();
                SealedFloat::from_neg_abs(neg, u128::from(abs), Self::FRAC_NBITS, Self::INT_NBITS)
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
                let (neg, abs) = SealedInt::neg_abs(self.to_bits());
                let (int_abs, frac_abs) = if Self::INT_NBITS == 0 {
                    (0, abs)
                } else if Self::FRAC_NBITS == 0 {
                    (abs, 0)
                } else {
                    ((abs >> Self::FRAC_NBITS), (abs << Self::INT_NBITS))
                };
                (neg, int_abs, frac_abs)
            }

            #[inline]
            fn wrapping_ceil(self) -> Self {
                self.wrapping_ceil()
            }

            #[inline]
            fn wrapping_floor(self) -> Self {
                self.wrapping_floor()
            }

            #[inline]
            fn wrapping_round(self) -> Self {
                self.wrapping_round()
            }

            #[inline]
            fn wrapping_neg(self) -> Self {
                self.wrapping_neg()
            }

            #[inline]
            fn wrapping_abs(self) -> Self {
                if_signed_unsigned! {
                    $Signedness,
                    self.wrapping_abs(),
                    self,
                }
            }
        }
    };
}

sealed_fixed! { FixedI8(i8, U8, Signed) }
sealed_fixed! { FixedI16(i16, U16, Signed) }
sealed_fixed! { FixedI32(i32, U32, Signed) }
sealed_fixed! { FixedI64(i64, U64, Signed) }
sealed_fixed! { FixedI128(i128, U128, Signed) }
sealed_fixed! { FixedU8(u8, U8, Unsigned) }
sealed_fixed! { FixedU16(u16, U16, Unsigned) }
sealed_fixed! { FixedU32(u32, U32, Unsigned) }
sealed_fixed! { FixedU64(u64, U64, Unsigned) }
sealed_fixed! { FixedU128(u128, U128, Unsigned) }
