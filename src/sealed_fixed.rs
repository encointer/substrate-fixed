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
    frac::Unsigned,
    sealed::{Fixed, SealedFloat, SealedInt},
    types::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    fmt::{Debug, Display},
    hash::Hash,
};

// Unsigned can have 0 ≤ x < 2↑128, that is its msb can be 0 or 1.
// Negative can have −2↑127 ≤ x < 0, that is its msb must be 1.
pub enum Widest {
    Unsigned(u128),
    Negative(i128),
}

pub trait SealedFixed: Copy {
    type FracNBits: Unsigned;
    type SBits: SealedInt;
    type Traits: Copy + Debug + Default + Into<Self> + Display + Eq + Hash + Ord;

    const FRAC_NBITS: u32 = Self::FracNBits::U32;
    const INT_NBITS: u32 = Self::SBits::NBITS - Self::FRAC_NBITS;

    const FRAC_MASK: u128 = !Self::INT_MASK;
    // split shift in two parts in case that FRAC_NBITS == 128
    const INT_MASK: u128 =
        !0 << (Self::FRAC_NBITS / 2) << (Self::FRAC_NBITS - Self::FRAC_NBITS / 2);
    // 0 for no frac bits
    const FRAC_MSB: u128 = Self::FRAC_MASK ^ (Self::FRAC_MASK >> 1);
    // 0 for no int bits
    const INT_LSB: u128 = Self::INT_MASK ^ (Self::INT_MASK << 1);

    fn traits(self) -> Self::Traits;

    #[inline]
    fn from_fixed<F: Fixed>(val: F) -> Self {
        let (wrapped, overflow) = SealedFixed::overflowing_from_fixed(val);
        debug_assert!(!overflow, "{} overflows", val.traits());
        let _ = overflow;
        wrapped
    }
    #[inline]
    fn checked_from_fixed<F: Fixed>(val: F) -> Option<Self> {
        match SealedFixed::overflowing_from_fixed(val) {
            (_, true) => None,
            (wrapped, false) => Some(wrapped),
        }
    }
    fn saturating_from_fixed<F: Fixed>(fixed: F) -> Self;
    #[inline]
    fn wrapping_from_fixed<F: Fixed>(val: F) -> Self {
        let (wrapped, _) = SealedFixed::overflowing_from_fixed(val);
        wrapped
    }
    fn overflowing_from_fixed<F: Fixed>(fixed: F) -> (Self, bool);

    fn saturating_from_float<F: SealedFloat>(float: F) -> Self;
    fn overflowing_from_float<F: SealedFloat>(float: F) -> (Self, bool);
    fn to_float<F: SealedFloat>(self) -> F;

    fn from_sbits(bits: Self::SBits) -> Self;
    fn to_sbits(self) -> Self::SBits;
    fn parts(
        self,
    ) -> (
        bool,
        <Self::SBits as SealedInt>::Unsigned,
        <Self::SBits as SealedInt>::Unsigned,
    );

    fn wrapping_ceil(self) -> Self;
    fn wrapping_floor(self) -> Self;
    fn wrapping_round(self) -> Self;
    fn wrapping_neg(self) -> Self;
    fn wrapping_abs(self) -> Self;
}

macro_rules! sealed_fixed {
    ($Fixed:ident($Bits:ty, $LenEqU:ident, $Signedness:tt)) => {
        impl<Frac: $LenEqU> SealedFixed for $Fixed<Frac> {
            type FracNBits = Frac;
            type SBits = $Bits;
            type Traits = $Fixed<Frac>;

            #[inline]
            fn traits(self) -> Self::Traits {
                self
            }

            #[inline]
            fn saturating_from_fixed<F: Fixed>(val: F) -> Self {
                let (value, _, overflow) = val.to_sbits().to_fixed_dir_overflow(
                    F::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                if overflow {
                    return if val.to_sbits().is_negative() {
                        SealedFixed::from_sbits(Self::SBits::min_value())
                    } else {
                        SealedFixed::from_sbits(Self::SBits::max_value())
                    };
                }
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match value {
                        Widest::Unsigned(bits) => {
                            if (bits as Self::SBits) < 0 {
                                return $Fixed::from_bits(Self::SBits::max_value());
                            }
                            bits as Self::SBits
                        }
                        Widest::Negative(bits) => bits as Self::SBits,
                    },
                    match value {
                        Widest::Unsigned(bits) => bits as Self::SBits,
                        Widest::Negative(_) => {
                            return $Fixed::from_bits(Self::SBits::min_value());
                        }
                    },
                );
                $Fixed::from_bits(bits)
            }

            #[inline]
            fn overflowing_from_fixed<F: Fixed>(val: F) -> (Self, bool) {
                let (value, _, mut overflow) = val.to_sbits().to_fixed_dir_overflow(
                    F::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match value {
                        Widest::Unsigned(bits) => {
                            if (bits as Self::SBits) < 0 {
                                overflow = true;
                            }
                            bits as Self::SBits
                        }
                        Widest::Negative(bits) => bits as Self::SBits,
                    },
                    match value {
                        Widest::Unsigned(bits) => bits as Self::SBits,
                        Widest::Negative(bits) => {
                            overflow = true;
                            bits as Self::SBits
                        }
                    },
                );
                ($Fixed::from_bits(bits), overflow)
            }

            #[inline]
            fn saturating_from_float<F: SealedFloat>(val: F) -> Self {
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
                            if (bits as Self::SBits) < 0 {
                                return Self::max_value();
                            }
                            bits as Self::SBits
                        }
                        Widest::Negative(bits) => bits as Self::SBits,
                    },
                    match value {
                        Widest::Unsigned(bits) => bits as Self::SBits,
                        Widest::Negative(_) => return Self::min_value(),
                    },
                );
                $Fixed::from_bits(bits)
            }
            #[inline]
            fn overflowing_from_float<F: SealedFloat>(val: F) -> (Self, bool) {
                if !val.is_finite() {
                    panic!("{} is not finite", val.traits());
                }
                let (value, _, mut overflow) =
                    val.to_fixed_dir_overflow(Self::FRAC_NBITS, Self::INT_NBITS);
                let bits = if_signed_unsigned!(
                    $Signedness,
                    match value {
                        Widest::Unsigned(bits) => {
                            if (bits as Self::SBits) < 0 {
                                overflow = true;
                            }
                            bits as Self::SBits
                        }
                        Widest::Negative(bits) => bits as Self::SBits,
                    },
                    match value {
                        Widest::Unsigned(bits) => bits as Self::SBits,
                        Widest::Negative(bits) => {
                            overflow = true;
                            bits as Self::SBits
                        }
                    },
                );
                ($Fixed::from_bits(bits), overflow)
            }

            #[inline]
            fn to_float<F: SealedFloat>(self) -> F {
                let (neg, abs) = self.to_bits().neg_abs();
                SealedFloat::from_neg_abs(neg, u128::from(abs), Self::FRAC_NBITS, Self::INT_NBITS)
            }

            #[inline]
            fn from_sbits(bits: Self::SBits) -> Self {
                $Fixed::from_bits(bits)
            }

            #[inline]
            fn to_sbits(self) -> Self::SBits {
                $Fixed::to_bits(self)
            }

            #[inline]
            fn parts(
                self,
            ) -> (
                bool,
                <Self::SBits as SealedInt>::Unsigned,
                <Self::SBits as SealedInt>::Unsigned,
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

sealed_fixed! { FixedI8(i8, LeEqU8, Signed) }
sealed_fixed! { FixedI16(i16, LeEqU16, Signed) }
sealed_fixed! { FixedI32(i32, LeEqU32, Signed) }
sealed_fixed! { FixedI64(i64, LeEqU64, Signed) }
sealed_fixed! { FixedI128(i128, LeEqU128, Signed) }
sealed_fixed! { FixedU8(u8, LeEqU8, Unsigned) }
sealed_fixed! { FixedU16(u16, LeEqU16, Unsigned) }
sealed_fixed! { FixedU32(u32, LeEqU32, Unsigned) }
sealed_fixed! { FixedU64(u64, LeEqU64, Unsigned) }
sealed_fixed! { FixedU128(u128, LeEqU128, Unsigned) }
