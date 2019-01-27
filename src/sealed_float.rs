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
use sealed::SealedInt;

pub trait SealedFloat: Copy {
    type Bits: SealedInt;

    fn prec() -> u32;

    #[inline]
    fn exp_bias() -> i32 {
        let nbits = Self::Bits::nbits();
        let exp_bits = nbits - Self::prec();
        (1 << (exp_bits - 1)) - 1
    }

    #[inline]
    fn exp_min() -> i32 {
        1 - Self::exp_bias()
    }

    #[inline]
    fn exp_max() -> i32 {
        Self::exp_bias()
    }

    fn zero(neg: bool) -> Self;
    fn infinity(neg: bool) -> Self;
    fn from_parts(neg: bool, exp: i32, mant: Self::Bits) -> Self;
    fn parts(self) -> (bool, i32, Self::Bits);
}

macro_rules! sealed_float {
    ($Float:ident($Bits:ty, $prec:expr)) => {
        impl SealedFloat for $Float {
            type Bits = $Bits;

            #[inline]
            fn prec() -> u32 {
                $prec
            }

            #[inline]
            fn zero(neg: bool) -> $Float {
                let nbits = <Self::Bits as SealedInt>::nbits();
                let neg_mask = !0 << (nbits - 1);
                let neg_bits = if neg { neg_mask } else { 0 };
                <$Float>::from_bits(neg_bits)
            }

            #[inline]
            fn infinity(neg: bool) -> $Float {
                let nbits = <Self::Bits as SealedInt>::nbits();
                let neg_mask = !0 << (nbits - 1);
                let mant_mask = !(!0 << ($prec - 1));
                let exp_mask = !(neg_mask | mant_mask);

                let neg_bits = if neg { neg_mask } else { 0 };
                <$Float>::from_bits(neg_bits | exp_mask)
            }

            #[inline]
            fn from_parts(neg: bool, exp: i32, mant: Self::Bits) -> $Float {
                let nbits = <Self::Bits as SealedInt>::nbits();
                let neg_mask = !0 << (nbits - 1);

                let neg_bits = if neg { neg_mask } else { 0 };
                let biased_exp = (exp + <$Float as SealedFloat>::exp_bias()) as Self::Bits;
                let exp_bits = biased_exp << ($prec - 1);
                <$Float>::from_bits(neg_bits | exp_bits | mant)
            }

            #[inline]
            fn parts(self) -> (bool, i32, $Bits) {
                let nbits = <Self::Bits as SealedInt>::nbits();
                let neg_mask = !0 << (nbits - 1);
                let mant_mask = !(!0 << ($prec - 1));
                let exp_mask = !(neg_mask | mant_mask);

                let bits = self.to_bits();
                let neg = bits & neg_mask != 0;
                let biased_exp = (bits & exp_mask) >> ($prec - 1);
                let exp = ({
                    #[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
                    {
                        biased_exp as i32
                    }
                }) - <$Float as SealedFloat>::exp_bias();
                let mant = bits & mant_mask;

                (neg, exp, mant)
            }
        }
    };
}

#[cfg(feature = "f16")]
sealed_float! { f16(u16, 11) }
sealed_float! { f32(u32, 24) }
sealed_float! { f64(u64, 53) }
