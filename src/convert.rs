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

use core::ops::{Add, Sub};
use frac::{IsGreaterOrEqual, IsLessOrEqual, True, Unsigned, U0, U1, U128, U16, U32, U64, U8};
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

macro_rules! convert {
    (($SrcU:ident, $SrcI:ident, $SrcBits:ident) -> ($DstU:ident, $DstI:ident, $DstBits:ident)) => {
        // Conditions: FracSrc <= FracDst <= FracSrc + ($DstBits - $SrcBits)
        impl<FracSrc, FracDst, FracMax> From<$SrcU<FracSrc>> for $DstU<FracDst>
        where
            FracSrc: Unsigned
                + IsLessOrEqual<$SrcBits, Output = True>
                + Add<<$DstBits as Sub<$SrcBits>>::Output, Output = FracMax>,
            FracDst: Unsigned
                + IsLessOrEqual<$DstBits, Output = True>
                + IsGreaterOrEqual<FracSrc, Output = True>
                + IsLessOrEqual<FracMax, Output = True>,
            FracMax: Unsigned,
        {
            #[inline]
            fn from(src: $SrcU<FracSrc>) -> $DstU<FracDst> {
                let unshifted = $DstU::<FracDst>::from_bits(src.to_bits().into()).to_bits();
                let shift = FracDst::to_u32() - FracSrc::to_u32();
                $DstU::<FracDst>::from_bits(unshifted << shift)
            }
        }

        // Conditions: FracSrc <= FracDst <= FracSrc + ($DstBits - $SrcBits)
        impl<FracSrc, FracDst, FracMax> From<$SrcI<FracSrc>> for $DstI<FracDst>
        where
            FracSrc: Unsigned
                + IsLessOrEqual<$SrcBits, Output = True>
                + Add<<$DstBits as Sub<$SrcBits>>::Output, Output = FracMax>,
            FracDst: Unsigned
                + IsLessOrEqual<$DstBits, Output = True>
                + IsGreaterOrEqual<FracSrc, Output = True>
                + IsLessOrEqual<FracMax, Output = True>,
            FracMax: Unsigned,
        {
            #[inline]
            fn from(src: $SrcI<FracSrc>) -> $DstI<FracDst> {
                let unshifted = $DstI::<FracDst>::from_bits(src.to_bits().into()).to_bits();
                let shift = FracDst::to_u32() - FracSrc::to_u32();
                $DstI::<FracDst>::from_bits(unshifted << shift)
            }
        }

        // Conditions: FracSrc <= FracDst <= FracSrc + ($DstBits - $SrcBits - 1)
        impl<FracSrc, FracDst, FracMax> From<$SrcU<FracSrc>> for $DstI<FracDst>
        where
            FracSrc: Unsigned
                + IsLessOrEqual<$SrcBits, Output = True>
                + Add<
                    <<$DstBits as Sub<$SrcBits>>::Output as Sub<U1>>::Output,
                    Output = FracMax,
                >,
            FracDst: Unsigned
                + IsLessOrEqual<$DstBits, Output = True>
                + IsGreaterOrEqual<FracSrc, Output = True>
                + IsLessOrEqual<FracMax, Output = True>,
            FracMax: Unsigned,
        {
            #[inline]
            fn from(src: $SrcU<FracSrc>) -> $DstI<FracDst> {
                let unshifted = $DstI::<FracDst>::from_bits(src.to_bits().into()).to_bits();
                let shift = FracDst::to_u32() - FracSrc::to_u32();
                $DstI::<FracDst>::from_bits(unshifted << shift)
            }
        }
    };
}

convert! { (FixedU8, FixedI8, U8) -> (FixedU16, FixedI16, U16) }
convert! { (FixedU8, FixedI8, U8) -> (FixedU32, FixedI32, U32) }
convert! { (FixedU8, FixedI8, U8) -> (FixedU64, FixedI64, U64) }
convert! { (FixedU8, FixedI8, U8) -> (FixedU128, FixedI128, U128) }

convert! { (FixedU16, FixedI16, U16) -> (FixedU32, FixedI32, U32) }
convert! { (FixedU16, FixedI16, U16) -> (FixedU64, FixedI64, U64) }
convert! { (FixedU16, FixedI16, U16) -> (FixedU128, FixedI128, U128) }

convert! { (FixedU32, FixedI32, U32) -> (FixedU64, FixedI64, U64) }
convert! { (FixedU32, FixedI32, U32) -> (FixedU128, FixedI128, U128) }

convert! { (FixedU64, FixedI64, U64) -> (FixedU128, FixedI128, U128) }

macro_rules! prim_to_fixed {
    (($SrcU:ident, $SrcI:ident, $SrcBits:ident) -> ($DstU:ident, $DstI:ident, $DstBits:ident)) => {
        // Condition: FracDst <= $DstBits - $SrcBits
        impl<FracDst> From<$SrcU> for $DstU<FracDst>
        where
            FracDst: Unsigned
                + IsLessOrEqual<$DstBits, Output = True>
                + IsLessOrEqual<<$DstBits as Sub<$SrcBits>>::Output, Output = True>,
        {
            #[inline]
            fn from(src: $SrcU) -> $DstU<FracDst> {
                let unshifted = $DstU::<FracDst>::from_bits(src.into()).to_bits();
                let shift = FracDst::to_u32();
                $DstU::<FracDst>::from_bits(unshifted << shift)
            }
        }

        // Condition: FracDst <= $DstBits - $SrcBits
        impl<FracDst> From<$SrcI> for $DstI<FracDst>
        where
            FracDst: Unsigned
                + IsLessOrEqual<$DstBits, Output = True>
                + IsLessOrEqual<<$DstBits as Sub<$SrcBits>>::Output, Output = True>,
        {
            #[inline]
            fn from(src: $SrcI) -> $DstI<FracDst> {
                let unshifted = $DstI::<FracDst>::from_bits(src.into()).to_bits();
                let shift = FracDst::to_u32();
                $DstI::<FracDst>::from_bits(unshifted << shift)
            }
        }

        // Condition: FracDst <= $DstBits - $SrcBits - 1
        impl<FracDst> From<$SrcU> for $DstI<FracDst>
        where
            FracDst: Unsigned
                + IsLessOrEqual<$DstBits, Output = True>
                + IsLessOrEqual<
                    <<$DstBits as Sub<$SrcBits>>::Output as Sub<U1>>::Output,
                    Output = True,
                >,
        {
            #[inline]
            fn from(src: $SrcU) -> $DstI<FracDst> {
                let unshifted = $DstI::<FracDst>::from_bits(src.into()).to_bits();
                let shift = FracDst::to_u32();
                $DstI::<FracDst>::from_bits(unshifted << shift)
            }
        }
    };

    (($SrcU:ident, $SrcI:ident) -> ($DstU:ident, $DstI:ident)) => {
        impl From<$SrcU> for $DstU<U0> {
            #[inline]
            fn from(src: $SrcU) -> $DstU<U0> {
                $DstU::<U0>::from_bits(src)
            }
        }

        impl From<$SrcI> for $DstI<U0> {
            #[inline]
            fn from(src: $SrcI) -> $DstI<U0> {
                $DstI::<U0>::from_bits(src)
            }
        }
    };
}

prim_to_fixed! { (u8, i8) -> (FixedU8, FixedI8) }
prim_to_fixed! { (u8, i8, U8) -> (FixedU16, FixedI16, U16) }
prim_to_fixed! { (u8, i8, U8) -> (FixedU32, FixedI32, U32) }
prim_to_fixed! { (u8, i8, U8) -> (FixedU64, FixedI64, U64) }
prim_to_fixed! { (u8, i8, U8) -> (FixedU128, FixedI128, U128) }

prim_to_fixed! { (u16, i16) -> (FixedU16, FixedI16) }
prim_to_fixed! { (u16, i16, U16) -> (FixedU32, FixedI32, U32) }
prim_to_fixed! { (u16, i16, U16) -> (FixedU64, FixedI64, U64) }
prim_to_fixed! { (u16, i16, U16) -> (FixedU128, FixedI128, U128) }

prim_to_fixed! { (u32, i32) -> (FixedU32, FixedI32) }
prim_to_fixed! { (u32, i32, U32) -> (FixedU64, FixedI64, U64) }
prim_to_fixed! { (u32, i32, U32) -> (FixedU128, FixedI128, U128) }

prim_to_fixed! { (u64, i64) -> (FixedU64, FixedI64) }
prim_to_fixed! { (u64, i64, U64) -> (FixedU128, FixedI128, U128) }

prim_to_fixed! { (u128, i128) -> (FixedU128, FixedI128) }

macro_rules! fixed_to_prim {
    (($SrcU:ident, $SrcI:ident) -> ($DstU:ident, $DstI:ident)) => {
        impl From<$SrcU<U0>> for $DstU {
            #[inline]
            fn from(src: $SrcU<U0>) -> $DstU {
                src.to_bits()
            }
        }

        impl From<$SrcI<U0>> for $DstI {
            #[inline]
            fn from(src: $SrcI<U0>) -> $DstI {
                src.to_bits()
            }
        }
    };
    (($SrcU:ident, $SrcI:ident) -> wider ($DstU:ident, $DstI:ident)) => {
        impl From<$SrcU<U0>> for $DstU {
            #[inline]
            fn from(src: $SrcU<U0>) -> $DstU {
                src.to_bits().into()
            }
        }

        impl From<$SrcI<U0>> for $DstI {
            #[inline]
            fn from(src: $SrcI<U0>) -> $DstI {
                src.to_bits().into()
            }
        }

        impl From<$SrcU<U0>> for $DstI {
            #[inline]
            fn from(src: $SrcU<U0>) -> $DstI {
                src.to_bits().into()
            }
        }
    };
}

fixed_to_prim! { (FixedU8, FixedI8) -> (u8, i8) }
fixed_to_prim! { (FixedU8, FixedI8) -> wider (u16, i16) }
fixed_to_prim! { (FixedU8, FixedI8) -> wider (u32, i32) }
fixed_to_prim! { (FixedU8, FixedI8) -> wider (u64, i64) }
fixed_to_prim! { (FixedU8, FixedI8) -> wider (u128, i128) }

fixed_to_prim! { (FixedU16, FixedI16) -> (u16, i16) }
fixed_to_prim! { (FixedU16, FixedI16) -> wider (u32, i32) }
fixed_to_prim! { (FixedU16, FixedI16) -> wider (u64, i64) }
fixed_to_prim! { (FixedU16, FixedI16) -> wider (u128, i128) }

fixed_to_prim! { (FixedU32, FixedI32) -> (u32, i32) }
fixed_to_prim! { (FixedU32, FixedI32) -> wider (u64, i64) }
fixed_to_prim! { (FixedU32, FixedI32) -> wider (u128, i128) }

fixed_to_prim! { (FixedU64, FixedI64) -> (u64, i64) }
fixed_to_prim! { (FixedU64, FixedI64) -> wider (u128, i128) }

fixed_to_prim! { (FixedU128, FixedI128) -> (u128, i128) }

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn expanding_from_unsigned() {
        type L8 = FixedU8<frac::U0>;
        type LL16 = FixedU16<frac::U0>;
        type LH16 = FixedU16<frac::U8>;
        type LL128 = FixedU128<frac::U0>;
        type LH128 = FixedU128<frac::U120>;

        type H8 = FixedU8<frac::U8>;
        type HL16 = FixedU16<frac::U8>;
        type HH16 = FixedU16<frac::U16>;
        type HL128 = FixedU128<frac::U8>;
        type HH128 = FixedU128<frac::U128>;

        let vals: &[u8] = &[0x00, 0x7f, 0x80, 0xff];
        for &val in vals {
            let val16 = u16::from(val);
            let val128 = u128::from(val);

            let l = L8::from_bits(val);
            assert_eq!(l, L8::from(val));
            assert_eq!(val, u8::from(l));
            assert_eq!(LL16::from(l), LL16::from_bits(val16));
            assert_eq!(LH16::from(l), LH16::from_bits(val16 << 8));
            assert_eq!(LL128::from(l), LL128::from_bits(val128));
            assert_eq!(LH128::from(l), LH128::from_bits(val128 << 120));

            let h = H8::from_bits(val);
            assert_eq!(HL16::from(h), HL16::from_bits(val16));
            assert_eq!(HH16::from(h), HH16::from_bits(val16 << 8));
            assert_eq!(HL128::from(h), HL128::from_bits(val128));
            assert_eq!(HH128::from(h), HH128::from_bits(val128 << 120));
        }
    }

    #[test]
    fn expanding_from_signed() {
        type L8 = FixedI8<frac::U0>;
        type LL16 = FixedI16<frac::U0>;
        type LH16 = FixedI16<frac::U8>;
        type LL128 = FixedI128<frac::U0>;
        type LH128 = FixedI128<frac::U120>;

        type H8 = FixedI8<frac::U8>;
        type HL16 = FixedI16<frac::U8>;
        type HH16 = FixedI16<frac::U16>;
        type HL128 = FixedI128<frac::U8>;
        type HH128 = FixedI128<frac::U128>;

        let vals: &[i8] = &[0x00, 0x7f, -0x80, -0x01];
        for &val in vals {
            let val16 = i16::from(val);
            let val128 = i128::from(val);

            let l = L8::from_bits(val);
            assert_eq!(l, L8::from(val));
            assert_eq!(val, i8::from(l));
            assert_eq!(LL16::from(l), LL16::from_bits(val16));
            assert_eq!(LH16::from(l), LH16::from_bits(val16 << 8));
            assert_eq!(LL128::from(l), LL128::from_bits(val128));
            assert_eq!(LH128::from(l), LH128::from_bits(val128 << 120));

            let h = H8::from_bits(val);
            assert_eq!(HL16::from(h), HL16::from_bits(val16));
            assert_eq!(HH16::from(h), HH16::from_bits(val16 << 8));
            assert_eq!(HL128::from(h), HL128::from_bits(val128));
            assert_eq!(HH128::from(h), HH128::from_bits(val128 << 120));
        }
    }

    #[test]
    fn expanding_from_unsigned_to_signed() {
        type L8 = FixedU8<frac::U0>;
        type LL16 = FixedI16<frac::U0>;
        type LH16 = FixedI16<frac::U7>;
        type LL128 = FixedI128<frac::U0>;
        type LH128 = FixedI128<frac::U119>;

        type H8 = FixedU8<frac::U8>;
        type HL16 = FixedI16<frac::U8>;
        type HH16 = FixedI16<frac::U15>;
        type HL128 = FixedI128<frac::U8>;
        type HH128 = FixedI128<frac::U127>;

        let vals: &[u8] = &[0x00, 0x7f, 0x80, 0xff];
        for &val in vals {
            let val16 = i16::from(val);
            let val128 = i128::from(val);

            let l = L8::from_bits(val);
            assert_eq!(l, L8::from(val));
            assert_eq!(val, u8::from(l));
            assert_eq!(LL16::from(l), LL16::from_bits(val16));
            assert_eq!(LH16::from(l), LH16::from_bits(val16 << 7));
            assert_eq!(LL128::from(l), LL128::from_bits(val128));
            assert_eq!(LH128::from(l), LH128::from_bits(val128 << 119));

            let h = H8::from_bits(val);
            assert_eq!(HL16::from(h), HL16::from_bits(val16));
            assert_eq!(HH16::from(h), HH16::from_bits(val16 << 7));
            assert_eq!(HL128::from(h), HL128::from_bits(val128));
            assert_eq!(HH128::from(h), HH128::from_bits(val128 << 119));
        }
    }
}
