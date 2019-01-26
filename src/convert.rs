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

use core::ops::{Add, Sub};
use frac::{IsGreaterOrEqual, IsLessOrEqual, True, Unsigned, U0, U1, U128, U16, U2, U32, U64, U8};
#[cfg(feature = "f16")]
use half::f16;
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

macro_rules! bool_to_fixed {
    ($DstU:ident, $DstI:ident, $DstBits:ident) => {
        // Condition: FracDst <= $DstBits - 1
        impl<FracDst> From<bool> for $DstU<FracDst>
        where
            FracDst: Unsigned
                + IsLessOrEqual<$DstBits, Output = True>
                + IsLessOrEqual<<$DstBits as Sub<U1>>::Output, Output = True>,
        {
            #[inline]
            fn from(src: bool) -> $DstU<FracDst> {
                let unshifted = $DstU::<FracDst>::from_bits(src.into()).to_bits();
                let shift = FracDst::to_u32();
                $DstU::<FracDst>::from_bits(unshifted << shift)
            }
        }

        // Condition: FracDst <= $DstBits - 2
        impl<FracDst> From<bool> for $DstI<FracDst>
        where
            FracDst: Unsigned
                + IsLessOrEqual<$DstBits, Output = True>
                + IsLessOrEqual<<$DstBits as Sub<U2>>::Output, Output = True>,
        {
            #[inline]
            fn from(src: bool) -> $DstI<FracDst> {
                let unshifted = $DstI::<FracDst>::from_bits(src.into()).to_bits();
                let shift = FracDst::to_u32();
                $DstI::<FracDst>::from_bits(unshifted << shift)
            }
        }
    };
}

bool_to_fixed! { FixedU8, FixedI8, U8 }
bool_to_fixed! { FixedU16, FixedI16, U16 }
bool_to_fixed! { FixedU32, FixedI32, U32 }
bool_to_fixed! { FixedU64, FixedI64, U64 }
bool_to_fixed! { FixedU128, FixedI128, U128 }

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

macro_rules! fixed_to_float {
    ($Fixed:ident($Len:ty):: $method:ident -> $Float:ident) => {
        impl<Frac> From<$Fixed<Frac>> for $Float
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn from(src: $Fixed<Frac>) -> $Float {
                src.$method()
            }
        }
    };
}

#[cfg(feature = "f16")]
fixed_to_float! { FixedI8(U8)::to_f16 -> f16 }
#[cfg(feature = "f16")]
fixed_to_float! { FixedU8(U8)::to_f16 -> f16 }
fixed_to_float! { FixedI8(U8)::to_f32 -> f32 }
fixed_to_float! { FixedI16(U16)::to_f32 -> f32 }
fixed_to_float! { FixedU8(U8)::to_f32 -> f32 }
fixed_to_float! { FixedU16(U16)::to_f32 -> f32 }
fixed_to_float! { FixedI8(U8)::to_f64 -> f64 }
fixed_to_float! { FixedI16(U16)::to_f64 -> f64 }
fixed_to_float! { FixedI32(U32)::to_f64 -> f64 }
fixed_to_float! { FixedU8(U8)::to_f64 -> f64 }
fixed_to_float! { FixedU16(U16)::to_f64 -> f64 }
fixed_to_float! { FixedU32(U32)::to_f64 -> f64 }

#[cfg_attr(feature = "cargo-clippy", allow(clippy::float_cmp))]
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

    #[test]
    fn from_bool() {
        assert_eq!(FixedI8::<frac::U6>::from(true), 1);
        assert_eq!(FixedI8::<frac::U6>::from(false), 0);
        assert_eq!(FixedI128::<frac::U64>::from(true), 1);
        assert_eq!(FixedU128::<frac::U127>::from(true), 1);
    }

    #[test]
    fn signed_from_f32() {
        type Fix = FixedI8<frac::U4>;
        // 1.1 -> 0001.1000
        assert_eq!(Fix::from_f32(3.0 / 2.0).unwrap(), Fix::from_bits(24));
        // 0.11 -> 0000.1100
        assert_eq!(Fix::from_f32(3.0 / 4.0).unwrap(), Fix::from_bits(12));
        // 0.011 -> 0000.0110
        assert_eq!(Fix::from_f32(3.0 / 8.0).unwrap(), Fix::from_bits(6));
        // 0.0011 -> 0000.0011
        assert_eq!(Fix::from_f32(3.0 / 16.0).unwrap(), Fix::from_bits(3));
        // 0.00011 -> 0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(3.0 / 32.0).unwrap(), Fix::from_bits(2));
        // 0.00101 -> 0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(5.0 / 32.0).unwrap(), Fix::from_bits(2));
        // 0.000011 -> 0000.0001 (nearest)
        assert_eq!(Fix::from_f32(3.0 / 64.0).unwrap(), Fix::from_bits(1));
        // 0.00001 -> 0000.0000 (tie to even)
        assert_eq!(Fix::from_f32(1.0 / 32.0).unwrap(), Fix::from_bits(0));

        // -1.1 -> -0001.1000
        assert_eq!(Fix::from_f32(-3.0 / 2.0).unwrap(), Fix::from_bits(-24));
        // -0.11 -> -0000.1100
        assert_eq!(Fix::from_f32(-3.0 / 4.0).unwrap(), Fix::from_bits(-12));
        // -0.011 -> -0000.0110
        assert_eq!(Fix::from_f32(-3.0 / 8.0).unwrap(), Fix::from_bits(-6));
        // -0.0011 -> -0000.0011
        assert_eq!(Fix::from_f32(-3.0 / 16.0).unwrap(), Fix::from_bits(-3));
        // -0.00011 -> -0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(-3.0 / 32.0).unwrap(), Fix::from_bits(-2));
        // -0.00101 -> -0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(-5.0 / 32.0).unwrap(), Fix::from_bits(-2));
        // -0.000011 -> -0000.0001 (nearest)
        assert_eq!(Fix::from_f32(-3.0 / 64.0).unwrap(), Fix::from_bits(-1));
        // -0.00001 -> 0000.0000 (tie to even)
        assert_eq!(Fix::from_f32(-1.0 / 32.0).unwrap(), Fix::from_bits(0));

        // 111.1111 -> 111.1111
        assert_eq!(Fix::from_f32(127.0 / 16.0).unwrap(), Fix::from_bits(127));
        // 111.11111 -> too large (tie to even)
        assert!(Fix::from_f32(255.0 / 32.0).is_none());

        // -111.1111 -> -111.1111
        assert_eq!(Fix::from_f32(-127.0 / 16.0).unwrap(), Fix::from_bits(-127));
        // -111.11111 -> -1000.0000 (tie to even)
        assert_eq!(Fix::from_f32(-255.0 / 32.0).unwrap(), Fix::from_bits(-128));
        // -1000.00001 -> -1000.0000 (tie to even)
        assert_eq!(Fix::from_f32(-257.0 / 32.0).unwrap(), Fix::from_bits(-128));
        // -1000.0001 -> too small
        assert!(Fix::from_f32(-129.0 / 16.0).is_none());
    }

    #[test]
    fn unsigned_from_f32() {
        type Fix = FixedU8<frac::U4>;
        // 1.1 -> 0001.1000
        assert_eq!(Fix::from_f32(3.0 / 2.0).unwrap(), Fix::from_bits(24));
        // 0.11 -> 0000.1100
        assert_eq!(Fix::from_f32(3.0 / 4.0).unwrap(), Fix::from_bits(12));
        // 0.011 -> 0000.0110
        assert_eq!(Fix::from_f32(3.0 / 8.0).unwrap(), Fix::from_bits(6));
        // 0.0011 -> 0000.0011
        assert_eq!(Fix::from_f32(3.0 / 16.0).unwrap(), Fix::from_bits(3));
        // 0.00011 -> 0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(3.0 / 32.0).unwrap(), Fix::from_bits(2));
        // 0.00101 -> 0000.0010 (tie to even)
        assert_eq!(Fix::from_f32(5.0 / 32.0).unwrap(), Fix::from_bits(2));
        // 0.000011 -> 0000.0001 (nearest)
        assert_eq!(Fix::from_f32(3.0 / 64.0).unwrap(), Fix::from_bits(1));
        // 0.00001 -> 0000.0000 (tie to even)
        assert_eq!(Fix::from_f32(1.0 / 32.0).unwrap(), Fix::from_bits(0));
        // -0.00001 -> 0000.0000 (tie to even)
        assert_eq!(Fix::from_f32(-1.0 / 32.0).unwrap(), Fix::from_bits(0));
        // -0.0001 -> too small
        assert!(Fix::from_f32(-1.0 / 16.0).is_none());

        // 1111.1111 -> 1111.1111
        assert_eq!(Fix::from_f32(255.0 / 16.0).unwrap(), Fix::from_bits(255));
        // 1111.11111 -> too large (tie to even)
        assert!(Fix::from_f32(511.0 / 32.0).is_none());
    }

    #[cfg(feature = "f16")]
    #[test]
    fn to_f16() {
        use half::f16;
        for u in 0x00..=0xff {
            let fu = FixedU8::<frac::U7>::from_bits(u);
            assert_eq!(fu.to_f16(), f16::from_f32(u as f32 / 128.0));
            let i = u as i8;
            let fi = FixedI8::<frac::U7>::from_bits(i);
            assert_eq!(fi.to_f16(), f16::from_f32(i as f32 / 128.0));

            for hi in &[
                0u32,
                0x0000_0100,
                0x7fff_ff00,
                0x8000_0000,
                0x8100_0000,
                0xffff_fe00,
                0xffff_ff00,
            ] {
                let uu = *hi | u as u32;
                let fuu = FixedU32::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f16(), f16::from_f32(uu as f32 / 128.0));
                let ii = uu as i32;
                let fii = FixedI32::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f16(), f16::from_f32(ii as f32 / 128.0));
            }

            for hi in &[
                0u128,
                0x0000_0000_0000_0000_0000_0000_0000_0100,
                0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
                0x8000_0000_0000_0000_0000_0000_0000_0000,
                0x8100_0000_0000_0000_0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u as u128;
                let fuu = FixedU128::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f16(), f16::from_f64(uu as f64 / 128.0));
                let ii = uu as i128;
                let fii = FixedI128::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f16(), f16::from_f64(ii as f64 / 128.0));
            }
        }
    }

    #[test]
    fn to_f32() {
        for u in 0x00..=0xff {
            let fu = FixedU8::<frac::U7>::from_bits(u);
            assert_eq!(fu.to_f32(), f32::from(u) / 128.0);
            let i = u as i8;
            let fi = FixedI8::<frac::U7>::from_bits(i);
            assert_eq!(fi.to_f32(), f32::from(i) / 128.0);

            for hi in &[
                0u32,
                0x0000_0100,
                0x7fff_ff00,
                0x8000_0000,
                0x8100_0000,
                0xffff_fe00,
                0xffff_ff00,
            ] {
                let uu = *hi | u32::from(u);
                let fuu = FixedU32::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f32(), uu as f32 / 128.0);
                let ii = uu as i32;
                let fii = FixedI32::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f32(), ii as f32 / 128.0);
            }

            for hi in &[
                0u128,
                0x0000_0000_0000_0000_0000_0000_0000_0100,
                0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
                0x8000_0000_0000_0000_0000_0000_0000_0000,
                0x8100_0000_0000_0000_0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u128::from(u);
                let fuu = FixedU128::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f32(), (uu as f64 / 128.0) as f32);
                let ii = uu as i128;
                let fii = FixedI128::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f32(), (ii as f64 / 128.0) as f32);
            }
        }
    }

    #[test]
    fn to_infinite_f32() {
        // too_large is 1.ffff_ffff_ffff... << 127,
        // which will be rounded to 1.0 << 128.
        let too_large = FixedU128::<frac::U0>::max_value();
        assert_eq!(too_large.count_ones(), 128);
        assert!(too_large.to_f32().is_infinite());

        // still_too_large is 1.ffff_ff << 127,
        // which is exactly midway between 1.0 << 128 (even)
        // and the largest normal f32 that is 1.ffff_fe << 127 (odd).
        // The tie will be rounded to even, which is to 1.0 << 128.
        let still_too_large = too_large << 103u32;
        assert_eq!(still_too_large.count_ones(), 25);
        assert!(still_too_large.to_f32().is_infinite());

        // not_too_large is 1.ffff_feff_ffff... << 127,
        // which will be rounded to 1.ffff_fe << 127.
        let not_too_large = still_too_large - FixedU128::from_bits(1);
        assert_eq!(not_too_large.count_ones(), 127);
        assert!(!not_too_large.to_f32().is_infinite());

        // min_128 is -1.0 << 127.
        let min_i128 = FixedI128::<frac::U0>::min_value();
        assert_eq!(min_i128.count_ones(), 1);
        assert_eq!(min_i128.to_f32(), -(127f32.exp2()));
    }

    #[test]
    fn to_f64() {
        for u in 0x00..=0xff {
            let fu = FixedU8::<frac::U7>::from_bits(u);
            assert_eq!(fu.to_f32(), f32::from(u) / 128.0);
            let i = u as i8;
            let fi = FixedI8::<frac::U7>::from_bits(i);
            assert_eq!(fi.to_f32(), f32::from(i) / 128.0);

            for hi in &[
                0u64,
                0x0000_0000_0000_0100,
                0x7fff_ffff_ffff_ff00,
                0x8000_0000_0000_0000,
                0x8100_0000_0000_0000,
                0xffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u64::from(u);
                let fuu = FixedU64::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f64(), uu as f64 / 128.0);
                let ii = uu as i64;
                let fii = FixedI64::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f64(), ii as f64 / 128.0);
            }

            for hi in &[
                0u128,
                0x0000_0000_0000_0000_0000_0000_0000_0100,
                0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
                0x8000_0000_0000_0000_0000_0000_0000_0000,
                0x8100_0000_0000_0000_0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u128::from(u);
                let fuu = FixedU128::<frac::U7>::from_bits(uu);
                assert_eq!(fuu.to_f64(), uu as f64 / 128.0);
                let ii = uu as i128;
                let fii = FixedI128::<frac::U7>::from_bits(ii);
                assert_eq!(fii.to_f64(), ii as f64 / 128.0);
            }
        }
    }
}
