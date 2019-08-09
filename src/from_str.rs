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
    frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8},
    sealed::SealedInt,
    wide_div::WideDivRem,
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    cmp::{self, Ordering},
    fmt::{Display, Formatter, Result as FmtResult},
    str::FromStr,
};

// 5^3 × 2 < 2^8 => (10^3 - 1) × 2^(8-3+1) < 2^16
// Returns None for large fractions that are rounded to 1.0
pub fn dec3_to_bin8(a: u16, dump_bits: u32) -> Option<u8> {
    debug_assert!(a < 10u16.pow(3));
    debug_assert!(dump_bits <= 8);
    let divisor = 5u16.pow(3) * 2;
    let shift = a << (8 - 3 + 1) >> dump_bits;
    let round = shift + (divisor / 2);
    if round >> (8 - dump_bits) >= divisor {
        None
    } else {
        Some((round / divisor) as u8)
    }
}
// 5^6 × 2 < 2^16 => (10^6 - 1) × 2^(16-6+1) < 2^32
// Returns None for large fractions that are rounded to 1.0
pub fn dec6_to_bin16(a: u32, dump_bits: u32) -> Option<u16> {
    debug_assert!(a < 10u32.pow(6));
    debug_assert!(dump_bits <= 16);
    let divisor = 5u32.pow(6) * 2;
    let shift = a << (16 - 6 + 1) >> dump_bits;
    let round = shift + (divisor / 2);
    if round >> (16 - dump_bits) >= divisor {
        None
    } else {
        Some((round / divisor) as u16)
    }
}
// 5^13 × 2 < 2^32 => (10^13 - 1) × 2^(32-13+1) < 2^64
// Returns None for large fractions that are rounded to 1.0
pub fn dec13_to_bin32(a: u64, dump_bits: u32) -> Option<u32> {
    debug_assert!(a < 10u64.pow(13));
    debug_assert!(dump_bits <= 32);
    let divisor = 5u64.pow(13) * 2;
    let shift = a << (32 - 13 + 1) >> dump_bits;
    let round = shift + (divisor / 2);
    if round >> (32 - dump_bits) >= divisor {
        None
    } else {
        Some((round / divisor) as u32)
    }
}
// 5^27 × 2 < 2^64 => (10^27 - 1) × 2^(64-27+1) < 2^128
// Returns None for large fractions that are rounded to 1.0
pub fn dec27_to_bin64(a: u128, dump_bits: u32) -> Option<u64> {
    debug_assert!(a < 10u128.pow(27));
    debug_assert!(dump_bits <= 64);
    let divisor = 5u128.pow(27) * 2;
    let shift = a << (64 - 27 + 1) >> dump_bits;;
    let round = shift + (divisor / 2);
    if round >> (64 - dump_bits) >= divisor {
        None
    } else {
        Some((round / divisor) as u64)
    }
}
// 5^54 × 2 < 2^128 => (10^54 - 1) × 2^(128-54+1) < 2^256
// Returns None for large fractions that are rounded to 1.0
pub fn dec27_27_to_bin128(hi: u128, lo: u128, dump_bits: u32) -> Option<u128> {
    debug_assert!(hi < 10u128.pow(27));
    debug_assert!(lo < 10u128.pow(27));
    debug_assert!(dump_bits <= 128);
    let divisor = 5u128.pow(54) * 2;
    // we actually need to combine (10^27*hi + lo) << (128 - 54 + 1)
    let (hi_hi, hi_lo) = mul_hi_lo(hi, 10u128.pow(27));
    let (comb_lo, overflow) = hi_lo.overflowing_add(lo);
    let comb_hi = if overflow { hi_hi + 1 } else { hi_hi };
    let shift_lo;
    let shift_hi;
    match (128 - 54 + 1).cmp(&dump_bits) {
        Ordering::Less => {
            let shr = dump_bits - (128 - 54 + 1);
            shift_lo = (comb_lo >> shr) | (comb_hi << (128 - shr));
            shift_hi = comb_hi >> shr;
        }
        Ordering::Greater => {
            let shl = (128 - 54 + 1) - dump_bits;
            shift_lo = comb_lo << shl;
            shift_hi = (comb_hi << shl) | (comb_lo >> (128 - shl));
        }
        Ordering::Equal => {
            shift_lo = comb_lo;
            shift_hi = comb_hi;
        }
    };
    let (round_lo, overflow) = shift_lo.overflowing_add(divisor / 2);
    let round_hi = if overflow { shift_hi + 1 } else { shift_hi };
    let whole_compare = if dump_bits == 0 {
        round_hi
    } else if dump_bits == 128 {
        round_lo
    } else {
        (round_lo >> (128 - dump_bits)) | (round_hi << dump_bits)
    };
    if whole_compare >= divisor {
        None
    } else {
        Some(div_wide(round_hi, round_lo, divisor))
    }
}
fn mul_hi_lo(lhs: u128, rhs: u128) -> (u128, u128) {
    const LO: u128 = !(!0 << 64);
    let (lhs_hi, lhs_lo) = (lhs >> 64, lhs & LO);
    let (rhs_hi, rhs_lo) = (rhs >> 64, rhs & LO);
    let lhs_lo_rhs_lo = lhs_lo.wrapping_mul(rhs_lo);
    let lhs_hi_rhs_lo = lhs_hi.wrapping_mul(rhs_lo);
    let lhs_lo_rhs_hi = lhs_lo.wrapping_mul(rhs_hi);
    let lhs_hi_rhs_hi = lhs_hi.wrapping_mul(rhs_hi);

    let col01 = lhs_lo_rhs_lo;
    let (col01_hi, col01_lo) = (col01 >> 64, col01 & LO);
    let partial_col12 = lhs_hi_rhs_lo + col01_hi;
    let (col12, carry_col3) = partial_col12.overflowing_add(lhs_lo_rhs_hi);
    let (col12_hi, col12_lo) = (col12 >> 64, col12 & LO);
    let ans01 = (col12_lo << 64) + col01_lo;
    let ans23 = lhs_hi_rhs_hi + col12_hi + if carry_col3 { 1u128 << 64 } else { 0 };
    (ans23, ans01)
}
fn div_wide(dividend_hi: u128, dividend_lo: u128, divisor: u128) -> u128 {
    divisor.lo_div_from(dividend_hi, dividend_lo)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Parse<'a> {
    neg: bool,
    int: &'a str,
    frac: &'a str,
}
#[derive(Debug)]
pub struct ParseFixedError {
    kind: ParseErrorKind,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParseErrorKind {
    InvalidDigit,
    NoDigits,
    TooManyPoints,
    Overflow,
}

macro_rules! err {
    ($cond:expr, $kind:ident) => {
        if $cond {
            err!($kind);
        }
    };
    ($kind:ident) => {
        return Err(ParseFixedError {
            kind: ParseErrorKind::$kind,
        });
    };
}

impl Display for ParseFixedError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use self::ParseErrorKind::*;
        let message = match self.kind {
            InvalidDigit => "invalid digit found in string",
            NoDigits => "string has no digits",
            TooManyPoints => "more than one decimal point found in string",
            Overflow => "overflow",
        };
        Display::fmt(message, f)
    }
}

fn parse(s: &str, can_be_neg: bool) -> Result<Parse<'_>, ParseFixedError> {
    let mut int = (0, 0);
    let mut frac = (0, 0);
    let mut has_sign = false;
    let mut is_negative = false;
    let mut has_digits = false;
    let mut has_point = false;
    for (index, c) in s.char_indices() {
        if c == '.' {
            err!(has_point, TooManyPoints);
            has_digits = false;
            has_point = true;
            frac.0 = index + c.len_utf8();
            continue;
        }
        match c {
            '+' => {
                err!(has_point || has_sign || has_digits, InvalidDigit);
                has_sign = true;
                continue;
            }
            '-' => {
                err!(
                    has_point || has_sign || has_digits || !can_be_neg,
                    InvalidDigit
                );
                has_sign = true;
                is_negative = true;
                continue;
            }
            '0'..='9' => {
                if !has_point && !has_digits {
                    int.0 = index;
                }
                has_digits = true;
                if !has_point {
                    int.1 = index + c.len_utf8();
                } else {
                    frac.1 = index + c.len_utf8();
                }
            }
            _ => {
                err!(InvalidDigit);
            }
        }
    }
    if frac.1 < frac.0 {
        frac.1 = frac.0;
    }
    err!(int.0 == int.1 && frac.0 == frac.1, NoDigits);
    Ok(Parse {
        neg: is_negative,
        int: &s[int.0..int.1],
        frac: &s[frac.0..frac.1],
    })
}

macro_rules! impl_from_str {
    ($Fixed:ident, $NBits:ident, $method:ident) => {
        impl<Frac> FromStr for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            type Err = ParseFixedError;
            #[inline]
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                $method(s, Self::int_nbits(), Self::frac_nbits()).map(Self::from_bits)
            }
        }
    };
}

macro_rules! impl_from_str_signed {
    (
        ($Fixed:ident, $NBits:ident, $Bits:ident, $DoubleBits:ident, $one:expr);
        fn $all:ident;
        fn $int:ident;
        $frac:ident;
    ) => {
        impl_from_str! { $Fixed, $NBits, $all }

        fn $all(s: &str, int_nbits: u32, frac_nbits: u32) -> Result<$Bits, ParseFixedError> {
            let Parse { neg, int, frac } = parse(s, true)?;
            let (frac, whole_frac) = match $frac(frac, frac_nbits) {
                Some(frac) => (frac, false),
                None => (0, true),
            };
            let frac = if frac_nbits == <$Bits>::NBITS {
                // special case: no int bits
                if neg {
                    if frac > <$Bits as SealedInt>::Unsigned::MSB {
                        err!(Overflow)
                    }
                    frac.wrapping_neg() as $Bits
                } else {
                    if frac >= <$Bits as SealedInt>::Unsigned::MSB {
                        err!(Overflow)
                    }
                    frac as $Bits
                }
            } else {
                frac as $Bits
            };
            let int = $int(neg, int, int_nbits, whole_frac)?;
            Ok(int | frac)
        }

        fn $int(
            neg: bool,
            int: &str,
            nbits: u32,
            whole_frac: bool,
        ) -> Result<$Bits, ParseFixedError> {
            let mut int = int;
            while int.starts_with('0') {
                int = &int[1..];
            }
            if nbits == 0 {
                err!(whole_frac || !int.is_empty(), Overflow);
                return Ok(0);
            }
            let max_abs_int = if neg {
                $one << (nbits - 1)
            } else {
                ($one << (nbits - 1)) - 1
            };
            let mut acc = match int.parse::<$DoubleBits>() {
                Ok(i) => {
                    err!(i > max_abs_int, Overflow);
                    i
                }
                Err(_) => err!(Overflow),
            };
            if whole_frac {
                acc += 1;
                err!(acc > max_abs_int, Overflow);
            }
            let signed = if neg {
                acc.wrapping_neg() as $Bits
            } else {
                acc as $Bits
            };
            Ok(signed << (<$Bits>::NBITS - nbits))
        }
    };
}

macro_rules! impl_from_str_unsigned {
    (
        ($Fixed:ident, $NBits:ident, $Bits:ident, $DoubleBits:ident, $one:expr);
        fn $all:ident;
        fn $int:ident;
        fn $frac:ident;
        $decode_frac:ident, $dec_frac_digits:expr;
    ) => {
        impl_from_str! { $Fixed, $NBits, $all }

        fn $all(s: &str, int_nbits: u32, frac_nbits: u32) -> Result<$Bits, ParseFixedError> {
            let Parse { int, frac, .. } = parse(s, false)?;
            let (frac, whole_frac) = match $frac(frac, frac_nbits) {
                Some(frac) => (frac, false),
                None => (0, true),
            };
            let int = $int(int, int_nbits, whole_frac)?;
            Ok(int | frac)
        }

        fn $int(int: &str, nbits: u32, whole_frac: bool) -> Result<$Bits, ParseFixedError> {
            let mut int = int;
            while int.starts_with('0') {
                int = &int[1..];
            }
            if nbits == 0 {
                err!(whole_frac || !int.is_empty(), Overflow);
                return Ok(0);
            }
            let max_abs_int = ($one << nbits) - 1;
            let mut acc = match int.parse::<$DoubleBits>() {
                Ok(i) => {
                    err!(i > max_abs_int, Overflow);
                    i
                }
                Err(_) => err!(Overflow),
            };
            if whole_frac {
                acc += 1;
                err!(acc > max_abs_int, Overflow);
            }
            Ok((acc as $Bits) << (<$Bits as SealedInt>::NBITS - nbits))
        }

        fn $frac(frac: &str, nbits: u32) -> Option<$Bits> {
            if frac.is_empty() {
                return Some(0);
            }
            let end = cmp::min(frac.len(), $dec_frac_digits);
            let rem = $dec_frac_digits - end;
            let i = frac[..end].parse::<$DoubleBits>().unwrap() * ($one * 10).pow(rem as u32);
            $decode_frac(i, <$Bits as SealedInt>::NBITS - nbits)
        }
    };
}

impl_from_str_signed! {
    (FixedI8, U8, i8, u16, 1u16);
    fn from_str_i8;
    fn get_int_i8;
    get_frac8;
}
impl_from_str_unsigned! {
    (FixedU8, U8, u8, u16, 1u16);
    fn from_str_u8;
    fn get_int_u8;
    fn get_frac8;
    dec3_to_bin8, 3;
}

impl_from_str_signed! {
    (FixedI16, U16, i16, u32, 1u32);
    fn from_str_i16;
    fn get_int_i16;
    get_frac16;
}
impl_from_str_unsigned! {
    (FixedU16, U16, u16, u32, 1u32);
    fn from_str_u16;
    fn get_int_u16;
    fn get_frac16;
    dec6_to_bin16, 6;
}

impl_from_str_signed! {
    (FixedI32, U32, i32, u64, 1u64);
    fn from_str_i32;
    fn get_int_i32;
    get_frac32;
}
impl_from_str_unsigned! {
    (FixedU32, U32, u32, u64, 1u64);
    fn from_str_u32;
    fn get_int_u32;
    fn get_frac32;
    dec13_to_bin32, 13;
}

impl_from_str_signed! {
    (FixedI64, U64, i64, u128, 1u128);
    fn from_str_i64;
    fn get_int_i64;
    get_frac64;
}
impl_from_str_unsigned! {
    (FixedU64, U64, u64, u128, 1u128);
    fn from_str_u64;
    fn get_int_u64;
    fn get_frac64;
    dec27_to_bin64, 27;
}

impl_from_str! { FixedI128, U128, from_str_i128 }

fn from_str_i128(s: &str, int_nbits: u32, frac_nbits: u32) -> Result<i128, ParseFixedError> {
    let Parse { neg, int, frac } = parse(s, true)?;
    let (frac, whole_frac) = match get_frac128(frac, frac_nbits) {
        Some(frac) => (frac, false),
        None => (0, true),
    };
    let frac = if frac_nbits == <i128>::NBITS {
        // special case: no int bits
        if neg {
            if frac > <i128 as SealedInt>::Unsigned::MSB {
                err!(Overflow)
            }
            frac.wrapping_neg() as i128
        } else {
            if frac >= <i128 as SealedInt>::Unsigned::MSB {
                err!(Overflow)
            }
            frac as i128
        }
    } else {
        frac as i128
    };
    let int = get_int_i128(neg, int, int_nbits, whole_frac)?;
    Ok(int | frac)
}

fn get_int_i128(
    neg: bool,
    int: &str,
    nbits: u32,
    whole_frac: bool,
) -> Result<i128, ParseFixedError> {
    let mut int = int;
    while int.starts_with('0') {
        int = &int[1..];
    }
    if nbits == 0 {
        err!(whole_frac || !int.is_empty(), Overflow);
        return Ok(0);
    }
    let max_abs_int = if neg {
        1u128 << (nbits - 1)
    } else {
        (1u128 << (nbits - 1)) - 1
    };
    let mut acc = match int.parse::<u128>() {
        Ok(i) => {
            err!(i > max_abs_int, Overflow);
            i
        }
        Err(_) => err!(Overflow),
    };
    if whole_frac {
        acc += 1;
        err!(acc > max_abs_int, Overflow);
    }
    let signed = if neg {
        acc.wrapping_neg() as i128
    } else {
        acc as i128
    };
    Ok(signed << (<i128>::NBITS - nbits))
}

impl_from_str! { FixedU128, U128, from_str_u128 }

fn from_str_u128(s: &str, int_nbits: u32, frac_nbits: u32) -> Result<u128, ParseFixedError> {
    let Parse { int, frac, .. } = parse(s, false)?;
    let (frac, whole_frac) = match get_frac128(frac, frac_nbits) {
        Some(frac) => (frac, false),
        None => (0, true),
    };
    let int = get_int_u128(int, int_nbits, whole_frac)?;
    Ok(int | frac)
}

fn get_int_u128(int: &str, nbits: u32, whole_frac: bool) -> Result<u128, ParseFixedError> {
    let mut int = int;
    while int.starts_with('0') {
        int = &int[1..];
    }
    if nbits == 0 {
        err!(whole_frac || !int.is_empty(), Overflow);
        return Ok(0);
    }
    let mut acc = match int.parse::<u128>() {
        Ok(i) => i,
        Err(_) => err!(Overflow),
    };
    if whole_frac {
        acc = match acc.overflowing_add(1) {
            (acc, false) => acc,
            (_, true) => err!(Overflow),
        };
    }
    Ok(acc << (<u128 as SealedInt>::NBITS - nbits))
}

fn get_frac128(frac: &str, nbits: u32) -> Option<u128> {
    if frac.is_empty() {
        return Some(0);
    }
    let (hi, lo) = if frac.is_empty() {
        (0, 0)
    } else if frac.len() <= 27 {
        let rem = 27 - frac.len();
        let hi = frac.parse::<u128>().unwrap() * 10u128.pow(rem as u32);
        (hi, 0)
    } else {
        let hi = frac[..27].parse::<u128>().unwrap();
        let lo_end = cmp::min(frac.len(), 54);
        let rem = 54 - lo_end;
        let lo = frac[27..lo_end].parse::<u128>().unwrap() * 10u128.pow(rem as u32);
        (hi, lo)
    };

    dec27_27_to_bin128(hi, lo, <u128 as SealedInt>::NBITS - nbits)
}

#[cfg(test)]
mod tests {
    use crate::{from_str::*, traits::Fixed};
    use core::fmt::Debug;

    #[test]
    fn check_dec3() {
        let two_pow = 8f64.exp2();
        let limit = 1000;
        for i in 0..limit {
            let ans = dec3_to_bin8(i, 0);
            let approx = two_pow * f64::from(i) / f64::from(limit);
            let error = (ans.map(f64::from).unwrap_or(two_pow) - approx).abs();
            assert!(
                error <= 0.5,
                "i {} ans {:?}  approx {} error {}",
                i,
                ans,
                approx,
                error
            );
        }
    }

    #[test]
    fn check_dec6() {
        let two_pow = 16f64.exp2();
        let limit = 1_000_000;
        for i in 0..limit {
            let ans = dec6_to_bin16(i, 0);
            let approx = two_pow * f64::from(i) / f64::from(limit);
            let error = (ans.map(f64::from).unwrap_or(two_pow) - approx).abs();
            assert!(
                error <= 0.5,
                "i {} ans {:?}  approx {} error {}",
                i,
                ans,
                approx,
                error
            );
        }
    }

    #[test]
    fn check_dec13() {
        let two_pow = 32f64.exp2();
        let limit = 10_000_000_000_000;
        for iter in 0..1_000_000 {
            for &i in &[
                iter,
                limit / 4 - 1 - iter,
                limit / 4 + iter,
                limit / 3 - 1 - iter,
                limit / 3 + iter,
                limit / 2 - 1 - iter,
                limit / 2 + iter,
                limit - iter - 1,
            ] {
                let ans = dec13_to_bin32(i, 0);
                let approx = two_pow * i as f64 / limit as f64;
                let error = (ans.map(f64::from).unwrap_or(two_pow) - approx).abs();
                assert!(
                    error <= 0.5,
                    "i {} ans {:?}  approx {} error {}",
                    i,
                    ans,
                    approx,
                    error
                );
            }
        }
    }

    #[test]
    fn check_dec27() {
        let two_pow = 64f64.exp2();
        let limit = 1_000_000_000_000_000_000_000_000_000;
        for iter in 0..200_000 {
            for &i in &[
                iter,
                limit / 4 - 1 - iter,
                limit / 4 + iter,
                limit / 3 - 1 - iter,
                limit / 3 + iter,
                limit / 2 - 1 - iter,
                limit / 2 + iter,
                limit - iter - 1,
            ] {
                let ans = dec27_to_bin64(i, 0);
                let approx = two_pow * i as f64 / limit as f64;
                let error = (ans.map(|x| x as f64).unwrap_or(two_pow) - approx).abs();
                assert!(
                    error <= 0.5,
                    "i {} ans {:?}  approx {} error {}",
                    i,
                    ans,
                    approx,
                    error
                );
            }
        }
    }

    #[test]
    fn check_dec27_27() {
        let nines = 10u128.pow(27) - 1;
        let zeros = 0;
        let too_big = dec27_27_to_bin128(nines, nines, 0);
        assert_eq!(too_big, None);
        let big = dec27_27_to_bin128(nines, zeros, 0);
        assert_eq!(
            big,
            Some(340_282_366_920_938_463_463_374_607_091_485_844_535)
        );
        let small = dec27_27_to_bin128(zeros, nines, 0);
        assert_eq!(small, Some(340_282_366_921));
        let zero = dec27_27_to_bin128(zeros, zeros, 0);
        assert_eq!(zero, Some(0));
        let x = dec27_27_to_bin128(
            123_456_789_012_345_678_901_234_567,
            987_654_321_098_765_432_109_876_543,
            0,
        );
        assert_eq!(x, Some(42_010_168_377_579_896_403_540_037_811_203_677_112));
    }

    #[test]
    fn check_parse_bounds() {
        let Parse { neg, int, frac } = parse("-12.34", true).unwrap();
        assert_eq!((neg, int, frac), (true, "12", "34"));
        let Parse { neg, int, frac } = parse("12.", true).unwrap();
        assert_eq!((neg, int, frac), (false, "12", ""));
        let Parse { neg, int, frac } = parse("+.34", false).unwrap();
        assert_eq!((neg, int, frac), (false, "", "34"));
        let Parse { neg, int, frac } = parse("0", false).unwrap();
        assert_eq!((neg, int, frac), (false, "0", ""));

        let ParseFixedError { kind } = parse("0 ", true).unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);
        let ParseFixedError { kind } = parse("+.", true).unwrap_err();
        assert_eq!(kind, ParseErrorKind::NoDigits);
        let ParseFixedError { kind } = parse(".1.", true).unwrap_err();
        assert_eq!(kind, ParseErrorKind::TooManyPoints);
        let ParseFixedError { kind } = parse("1+2", true).unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);
        let ParseFixedError { kind } = parse("1-2", true).unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);
        let ParseFixedError { kind } = parse("-12", false).unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);
    }

    fn assert_ok<F>(s: &str, bits: F::Bits)
    where
        F: Fixed + FromStr<Err = ParseFixedError>,
        F::Bits: Eq + Debug,
    {
        match s.parse::<F>() {
            Ok(f) => assert_eq!(f.to_bits(), bits),
            Err(ParseFixedError { .. }) => panic!("could not parse {}", s),
        }
    }
    fn assert_err<F>(s: &str, kind: ParseErrorKind)
    where
        F: Fixed + FromStr<Err = ParseFixedError>,
    {
        match s.parse::<F>() {
            Ok(_) => panic!("incorrectly parsed {}", s),
            Err(ParseFixedError { kind: err }) => assert_eq!(err, kind),
        }
    }

    #[test]
    fn check_i8_u8_from_str() {
        use crate::types::*;

        assert_ok::<I0F8>("0.498", 0x7F);
        assert_err::<I0F8>("0.499", ParseErrorKind::Overflow);
        assert_err::<I0F8>("1", ParseErrorKind::Overflow);

        assert_ok::<I0F8>("-0.501", -0x80);
        assert_err::<I0F8>("-0.502", ParseErrorKind::Overflow);
        assert_err::<I0F8>("-1", ParseErrorKind::Overflow);

        assert_ok::<I8F0>("000127.499", 0x7F);
        assert_err::<I8F0>("127.5", ParseErrorKind::Overflow);

        assert_ok::<I8F0>("-128.499", -0x80);
        assert_err::<I8F0>("-128.5", ParseErrorKind::Overflow);

        assert_ok::<U0F8>("0.498", 0x7F);
        assert_ok::<U0F8>("0.499", 0x80);
        assert_ok::<U0F8>("0.998", 0xFF);
        assert_err::<U0F8>("0.999", ParseErrorKind::Overflow);
        assert_err::<U0F8>("1", ParseErrorKind::Overflow);

        assert_err::<U0F8>("-0", ParseErrorKind::InvalidDigit);

        assert_ok::<U8F0>("000127.499", 0x7F);
        assert_ok::<U8F0>("000127.5", 0x80);
        assert_ok::<U8F0>("255.499", 0xFF);
        assert_err::<U8F0>("255.5", ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i16_u16_from_str() {
        use crate::types::*;

        assert_ok::<I0F16>("0.499992", 0x7FFF);
        assert_err::<I0F16>("0.499993", ParseErrorKind::Overflow);
        assert_err::<I0F16>("1", ParseErrorKind::Overflow);

        assert_ok::<I0F16>("-0.500007", -0x8000);
        assert_err::<I0F16>("-0.500008", ParseErrorKind::Overflow);
        assert_err::<I0F16>("-1", ParseErrorKind::Overflow);

        assert_ok::<I16F0>("00032767.499999", 0x7FFF);
        assert_err::<I16F0>("32767.5", ParseErrorKind::Overflow);

        assert_ok::<I16F0>("-32768.499999", -0x8000);
        assert_err::<I16F0>("-32768.5", ParseErrorKind::Overflow);

        assert_ok::<U0F16>("0.499992", 0x7FFF);
        assert_ok::<U0F16>("0.499993", 0x8000);
        assert_ok::<U0F16>("0.999992", 0xFFFF);
        assert_err::<U0F16>("0.999993", ParseErrorKind::Overflow);
        assert_err::<U0F16>("1", ParseErrorKind::Overflow);

        assert_err::<U0F16>("-0", ParseErrorKind::InvalidDigit);

        assert_ok::<U16F0>("00032767.499999", 0x7FFF);
        assert_ok::<U16F0>("00032767.5", 0x8000);
        assert_ok::<U16F0>("65535.499999", 0xFFFF);
        assert_err::<U16F0>("65535.5", ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i32_u32_from_str() {
        use crate::types::*;

        assert_ok::<I0F32>("0.4999999998", 0x7FFF_FFFF);
        assert_err::<I0F32>("0.4999999999", ParseErrorKind::Overflow);
        assert_err::<I0F32>("1", ParseErrorKind::Overflow);

        assert_ok::<I0F32>("-0.5000000001", -0x8000_0000);
        assert_err::<I0F32>("-0.5000000002", ParseErrorKind::Overflow);
        assert_err::<I0F32>("-1", ParseErrorKind::Overflow);

        assert_ok::<I32F0>("0002147483647.4999999999", 0x7FFF_FFFF);
        assert_err::<I32F0>("2147483647.5", ParseErrorKind::Overflow);

        assert_ok::<I32F0>("-2147483648.499999", -0x8000_0000);
        assert_err::<I32F0>("-2147483648.5", ParseErrorKind::Overflow);

        assert_ok::<U0F32>("0.4999999998", 0x7FFF_FFFF);
        assert_ok::<U0F32>("0.4999999999", 0x8000_0000);
        assert_ok::<U0F32>("0.9999999998", 0xFFFF_FFFF);
        assert_err::<U0F32>("0.9999999999", ParseErrorKind::Overflow);
        assert_err::<U0F32>("1", ParseErrorKind::Overflow);

        assert_err::<U0F32>("-0", ParseErrorKind::InvalidDigit);

        assert_ok::<U32F0>("0002147483647.4999999999", 0x7FFF_FFFF);
        assert_ok::<U32F0>("0002147483647.5", 0x8000_0000);
        assert_ok::<U32F0>("4294967295.4999999999", 0xFFFF_FFFF);
        assert_err::<U32F0>("4294967295.5", ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i64_u64_from_str() {
        use crate::types::*;

        assert_ok::<I0F64>("0.49999999999999999997", 0x7FFF_FFFF_FFFF_FFFF);
        assert_err::<I0F64>("0.49999999999999999998", ParseErrorKind::Overflow);
        assert_err::<I0F64>("1", ParseErrorKind::Overflow);

        assert_ok::<I0F64>("-0.50000000000000000002", -0x8000_0000_0000_0000);
        assert_err::<I0F64>("-0.50000000000000000003", ParseErrorKind::Overflow);
        assert_err::<I0F64>("-1", ParseErrorKind::Overflow);

        assert_ok::<I64F0>(
            "0009223372036854775807.49999999999999999999",
            0x7FFF_FFFF_FFFF_FFFF,
        );
        assert_err::<I64F0>("9223372036854775807.5", ParseErrorKind::Overflow);

        assert_ok::<I64F0>(
            "-9223372036854775808.49999999999999999999",
            -0x8000_0000_0000_0000,
        );
        assert_err::<I64F0>("-9223372036854775808.5", ParseErrorKind::Overflow);

        assert_ok::<U0F64>("0.49999999999999999997", 0x7FFF_FFFF_FFFF_FFFF);
        assert_ok::<U0F64>("0.49999999999999999998", 0x8000_0000_0000_0000);
        assert_ok::<U0F64>("0.99999999999999999997", 0xFFFF_FFFF_FFFF_FFFF);
        assert_err::<U0F64>("0.99999999999999999998", ParseErrorKind::Overflow);
        assert_err::<U0F64>("1", ParseErrorKind::Overflow);

        assert_err::<U0F64>("-0", ParseErrorKind::InvalidDigit);

        assert_ok::<U64F0>(
            "0009223372036854775807.49999999999999999999",
            0x7FFF_FFFF_FFFF_FFFF,
        );
        assert_ok::<U64F0>("0009223372036854775807.5", 0x8000_0000_0000_0000);
        assert_ok::<U64F0>(
            "18446744073709551615.49999999999999999999",
            0xFFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<U64F0>("18446744073709551615.5", ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i128_u128_from_str() {
        use crate::types::*;

        assert_ok::<I0F128>(
            "0.499999999999999999999999999999999999998",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<I0F128>(
            "0.499999999999999999999999999999999999999",
            ParseErrorKind::Overflow,
        );
        assert_err::<I0F128>("1", ParseErrorKind::Overflow);

        assert_ok::<I0F128>(
            "-0.500000000000000000000000000000000000001",
            -0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_err::<I0F128>(
            "-0.500000000000000000000000000000000000002",
            ParseErrorKind::Overflow,
        );
        assert_err::<I0F128>("-1", ParseErrorKind::Overflow);

        assert_ok::<I128F0>(
            "000170141183460469231731687303715884105727.4999999999999999999999999999999999999999",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<I128F0>(
            "170141183460469231731687303715884105727.5",
            ParseErrorKind::Overflow,
        );

        assert_ok::<I128F0>(
            "-170141183460469231731687303715884105728.4999999999999999999999999999999999999999",
            -0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_err::<I128F0>(
            "-170141183460469231731687303715884105728.5",
            ParseErrorKind::Overflow,
        );

        assert_ok::<U0F128>(
            "0.499999999999999999999999999999999999998",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_ok::<U0F128>(
            "0.499999999999999999999999999999999999999",
            0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok::<U0F128>(
            "0.999999999999999999999999999999999999998",
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<U0F128>(
            "0.999999999999999999999999999999999999999",
            ParseErrorKind::Overflow,
        );
        assert_err::<U0F128>("1", ParseErrorKind::Overflow);

        assert_err::<U0F128>("-0", ParseErrorKind::InvalidDigit);

        assert_ok::<U128F0>(
            "000170141183460469231731687303715884105727.4999999999999999999999999999999999999999",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_ok::<U128F0>(
            "000170141183460469231731687303715884105727.5",
            0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok::<U128F0>(
            "340282366920938463463374607431768211455.4999999999999999999999999999999999999999",
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<U128F0>(
            "340282366920938463463374607431768211455.5",
            ParseErrorKind::Overflow,
        );
    }
}
