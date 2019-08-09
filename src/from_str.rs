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
    display,
    frac::{IsLessOrEqual, True, Unsigned, U8},
    wide_div::WideDivRem,
    FixedI8, FixedU8,
};
use core::{
    cmp::Ordering,
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
    int: &'a [u8],
    frac: &'a [u8],
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
        int: s[int.0..int.1].as_bytes(),
        frac: s[frac.0..frac.1].as_bytes(),
    })
}

impl<Frac> FromStr for FixedI8<Frac>
where
    Frac: Unsigned + IsLessOrEqual<U8, Output = True>,
{
    type Err = ParseFixedError;
    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_i8(s, Self::int_nbits(), Self::frac_nbits()).map(Self::from_bits)
    }
}

impl<Frac> FromStr for FixedU8<Frac>
where
    Frac: Unsigned + IsLessOrEqual<U8, Output = True>,
{
    type Err = ParseFixedError;
    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_u8(s, Self::int_nbits(), Self::frac_nbits()).map(Self::from_bits)
    }
}

fn from_str_i8(s: &str, int_nbits: u32, frac_nbits: u32) -> Result<i8, ParseFixedError> {
    let Parse { neg, int, frac } = parse(s, true)?;
    let (frac, whole_frac) = match get_frac8(frac, frac_nbits) {
        Some(frac) => (frac, false),
        None => (0, true),
    };
    let frac = if frac_nbits == 8 {
        // special case: no int bits
        if neg {
            if frac > 0x80 {
                err!(Overflow)
            }
            frac.wrapping_neg() as i8
        } else {
            if frac >= 0x80 {
                err!(Overflow)
            }
            frac as i8
        }
    } else {
        frac as i8
    };
    let int = get_int_i8(neg, int, int_nbits, whole_frac)?;
    Ok(int | frac)
}

fn from_str_u8(s: &str, int_nbits: u32, frac_nbits: u32) -> Result<u8, ParseFixedError> {
    let Parse { neg: _, int, frac } = parse(s, false)?;
    let (frac, whole_frac) = match get_frac8(frac, frac_nbits) {
        Some(frac) => (frac, false),
        None => (0, true),
    };
    let int = get_int_u8(int, int_nbits, whole_frac)?;
    Ok(int | frac)
}

fn get_int_i8(neg: bool, int: &[u8], nbits: u32, whole_frac: bool) -> Result<i8, ParseFixedError> {
    let mut int = int;
    while !int.is_empty() && int[0] == b'0' {
        int = &int[1..];
    }
    if nbits == 0 {
        err!(whole_frac || !int.is_empty(), Overflow);
        return Ok(0);
    }
    let max_abs_int = if neg {
        1u16 << (nbits - 1)
    } else {
        (1u16 << (nbits - 1)) - 1
    };
    let mut acc = 0;
    for &c in int {
        acc = acc * 10 + (c - b'0') as u16;
        err!(acc > max_abs_int, Overflow);
    }
    if whole_frac {
        acc += 1;
        err!(acc > max_abs_int, Overflow);
    }
    let signed = if neg {
        acc.wrapping_neg() as i8
    } else {
        acc as i8
    };
    Ok(signed << (8 - nbits))
}

fn get_int_u8(int: &[u8], nbits: u32, whole_frac: bool) -> Result<u8, ParseFixedError> {
    let mut int = int;
    while !int.is_empty() && int[0] == b'0' {
        int = &int[1..];
    }
    if nbits == 0 {
        err!(whole_frac || !int.is_empty(), Overflow);
        return Ok(0);
    }
    let max_abs_int = (1u16 << nbits) - 1;
    let mut acc = 0;
    for &c in int {
        acc = acc * 10 + (c - b'0') as u16;
        err!(acc > max_abs_int, Overflow);
    }
    if whole_frac {
        acc += 1;
        err!(acc > max_abs_int, Overflow);
    }
    Ok((acc as u8) << (8 - nbits))
}

fn get_frac8(frac: &[u8], nbits: u32) -> Option<u8> {
    if frac.is_empty() {
        return Some(0);
    }
    let mut digits = display::dec_frac_digits(8);
    debug_assert!(digits <= 3);
    let mut acc = 0;
    for &c in frac {
        if digits == 0 {
            break;
        }
        digits -= 1;
        acc = acc * 10 + (c - b'0') as u16;
    }
    for _ in 0..digits {
        acc *= 10;
    }
    dec3_to_bin8(acc, 8 - nbits)
}

#[cfg(test)]
mod tests {
    use crate::from_str::*;

    #[test]
    fn check_dec3() {
        let two_pow = 8f64.exp2();
        let limit = 1000;
        for i in 0..limit {
            let ans = dec3_to_bin8(i, 0);
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

    #[test]
    fn check_dec6() {
        let two_pow = 16f64.exp2();
        let limit = 1_000_000;
        for i in 0..limit {
            let ans = dec6_to_bin16(i, 0);
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

    #[test]
    fn check_dec13() {
        let two_pow = 32f64.exp2();
        let limit = 10_000_000_000_000;
        for iter in 0..1000000 {
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
    fn check_dec27() {
        let two_pow = 64f64.exp2();
        let limit = 1_000_000_000_000_000_000_000_000_000;
        for iter in 0..1000000 {
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
        let ones = 999999999999999999999999999;
        let zeros = 0;
        let too_big = dec27_27_to_bin128(ones, ones, 0);
        assert_eq!(too_big, None);
        let big = dec27_27_to_bin128(ones, zeros, 0);
        assert_eq!(big, Some(340282366920938463463374607091485844535));
        let small = dec27_27_to_bin128(zeros, ones, 0);
        assert_eq!(small, Some(340282366921));
        let zero = dec27_27_to_bin128(zeros, zeros, 0);
        assert_eq!(zero, Some(0));
        let x = dec27_27_to_bin128(123456789012345678901234567, 987654321098765432109876543, 0);
        assert_eq!(x, Some(42010168377579896403540037811203677112));
    }

    #[test]
    fn check_parse_bounds() {
        let Parse { neg, int, frac } = parse("-12.34", true).unwrap();
        assert_eq!((neg, int, frac), (true, &b"12"[..], &b"34"[..]));
        let Parse { neg, int, frac } = parse("12.", true).unwrap();
        assert_eq!((neg, int, frac), (false, &b"12"[..], &b""[..]));
        let Parse { neg, int, frac } = parse("+.34", false).unwrap();
        assert_eq!((neg, int, frac), (false, &b""[..], &b"34"[..]));
        let Parse { neg, int, frac } = parse("0", false).unwrap();
        assert_eq!((neg, int, frac), (false, &b"0"[..], &b""[..]));

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

    #[test]
    fn check_i8_from_str() {
        use crate::types::*;

        assert_eq!("0.498".parse::<I0F8>().unwrap(), I0F8::from_bits(127));
        let ParseFixedError { kind } = "0.499".parse::<I0F8>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);
        let ParseFixedError { kind } = "1".parse::<I0F8>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);

        assert_eq!("-0.501".parse::<I0F8>().unwrap(), I0F8::from_bits(-128));
        let ParseFixedError { kind } = "-0.502".parse::<I0F8>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);
        let ParseFixedError { kind } = "-1".parse::<I0F8>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);

        assert_eq!("000127.499".parse::<I8F0>().unwrap(), I8F0::from_bits(127));
        let ParseFixedError { kind } = "127.5".parse::<I8F0>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);

        assert_eq!("-128.499".parse::<I8F0>().unwrap(), I8F0::from_bits(-128));
        let ParseFixedError { kind } = "-128.5".parse::<I8F0>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);
    }

    #[test]
    fn check_u8_from_str() {
        use crate::types::*;

        assert_eq!("0.498".parse::<U0F8>().unwrap(), U0F8::from_bits(127));
        assert_eq!("0.499".parse::<U0F8>().unwrap(), U0F8::from_bits(128));
        assert_eq!("0.998".parse::<U0F8>().unwrap(), U0F8::from_bits(255));
        let ParseFixedError { kind } = "0.999".parse::<U0F8>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);
        let ParseFixedError { kind } = "1".parse::<U0F8>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);

        let ParseFixedError { kind } = "-0".parse::<U0F8>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);

        assert_eq!("000127.499".parse::<U8F0>().unwrap(), U8F0::from_bits(127));
        assert_eq!("000127.5".parse::<U8F0>().unwrap(), U8F0::from_bits(128));
        assert_eq!("255.499".parse::<U8F0>().unwrap(), U8F0::from_bits(255));
        let ParseFixedError { kind } = "255.5".parse::<U8F0>().unwrap_err();
        assert_eq!(kind, ParseErrorKind::Overflow);
    }
}
