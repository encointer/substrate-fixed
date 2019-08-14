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
    display::Mul10,
    frac::False,
    sealed::SealedInt,
    types::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    wide_div::WideDivRem,
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    cmp::Ordering,
    fmt::{Display, Formatter, Result as FmtResult},
    ops::{Add, Mul, Shl, Shr},
    str::FromStr,
};

fn bin_str_int_to_bin<I>(s: &str) -> Option<I>
where
    I: SealedInt<IsSigned = False> + From<u8>,
    I: Shl<u32, Output = I> + Shr<u32, Output = I> + Add<Output = I>,
{
    debug_assert!(!s.is_empty());
    let mut bytes = s.as_bytes().iter();
    let first_val = *bytes.next().unwrap() - b'0';
    let mut acc = I::from(first_val);
    let mut leading_zeros = acc.leading_zeros();
    for &byte in bytes {
        let val = byte - b'0';
        leading_zeros = leading_zeros.checked_sub(1)?;
        acc = (acc << 1) + I::from(val);
    }
    Some(acc)
}

fn bin_str_frac_to_bin<I>(s: &str, nbits: u32) -> Option<I>
where
    I: SealedInt<IsSigned = False> + From<u8>,
    I: Shl<u32, Output = I> + Shr<u32, Output = I> + Add<Output = I>,
{
    debug_assert!(!s.is_empty());
    let dump_bits = I::NBITS - nbits;
    let mut rem_bits = nbits;
    let mut acc = I::ZERO;
    for &byte in s.as_bytes() {
        let val = byte - b'0';
        if rem_bits < 1 {
            // round
            acc = acc.checked_add(I::from(val))?;
            if dump_bits != 0 && !(acc >> nbits).is_zero() {
                return None;
            }
            return Some(acc);
        }
        acc = (acc << 1) + I::from(val);
        rem_bits -= 1;
    }
    Some(acc << rem_bits)
}

fn oct_str_int_to_bin<I>(s: &str) -> Option<I>
where
    I: SealedInt<IsSigned = False> + From<u8>,
    I: Shl<u32, Output = I> + Shr<u32, Output = I> + Add<Output = I>,
{
    debug_assert!(!s.is_empty());
    let mut bytes = s.as_bytes().iter();
    let first_val = *bytes.next().unwrap() - b'0';
    let mut acc = I::from(first_val);
    let mut leading_zeros = acc.leading_zeros();
    for &byte in bytes {
        let val = byte - b'0';
        leading_zeros = leading_zeros.checked_sub(3)?;
        acc = (acc << 3) + I::from(val);
    }
    Some(acc)
}

fn oct_str_frac_to_bin<I>(s: &str, nbits: u32) -> Option<I>
where
    I: SealedInt<IsSigned = False> + From<u8>,
    I: Shl<u32, Output = I> + Shr<u32, Output = I> + Add<Output = I>,
{
    debug_assert!(!s.is_empty());
    let dump_bits = I::NBITS - nbits;
    let mut rem_bits = nbits;
    let mut acc = I::ZERO;
    for &byte in s.as_bytes() {
        let val = byte - b'0';
        if rem_bits < 3 {
            acc = (acc << rem_bits) + I::from(val >> (3 - rem_bits));
            // round
            acc = acc.checked_add(I::from((val >> (2 - rem_bits)) & 1))?;
            if dump_bits != 0 && !(acc >> nbits).is_zero() {
                return None;
            }
            return Some(acc);
        }
        acc = (acc << 3) + I::from(val);
        rem_bits -= 3;
    }
    Some(acc << rem_bits)
}

fn unchecked_hex_digit(byte: u8) -> u8 {
    // We know that byte is a valid hex:
    //   * b'0'..=b'9' (0x30..=0x39) => byte & 0x0f
    //   * b'A'..=b'F' (0x41..=0x46) => byte & 0x0f + 9
    //   * b'a'..=b'f' (0x61..=0x66) => byte & 0x0f + 9
    (byte & 0x0f) + if byte >= 0x40 { 9 } else { 0 }
}

fn hex_str_int_to_bin<I>(s: &str) -> Option<I>
where
    I: SealedInt<IsSigned = False> + From<u8>,
    I: Shl<u32, Output = I> + Add<Output = I>,
{
    debug_assert!(!s.is_empty());
    let mut bytes = s.as_bytes().iter();
    let first_val = unchecked_hex_digit(*bytes.next().unwrap());
    let mut acc = I::from(first_val);
    let mut leading_zeros = acc.leading_zeros();
    for &byte in bytes {
        let val = unchecked_hex_digit(byte);
        leading_zeros = leading_zeros.checked_sub(4)?;
        acc = (acc << 4) + I::from(val);
    }
    Some(acc)
}

fn hex_str_frac_to_bin<I>(s: &str, nbits: u32) -> Option<I>
where
    I: SealedInt<IsSigned = False> + From<u8>,
    I: Shl<u32, Output = I> + Shr<u32, Output = I> + Add<Output = I>,
{
    debug_assert!(!s.is_empty());
    let dump_bits = I::NBITS - nbits;
    let mut rem_bits = nbits;
    let mut acc = I::ZERO;
    for &byte in s.as_bytes() {
        let val = unchecked_hex_digit(byte);
        if rem_bits < 4 {
            acc = (acc << rem_bits) + I::from(val >> (4 - rem_bits));
            // round
            acc = acc.checked_add(I::from((val >> (3 - rem_bits)) & 1))?;
            if dump_bits != 0 && !(acc >> nbits).is_zero() {
                return None;
            }
            return Some(acc);
        }
        acc = (acc << 4) + I::from(val);
        rem_bits -= 4;
    }
    Some(acc << rem_bits)
}

enum Round {
    Nearest,
    Floor,
}

// Decode fractional decimal digits into nbits fractional bits.
//
// For an output with BIN = 8 bits, we can take DEC = 3 decimal digits.
//
//     0 ≤ val ≤ 999, 0 ≤ nbits ≤ 8
//
// In general,
//
//     0 ≤ val ≤ 10^DEC - 1, 0 ≤ nbits ≤ BIN
//
// We can either floor the result or round to the nearest (ties away from zero).
// If rounding results in more than nbits bits, returns None.
//
// Examples: (for DEC = 3, BIN = 8)
//
//    dec_to_bin(999, 8, Round::Floor) -> floor(999 × 256 / 1000) -> 255 -> Some(255)
//    dec_to_bin(999, 8, Round::Nearest) -> floor(999 × 256 / 1000 + 0.5) -> 256 -> None
//    dec_to_bin(999, 5, Round::Floor) -> floor(999 × 32 / 1000) -> 31 -> Some(31)
//    dec_to_bin(999, 5, Round::Nearest) -> floor(999 × 32 / 1000 + 0.5) -> 32 -> None
//    dec_to_bin(499, 0, Round::Floor) -> floor(499 / 1000) -> 0 -> Some(0)
//    dec_to_bin(499, 0, Round::Nearest) -> floor(499 / 1000 + 0.5) -> 0 -> Some(0)
//    dec_to_bin(500, 0, Round::Nearest) -> floor(500 / 1000 + 0.5) -> 1 -> None
//
// For flooring:
//
//     floor(val × 2^nbits / 10^3) = floor(val × 2^(nbits - 3) / 5^3)
//
// For rounding:
//
//     floor(val × 2^nbits / 10^3 + 0.5) = floor((val × 2^(nbits - 2) + 5^3) / (2 × 5^3))
//
// Using integer arithmetic, this is equal to:
//
//     ((val << 6 >> (8 - nbits)) + if rounding { 125 } else { 0 }) / 250
//
// Note that val << 6 cannot overflow u16, as val < 1000 and 1000 × 2^6 < 2^16.
//
// In general:
//
//     ((val << (BIN - DEC + 1) >> (8 - nbits)) + if rounding { 5^DEC } else { 0 }) / (2 × 5^DEC)
//
// And we ensure that 10^DEC × 2^(BIN - DEC + 1) < 2^(2 × BIN), which simplifies to
//
//     5^DEC × 2 < 2^BIN
//
// From this it also follows that val << (BIN - DEC + 1) never overflows a (2 × BIN)-bit number.
//
// So for u8, BIN = 8, DEC  3
// So for u16, BIN = 16, DEC ≤ 6
// So for u32, BIN = 32, DEC ≤ 13
// So for u64, BIN = 64, DEC ≤ 27
// So for u128, BIN = 128, DEC ≤ 54
trait DecToBin: Sized {
    type Double;
    fn dec_to_bin(val: Self::Double, nbits: u32, round: Round) -> Option<Self>;
    fn parse_is_short(s: &str) -> (Self::Double, bool);
}

macro_rules! impl_dec_to_bin {
    ($Single:ident, $Double:ident, $dec:expr, $bin:expr) => {
        impl DecToBin for $Single {
            type Double = $Double;
            fn dec_to_bin(val: $Double, nbits: u32, round: Round) -> Option<$Single> {
                debug_assert!(val < $Double::pow(10, $dec));
                debug_assert!(nbits <= $bin);
                let fives = $Double::pow(5, $dec);
                let denom = fives * 2;
                let mut numer = val << ($bin - $dec + 1) >> ($bin - nbits);
                match round {
                    Round::Nearest => {
                        numer += fives;
                        if numer >> nbits >= denom {
                            return None;
                        }
                    }
                    Round::Floor => {}
                }
                Some((numer / denom) as $Single)
            }

            fn parse_is_short(s: &str) -> ($Double, bool) {
                let (is_short, slice, pad) = if let Some(rem) = usize::checked_sub($dec, s.len()) {
                    (true, s, $Double::pow(10, rem as u32))
                } else {
                    (false, &s[..$dec], 1)
                };
                let val = slice.parse::<$Double>().unwrap() * pad;
                (val, is_short)
            }
        }
    };
}
impl_dec_to_bin! { u8, u16, 3, 8 }
impl_dec_to_bin! { u16, u32, 6, 16 }
impl_dec_to_bin! { u32, u64, 13, 32 }
impl_dec_to_bin! { u64, u128, 27, 64 }

impl DecToBin for u128 {
    type Double = (u128, u128);
    fn dec_to_bin((hi, lo): (u128, u128), nbits: u32, round: Round) -> Option<u128> {
        debug_assert!(hi < 10u128.pow(27));
        debug_assert!(lo < 10u128.pow(27));
        debug_assert!(nbits <= 128);
        let fives = 5u128.pow(54);
        let denom = fives * 2;
        // we need to combine (10^27*hi + lo) << (128 - 54 + 1)
        let (hi_hi, hi_lo) = mul_hi_lo(hi, 10u128.pow(27));
        let (mut numer_lo, overflow) = hi_lo.overflowing_add(lo);
        let mut numer_hi = if overflow { hi_hi + 1 } else { hi_hi };
        match nbits.cmp(&(54 - 1)) {
            Ordering::Less => {
                let shr = (54 - 1) - nbits;
                numer_lo = (numer_lo >> shr) | (numer_hi << (128 - shr));
                numer_hi >>= shr;
            }
            Ordering::Greater => {
                let shl = nbits - (54 - 1);
                numer_hi = (numer_hi << shl) | (numer_lo >> (128 - shl));
                numer_lo <<= shl;
            }
            Ordering::Equal => {}
        };
        match round {
            Round::Nearest => {
                let (wrapped, overflow) = numer_lo.overflowing_add(fives);
                numer_lo = wrapped;
                if overflow {
                    numer_hi += 1;
                }
                let check_overflow = if nbits == 128 {
                    numer_hi
                } else if nbits == 0 {
                    numer_lo
                } else {
                    (numer_lo >> nbits) | (numer_hi << (128 - nbits))
                };
                if check_overflow >= denom {
                    return None;
                }
            }
            Round::Floor => {}
        }
        Some(div_wide(numer_hi, numer_lo, denom))
    }

    fn parse_is_short(s: &str) -> ((u128, u128), bool) {
        if let Some(rem) = 27usize.checked_sub(s.len()) {
            let hi = s.parse::<u128>().unwrap() * 10u128.pow(rem as u32);
            ((hi, 0), true)
        } else {
            let hi = s[..27].parse::<u128>().unwrap();

            let (is_short, slice, pad) = if let Some(rem) = 54usize.checked_sub(s.len()) {
                (true, &s[27..], 10u128.pow(rem as u32))
            } else {
                (false, &s[27..54], 1)
            };
            let lo = slice.parse::<u128>().unwrap() * pad;
            ((hi, lo), is_short)
        }
    }
}

fn dec_str_frac_to_bin<I>(s: &str, nbits: u32) -> Option<I>
where
    I: SealedInt<IsSigned = False> + FromStr + From<u8> + DecToBin,
    I: Mul10 + Shl<u32, Output = I> + Shr<u32, Output = I> + Add<Output = I> + Mul<Output = I>,
{
    let (val, is_short) = I::parse_is_short(s);
    let one = I::from(1u8);
    let dump_bits = I::NBITS - nbits;
    // if is_short, dec_to_bin can round and give correct answer immediately
    let round = if is_short {
        Round::Nearest
    } else {
        Round::Floor
    };
    let floor = I::dec_to_bin(val, nbits, round)?;
    if is_short {
        return Some(floor);
    }
    // since !is_short, we have a floor and we have to check whether we need to increment

    // add_5 is to add rounding when all bits are used
    let (mut boundary, mut add_5) = if nbits == 0 {
        (one << (I::NBITS - 1), false)
    } else if dump_bits == 0 {
        (floor, true)
    } else {
        ((floor << dump_bits) + (one << (dump_bits - 1)), false)
    };
    for &byte in s.as_bytes() {
        let mut boundary_digit = boundary.mul10_assign();
        if add_5 {
            let (wrapped, overflow) = boundary.overflowing_add(I::from(5u8));
            boundary = wrapped;
            if overflow {
                boundary_digit += 1;
            }
            add_5 = false;
        }
        if byte - b'0' < boundary_digit {
            return Some(floor);
        }
        if byte - b'0' > boundary_digit {
            break;
        }
    }
    // ≥ boundary, so we round up
    let next_up = floor.checked_add(one)?;
    if dump_bits != 0 && (next_up >> nbits).traits().ne(&I::ZERO.traits()) {
        None
    } else {
        Some(next_up)
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

/**
An error which can be returned when parsing a fixed-point number.

# Examples

```rust
use fixed::{types::I16F16, ParseFixedError};
// This string is not a fixed-point number.
let s = "something completely different (_!_!_)";
let error: ParseFixedError = match s.parse::<I16F16>() {
    Ok(_) => unreachable!(),
    Err(error) => error,
};
println!("Parse error: {}", error);
```
*/
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

impl From<ParseErrorKind> for ParseFixedError {
    fn from(kind: ParseErrorKind) -> ParseFixedError {
        ParseFixedError { kind }
    }
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

// also trims zeros at start of int and at end of frac
fn parse_bounds(s: &str, can_be_neg: bool, radix: u32) -> Result<Parse<'_>, ParseFixedError> {
    let mut sign: Option<bool> = None;
    let mut trimmed_int_start: Option<usize> = None;
    let mut point: Option<usize> = None;
    let mut trimmed_frac_end: Option<usize> = None;
    let mut has_any_digit = false;

    for (index, &byte) in s.as_bytes().iter().enumerate() {
        match (byte, radix) {
            (b'+', _) => {
                if sign.is_some() || point.is_some() || has_any_digit {
                    Err(ParseErrorKind::InvalidDigit)?;
                }
                sign = Some(false);
                continue;
            }
            (b'-', _) => {
                if !can_be_neg || sign.is_some() || point.is_some() || has_any_digit {
                    Err(ParseErrorKind::InvalidDigit)?;
                }
                sign = Some(true);
                continue;
            }
            (b'.', _) => {
                if point.is_some() {
                    Err(ParseErrorKind::TooManyPoints)?;
                }
                point = Some(index);
                trimmed_frac_end = Some(index + 1);
                continue;
            }
            (b'0'..=b'1', 2)
            | (b'0'..=b'7', 8)
            | (b'0'..=b'9', 10)
            | (b'0'..=b'9', 16)
            | (b'a'..=b'f', 16)
            | (b'A'..=b'F', 16) => {
                if trimmed_int_start.is_none() && point.is_none() && byte != b'0' {
                    trimmed_int_start = Some(index);
                }
                if trimmed_frac_end.is_some() && byte != b'0' {
                    trimmed_frac_end = Some(index + 1);
                }
                has_any_digit = true;
            }
            _ => Err(ParseErrorKind::InvalidDigit)?,
        }
    }
    if !has_any_digit {
        Err(ParseErrorKind::NoDigits)?;
    }
    let neg = sign.unwrap_or(false);
    let int = match (trimmed_int_start, point) {
        (Some(start), Some(point)) => &s[start..point],
        (Some(start), None) => &s[start..],
        (None, _) => "",
    };
    let frac = match (point, trimmed_frac_end) {
        (Some(point), Some(end)) => &s[(point + 1)..end],
        _ => "",
    };
    Ok(Parse { neg, int, frac })
}

pub(crate) trait FromStrRadix: Sized {
    type Err;
    fn from_str_radix(s: &str, radix: u32) -> Result<Self, Self::Err>;
}

macro_rules! impl_from_str {
    ($Fixed:ident, $LeEqU:ident, $method:ident) => {
        impl<Frac: $LeEqU> FromStr for $Fixed<Frac> {
            type Err = ParseFixedError;
            #[inline]
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                $method(s, 10, Self::int_nbits(), Self::frac_nbits()).map(Self::from_bits)
            }
        }
        impl<Frac: $LeEqU> FromStrRadix for $Fixed<Frac> {
            type Err = ParseFixedError;
            #[inline]
            fn from_str_radix(s: &str, radix: u32) -> Result<Self, Self::Err> {
                $method(s, radix, Self::int_nbits(), Self::frac_nbits()).map(Self::from_bits)
            }
        }
    };
}

macro_rules! impl_from_str_signed {
    (
        $Fixed:ident, $LeEqU:ident, $Bits:ident;
        fn $all:ident;
        $int:ident;
        $frac:ident;
    ) => {
        impl_from_str! { $Fixed, $LeEqU, $all }

        fn $all(
            s: &str,
            radix: u32,
            int_nbits: u32,
            frac_nbits: u32,
        ) -> Result<$Bits, ParseFixedError> {
            let Parse { neg, int, frac } = parse_bounds(s, true, radix)?;
            let (abs_frac, whole_frac) = match $frac(frac, radix, frac_nbits) {
                Some(frac) => (frac, false),
                None => (0, true),
            };
            let abs_int =
                $int(int, radix, int_nbits, whole_frac).ok_or(ParseErrorKind::Overflow)?;
            let abs = abs_int | abs_frac;
            let max_abs = if neg {
                <$Bits as SealedInt>::Unsigned::MSB
            } else {
                <$Bits as SealedInt>::Unsigned::MSB - 1
            };
            if abs > max_abs {
                Err(ParseErrorKind::Overflow)?;
            }
            let f = if neg {
                abs.wrapping_neg() as $Bits
            } else {
                abs as $Bits
            };
            Ok(f)
        }
    };
}

macro_rules! impl_from_str_unsigned {
    (
        $Fixed:ident, $LeEqU:ident, $Bits:ident;
        fn $all:ident;
        fn $int:ident, ($int_half:ident, $int_half_cond:expr);
        fn $frac:ident, ($frac_half:ident, $frac_half_cond:expr);
    ) => {
        impl_from_str! { $Fixed, $LeEqU, $all }

        fn $all(
            s: &str,
            radix: u32,
            int_nbits: u32,
            frac_nbits: u32,
        ) -> Result<$Bits, ParseFixedError> {
            let Parse { int, frac, .. } = parse_bounds(s, false, radix)?;
            let (frac, whole_frac) = match $frac(frac, radix, frac_nbits) {
                Some(frac) => (frac, false),
                None => (0, true),
            };
            let int = $int(int, radix, int_nbits, whole_frac).ok_or(ParseErrorKind::Overflow)?;
            Ok(int | frac)
        }

        fn $int(int: &str, radix: u32, nbits: u32, whole_frac: bool) -> Option<$Bits> {
            const HALF: u32 = <$Bits as SealedInt>::NBITS / 2;
            if $int_half_cond && nbits <= HALF {
                return $int_half(int, radix, nbits, whole_frac).map(|x| $Bits::from(x) << HALF);
            }

            if int.is_empty() && !whole_frac {
                return Some(0);
            } else if int.is_empty() && nbits != 0 {
                return Some(1);
            } else if int.is_empty() {
                return None;
            } else if nbits == 0 {
                return None;
            }
            let mut parsed_int = match radix {
                2 => bin_str_int_to_bin(int)?,
                8 => oct_str_int_to_bin(int)?,
                16 => hex_str_int_to_bin(int)?,
                10 => int.parse::<$Bits>().ok()?,
                _ => unreachable!(),
            };
            if whole_frac {
                parsed_int = parsed_int.checked_add(1)?;
            }
            let remove_bits = <$Bits as SealedInt>::NBITS - nbits;
            if remove_bits > 0 && (parsed_int >> nbits) != 0 {
                None
            } else {
                Some(parsed_int << remove_bits)
            }
        }

        fn $frac(frac: &str, radix: u32, nbits: u32) -> Option<$Bits> {
            if $frac_half_cond && nbits <= <$Bits as SealedInt>::NBITS / 2 {
                return $frac_half(frac, radix, nbits).map($Bits::from);
            }
            if frac.is_empty() {
                return Some(0);
            }
            match radix {
                2 => bin_str_frac_to_bin(frac, nbits),
                8 => oct_str_frac_to_bin(frac, nbits),
                16 => hex_str_frac_to_bin(frac, nbits),
                10 => dec_str_frac_to_bin(frac, nbits),
                _ => unreachable!(),
            }
        }
    };
}

impl_from_str_signed! {
    FixedI8, LeEqU8, i8;
    fn from_str_i8;
    get_int8;
    get_frac8;
}
impl_from_str_unsigned! {
    FixedU8, LeEqU8, u8;
    fn from_str_u8;
    fn get_int8, (get_int8, false);
    fn get_frac8, (get_frac8, false);
}

impl_from_str_signed! {
    FixedI16, LeEqU16, i16;
    fn from_str_i16;
    get_int16;
    get_frac16;
}
impl_from_str_unsigned! {
    FixedU16, LeEqU16, u16;
    fn from_str_u16;
    fn get_int16, (get_int8, true);
    fn get_frac16, (get_frac8, true);
}

impl_from_str_signed! {
    FixedI32, LeEqU32, i32;
    fn from_str_i32;
    get_int32;
    get_frac32;
}
impl_from_str_unsigned! {
    FixedU32, LeEqU32, u32;
    fn from_str_u32;
    fn get_int32, (get_int16, true);
    fn get_frac32, (get_frac16, true);
}

impl_from_str_signed! {
    FixedI64, LeEqU64, i64;
    fn from_str_i64;
    get_int64;
    get_frac64;
}
impl_from_str_unsigned! {
    FixedU64, LeEqU64, u64;
    fn from_str_u64;
    fn get_int64, (get_int32, true);
    fn get_frac64, (get_frac32, true);
}

impl_from_str_signed! {
    FixedI128, LeEqU128, i128;
    fn from_str_i128;
    get_int128;
    get_frac128;
}
impl_from_str_unsigned! {
    FixedU128, LeEqU128, u128;
    fn from_str_u128;
    fn get_int128, (get_int64, true);
    fn get_frac128, (get_frac64, true);
}

#[cfg(test)]
mod tests {
    use crate::{from_str::*, traits::Fixed, types::*};
    use std::{fmt::Debug, format, string::String};

    #[test]
    fn check_dec_8() {
        let two_pow = 8f64.exp2();
        let limit = 1000;
        for i in 0..limit {
            let ans = <u8 as DecToBin>::dec_to_bin(i, 8, Round::Nearest);
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
    fn check_dec_16() {
        let two_pow = 16f64.exp2();
        let limit = 1_000_000;
        for i in 0..limit {
            let ans = <u16 as DecToBin>::dec_to_bin(i, 16, Round::Nearest);
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
    fn check_dec_32() {
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
                let ans = <u32 as DecToBin>::dec_to_bin(i, 32, Round::Nearest);
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
    fn check_dec_64() {
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
                let ans = <u64 as DecToBin>::dec_to_bin(i, 64, Round::Nearest);
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
    fn check_dec_128() {
        let nines = 10u128.pow(27) - 1;
        let zeros = 0;
        let too_big = <u128 as DecToBin>::dec_to_bin((nines, nines), 128, Round::Nearest);
        assert_eq!(too_big, None);
        let big = <u128 as DecToBin>::dec_to_bin((nines, zeros), 128, Round::Nearest);
        assert_eq!(
            big,
            Some(340_282_366_920_938_463_463_374_607_091_485_844_535)
        );
        let small = <u128 as DecToBin>::dec_to_bin((zeros, nines), 128, Round::Nearest);
        assert_eq!(small, Some(340_282_366_921));
        let zero = <u128 as DecToBin>::dec_to_bin((zeros, zeros), 128, Round::Nearest);
        assert_eq!(zero, Some(0));
        let x = <u128 as DecToBin>::dec_to_bin(
            (
                123_456_789_012_345_678_901_234_567,
                987_654_321_098_765_432_109_876_543,
            ),
            128,
            Round::Nearest,
        );
        assert_eq!(x, Some(42_010_168_377_579_896_403_540_037_811_203_677_112));
    }

    #[test]
    fn check_parse_bounds() {
        let Parse { neg, int, frac } = parse_bounds("-12.34", true, 10).unwrap();
        assert_eq!((neg, int, frac), (true, "12", "34"));
        let Parse { neg, int, frac } = parse_bounds("012.", true, 10).unwrap();
        assert_eq!((neg, int, frac), (false, "12", ""));
        let Parse { neg, int, frac } = parse_bounds("+.340", false, 10).unwrap();
        assert_eq!((neg, int, frac), (false, "", "34"));
        let Parse { neg, int, frac } = parse_bounds("0", false, 10).unwrap();
        assert_eq!((neg, int, frac), (false, "", ""));
        let Parse { neg, int, frac } = parse_bounds("-.C1A0", true, 16).unwrap();
        assert_eq!((neg, int, frac), (true, "", "C1A"));

        let ParseFixedError { kind } = parse_bounds("0 ", true, 10).unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);
        let ParseFixedError { kind } = parse_bounds("+.", true, 10).unwrap_err();
        assert_eq!(kind, ParseErrorKind::NoDigits);
        let ParseFixedError { kind } = parse_bounds(".1.", true, 10).unwrap_err();
        assert_eq!(kind, ParseErrorKind::TooManyPoints);
        let ParseFixedError { kind } = parse_bounds("1+2", true, 10).unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);
        let ParseFixedError { kind } = parse_bounds("1-2", true, 10).unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);
        let ParseFixedError { kind } = parse_bounds("-12", false, 10).unwrap_err();
        assert_eq!(kind, ParseErrorKind::InvalidDigit);
    }

    fn assert_ok<F>(s: &str, bits: F::Bits)
    where
        F: Fixed + FromStr<Err = ParseFixedError>,
        F::Bits: Eq + Debug,
    {
        match s.parse::<F>() {
            Ok(f) => assert_eq!(f.to_bits(), bits),
            Err(e) => panic!("could not parse {}: {}", s, e),
        }
    }
    fn assert_err<F>(s: &str, kind: ParseErrorKind)
    where
        F: Fixed + FromStr<Err = ParseFixedError>,
    {
        match s.parse::<F>() {
            Ok(f) => panic!("incorrectly parsed {} as {}", s, f),
            Err(ParseFixedError { kind: err }) => assert_eq!(err, kind),
        }
    }

    fn assert_ok_radix<F>(s: &str, radix: u32, bits: F::Bits)
    where
        F: Fixed + FromStrRadix<Err = ParseFixedError>,
        F::Bits: Eq + Debug,
    {
        match <F as FromStrRadix>::from_str_radix(s, radix) {
            Ok(f) => assert_eq!(f.to_bits(), bits),
            Err(e) => panic!("could not parse {}: {}", s, e),
        }
    }
    fn assert_err_radix<F>(s: &str, radix: u32, kind: ParseErrorKind)
    where
        F: Fixed + FromStrRadix<Err = ParseFixedError>,
    {
        match <F as FromStrRadix>::from_str_radix(s, radix) {
            Ok(f) => panic!("incorrectly parsed {} as {}", s, f),
            Err(ParseFixedError { kind: err }) => assert_eq!(err, kind),
        }
    }

    #[test]
    fn check_i8_u8_from_str() {
        assert_err::<I0F8>("-1", ParseErrorKind::Overflow);
        assert_err::<I0F8>("-0.502", ParseErrorKind::Overflow);
        assert_ok::<I0F8>("-0.501", -0x80);
        assert_ok::<I0F8>("0.498", 0x7F);
        assert_err::<I0F8>("0.499", ParseErrorKind::Overflow);
        assert_err::<I0F8>("1", ParseErrorKind::Overflow);

        assert_err::<I4F4>("-8.04", ParseErrorKind::Overflow);
        assert_ok::<I4F4>("-8.03", -0x80);
        assert_ok::<I4F4>("7.96", 0x7F);
        assert_err::<I4F4>("7.97", ParseErrorKind::Overflow);

        assert_err::<I8F0>("-128.5", ParseErrorKind::Overflow);
        assert_ok::<I8F0>("-128.499", -0x80);
        assert_ok::<I8F0>("127.499", 0x7F);
        assert_err::<I8F0>("127.5", ParseErrorKind::Overflow);

        assert_err::<U0F8>("-0", ParseErrorKind::InvalidDigit);
        assert_ok::<U0F8>("0.498", 0x7F);
        assert_ok::<U0F8>("0.499", 0x80);
        assert_ok::<U0F8>("0.998", 0xFF);
        assert_err::<U0F8>("0.999", ParseErrorKind::Overflow);
        assert_err::<U0F8>("1", ParseErrorKind::Overflow);

        assert_ok::<U4F4>("7.96", 0x7F);
        assert_ok::<U4F4>("7.97", 0x80);
        assert_ok::<U4F4>("15.96", 0xFF);
        assert_err::<U4F4>("15.97", ParseErrorKind::Overflow);

        assert_ok::<U8F0>("127.499", 0x7F);
        assert_ok::<U8F0>("127.5", 0x80);
        assert_ok::<U8F0>("255.499", 0xFF);
        assert_err::<U8F0>("255.5", ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i16_u16_from_str() {
        assert_err::<I0F16>("-1", ParseErrorKind::Overflow);
        assert_err::<I0F16>("-0.500008", ParseErrorKind::Overflow);
        assert_ok::<I0F16>("-0.500007", -0x8000);
        assert_ok::<I0F16>("0.499992", 0x7FFF);
        assert_err::<I0F16>("0.499993", ParseErrorKind::Overflow);
        assert_err::<I0F16>("1", ParseErrorKind::Overflow);

        assert_err::<I8F8>("-128.002", ParseErrorKind::Overflow);
        assert_ok::<I8F8>("-128.001", -0x8000);
        assert_ok::<I8F8>("127.998", 0x7FFF);
        assert_err::<I8F8>("127.999", ParseErrorKind::Overflow);

        assert_err::<I16F0>("-32768.5", ParseErrorKind::Overflow);
        assert_ok::<I16F0>("-32768.499999", -0x8000);
        assert_ok::<I16F0>("32767.499999", 0x7FFF);
        assert_err::<I16F0>("32767.5", ParseErrorKind::Overflow);

        assert_err::<U0F16>("-0", ParseErrorKind::InvalidDigit);
        assert_ok::<U0F16>("0.499992", 0x7FFF);
        assert_ok::<U0F16>("0.499993", 0x8000);
        assert_ok::<U0F16>("0.999992", 0xFFFF);
        assert_err::<U0F16>("0.999993", ParseErrorKind::Overflow);
        assert_err::<U0F16>("1", ParseErrorKind::Overflow);

        assert_ok::<U8F8>("127.998", 0x7FFF);
        assert_ok::<U8F8>("127.999", 0x8000);
        assert_ok::<U8F8>("255.998", 0xFFFF);
        assert_err::<U8F8>("255.999", ParseErrorKind::Overflow);

        assert_ok::<U16F0>("32767.499999", 0x7FFF);
        assert_ok::<U16F0>("32767.5", 0x8000);
        assert_ok::<U16F0>("65535.499999", 0xFFFF);
        assert_err::<U16F0>("65535.5", ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i32_u32_from_str() {
        assert_err::<I0F32>("-1", ParseErrorKind::Overflow);
        assert_err::<I0F32>("-0.5000000002", ParseErrorKind::Overflow);
        assert_ok::<I0F32>("-0.5000000001", -0x8000_0000);
        assert_ok::<I0F32>("0.4999999998", 0x7FFF_FFFF);
        assert_err::<I0F32>("0.4999999999", ParseErrorKind::Overflow);
        assert_err::<I0F32>("1", ParseErrorKind::Overflow);

        assert_err::<I16F16>("-32768.000008", ParseErrorKind::Overflow);
        assert_ok::<I16F16>("-32768.000007", -0x8000_0000);
        assert_ok::<I16F16>("32767.999992", 0x7FFF_FFFF);
        assert_err::<I16F16>("32767.999993", ParseErrorKind::Overflow);

        assert_err::<I32F0>("-2147483648.5", ParseErrorKind::Overflow);
        assert_ok::<I32F0>("-2147483648.4999999999", -0x8000_0000);
        assert_ok::<I32F0>("2147483647.4999999999", 0x7FFF_FFFF);
        assert_err::<I32F0>("2147483647.5", ParseErrorKind::Overflow);

        assert_err::<U0F32>("-0", ParseErrorKind::InvalidDigit);
        assert_ok::<U0F32>("0.4999999998", 0x7FFF_FFFF);
        assert_ok::<U0F32>("0.4999999999", 0x8000_0000);
        assert_ok::<U0F32>("0.9999999998", 0xFFFF_FFFF);
        assert_err::<U0F32>("0.9999999999", ParseErrorKind::Overflow);
        assert_err::<U0F32>("1", ParseErrorKind::Overflow);

        assert_ok::<U16F16>("32767.999992", 0x7FFF_FFFF);
        assert_ok::<U16F16>("32767.999993", 0x8000_0000);
        assert_ok::<U16F16>("65535.999992", 0xFFFF_FFFF);
        assert_err::<U16F16>("65535.999993", ParseErrorKind::Overflow);

        assert_ok::<U32F0>("2147483647.4999999999", 0x7FFF_FFFF);
        assert_ok::<U32F0>("2147483647.5", 0x8000_0000);
        assert_ok::<U32F0>("4294967295.4999999999", 0xFFFF_FFFF);
        assert_err::<U32F0>("4294967295.5", ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i16_u16_from_str_binary() {
        assert_err_radix::<I0F16>("-1", 2, ParseErrorKind::Overflow);
        assert_err_radix::<I0F16>("-0.100000000000000010", 2, ParseErrorKind::Overflow);
        assert_ok_radix::<I0F16>("-0.100000000000000001", 2, -0x8000);
        assert_ok_radix::<I0F16>("0.011111111111111101", 2, 0x7FFF);
        assert_err_radix::<I0F16>("0.011111111111111110", 2, ParseErrorKind::Overflow);
        assert_err_radix::<I0F16>("1", 2, ParseErrorKind::Overflow);

        assert_err_radix::<I8F8>("-10000000.0000000010", 2, ParseErrorKind::Overflow);
        assert_ok_radix::<I8F8>("-10000000.0000000001", 2, -0x8000);
        assert_ok_radix::<I8F8>("1111111.1111111101", 2, 0x7FFF);
        assert_err_radix::<I8F8>("1111111.1111111110", 2, ParseErrorKind::Overflow);

        assert_err_radix::<I16F0>("-1000000000000000.10", 2, ParseErrorKind::Overflow);
        assert_ok_radix::<I16F0>("-1000000000000000.01", 2, -0x8000);
        assert_ok_radix::<I16F0>("111111111111111.01", 2, 0x7FFF);
        assert_err_radix::<I16F0>("111111111111111.10", 2, ParseErrorKind::Overflow);

        assert_err_radix::<U0F16>("-0", 2, ParseErrorKind::InvalidDigit);
        assert_ok_radix::<U0F16>("0.011111111111111101", 2, 0x7FFF);
        assert_ok_radix::<U0F16>("0.011111111111111110", 2, 0x8000);
        assert_ok_radix::<U0F16>("0.111111111111111101", 2, 0xFFFF);
        assert_err_radix::<U0F16>("0.111111111111111110", 2, ParseErrorKind::Overflow);
        assert_err_radix::<U0F16>("1", 2, ParseErrorKind::Overflow);

        assert_ok_radix::<U8F8>("1111111.1111111101", 2, 0x7FFF);
        assert_ok_radix::<U8F8>("1111111.1111111110", 2, 0x8000);
        assert_ok_radix::<U8F8>("11111111.1111111101", 2, 0xFFFF);
        assert_err_radix::<U8F8>("11111111.1111111110", 2, ParseErrorKind::Overflow);

        assert_ok_radix::<U16F0>("111111111111111.01", 2, 0x7FFF);
        assert_ok_radix::<U16F0>("111111111111111.10", 2, 0x8000);
        assert_ok_radix::<U16F0>("1111111111111111.01", 2, 0xFFFF);
        assert_err_radix::<U16F0>("1111111111111111.10", 2, ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i16_u16_from_str_octal() {
        assert_err_radix::<I0F16>("-1", 8, ParseErrorKind::Overflow);
        assert_err_radix::<I0F16>("-0.400002", 8, ParseErrorKind::Overflow);
        assert_ok_radix::<I0F16>("-0.400001", 8, -0x8000);
        assert_ok_radix::<I0F16>("0.377775", 8, 0x7FFF);
        assert_err_radix::<I0F16>("0.377776", 8, ParseErrorKind::Overflow);
        assert_err_radix::<I0F16>("1", 8, ParseErrorKind::Overflow);

        assert_err_radix::<I8F8>("-2000.0010", 8, ParseErrorKind::Overflow);
        assert_ok_radix::<I8F8>("-200.0007", 8, -0x8000);
        assert_ok_radix::<I8F8>("177.7767", 8, 0x7FFF);
        assert_err_radix::<I8F8>("177.7770", 8, ParseErrorKind::Overflow);

        assert_err_radix::<I16F0>("-100000.4", 8, ParseErrorKind::Overflow);
        assert_ok_radix::<I16F0>("-100000.3", 8, -0x8000);
        assert_ok_radix::<I16F0>("77777.3", 8, 0x7FFF);
        assert_err_radix::<I16F0>("77777.4", 8, ParseErrorKind::Overflow);

        assert_err_radix::<U0F16>("-0", 8, ParseErrorKind::InvalidDigit);
        assert_ok_radix::<U0F16>("0.377775", 8, 0x7FFF);
        assert_ok_radix::<U0F16>("0.377776", 8, 0x8000);
        assert_ok_radix::<U0F16>("0.777775", 8, 0xFFFF);
        assert_err_radix::<U0F16>("0.777776", 8, ParseErrorKind::Overflow);
        assert_err_radix::<U0F16>("1", 8, ParseErrorKind::Overflow);

        assert_ok_radix::<U8F8>("177.7767", 8, 0x7FFF);
        assert_ok_radix::<U8F8>("177.7770", 8, 0x8000);
        assert_ok_radix::<U8F8>("377.7767", 8, 0xFFFF);
        assert_err_radix::<U8F8>("377.7770", 8, ParseErrorKind::Overflow);

        assert_ok_radix::<U16F0>("77777.3", 8, 0x7FFF);
        assert_ok_radix::<U16F0>("77777.4", 8, 0x8000);
        assert_ok_radix::<U16F0>("177777.3", 8, 0xFFFF);
        assert_err_radix::<U16F0>("177777.4", 8, ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i16_u16_from_str_hex() {
        assert_err_radix::<I0F16>("-1", 16, ParseErrorKind::Overflow);
        assert_err_radix::<I0F16>("-0.80008", 16, ParseErrorKind::Overflow);
        assert_ok_radix::<I0F16>("-0.80007", 16, -0x8000);
        assert_ok_radix::<I0F16>("0.7FFF7", 16, 0x7FFF);
        assert_err_radix::<I0F16>("0.7FFF8", 16, ParseErrorKind::Overflow);
        assert_err_radix::<I0F16>("1", 16, ParseErrorKind::Overflow);

        assert_err_radix::<I8F8>("-80.008", 16, ParseErrorKind::Overflow);
        assert_ok_radix::<I8F8>("-80.007", 16, -0x8000);
        assert_ok_radix::<I8F8>("7F.FF7", 16, 0x7FFF);
        assert_err_radix::<I8F8>("7F.FF8", 16, ParseErrorKind::Overflow);

        assert_err_radix::<I16F0>("-8000.8", 16, ParseErrorKind::Overflow);
        assert_ok_radix::<I16F0>("-8000.7", 16, -0x8000);
        assert_ok_radix::<I16F0>("7FFF.7", 16, 0x7FFF);
        assert_err_radix::<I16F0>("7FFF.8", 16, ParseErrorKind::Overflow);

        assert_err_radix::<U0F16>("-0", 16, ParseErrorKind::InvalidDigit);
        assert_ok_radix::<U0F16>("0.7FFF7", 16, 0x7FFF);
        assert_ok_radix::<U0F16>("0.7FFF8", 16, 0x8000);
        assert_ok_radix::<U0F16>("0.FFFF7", 16, 0xFFFF);
        assert_err_radix::<U0F16>("0.FFFF8", 16, ParseErrorKind::Overflow);
        assert_err_radix::<U0F16>("1", 16, ParseErrorKind::Overflow);

        assert_ok_radix::<U8F8>("7F.FF7", 16, 0x7FFF);
        assert_ok_radix::<U8F8>("7F.FF8", 16, 0x8000);
        assert_ok_radix::<U8F8>("FF.FF7", 16, 0xFFFF);
        assert_err_radix::<U8F8>("FF.FF8", 16, ParseErrorKind::Overflow);

        assert_ok_radix::<U16F0>("7FFF.7", 16, 0x7FFF);
        assert_ok_radix::<U16F0>("7FFF.8", 16, 0x8000);
        assert_ok_radix::<U16F0>("FFFF.7", 16, 0xFFFF);
        assert_err_radix::<U16F0>("FFFF.8", 16, ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i64_u64_from_str() {
        assert_err::<I0F64>("-1", ParseErrorKind::Overflow);
        assert_err::<I0F64>("-0.50000000000000000003", ParseErrorKind::Overflow);
        assert_ok::<I0F64>("-0.50000000000000000002", -0x8000_0000_0000_0000);
        assert_ok::<I0F64>("0.49999999999999999997", 0x7FFF_FFFF_FFFF_FFFF);
        assert_err::<I0F64>("0.49999999999999999998", ParseErrorKind::Overflow);
        assert_err::<I0F64>("1", ParseErrorKind::Overflow);

        assert_err::<I32F32>("-2147483648.0000000002", ParseErrorKind::Overflow);
        assert_ok::<I32F32>("-2147483648.0000000001", -0x8000_0000_0000_0000);
        assert_ok::<I32F32>("2147483647.9999999998", 0x7FFF_FFFF_FFFF_FFFF);
        assert_err::<I32F32>("2147483647.9999999999", ParseErrorKind::Overflow);

        assert_err::<I64F0>("-9223372036854775808.5", ParseErrorKind::Overflow);
        assert_ok::<I64F0>(
            "-9223372036854775808.49999999999999999999",
            -0x8000_0000_0000_0000,
        );
        assert_ok::<I64F0>(
            "9223372036854775807.49999999999999999999",
            0x7FFF_FFFF_FFFF_FFFF,
        );
        assert_err::<I64F0>("9223372036854775807.5", ParseErrorKind::Overflow);

        assert_err::<U0F64>("-0", ParseErrorKind::InvalidDigit);
        assert_ok::<U0F64>("0.49999999999999999997", 0x7FFF_FFFF_FFFF_FFFF);
        assert_ok::<U0F64>("0.49999999999999999998", 0x8000_0000_0000_0000);
        assert_ok::<U0F64>("0.99999999999999999997", 0xFFFF_FFFF_FFFF_FFFF);
        assert_err::<U0F64>("0.99999999999999999998", ParseErrorKind::Overflow);
        assert_err::<U0F64>("1", ParseErrorKind::Overflow);

        assert_ok::<U32F32>("2147483647.9999999998", 0x7FFF_FFFF_FFFF_FFFF);
        assert_ok::<U32F32>("2147483647.9999999999", 0x8000_0000_0000_0000);
        assert_ok::<U32F32>("4294967295.9999999998", 0xFFFF_FFFF_FFFF_FFFF);
        assert_err::<U32F32>("4294967295.9999999999", ParseErrorKind::Overflow);

        assert_ok::<U64F0>(
            "9223372036854775807.49999999999999999999",
            0x7FFF_FFFF_FFFF_FFFF,
        );
        assert_ok::<U64F0>("9223372036854775807.5", 0x8000_0000_0000_0000);
        assert_ok::<U64F0>(
            "18446744073709551615.49999999999999999999",
            0xFFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<U64F0>("18446744073709551615.5", ParseErrorKind::Overflow);
    }

    #[test]
    fn check_i128_u128_from_str() {
        assert_err::<I0F128>("-1", ParseErrorKind::Overflow);
        assert_err::<I0F128>(
            "-0.500000000000000000000000000000000000002",
            ParseErrorKind::Overflow,
        );
        assert_ok::<I0F128>(
            "-0.500000000000000000000000000000000000001",
            -0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok::<I0F128>(
            "0.499999999999999999999999999999999999998",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<I0F128>(
            "0.499999999999999999999999999999999999999",
            ParseErrorKind::Overflow,
        );
        assert_err::<I0F128>("1", ParseErrorKind::Overflow);

        assert_err::<I64F64>(
            "-9223372036854775808.00000000000000000003",
            ParseErrorKind::Overflow,
        );
        assert_ok::<I64F64>(
            "-9223372036854775808.00000000000000000002",
            -0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok::<I64F64>(
            "9223372036854775807.99999999999999999997",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<I64F64>(
            "9223372036854775807.99999999999999999998",
            ParseErrorKind::Overflow,
        );

        assert_err::<I128F0>(
            "-170141183460469231731687303715884105728.5",
            ParseErrorKind::Overflow,
        );
        assert_ok::<I128F0>(
            "-170141183460469231731687303715884105728.4999999999999999999999999999999999999999",
            -0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok::<I128F0>(
            "170141183460469231731687303715884105727.4999999999999999999999999999999999999999",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<I128F0>(
            "170141183460469231731687303715884105727.5",
            ParseErrorKind::Overflow,
        );

        assert_err::<U0F128>("-0", ParseErrorKind::InvalidDigit);
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

        assert_ok::<U64F64>(
            "9223372036854775807.99999999999999999997",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_ok::<U64F64>(
            "9223372036854775807.99999999999999999998",
            0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok::<U64F64>(
            "18446744073709551615.99999999999999999997",
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err::<U64F64>(
            "18446744073709551615.99999999999999999998",
            ParseErrorKind::Overflow,
        );

        assert_ok::<U128F0>(
            "170141183460469231731687303715884105727.4999999999999999999999999999999999999999",
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_ok::<U128F0>(
            "170141183460469231731687303715884105727.5",
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

    #[test]
    fn check_i128_u128_from_str_hex() {
        assert_err_radix::<I0F128>("-1", 16, ParseErrorKind::Overflow);
        assert_err_radix::<I0F128>(
            "-0.800000000000000000000000000000008",
            16,
            ParseErrorKind::Overflow,
        );
        assert_ok_radix::<I0F128>(
            "-0.800000000000000000000000000000007",
            16,
            -0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok_radix::<I0F128>(
            "0.7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7",
            16,
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err_radix::<I0F128>(
            "0.7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8",
            16,
            ParseErrorKind::Overflow,
        );
        assert_err_radix::<I0F128>("1", 16, ParseErrorKind::Overflow);

        assert_err_radix::<I64F64>(
            "-8000000000000000.00000000000000008",
            16,
            ParseErrorKind::Overflow,
        );
        assert_ok_radix::<I64F64>(
            "-8000000000000000.00000000000000007",
            16,
            -0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok_radix::<I64F64>(
            "7FFFFFFFFFFFFFFF.FFFFFFFFFFFFFFFF7",
            16,
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err_radix::<I64F64>(
            "7FFFFFFFFFFFFFFF.FFFFFFFFFFFFFFFF8",
            16,
            ParseErrorKind::Overflow,
        );

        assert_err_radix::<I128F0>(
            "-80000000000000000000000000000000.8",
            16,
            ParseErrorKind::Overflow,
        );
        assert_ok_radix::<I128F0>(
            "-80000000000000000000000000000000.7",
            16,
            -0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok_radix::<I128F0>(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF.7",
            16,
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err_radix::<I128F0>(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF.8",
            16,
            ParseErrorKind::Overflow,
        );

        assert_err_radix::<U0F128>("-0", 16, ParseErrorKind::InvalidDigit);
        assert_ok_radix::<U0F128>(
            "0.7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7",
            16,
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_ok_radix::<U0F128>(
            "0.7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8",
            16,
            0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok_radix::<U0F128>(
            "0.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7",
            16,
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err_radix::<U0F128>(
            "0.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8",
            16,
            ParseErrorKind::Overflow,
        );
        assert_err_radix::<U0F128>("1", 16, ParseErrorKind::Overflow);

        assert_ok_radix::<U64F64>(
            "7FFFFFFFFFFFFFFF.FFFFFFFFFFFFFFFF7",
            16,
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_ok_radix::<U64F64>(
            "7FFFFFFFFFFFFFFF.FFFFFFFFFFFFFFFF8",
            16,
            0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok_radix::<U64F64>(
            "FFFFFFFFFFFFFFFF.FFFFFFFFFFFFFFFF7",
            16,
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err_radix::<U64F64>(
            "FFFFFFFFFFFFFFFF.FFFFFFFFFFFFFFFF8",
            16,
            ParseErrorKind::Overflow,
        );

        assert_ok_radix::<U128F0>(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF.7",
            16,
            0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_ok_radix::<U128F0>(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF.8",
            16,
            0x8000_0000_0000_0000_0000_0000_0000_0000,
        );
        assert_ok_radix::<U128F0>(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF.7",
            16,
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        );
        assert_err_radix::<U128F0>(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF.8",
            16,
            ParseErrorKind::Overflow,
        );
    }

    struct Fractions {
        zero: String,
        eps: String,
        one_minus_eps: String,
        one: String,
    }
    fn without_last(a: &str) -> &str {
        &a[..a.len() - 1]
    }
    fn make_fraction_strings(prefix: &str, eps_frac: &str) -> Fractions {
        let eps_frac_compl: String = eps_frac
            .chars()
            .map(|digit| (b'0' + b'9' - digit as u8) as char)
            .collect();
        let eps_frac_compl = String::from(without_last(&eps_frac_compl)) + "5";

        let zero = String::from("0.") + without_last(&eps_frac) + "499999";
        let eps = String::from("0.") + eps_frac;
        let one_minus_eps = String::from(prefix) + without_last(&eps_frac_compl) + "499999";
        let one = String::from(prefix) + &eps_frac_compl;
        Fractions {
            zero,
            eps,
            one_minus_eps,
            one,
        }
    }

    // check that for example for four fractional bits,
    //   * 0.0312499999 (just below 1/32) is parsed as 0 and
    //   * 0.03125 (exactly 1/32) is parsed as 0.0625 (1/16)
    #[test]
    fn check_exact_decimal() {
        let prefix0 = String::from("0.");
        let prefix4 = String::from("15.");
        let prefix8 = format!("{}.", !0u8);
        let prefix16 = format!("{}.", !0u16);
        let prefix28 = format!("{}.", !0u32 >> 4);
        let prefix32 = format!("{}.", !0u32);
        let prefix64 = format!("{}.", !0u64);
        let prefix124 = format!("{}.", !0u128 >> 4);
        let prefix128 = format!("{}.", !0u128);

        // Note: fractions can be generated with this:
        //
        //     use rug::Integer;
        //     for &i in &[0, 4, 8, 16, 28, 32, 64, 124, 128] {
        //         let eps = Integer::from(Integer::u_pow_u(5, i + 1));
        //         println!("let eps{} = \"{:02$}\";", i, eps, i as usize + 1);
        //     }

        // eps0 = 0.5 >> 0 = 0.5
        // eps4 = 0.5 >> 4 = 0.03125
        // eps8 = 0.5 >> 8 = 0.001953125
        // etc.
        let eps0 = "5";
        let eps4 = "03125";
        let eps8 = "001953125";
        let eps16 = "00000762939453125";
        let eps28 = "00000000186264514923095703125";
        let eps32 = "000000000116415321826934814453125";
        let eps64 = "00000000000000000002710505431213761085018632002174854278564453125";
        let eps124 = "0000000000000000000000000000000000000235098870164457501593747307\
                      4444491355637331113544175043017503412556834518909454345703125";
        let eps128 = "0000000000000000000000000000000000000014693679385278593849609206\
                      71527807097273331945965109401885939632848021574318408966064453125";

        let frac_0_8 = make_fraction_strings(&prefix0, eps8);
        assert_ok::<U0F8>(&frac_0_8.zero, 0);
        assert_ok::<U0F8>(&frac_0_8.eps, 1);
        assert_ok::<U0F8>(&frac_0_8.one_minus_eps, !0);
        assert_err::<U0F8>(&frac_0_8.one, ParseErrorKind::Overflow);

        let frac_4_4 = make_fraction_strings(&prefix4, eps4);
        assert_ok::<U4F4>(&frac_4_4.zero, 0);
        assert_ok::<U4F4>(&frac_4_4.eps, 1);
        assert_ok::<U4F4>(&frac_4_4.one_minus_eps, !0);
        assert_err::<U4F4>(&frac_4_4.one, ParseErrorKind::Overflow);

        let frac_8_0 = make_fraction_strings(&prefix8, eps0);
        assert_ok::<U8F0>(&frac_8_0.zero, 0);
        assert_ok::<U8F0>(&frac_8_0.eps, 1);
        assert_ok::<U8F0>(&frac_8_0.one_minus_eps, !0);
        assert_err::<U8F0>(&frac_8_0.one, ParseErrorKind::Overflow);

        let frac_0_32 = make_fraction_strings(&prefix0, eps32);
        assert_ok::<U0F32>(&frac_0_32.zero, 0);
        assert_ok::<U0F32>(&frac_0_32.eps, 1);
        assert_ok::<U0F32>(&frac_0_32.one_minus_eps, !0);
        assert_err::<U0F32>(&frac_0_32.one, ParseErrorKind::Overflow);

        let frac_4_28 = make_fraction_strings(&prefix4, eps28);
        assert_ok::<U4F28>(&frac_4_28.zero, 0);
        assert_ok::<U4F28>(&frac_4_28.eps, 1);
        assert_ok::<U4F28>(&frac_4_28.one_minus_eps, !0);
        assert_err::<U4F28>(&frac_4_28.one, ParseErrorKind::Overflow);

        let frac_16_16 = make_fraction_strings(&prefix16, eps16);
        assert_ok::<U16F16>(&frac_16_16.zero, 0);
        assert_ok::<U16F16>(&frac_16_16.eps, 1);
        assert_ok::<U16F16>(&frac_16_16.one_minus_eps, !0);
        assert_err::<U16F16>(&frac_16_16.one, ParseErrorKind::Overflow);

        let frac_28_4 = make_fraction_strings(&prefix28, eps4);
        assert_ok::<U28F4>(&frac_28_4.zero, 0);
        assert_ok::<U28F4>(&frac_28_4.eps, 1);
        assert_ok::<U28F4>(&frac_28_4.one_minus_eps, !0);
        assert_err::<U28F4>(&frac_28_4.one, ParseErrorKind::Overflow);

        let frac_32_0 = make_fraction_strings(&prefix32, eps0);
        assert_ok::<U32F0>(&frac_32_0.zero, 0);
        assert_ok::<U32F0>(&frac_32_0.eps, 1);
        assert_ok::<U32F0>(&frac_32_0.one_minus_eps, !0);
        assert_err::<U32F0>(&frac_32_0.one, ParseErrorKind::Overflow);

        let frac_0_128 = make_fraction_strings(&prefix0, eps128);
        assert_ok::<U0F128>(&frac_0_128.zero, 0);
        assert_ok::<U0F128>(&frac_0_128.eps, 1);
        assert_ok::<U0F128>(&frac_0_128.one_minus_eps, !0);
        assert_err::<U0F128>(&frac_0_128.one, ParseErrorKind::Overflow);

        let frac_4_124 = make_fraction_strings(&prefix4, eps124);
        assert_ok::<U4F124>(&frac_4_124.zero, 0);
        assert_ok::<U4F124>(&frac_4_124.eps, 1);
        assert_ok::<U4F124>(&frac_4_124.one_minus_eps, !0);
        assert_err::<U4F124>(&frac_4_124.one, ParseErrorKind::Overflow);

        let frac_64_64 = make_fraction_strings(&prefix64, eps64);
        assert_ok::<U64F64>(&frac_64_64.zero, 0);
        assert_ok::<U64F64>(&frac_64_64.eps, 1);
        assert_ok::<U64F64>(&frac_64_64.one_minus_eps, !0);
        assert_err::<U64F64>(&frac_64_64.one, ParseErrorKind::Overflow);

        let frac_124_4 = make_fraction_strings(&prefix124, eps4);
        assert_ok::<U124F4>(&frac_124_4.zero, 0);
        assert_ok::<U124F4>(&frac_124_4.eps, 1);
        assert_ok::<U124F4>(&frac_124_4.one_minus_eps, !0);
        assert_err::<U124F4>(&frac_124_4.one, ParseErrorKind::Overflow);

        let frac_128_0 = make_fraction_strings(&prefix128, eps0);
        assert_ok::<U128F0>(&frac_128_0.zero, 0);
        assert_ok::<U128F0>(&frac_128_0.eps, 1);
        assert_ok::<U128F0>(&frac_128_0.one_minus_eps, !0);
        assert_err::<U128F0>(&frac_128_0.one, ParseErrorKind::Overflow);
    }
}
