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
    helpers::IntHelper,
    traits::Fixed,
    types::extra::{False, LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    cmp::{self},
    fmt::{
        Alignment, Binary, Debug, Display, Formatter, LowerHex, Octal, Result as FmtResult,
        UpperHex,
    },
    mem, str,
};

fn pad(
    is_neg: bool,
    maybe_prefix: &str,
    abs: &str,
    end_zeros: usize,
    fmt: &mut Formatter,
) -> FmtResult {
    use core::fmt::Write;
    let sign = if is_neg {
        "-"
    } else if fmt.sign_plus() {
        "+"
    } else {
        ""
    };
    let prefix = if fmt.alternate() { maybe_prefix } else { "" };
    let req_width = sign.len() + prefix.len() + abs.len() + end_zeros;
    let pad = fmt
        .width()
        .and_then(|w| w.checked_sub(req_width))
        .unwrap_or(0);
    let (pad_left, pad_zeros, pad_right) = if fmt.sign_aware_zero_pad() {
        (0, pad, 0)
    } else {
        match fmt.align() {
            Some(Alignment::Left) => (0, 0, pad),
            Some(Alignment::Center) => (pad / 2, 0, pad - pad / 2),
            None | Some(Alignment::Right) => (pad, 0, 0),
        }
    };
    let fill = fmt.fill();
    for _ in 0..pad_left {
        fmt.write_char(fill)?;
    }
    fmt.write_str(sign)?;
    fmt.write_str(prefix)?;
    for _ in 0..pad_zeros {
        fmt.write_char('0')?;
    }
    fmt.write_str(abs)?;
    for _ in 0..end_zeros {
        fmt.write_char('0')?;
    }
    for _ in 0..pad_right {
        fmt.write_char(fill)?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum Radix2 {
    Bin,
    Oct,
    LowHex,
    UpHex,
}
impl Radix2 {
    fn digit_bits(self) -> u32 {
        match self {
            Radix2::Bin => 1,
            Radix2::Oct => 3,
            Radix2::LowHex => 4,
            Radix2::UpHex => 4,
        }
    }
    fn prefix(self) -> &'static str {
        match self {
            Radix2::Bin => "0b",
            Radix2::Oct => "0o",
            Radix2::LowHex => "0x",
            Radix2::UpHex => "0x",
        }
    }
    fn encode_digits(self, digits: &mut [u8]) {
        for digit in digits.iter_mut() {
            if *digit < 10 {
                *digit += b'0';
            } else if *digit < 16 {
                match self {
                    Radix2::LowHex => *digit += b'a' - 10,
                    _ => *digit += b'A' - 10,
                }
            }
        }
    }
}

// Returns the number of zeros at the end.
//
// Note that rounding up may cause the number of integer bits to
// increase. This has no effect on the precision argument as the
// precision argument really means digits after the radix point. (And
// also, for rounding to carry through to the most significant digit,
// it would leave a long string of zeros in its wake, resulting in
// something like "1000000" with no precision argument or
// "1000000.000000" with an explicit precision argument.
fn round_up_and_count_trailing_zeros<I>(frac_rem: I, buf: &mut [u8], mut has_frac: bool) -> usize
where
    I: IntHelper<IsSigned = False>,
{
    let mut trailing_zeros = 0;
    if frac_rem > I::MSB || (frac_rem == I::MSB && buf.last().unwrap().is_odd()) {
        for b in buf.iter_mut().rev() {
            if *b < 9 {
                *b += 1;
                break;
            }
            if *b == b'.' {
                has_frac = false;
                continue;
            }
            *b = 0;
            if has_frac {
                trailing_zeros += 1;
            }
        }
    } else if has_frac {
        for b in buf.iter().rev() {
            if *b != 0 {
                break;
            }
            trailing_zeros += 1;
        }
    }
    trailing_zeros
}

fn fmt_radix2_helper<I>(
    (is_neg, mut int, mut frac): (bool, I, I),
    radix: Radix2,
    fmt: &mut Formatter,
) -> FmtResult
where
    I: IntHelper<IsSigned = False>,
{
    let digit_bits = radix.digit_bits();
    let compl_digit_bits = I::NBITS - digit_bits;
    let int_digit_mask = !((!I::ZERO) << digit_bits);
    // 128 binary digits, one radix point, one leading zero.
    // The leading zero has two purposes:
    //  1. If there are no integer bits, we still want to print "0." instead of ".".
    //  2. If rounding causes a carry, we can carry into this extra zero.
    let mut buf = [0u8; 130];

    // buf[1..int_digits + 1] => significant integer digits (could be b"")
    let int_digits = ((I::NBITS - int.leading_zeros() + digit_bits - 1) / digit_bits) as usize;
    for b in buf[1..=int_digits].iter_mut().rev() {
        debug_assert!(int != I::ZERO);
        *b = (int & int_digit_mask).lower_byte();
        int = int >> digit_bits;
    }
    debug_assert!(int == I::ZERO);

    // buf[int_digits + 1..int_digits + 2] => b"."
    buf[int_digits + 1] = b'.';

    // buf[int_digits + 2..int_digits + frac_digits + 2] => fractional digits
    let mut frac_digits =
        ((I::NBITS - frac.trailing_zeros() + digit_bits - 1) / digit_bits) as usize;
    if let Some(precision) = fmt.precision() {
        frac_digits = cmp::min(frac_digits, precision);
    }
    for (i, b) in buf[int_digits + 2..int_digits + frac_digits + 2]
        .iter_mut()
        .enumerate()
    {
        *b = (frac >> compl_digit_bits).lower_byte();
        frac = frac << digit_bits;
        if frac == I::ZERO {
            frac_digits = i + 1;
            break;
        }
    }
    let (has_frac, len) = if frac_digits > 0 {
        (true, int_digits + frac_digits + 2)
    } else {
        (false, int_digits + 1)
    };
    let trailing_zeros = round_up_and_count_trailing_zeros(frac, &mut buf[..len], has_frac);
    frac_digits -= trailing_zeros;
    let end_zeros = fmt.precision().map(|x| x - frac_digits).unwrap_or(0);
    let begin = if buf[0] > 0 || buf[1] == b'.' { 0 } else { 1 };
    let end = if frac_digits > 0 {
        int_digits + frac_digits + 2
    } else if end_zeros > 0 {
        int_digits + 2
    } else {
        int_digits + 1
    };
    let used_buf = &mut buf[begin..end];
    radix.encode_digits(used_buf);
    let str_buf = str::from_utf8(used_buf).unwrap();
    pad(is_neg, radix.prefix(), str_buf, end_zeros, fmt)
}

fn parts<F: Fixed>(
    num: F,
) -> (
    bool,
    <F::Bits as IntHelper>::Unsigned,
    <F::Bits as IntHelper>::Unsigned,
)
where
    F::Bits: IntHelper,
{
    let (neg, abs) = num.to_bits().neg_abs();
    let (int_nbits, frac_nbits) = (F::int_nbits(), F::frac_nbits());
    if int_nbits == 0 {
        (neg, IntHelper::ZERO, abs)
    } else if frac_nbits == 0 {
        (neg, abs, IntHelper::ZERO)
    } else {
        (neg, abs >> frac_nbits, abs << int_nbits)
    }
}

fn fmt_radix2<F: Fixed>(num: F, radix: Radix2, fmt: &mut Formatter) -> FmtResult
where
    F::Bits: IntHelper,
    <F::Bits as IntHelper>::Unsigned: IntHelper<IsSigned = False>,
{
    fmt_radix2_helper(parts(num), radix, fmt)
}

macro_rules! impl_fmt {
    ($Fixed:ident($LeEqU:ident)) => {
        impl<Frac: $LeEqU> Display for $Fixed<Frac> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_dec(*self, f)
            }
        }

        impl<Frac: $LeEqU> Debug for $Fixed<Frac> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_dec(*self, f)
            }
        }

        impl<Frac: $LeEqU> Binary for $Fixed<Frac> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_radix2(*self, Radix2::Bin, f)
            }
        }

        impl<Frac: $LeEqU> Octal for $Fixed<Frac> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_radix2(*self, Radix2::Oct, f)
            }
        }

        impl<Frac: $LeEqU> LowerHex for $Fixed<Frac> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_radix2(*self, Radix2::LowHex, f)
            }
        }

        impl<Frac: $LeEqU> UpperHex for $Fixed<Frac> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_radix2(*self, Radix2::UpHex, f)
            }
        }
    };
}

impl_fmt! { FixedU8(LeEqU8) }
impl_fmt! { FixedU16(LeEqU16) }
impl_fmt! { FixedU32(LeEqU32) }
impl_fmt! { FixedU64(LeEqU64) }
impl_fmt! { FixedU128(LeEqU128) }
impl_fmt! { FixedI8(LeEqU8) }
impl_fmt! { FixedI16(LeEqU16) }
impl_fmt! { FixedI32(LeEqU32) }
impl_fmt! { FixedI64(LeEqU64) }
impl_fmt! { FixedI128(LeEqU128) }

// approximate ceil(i × log_10 2), works up to 13300
fn ceil_log10_2_times(int_bits: u32) -> u32 {
    assert!(int_bits <= 13_300);
    // log_10 2 = 0.301_029_995_664
    (int_bits * 30_103 + 99_999) / 100_000
}

fn encode_decimal_digits(digits: &mut [u8]) {
    for digit in digits.iter_mut() {
        if *digit < 10 {
            *digit += b'0';
        }
    }
}

pub(crate) trait Mul10: Sized {
    fn mul10_assign(&mut self) -> u8;
}
macro_rules! mul10_widen {
    ($Single:ty, $Double:ty) => {
        impl Mul10 for $Single {
            #[inline]
            fn mul10_assign(&mut self) -> u8 {
                const NBITS: usize = 8 * mem::size_of::<$Single>();
                let prod = <$Double>::from(*self) * 10;
                *self = prod as $Single;
                (prod >> NBITS) as u8
            }
        }
    };
}
mul10_widen! { u8, u16 }
mul10_widen! { u16, u32 }
mul10_widen! { u32, u64 }
mul10_widen! { u64, u128 }
impl Mul10 for u128 {
    #[inline]
    fn mul10_assign(&mut self) -> u8 {
        const LO_MASK: u128 = !(!0 << 64);
        let hi = (*self >> 64) * 10;
        let lo = (*self & LO_MASK) * 10;
        // Workaround for https://github.com/rust-lang/rust/issues/63384
        // let (wrapped, overflow) = (hi << 64).overflowing_add(lo);
        // ((hi >> 64) as u8 + u8::from(overflow), wrapped)
        let (hi_lo, hi_hi) = (hi as u64, (hi >> 64) as u64);
        let (lo_lo, lo_hi) = (lo as u64, (lo >> 64) as u64);
        let (wrapped, overflow) = hi_lo.overflowing_add(lo_hi);
        *self = (u128::from(wrapped) << 64) | u128::from(lo_lo);
        hi_hi as u8 + u8::from(overflow)
    }
}

trait FmtDecHelper: IntHelper {
    fn take_int_digit(&mut self) -> u8;
    fn take_frac_digit(&mut self) -> u8;
}

fn fmt_dec_helper<I>(
    frac_nbits: u32,
    (is_neg, mut int, mut frac): (bool, I, I),
    fmt: &mut Formatter,
) -> FmtResult
where
    I: IntHelper<IsSigned = False> + Mul10 + From<u8>,
{
    // For integer part, one decimal digit is always enough for one bit.
    // For fractional part, the same holds as 10 is a multiple of 2.
    // We need a maximum 128 digits, one decimal point, one leading zero.
    // The leading zero has two purposes:
    //  1. If there are no integer bits, we still want to print "0." instead of ".".
    //  2. If rounding causes a carry, we can carry into this extra zero.
    let mut buf = [0u8; 130];

    // buf[1..int_digits + 1 ] => significant integer digits (could be b"")
    let int_digits = ceil_log10_2_times(I::NBITS - int.leading_zeros()) as usize;
    for b in buf[1..=int_digits].iter_mut().rev() {
        debug_assert!(int != I::ZERO);
        *b = (int % I::from(10)).lower_byte();
        int = int / I::from(10);
    }
    debug_assert!(int == I::ZERO);

    // buf[int_digits + 1..int_digits + 2] => b"."
    buf[int_digits + 1] = b'.';

    // buf[int_digits + 2..int_digits + frac_digits + 2] => fractional digits
    let precision = fmt.precision();
    let mut frac_digits = if let Some(precision) = precision {
        let significant = (I::NBITS - frac.trailing_zeros()) as usize;
        cmp::min(significant, precision)
    } else {
        ceil_log10_2_times(frac_nbits) as usize
    };
    // add_5 is to add rounding when all bits are used
    let (mut boundary, mut add_5) = if frac_nbits == I::NBITS {
        (I::ZERO, true)
    } else {
        ((I::from(1) << (I::NBITS - frac_nbits - 1)), false)
    };
    for (i, b) in buf[int_digits + 2..int_digits + frac_digits + 2]
        .iter_mut()
        .enumerate()
    {
        *b = frac.mul10_assign();

        // Check if very close to zero, to avoid things like 0.19999999 and 0.20000001.
        // This takes place even if we have a precision.
        if frac < I::from(10) || frac.wrapping_neg() < I::from(10) {
            frac_digits = i + 1;
            break;
        }

        // in last digit, check will overflow so that mul10_assign() returns non-zero
        if precision.is_none() {
            let boundary_overflow = boundary.mul10_assign();
            if add_5 {
                boundary = boundary + I::from(5);
                add_5 = false;
            }
            debug_assert!(boundary_overflow == 0 || frac_digits == i + 1);
            let _ = boundary_overflow;
            // if boundary_overflow, the following condition has no
            // effect, so we don't care whether it's taken or not
            if frac < boundary || frac.wrapping_neg() < boundary {
                frac_digits = i + 1;
                break;
            }
        }
    }
    let (has_frac, len) = if frac_digits > 0 {
        (true, int_digits + frac_digits + 2)
    } else {
        (false, int_digits + 1)
    };
    let trailing_zeros = round_up_and_count_trailing_zeros(frac, &mut buf[..len], has_frac);
    frac_digits -= trailing_zeros;
    let end_zeros = fmt.precision().map(|x| x - frac_digits).unwrap_or(0);
    let begin = if buf[0] > 0 || buf[1] == b'.' { 0 } else { 1 };
    let end = if frac_digits > 0 {
        int_digits + frac_digits + 2
    } else if end_zeros > 0 {
        int_digits + 2
    } else {
        int_digits + 1
    };
    let used_buf = &mut buf[begin..end];
    encode_decimal_digits(used_buf);
    let str_buf = str::from_utf8(used_buf).unwrap();
    pad(is_neg, "", str_buf, end_zeros, fmt)
}

fn fmt_dec<F: Fixed>(num: F, fmt: &mut Formatter) -> FmtResult
where
    F::Bits: IntHelper,
    <F::Bits as IntHelper>::Unsigned: IntHelper<IsSigned = False> + Mul10 + From<u8>,
{
    fmt_dec_helper(F::frac_nbits(), parts(num), fmt)
}

#[allow(clippy::float_cmp)]
#[cfg(test)]
mod tests {
    use crate::types::*;
    use std::{format, string::String};

    fn trim_frac_zeros(mut x: &str) -> &str {
        while x.ends_with('0') {
            x = &x[..x.len() - 1];
        }
        if x.ends_with('.') {
            x = &x[..x.len() - 1];
        }
        x
    }

    fn up_frac_digits(x: &mut String, frac_digits: usize) {
        if let Some(point) = x.find('.') {
            if let Some(additional) = frac_digits.checked_sub(x.len() - point - 1) {
                x.reserve(additional);
                for _ in 0..additional {
                    x.push('0');
                }
            }
        } else {
            x.reserve(frac_digits + 1);
            x.push('.');
            for _ in 0..frac_digits {
                x.push('0');
            }
        }
    }

    #[test]
    fn hex() {
        for i in 0..(1u32 << 7) {
            let p = 0x1234_5678_9abc_def0u64 ^ u64::from(i);
            let n = -0x1234_5678_9abc_def0i64 ^ i64::from(i);
            let f_p = U57F7::from_bits(p);
            let f_n = I57F7::from_bits(n);
            let mut check_p = format!("{:x}.{:02x}", p >> 7, (p & 0x7f) << 1);
            up_frac_digits(&mut check_p, 1000);
            let trimmed_p = trim_frac_zeros(&check_p);
            let mut check_n = format!("-{:x}.{:02x}", n.abs() >> 7, (n.abs() & 0x7f) << 1);
            up_frac_digits(&mut check_n, 1000);
            let trimmed_n = trim_frac_zeros(&check_n);
            assert_eq!(format!("{:.1000x}", f_p), check_p);
            assert_eq!(format!("{:x}", f_p), trimmed_p);
            assert_eq!(format!("{:.1000x}", f_n), check_n);
            assert_eq!(format!("{:x}", f_n), trimmed_n);
        }
    }

    #[test]
    fn dec() {
        for i in 0..(1 << 7) {
            // use 24 bits of precision to be like f32
            let bits = (!0u32 >> 8) ^ i;
            let fix = U25F7::from_bits(bits);
            let flt = (bits as f32) / 7f32.exp2();
            assert_eq!(format!("{}", fix), format!("{}", flt));
            assert_eq!(U25F7::from_num(flt), fix);
            assert_eq!(fix.to_num::<f32>(), flt);
        }
    }

    #[test]
    fn display_frac() {
        assert_eq!(
            format!("{:X}", I0F128::from_bits(!0)),
            "-0.00000000000000000000000000000001"
        );
        assert_eq!(format!("{:X}", I0F64::from_bits(!0)), "-0.0000000000000001");
        assert_eq!(format!("{:X}", I0F32::from_bits(!0)), "-0.00000001");
        assert_eq!(format!("{:X}", I0F16::from_bits(!0)), "-0.0001");
        assert_eq!(format!("{:X}", I0F8::from_bits(!0)), "-0.01");
        assert_eq!(
            format!("{:X}", U0F128::from_bits(!0)),
            "0.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
        );
        assert_eq!(format!("{:X}", U0F64::from_bits(!0)), "0.FFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:X}", U0F32::from_bits(!0)), "0.FFFFFFFF");
        assert_eq!(format!("{:X}", U0F16::from_bits(!0)), "0.FFFF");
        assert_eq!(format!("{:X}", U0F8::from_bits(!0)), "0.FF");

        assert_eq!(
            format!("{}", I0F128::from_bits(!0)),
            "-0.000000000000000000000000000000000000003"
        );
        assert_eq!(
            format!("{}", I0F64::from_bits(!0)),
            "-0.00000000000000000005"
        );
        assert_eq!(format!("{}", I0F32::from_bits(!0)), "-0.0000000002");
        assert_eq!(format!("{}", I0F16::from_bits(!0)), "-0.00002");
        assert_eq!(format!("{}", I0F8::from_bits(!0)), "-0.004");
        assert_eq!(
            format!("{}", U0F128::from_bits(!0)),
            "0.999999999999999999999999999999999999997"
        );
        assert_eq!(
            format!("{}", U0F64::from_bits(!0)),
            "0.99999999999999999995"
        );
        assert_eq!(format!("{}", U0F32::from_bits(!0)), "0.9999999998");
        assert_eq!(format!("{}", U0F16::from_bits(!0)), "0.99998");
        assert_eq!(format!("{}", U0F8::from_bits(!0)), "0.996");

        // check overflow issues in <u128 as Mul10>::mul10
        let no_internal_overflow_bits = 0xe666_6666_6666_6665_ffff_ffff_ffff_ffffu128;
        let internal_overflow_bits = 0xe666_6666_6666_6666_ffff_ffff_ffff_ffffu128;
        assert_eq!(
            format!("{:X}", U0F128::from_bits(no_internal_overflow_bits)),
            "0.E666666666666665FFFFFFFFFFFFFFFF"
        );
        assert_eq!(
            format!("{:X}", U0F128::from_bits(internal_overflow_bits)),
            "0.E666666666666666FFFFFFFFFFFFFFFF"
        );
        assert_eq!(
            format!("{}", U0F128::from_bits(no_internal_overflow_bits)),
            "0.899999999999999999978315956550289911317"
        );
        assert_eq!(
            format!("{}", U0F128::from_bits(internal_overflow_bits)),
            "0.900000000000000000032526065174565133017"
        );
    }

    #[test]
    fn close_to_round_decimal() {
        for i in 0..1000u16 {
            // f32 has 24 bits of precision, so we use 1 bit for the
            // integer part to have exactly 23 bits for the fraction
            let float = f32::from(i + 1000) / 1000.;
            let fix = U9F23::from_num(float);
            let check = format!("1.{:03}", i);
            assert_eq!(format!("{}", fix), trim_frac_zeros(&check));
            assert_eq!(format!("{}", fix), format!("{}", float));
            for prec in 0..10 {
                assert_eq!(format!("{:.*}", prec, fix), format!("{:.*}", prec, float));
            }
        }
    }

    #[test]
    fn check_ceil_log10_2_times() {
        use super::ceil_log10_2_times;
        for i in 0..=13_300 {
            let check = (f64::from(i) * 2f64.log10()).ceil() as u32;
            assert_eq!(ceil_log10_2_times(i), check);
        }
    }
}
