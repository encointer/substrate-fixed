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
    frac::False,
    helpers::IntHelper,
    traits::Fixed,
    types::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    cmp::{self, Ordering},
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
    #[inline]
    fn digit_bits(self) -> u32 {
        match self {
            Radix2::Bin => 1,
            Radix2::Oct => 3,
            Radix2::LowHex => 4,
            Radix2::UpHex => 4,
        }
    }
    #[inline]
    fn prefix(self) -> &'static str {
        match self {
            Radix2::Bin => "0b",
            Radix2::Oct => "0o",
            Radix2::LowHex => "0x",
            Radix2::UpHex => "0x",
        }
    }
    #[inline]
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
    let int_digit_mask = !(!I::ZERO << digit_bits);
    // 128 binary digits, one radix point, one leading zero.
    // The leading zero has two purposes:
    //  1. If there are no integer bits, we still want to print "0." instead of ".".
    //  2. If rounding causes a carry, we can carry into this extra zero.
    let mut buf = [0u8; 130];

    // buf[1..int_digits + 1] => significant integer digits (could be b"")
    let int_digits = ((I::NBITS - int.leading_zeros() + digit_bits - 1) / digit_bits) as usize;
    for b in buf[1..int_digits + 1].iter_mut().rev() {
        *b = (int & int_digit_mask).lower_byte();
        int = int >> digit_bits;
    }

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
    let least_significant_index = if frac_digits > 0 {
        int_digits + frac_digits + 1
    } else {
        int_digits
    };
    let round_up = frac > I::MSB || (frac == I::MSB && buf[least_significant_index].is_odd());
    if round_up {
        for b in buf[0..int_digits + frac_digits + 2].iter_mut().rev() {
            if *b < int_digit_mask.lower_byte() {
                *b += 1;
                break;
            }
            if *b == b'.' {
                continue;
            }
            *b = 0;
            if frac_digits > 0 {
                frac_digits -= 1;
            }
        }
    }
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

#[inline]
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

#[inline]
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

fn dec_int_digits(int_bits: u32) -> u32 {
    assert!(int_bits < 299);
    if int_bits == 0 {
        return 0;
    }
    let i = if int_bits >= 196 {
        12
    } else if int_bits >= 103 {
        11
    } else {
        10
    };
    (int_bits * 3 + i) / 10
}

fn dec_frac_digits(frac_bits: u32) -> u32 {
    assert!(frac_bits < 299);
    let i = if frac_bits >= 196 {
        12
    } else if frac_bits >= 103 {
        11
    } else {
        10
    };
    (frac_bits * 3 + i) / 10
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

macro_rules! fmt_dec_helper {
    ($($UInner:ty)*) => { $(
        impl FmtDecHelper for $UInner {
            #[inline]
            fn take_int_digit(&mut self) -> u8 {
                let ret = (*self % 10) as u8;
                *self /= 10;
                ret
            }

            #[inline]
            fn take_frac_digit(&mut self) -> u8 {
                self.mul10_assign()
            }
        }
    )* };
}

fmt_dec_helper! { u8 u16 u32 u64 u128 }

fn fmt_dec_helper<F: FmtDecHelper>(
    frac_bits: u32,
    (is_neg, mut int, mut frac): (bool, F, F),
    fmt: &mut Formatter,
) -> FmtResult {
    let int_bits = F::NBITS - frac_bits;
    // 40 int digits
    // + 128 frac digits
    // + 1 dec point,
    // + 1 leading zero or padding for carry due to rounding up,
    // = 170
    let mut buf: [u8; 170] = [0; 170];
    let max_int_digits = dec_int_digits(int_bits);
    let req_frac_digits = dec_frac_digits(frac_bits);
    // precision is limited to frac bits, which would always print
    // exact non-rounded number anyway
    let frac_digits = if let Some(prec) = fmt.precision().map(|x| x as u32) {
        if prec > frac_bits {
            frac_bits
        } else {
            prec
        }
    } else {
        req_frac_digits
    };
    let mut int_start;
    let frac_start;
    if max_int_digits == 0 {
        buf[0] = b'0';
        buf[1] = b'.';
        int_start = 0;
        frac_start = 2;
    } else {
        // pad by one in case rounding results in another digit
        int_start = max_int_digits + 1;
        buf[int_start as usize] = b'.';
        frac_start = int_start + 1;
        for r in buf[1..int_start as usize].iter_mut().rev() {
            *r = b'0' + int.take_int_digit();
            int_start -= 1;
            if int == F::ZERO {
                break;
            }
        }
    }
    let end;
    if frac_digits == 0 {
        end = frac_start - 1;
    } else {
        end = frac_start + frac_digits;
        for r in buf[frac_start as usize..end as usize].iter_mut() {
            *r = b'0' + frac.take_frac_digit();
        }
        // check for rounding up
        let round_up = match frac.cmp(&F::MSB) {
            Ordering::Less => false,
            Ordering::Greater => true,
            Ordering::Equal => {
                let last_digit = buf[(end - 1) as usize];
                debug_assert!(b'0' <= last_digit && last_digit <= b'9');
                // round up only if odd, so that we round to even
                (last_digit & 1) != 0
            }
        };
        if round_up {
            let mut done = false;
            for r in buf[int_start as usize..end as usize].iter_mut().rev() {
                if *r == b'9' {
                    *r = b'0';
                } else if *r != b'.' {
                    *r += 1;
                    done = true;
                    break;
                }
            }
            if !done {
                int_start -= 1;
                buf[int_start as usize] = b'1';
            }
        }
    }
    let buf = str::from_utf8(&buf[int_start as usize..end as usize]).unwrap();
    fmt.pad_integral(!is_neg, "", buf)
}

#[inline]
fn fmt_dec<F: Fixed>(num: F, fmt: &mut Formatter) -> FmtResult
where
    F::Bits: IntHelper,
    <F::Bits as IntHelper>::Unsigned: FmtDecHelper,
{
    fmt_dec_helper(F::frac_nbits(), parts(num), fmt)
}

#[cfg(test)]
mod tests {
    use crate::{frac::Unsigned, *};
    use std::{
        fmt::{Debug, Error as FmtError, Formatter, Result as FmtResult, Write},
        format, mem,
        string::String,
    };

    struct Buf([u8; 256]);
    impl Buf {
        fn new() -> Buf {
            Buf([0u8; 256])
        }
        fn target(&mut self) -> BufSlice {
            BufSlice(&mut self.0)
        }
    }

    struct BufSlice<'a>(&'a mut [u8]);

    impl<'a> Write for BufSlice<'a> {
        fn write_str(&mut self, s: &str) -> FmtResult {
            let s_len = s.len();
            if s_len > self.0.len() {
                Err(FmtError)
            } else {
                self.0[..s_len].copy_from_slice(s.as_bytes());
                let rem = mem::replace(&mut self.0, &mut []);
                self.0 = &mut rem[s_len..];
                Ok(())
            }
        }
    }

    impl Eq for Buf {}

    impl PartialEq<Buf> for Buf {
        fn eq(&self, rhs: &Buf) -> bool {
            self.0.iter().zip(rhs.0.iter()).all(|(a, b)| a == b)
        }
    }

    impl Debug for Buf {
        fn fmt(&self, f: &mut Formatter) -> FmtResult {
            f.write_str("\"")?;
            for &i in &self.0[..] {
                if i == 0 {
                    break;
                } else if i < 0x20 || i > 0x7f {
                    write!(f, "\\x{:02x}", i)?;
                } else {
                    f.write_char(i as char)?;
                }
            }
            f.write_str("\"")
        }
    }

    macro_rules! assert_eq_fmt {
        (($f1:expr, $($arg1:tt)*), ($f2:expr, $($arg2:tt)*)) => {{
            let mut buf1 = Buf::new();
            write!(buf1.target(), $f1, $($arg1)*).unwrap();
            let mut buf2 = Buf::new();
            write!(buf2.target(), $f2, $($arg2)*).unwrap();
            assert_eq!(buf1, buf2);
        }};
    }

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
        match x.find('.') {
            Some(point) => match frac_digits.checked_sub(x.len() - point - 1) {
                Some(additional) => {
                    x.reserve(additional);
                    for _ in 0..additional {
                        x.push('0');
                    }
                }
                None => {}
            },
            None => {
                x.reserve(frac_digits + 1);
                x.push('.');
                for _ in 0..frac_digits {
                    x.push('0');
                }
            }
        }
    }

    #[test]
    fn hex() {
        use crate::frac::U7 as Frac;
        let frac = Frac::U32;
        for i in 0..(1u32 << frac) {
            let p = 0x1234_5678_9abc_def0u64 ^ u64::from(i);
            let n = -0x1234_5678_9abc_def0i64 ^ i64::from(i);
            let f_p = FixedU64::<Frac>::from_bits(p);
            let f_n = FixedI64::<Frac>::from_bits(n);
            let mut check_p = format!("{:x}.{:02x}", p >> frac, (p & 0x7f) << 1);
            up_frac_digits(&mut check_p, 1000);
            let trimmed_p = trim_frac_zeros(&check_p);
            let mut check_n = format!("-{:x}.{:02x}", n.abs() >> frac, (n.abs() & 0x7f) << 1);
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
        use crate::frac::U7 as Frac;
        let frac = Frac::U32;
        for i in 0..(1 << frac) {
            let bits = !0u32 ^ i;
            let flt = f64::from(bits) / f64::from(frac).exp2();
            let fix = FixedU32::<Frac>::from_bits(bits);
            assert_eq_fmt!(("{}", fix), ("{:.3}", flt));
        }
    }

    #[test]
    fn display_frac() {
        use crate::types::{I0F128, I0F16, I0F32, I0F64, I0F8, U0F128, U0F16, U0F32, U0F64, U0F8};
        assert_eq_fmt!(
            ("{:X}", I0F128::from_bits(!0)),
            ("{}", "-0.00000000000000000000000000000001")
        );
        assert_eq_fmt!(
            ("{:X}", I0F64::from_bits(!0)),
            ("{}", "-0.0000000000000001")
        );
        assert_eq_fmt!(("{:X}", I0F32::from_bits(!0)), ("{}", "-0.00000001"));
        assert_eq_fmt!(("{:X}", I0F16::from_bits(!0)), ("{}", "-0.0001"));
        assert_eq_fmt!(("{:X}", I0F8::from_bits(!0)), ("{}", "-0.01"));
        assert_eq_fmt!(
            ("{:X}", U0F128::from_bits(!0)),
            ("{}", "0.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
        );
        assert_eq_fmt!(("{:X}", U0F64::from_bits(!0)), ("{}", "0.FFFFFFFFFFFFFFFF"));
        assert_eq_fmt!(("{:X}", U0F32::from_bits(!0)), ("{}", "0.FFFFFFFF"));
        assert_eq_fmt!(("{:X}", U0F16::from_bits(!0)), ("{}", "0.FFFF"));
        assert_eq_fmt!(("{:X}", U0F8::from_bits(!0)), ("{}", "0.FF"));

        assert_eq_fmt!(
            ("{}", I0F128::from_bits(!0)),
            ("{}", "-0.000000000000000000000000000000000000003")
        );
        assert_eq_fmt!(
            ("{}", I0F64::from_bits(!0)),
            ("{}", "-0.00000000000000000005")
        );
        assert_eq_fmt!(("{}", I0F32::from_bits(!0)), ("{}", "-0.0000000002"));
        assert_eq_fmt!(("{}", I0F16::from_bits(!0)), ("{}", "-0.00002"));
        assert_eq_fmt!(("{}", I0F8::from_bits(!0)), ("{}", "-0.004"));
        assert_eq_fmt!(
            ("{}", U0F128::from_bits(!0)),
            ("{}", "0.999999999999999999999999999999999999997")
        );
        assert_eq_fmt!(
            ("{}", U0F64::from_bits(!0)),
            ("{}", "0.99999999999999999995")
        );
        assert_eq_fmt!(("{}", U0F32::from_bits(!0)), ("{}", "0.9999999998"));
        assert_eq_fmt!(("{}", U0F16::from_bits(!0)), ("{}", "0.99998"));
        assert_eq_fmt!(("{}", U0F8::from_bits(!0)), ("{}", "0.996"));

        // check overflow issues in <u128 as Mul10>::mul10
        let no_internal_overflow_bits = 0xe666_6666_6666_6665_ffff_ffff_ffff_ffffu128;
        let internal_overflow_bits = 0xe666_6666_6666_6666_ffff_ffff_ffff_ffffu128;
        assert_eq_fmt!(
            ("{:X}", U0F128::from_bits(no_internal_overflow_bits)),
            ("{}", "0.E666666666666665FFFFFFFFFFFFFFFF")
        );
        assert_eq_fmt!(
            ("{:X}", U0F128::from_bits(internal_overflow_bits)),
            ("{}", "0.E666666666666666FFFFFFFFFFFFFFFF")
        );
        assert_eq_fmt!(
            ("{}", U0F128::from_bits(no_internal_overflow_bits)),
            ("{}", "0.899999999999999999978315956550289911317")
        );
        assert_eq_fmt!(
            ("{}", U0F128::from_bits(internal_overflow_bits)),
            ("{}", "0.900000000000000000032526065174565133017")
        );
    }

    fn pow(base: u32, mut exp: u32) -> f64 {
        let mut mult = f64::from(base);
        let mut result = 1.0;
        loop {
            if exp % 2 != 0 {
                result *= mult;
            }
            exp /= 2;
            if exp == 0 {
                break;
            }
            mult *= mult;
        }
        result
    }

    #[test]
    fn dec_int_digits() {
        use super::dec_int_digits;
        assert_eq!(dec_int_digits(0), 0);
        assert_eq!(dec_int_digits(1), 1);
        for int_bits in 2..299 {
            let check = (pow(2, int_bits) - 1.0).log10().ceil() as u32;
            assert_eq!(dec_int_digits(int_bits), check, "int_bits {}", int_bits);
        }
    }

    #[test]
    fn dec_frac_digits() {
        use super::dec_frac_digits;
        for frac_bits in 0..299 {
            let error = 1.0 / pow(10, dec_frac_digits(frac_bits));
            let error_with_one_less_dec_digit = error * 10.0;
            let delta = 1.0 / pow(2, frac_bits);
            assert!(
                error < delta,
                "frac_bits {}, error {:e}, delta {:e}",
                frac_bits,
                error,
                delta
            );
            assert!(
                error_with_one_less_dec_digit >= delta,
                "frac_bits {}, error with one less digit {:e}, delta {:e}",
                frac_bits,
                error_with_one_less_dec_digit,
                delta
            );
        }
    }
}
