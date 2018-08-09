use std::cmp::Ordering;
use std::fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, Result as FmtResult, UpperHex};
use std::str;
use FixedNum;

use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

trait Radix2 {
    const BITS: u8;
    fn radix() -> u8;
    fn prefix() -> &'static str;
    fn digit(val: u8) -> u8;
}

macro_rules! radix2 {
    ($Radix:ident($bits:expr, $prefix:expr), $($range:pat => $inc:expr),+) => {
        struct $Radix;
        impl Radix2 for $Radix {
            const BITS: u8 = $bits;
            #[inline(always)]
            fn radix() -> u8 {
                1 << <$Radix as Radix2>::BITS
            }
            #[inline(always)]
            fn prefix() -> &'static str {
                $prefix
            }
            #[inline]
            fn digit(val: u8) -> u8 {
                match val {
                    $($range => val + $inc,)+
                    _ => unreachable!(),
                }
            }
        }
    };
}

radix2! { Bin(1, "0b"), 0..=1 => b'0' }
radix2! { Oct(3, "0o"), 0..=7 => b'0' }
radix2! { LowHex(4, "0x"), 0..=9 => b'0', 10..=15 => b'a' - 10 }
radix2! { UpHex(4, "0x"), 0..=9 => b'0', 10..=15 => b'A' - 10 }

fn fmt_radix2<F: FixedNum, R: Radix2>(num: F, _radix: R, fmt: &mut Formatter) -> FmtResult {
    let digit_bits: u32 = R::BITS.into();
    let (int_bits, frac_bits) = (F::int_bits(), F::frac_bits());
    let (is_neg, mut int, mut frac) = num.parts();
    // 128 binary digits, one radix point, one leading zero
    let mut buf: [u8; 130] = [0; 130];
    let max_int_digits = (int_bits + digit_bits - 1) / digit_bits;
    let frac_digits = (frac_bits + digit_bits - 1) / digit_bits;
    let mut int_start;
    let frac_start;
    if max_int_digits == 0 {
        buf[0] = b'0';
        buf[1] = b'.';
        int_start = 0;
        frac_start = 2;
    } else {
        int_start = max_int_digits;
        for r in buf[0..max_int_digits as usize].iter_mut().rev() {
            *r = R::digit(F::take_int_digit(&mut int, digit_bits));
            int_start -= 1;
            if F::part_is_zero(&int) {
                break;
            }
        }
        buf[max_int_digits as usize] = b'.';
        frac_start = max_int_digits + 1;
    }
    let end;
    if frac_digits == 0 {
        end = frac_start - 1;
    } else {
        end = frac_start + frac_digits;
        for r in buf[frac_start as usize..end as usize].iter_mut() {
            *r = R::digit(F::take_frac_digit(&mut frac, digit_bits));
        }
    }
    let buf = str::from_utf8(&buf[int_start as usize..end as usize]).unwrap();
    fmt.pad_integral(!is_neg, R::prefix(), buf)
}

macro_rules! impl_fmt {
    ($($Fixed:ident)*) => { $(
        impl Display for $Fixed {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_dec(*self, f)
            }
        }
        impl Debug for $Fixed {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_dec(*self, f)
            }
        }
        impl Binary for $Fixed {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_radix2(*self, Bin, f)
            }
        }
        impl Octal for $Fixed {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_radix2(*self, Oct, f)
            }
        }
        impl LowerHex for $Fixed {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_radix2(*self, LowHex, f)
            }
        }
        impl UpperHex for $Fixed {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                fmt_radix2(*self, UpHex, f)
            }
        }
    )* };
}

impl_fmt!{ FixedU8 FixedU16 FixedU32 FixedU64 FixedU128 }
impl_fmt!{ FixedI8 FixedI16 FixedI32 FixedI64 FixedI128 }

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
    let digits = (int_bits * 3 + i) / 10;

    // check that digits is ceil(log10(2^int_bits - 1)), except when int_bits < 2
    debug_assert!(int_bits < 2 || digits == ((int_bits as f64).exp2() - 1.0).log10().ceil() as u32);

    digits
}

fn dec_frac_digits(frac_bits: u32) -> u32 {
    assert!(frac_bits < 300);
    let i = if frac_bits >= 197 {
        9
    } else if frac_bits >= 104 {
        8
    } else {
        7
    };
    let digits = (frac_bits * 3 + i) / 10;

    // check that error < delta, where
    // error = 0.5 * 10^-digits
    // delta = 2^-frac_bits
    debug_assert!(0.5 * 10f64.powi(0 - digits as i32) < (-(frac_bits as f64)).exp2());
    // check that error with one less digit >= delta
    debug_assert!(0.5 * 10f64.powi(1 - digits as i32) >= (-(frac_bits as f64)).exp2());

    digits
}

fn fmt_dec<F: FixedNum>(num: F, fmt: &mut Formatter) -> FmtResult {
    let (int_bits, frac_bits) = (F::int_bits(), F::frac_bits());
    let (is_neg, mut int, mut frac) = num.parts();
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
            *r = b'0' + F::take_int_dec_digit(&mut int);
            int_start -= 1;
            if F::part_is_zero(&int) {
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
            *r = b'0' + F::take_frac_dec_digit(&mut frac);
        }
        // check for rounding up
        let round_up = match F::part_cmp_half(&frac) {
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

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn hex() {
        for i in 0..128 {
            let p = 0x1234_5678_9abc_def0u64 ^ i as u64;
            let n = -0x1234_5678_9abc_def0i64 ^ i as i64;
            let f_p = FixedU64::from_bits(p);
            let f_n = FixedI64::from_bits(n);
            assert_eq!(
                format!("{:x}", f_p),
                format!("{:x}.{:02x}", p >> 7, (p & 0x7f) << 1)
            );
            assert_eq!(
                format!("{:x}", f_n),
                format!("-{:x}.{:02x}", n.abs() >> 7, (n.abs() & 0x7f) << 1)
            );
        }
    }

    #[test]
    fn dec() {
        for i in 0..128 {
            let bits = !0u32 ^ i;
            let flt = bits as f64 / 128.0;
            let fix = FixedU32::from_bits(bits);
            println!("i is {}", i);
            assert_eq!(format!("{}", fix), format!("{:.2}", flt));
        }
    }
}
