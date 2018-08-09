use std::cmp::Ordering;
use std::mem;

use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

pub(crate) trait FixedNum: Copy {
    type Part;
    fn parts(self) -> (bool, Self::Part, Self::Part);
    #[inline(always)]
    fn int_bits() -> u32 {
        mem::size_of::<Self::Part>() as u32 * 8 - Self::frac_bits()
    }
    #[inline(always)]
    fn frac_bits() -> u32 {
        ::F
    }
    fn take_int_digit(int_part: &mut Self::Part, digit_bits: u32) -> u8;
    fn take_frac_digit(frac_part: &mut Self::Part, digit_bits: u32) -> u8;
    fn take_int_dec_digit(int_part: &mut Self::Part) -> u8;
    fn take_frac_dec_digit(int_part: &mut Self::Part) -> u8;
    fn part_is_zero(part: &Self::Part) -> bool;
    fn part_cmp_half(part: &Self::Part) -> Ordering;
}

macro_rules! fixed_num_common {
    ($Fixed:ident($Part:ty); $($rem:tt)+) => {
        impl FixedNum for $Fixed {
            type Part = $Part;

            $($rem)+

            #[inline]
            fn take_int_digit(int_part: &mut $Part, digit_bits: u32) -> u8 {
                let mask = (1 << digit_bits) - 1;
                let ret = (*int_part & mask) as u8;
                *int_part >>= digit_bits;
                ret
            }

            #[inline]
            fn take_frac_digit(frac_part: &mut $Part, digit_bits: u32) -> u8 {
                let rem_bits = mem::size_of::<$Part>() as u32 * 8 - digit_bits;
                let mask = !0 << rem_bits;
                let ret = ((*frac_part & mask) >> rem_bits) as u8;
                *frac_part <<= digit_bits;
                ret
            }

            #[inline]
            fn take_int_dec_digit(int_part: &mut $Part) -> u8 {
                println!("int part {}", int_part);
                let ret = (*int_part % 10) as u8;
                *int_part /= 10;
                ret
            }

            #[inline]
            fn take_frac_dec_digit(frac_part: &mut $Part) -> u8 {
                let next = frac_part.wrapping_mul(10);
                let ret = ((*frac_part - next / 10) / (!0 / 10)) as u8;
                *frac_part = next;
                ret
            }

            #[inline]
            fn part_is_zero(part: &$Part) -> bool {
                *part == 0
            }

            #[inline]
            fn part_cmp_half(part: &$Part) -> Ordering {
                part.cmp(&!(!0 >> 1))
            }
        }
    };
}

macro_rules! fixed_num_unsigned {
    ($Fixed:ident($Part:ty)) => {
        fixed_num_common! {
            $Fixed($Part);
            #[inline]
            fn parts(self) -> (bool, $Part, $Part) {
                let bits = self.to_bits();
                let int_bits = <$Fixed as FixedNum>::int_bits();
                let frac_bits = <$Fixed as FixedNum>::frac_bits();
                let int_part = if int_bits == 0 { 0 } else { bits >> frac_bits };
                let frac_part = if frac_bits == 0 { 0 } else { bits << int_bits };
                (false, int_part, frac_part)
            }
        }
    };
}

macro_rules! fixed_num_signed {
    ($Fixed:ident($Part:ty)) => {
        fixed_num_common! {
            $Fixed($Part);
            #[inline]
            fn parts(self) -> (bool, $Part, $Part) {
                let bits = self.to_bits().wrapping_abs() as $Part;
                let int_bits = <$Fixed as FixedNum>::int_bits();
                let frac_bits = <$Fixed as FixedNum>::frac_bits();
                let int_part = if int_bits == 0 { 0 } else { bits >> frac_bits };
                let frac_part = if frac_bits == 0 { 0 } else { bits << int_bits };
                (self.0 < 0, int_part,frac_part)
            }
        }
    };
}

fixed_num_unsigned! { FixedU8(u8) }
fixed_num_unsigned! { FixedU16(u16) }
fixed_num_unsigned! { FixedU32(u32) }
fixed_num_unsigned! { FixedU64(u64) }
fixed_num_unsigned! { FixedU128(u128) }
fixed_num_signed! { FixedI8(u8) }
fixed_num_signed! { FixedI16(u16) }
fixed_num_signed! { FixedI32(u32) }
fixed_num_signed! { FixedI64(u64) }
fixed_num_signed! { FixedI128(u128) }
