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
    from_str::ParseFixedError,
    traits::{Fixed, FixedSigned, ToFixed},
    types::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    fmt::{Display, Formatter, Result as FmtResult},
    iter::{Product, Sum},
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};

/// Provides intentionally wrapped arithmetic on fixed-point numbers.
///
/// The underlying value can be retrieved through the `.0` index.
///
/// # Examples
///
/// ```rust
/// use fixed::{types::I16F16, Wrapping};
/// let max = Wrapping(I16F16::max_value());
/// let delta = Wrapping(I16F16::from_bits(1));
/// assert_eq!(I16F16::min_value(), (max + delta).0);
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, Default, Hash, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Wrapping<F>(pub F);

impl<F: Fixed> Wrapping<F> {
    /// Wrapping conversion from another number.
    ///
    /// The other number can be:
    ///
    ///   * A fixed-point number. Any extra fractional bits are truncated.
    ///   * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    ///     [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    ///     [`usize`].
    ///   * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    ///     feature] is enabled, it can also be of type [`f16`]. For this
    ///     conversion, the method rounds to the nearest, with ties rounding
    ///     to even.
    ///   * Any other number `src` for which [`ToFixed`] is implemented, in
    ///     which case this method returns
    ///     <code>[Wrapping][`Wrapping`]([src.wrapping_to_fixed()][`wrapping_to_fixed`])</code>.
    ///
    /// # Panics
    ///
    /// For floating-point numbers, panics if the value is not [finite].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{
    ///     types::{I4F4, I16F16},
    ///     Wrapping,
    /// };
    ///
    /// // 0x1234.5678 wraps into 0x4.5
    /// let src = I16F16::from_bits(0x1234_5678);
    /// let dst = Wrapping::<I4F4>::from_num(src);
    /// assert_eq!(dst, Wrapping(I4F4::from_bits(0x45)));
    ///
    /// // 0x1234 wraps into 0x4.0
    /// let src_int = 0x1234_i32;
    /// let dst_int = Wrapping::<I4F4>::from_num(src_int);
    /// assert_eq!(dst_int, Wrapping(I4F4::from_bits(0x40)));
    ///
    /// // 129.75 wrapped into 1.75 (binary 1.1100)
    /// let src_float = 129.75;
    /// let dst_float = Wrapping::<I4F4>::from_num(src_float);
    /// assert_eq!(dst_float, Wrapping(I4F4::from_bits(0b11100)));
    /// ```
    ///
    /// [`ToFixed`]: traits/trait.ToFixed.html
    /// [`Wrapping`]: struct.Wrapping.html
    /// [`f16` feature]: index.html#optional-features
    /// [`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
    /// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
    /// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
    /// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
    /// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
    /// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
    /// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
    /// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
    /// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
    /// [`wrapping_to_fixed`]: traits/trait.ToFixed.html#tymethod.wrapping_to_fixed
    /// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
    /// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
    /// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
    /// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
    /// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
    /// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
    /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    pub fn from_num<Src: ToFixed>(src: Src) -> Self {
        Wrapping(src.wrapping_to_fixed())
    }

    /// Converts a string slice containing binary digits to a fixed-point number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I8F8, Wrapping};
    /// let check = Wrapping(I8F8::from_bits(0b1110001 << (8 - 1)));
    /// assert_eq!(Wrapping::<I8F8>::from_str_binary("101100111000.1"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_binary(src: &str) -> Result<Self, ParseFixedError> {
        F::wrapping_from_str_binary(src).map(Wrapping)
    }

    /// Converts a string slice containing octal digits to a fixed-point number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I8F8, Wrapping};
    /// let check = Wrapping(I8F8::from_bits(0o1654 << (8 - 3)));
    /// assert_eq!(Wrapping::<I8F8>::from_str_octal("7165.4"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_octal(src: &str) -> Result<Self, ParseFixedError> {
        F::wrapping_from_str_octal(src).map(Wrapping)
    }

    /// Converts a string slice containing hexadecimal digits to a fixed-point number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I8F8, Wrapping};
    /// let check = Wrapping(I8F8::from_bits(0xFFE));
    /// assert_eq!(Wrapping::<I8F8>::from_str_hex("C0F.FE"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_hex(src: &str) -> Result<Self, ParseFixedError> {
        F::wrapping_from_str_hex(src).map(Wrapping)
    }

    /// Wrapping ceil. Rounds to the next integer towards +∞, wrapping
    /// on overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Wrapping};
    /// let two_half = Wrapping(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.ceil(), Wrapping(I16F16::from_num(3)));
    /// assert_eq!(Wrapping(I16F16::max_value()).ceil(), Wrapping(I16F16::min_value()));
    /// ```
    pub fn ceil(self) -> Wrapping<F> {
        Wrapping(self.0.wrapping_ceil())
    }

    /// Wrapping floor. Rounds to the next integer towards −∞,
    /// wrapping on overflow.
    ///
    /// Overflow can only occur for signed numbers with zero integer
    /// bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{
    ///     types::{I0F32, I16F16},
    ///     Wrapping,
    /// };
    /// let two_half = Wrapping(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.floor(), Wrapping(I16F16::from_num(2)));
    /// assert_eq!(Wrapping(I0F32::min_value()).floor(), Wrapping(I0F32::from_num(0)));
    /// ```
    pub fn floor(self) -> Wrapping<F> {
        Wrapping(self.0.wrapping_floor())
    }

    /// Wrapping round. Rounds to the next integer to the nearest,
    /// with ties rounded away from zero, and wrapping on overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Wrapping};
    /// let two_half = Wrapping(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.round(), Wrapping(I16F16::from_num(3)));
    /// assert_eq!((-two_half).round(), Wrapping(I16F16::from_num(-3)));
    /// assert_eq!(Wrapping(I16F16::max_value()).round(), Wrapping(I16F16::min_value()));
    /// ```
    pub fn round(self) -> Wrapping<F> {
        Wrapping(self.0.wrapping_round())
    }

    /// Wrapping absolute value. Returns the absolute value, wrapping
    /// on overflow.
    ///
    /// Overflow can only occur for signed numbers when trying to find
    /// the absolute value of the minimum value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping(I16F16::from_num(-5)).abs(), Wrapping(I16F16::from_num(5)));
    /// assert_eq!(Wrapping(I16F16::min_value()).abs(), Wrapping(I16F16::min_value()));
    /// ```
    pub fn abs(self) -> Wrapping<F>
    where
        F: FixedSigned,
    {
        Wrapping(self.0.wrapping_abs())
    }
}

impl<F: Fixed> Display for Wrapping<F> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self.0, f)
    }
}

impl<F: Fixed> From<F> for Wrapping<F> {
    #[inline]
    fn from(src: F) -> Wrapping<F> {
        Wrapping(src)
    }
}

impl<F: Fixed> FromStr for Wrapping<F> {
    type Err = ParseFixedError;
    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        F::wrapping_from_str(s).map(Wrapping)
    }
}

macro_rules! op {
    ($wrapping:ident, $Op:ident $op:ident, $OpAssign:ident $op_assign:ident) => {
        impl<F: Fixed> $Op<Wrapping<F>> for Wrapping<F> {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: Wrapping<F>) -> Wrapping<F> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, F: Fixed> $Op<Wrapping<F>> for &'a Wrapping<F> {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: Wrapping<F>) -> Wrapping<F> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, F: Fixed> $Op<&'a Wrapping<F>> for Wrapping<F> {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: &Wrapping<F>) -> Wrapping<F> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<'a, 'b, F: Fixed> $Op<&'a Wrapping<F>> for &'b Wrapping<F> {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: &Wrapping<F>) -> Wrapping<F> {
                Wrapping((self.0).$wrapping(other.0))
            }
        }
        impl<F: Fixed> $OpAssign<Wrapping<F>> for Wrapping<F> {
            #[inline]
            fn $op_assign(&mut self, other: Wrapping<F>) {
                self.0 = (self.0).$wrapping(other.0);
            }
        }
        impl<'a, F: Fixed> $OpAssign<&'a Wrapping<F>> for Wrapping<F> {
            #[inline]
            fn $op_assign(&mut self, other: &Wrapping<F>) {
                self.0 = (self.0).$wrapping(other.0);
            }
        }
    };
}

macro_rules! op_rhs {
    (
        $wrapping:ident($Rhs:ty), $Op:ident $op:ident, $OpAssign:ident $op_assign:ident
    ) => {
        impl<F: Fixed> $Op<$Rhs> for Wrapping<F> {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: $Rhs) -> Wrapping<F> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, F: Fixed> $Op<$Rhs> for &'a Wrapping<F> {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: $Rhs) -> Wrapping<F> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, F: Fixed> $Op<&'a $Rhs> for Wrapping<F> {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: &$Rhs) -> Wrapping<F> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<'a, 'b, F: Fixed> $Op<&'a $Rhs> for &'b Wrapping<F> {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: &$Rhs) -> Wrapping<F> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<F: Fixed> $OpAssign<$Rhs> for Wrapping<F> {
            #[inline]
            fn $op_assign(&mut self, other: $Rhs) {
                self.0 = (self.0).$wrapping(other);
            }
        }
        impl<'a, F: Fixed> $OpAssign<&'a $Rhs> for Wrapping<F> {
            #[inline]
            fn $op_assign(&mut self, other: &$Rhs) {
                self.0 = (self.0).$wrapping(*other);
            }
        }
    };
}

impl<F: Fixed> Neg for Wrapping<F> {
    type Output = Wrapping<F>;
    #[inline]
    fn neg(self) -> Wrapping<F> {
        Wrapping((self.0).wrapping_neg())
    }
}

impl<'a, F: Fixed> Neg for &'a Wrapping<F> {
    type Output = Wrapping<F>;
    #[inline]
    fn neg(self) -> Wrapping<F> {
        Wrapping((self.0).wrapping_neg())
    }
}
op! { wrapping_add, Add add, AddAssign add_assign }
op! { wrapping_sub, Sub sub, SubAssign sub_assign }
op! { wrapping_mul, Mul mul, MulAssign mul_assign }
op! { wrapping_div, Div div, DivAssign div_assign }

impl<F: Fixed> Not for Wrapping<F> {
    type Output = Wrapping<F>;
    #[inline]
    fn not(self) -> Wrapping<F> {
        Wrapping((self.0).not())
    }
}
impl<'a, F: Fixed> Not for &'a Wrapping<F> {
    type Output = Wrapping<F>;
    #[inline]
    fn not(self) -> Wrapping<F> {
        Wrapping((self.0).not())
    }
}
op! { bitand, BitAnd bitand, BitAndAssign bitand_assign }
op! { bitor, BitOr bitor, BitOrAssign bitor_assign }
op! { bitxor, BitXor bitxor, BitXorAssign bitxor_assign }

op_rhs! { wrapping_shl(u32), Shl shl, ShlAssign shl_assign }
op_rhs! { wrapping_shr(u32), Shr shr, ShrAssign shr_assign }

impl<F: Fixed> Sum<Wrapping<F>> for Wrapping<F> {
    fn sum<I>(iter: I) -> Wrapping<F>
    where
        I: Iterator<Item = Wrapping<F>>,
    {
        iter.fold(Wrapping(F::from_num(0)), Add::add)
    }
}

impl<'a, F: 'a + Fixed> Sum<&'a Wrapping<F>> for Wrapping<F> {
    fn sum<I>(iter: I) -> Wrapping<F>
    where
        I: Iterator<Item = &'a Wrapping<F>>,
    {
        iter.fold(Wrapping(F::from_num(0)), Add::add)
    }
}

impl<F: Fixed> Product<Wrapping<F>> for Wrapping<F> {
    fn product<I>(mut iter: I) -> Wrapping<F>
    where
        I: Iterator<Item = Wrapping<F>>,
    {
        match iter.next() {
            None => Wrapping(1.wrapping_to_fixed()),
            Some(first) => iter.fold(first, Mul::mul),
        }
    }
}

impl<'a, F: 'a + Fixed> Product<&'a Wrapping<F>> for Wrapping<F> {
    fn product<I>(mut iter: I) -> Wrapping<F>
    where
        I: Iterator<Item = &'a Wrapping<F>>,
    {
        match iter.next() {
            None => Wrapping(1.wrapping_to_fixed()),
            Some(first) => iter.fold(*first, Mul::mul),
        }
    }
}

// The following cannot be implemented for Wrapping<F> where F: Fixed,
// otherwise there will be a conflicting implementation error, so we
// need to implement on typed direcly.

macro_rules! op_bits {
    (
        $Fixed:ident($LeEqU:ident)::$wrapping:ident,
        $Bits:ident,
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac: $LeEqU> $Op<$Bits> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, Frac: $LeEqU> $Op<$Bits> for &'a Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, Frac: $LeEqU> $Op<&'a $Bits> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<'a, 'b, Frac: $LeEqU> $Op<&'a $Bits> for &'b Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<Frac: $LeEqU> $OpAssign<$Bits> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: $Bits) {
                self.0 = (self.0).$wrapping(other);
            }
        }
        impl<'a, Frac: $LeEqU> $OpAssign<&'a $Bits> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: &$Bits) {
                self.0 = (self.0).$wrapping(*other);
            }
        }
    };
}

macro_rules! ops {
    ($Fixed:ident($LeEqU:ident, $Bits:ident)) => {
        op_bits! { $Fixed($LeEqU)::wrapping_mul_int, $Bits, Mul mul, MulAssign mul_assign }
        op_bits! { $Fixed($LeEqU)::wrapping_div_int, $Bits, Div div, DivAssign div_assign }
        op_bits! { $Fixed($LeEqU)::wrapping_rem_int, $Bits, Rem rem, RemAssign rem_assign }
    };
}
ops! { FixedI8(LeEqU8, i8) }
ops! { FixedI16(LeEqU16, i16) }
ops! { FixedI32(LeEqU32, i32) }
ops! { FixedI64(LeEqU64, i64) }
ops! { FixedI128(LeEqU128, i128) }
ops! { FixedU8(LeEqU8, u8) }
ops! { FixedU16(LeEqU16, u16) }
ops! { FixedU32(LeEqU32, u32) }
ops! { FixedU64(LeEqU64, u64) }
ops! { FixedU128(LeEqU128, u128) }
