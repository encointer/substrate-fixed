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

#![allow(clippy::suspicious_op_assign_impl)]

use crate::{
    from_str::ParseFixedError,
    traits::{Fixed, FixedSigned, FixedUnsigned, FromFixed, ToFixed},
    types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    fmt::{Display, Formatter, Result as FmtResult},
    iter::{Product, Sum},
    mem,
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
/// use substrate_fixed::{types::I16F16, Wrapping};
/// let max = Wrapping(I16F16::max_value());
/// let delta = Wrapping(I16F16::from_bits(1));
/// assert_eq!(I16F16::min_value(), (max + delta).0);
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, Default, Hash, Debug, Eq, PartialEq, Ord, PartialOrd, scale_info::TypeInfo)]
pub struct Wrapping<F>(pub F);

impl<F: Fixed> Wrapping<F> {
    /// Returns the smallest value that can be represented.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping::<I16F16>::min_value(), Wrapping(I16F16::min_value()));
    /// ```
    #[inline]
    pub fn min_value() -> Wrapping<F> {
        Wrapping(F::min_value())
    }

    /// Returns the largest value that can be represented.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping::<I16F16>::max_value(), Wrapping(I16F16::max_value()));
    /// ```
    #[inline]
    pub fn max_value() -> Wrapping<F> {
        Wrapping(F::max_value())
    }

    /// Returns the number of integer bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping::<I16F16>::int_nbits(), I16F16::int_nbits());
    /// ```
    #[inline]
    pub fn int_nbits() -> u32 {
        F::int_nbits()
    }

    /// Returns the number of fractional bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping::<I16F16>::frac_nbits(), I16F16::frac_nbits());
    /// ```
    #[inline]
    pub fn frac_nbits() -> u32 {
        F::frac_nbits()
    }

    /// Creates a fixed-point number that has a bitwise representation
    /// identical to the given integer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping::<I16F16>::from_bits(0x1C), Wrapping(I16F16::from_bits(0x1C)));
    /// ```
    #[inline]
    pub fn from_bits(bits: F::Bits) -> Wrapping<F> {
        Wrapping(F::from_bits(bits))
    }

    /// Creates an integer that has a bitwise representation identical
    /// to the given fixed-point number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let w = Wrapping(I16F16::from_bits(0x1C));
    /// assert_eq!(w.to_bits(), 0x1C);
    /// ```
    #[inline]
    pub fn to_bits(self) -> F::Bits {
        self.0.to_bits()
    }

    /// Wrapping conversion from another number.
    ///
    /// The other number can be:
    ///
    ///   * A fixed-point number. Any extra fractional bits are truncated.
    ///   * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    ///     [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    ///     [`usize`].
    ///   * A floating-point number of type [`f32`] or [`f64`]. If the
    ///     [`f16` feature] is enabled, it can also be of type [`f16`]
    ///     or [`bf16`]. For this conversion, the method rounds to the
    ///     nearest, with ties rounding to even.
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
    /// use substrate_fixed::{
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
    /// [`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
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
    #[inline]
    pub fn from_num<Src: ToFixed>(src: Src) -> Wrapping<F> {
        Wrapping(src.wrapping_to_fixed())
    }

    /// Converts a fixed-point number to another number, wrapping the
    /// value on overflow.
    ///
    /// The other number can be:
    ///
    ///   * Another fixed-point number. Any extra fractional bits are truncated.
    ///   * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    ///     [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    ///     [`usize`]. Any fractional bits are truncated.
    ///   * A floating-point number of type [`f32`] or [`f64`]. If the
    ///     [`f16` feature] is enabled, it can also be of type [`f16`]
    ///     or [`bf16`]. For this conversion, the method rounds to the
    ///     nearest, with ties rounding to even.
    ///   * Any other type `Dst` for which [`FromFixed`] is implemented, in
    ///     which case this method returns
    ///     [`Dst::wrapping_from_fixed(self.0)`][`wrapping_from_fixed`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{
    ///     types::{I16F16, I2F6, I4F4},
    ///     Wrapping,
    /// };
    ///
    /// // conversion that fits
    /// let src = Wrapping(I4F4::from_num(1.75));
    /// let expected = I16F16::from_num(1.75);
    /// assert_eq!(src.to_num::<I16F16>(), expected);
    ///
    /// // conversion that wraps
    /// let src = Wrapping(I4F4::max_value());
    /// let wrapped = I2F6::from_bits(I2F6::max_value().to_bits() << 2);
    /// assert_eq!(src.to_num::<I2F6>(), wrapped);
    /// ```
    ///
    /// [`FromFixed`]: traits/trait.FromFixed.html
    /// [`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
    /// [`f16` feature]: index.html#optional-features
    /// [`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
    /// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
    /// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
    /// [`wrapping_from_fixed`]: traits/trait.FromFixed.html#tymethod.wrapping_from_fixed
    /// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
    /// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
    /// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
    /// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
    /// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
    /// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
    /// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
    /// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
    /// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
    /// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
    /// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
    /// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
    #[inline]
    pub fn to_num<Dst: FromFixed>(self) -> Dst {
        Dst::wrapping_from_fixed(self.0)
    }

    /// Parses a string slice containing binary digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I8F8, Wrapping};
    /// let check = Wrapping(I8F8::from_bits(0b1110001 << (8 - 1)));
    /// assert_eq!(Wrapping::<I8F8>::from_str_binary("101100111000.1"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_binary(src: &str) -> Result<Wrapping<F>, ParseFixedError> {
        F::wrapping_from_str_binary(src).map(Wrapping)
    }

    /// Parses a string slice containing octal digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I8F8, Wrapping};
    /// let check = Wrapping(I8F8::from_bits(0o1654 << (8 - 3)));
    /// assert_eq!(Wrapping::<I8F8>::from_str_octal("7165.4"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_octal(src: &str) -> Result<Wrapping<F>, ParseFixedError> {
        F::wrapping_from_str_octal(src).map(Wrapping)
    }

    /// Parses a string slice containing hexadecimal digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I8F8, Wrapping};
    /// let check = Wrapping(I8F8::from_bits(0xFFE));
    /// assert_eq!(Wrapping::<I8F8>::from_str_hex("C0F.FE"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_hex(src: &str) -> Result<Wrapping<F>, ParseFixedError> {
        F::wrapping_from_str_hex(src).map(Wrapping)
    }

    /// Returns the integer part.
    ///
    /// Note that since the numbers are stored in two’s complement,
    /// negative numbers with non-zero fractional parts will be
    /// rounded towards −∞, except in the case where there are no
    /// integer bits, for example for the type
    /// <code>[Wrapping][`Wrapping`]&lt;[I0F16][`I0F16`]&gt;</code>,
    /// where the return value is always zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping(I16F16::from_num(12.25)).int(), Wrapping(I16F16::from_num(12)));
    /// assert_eq!(Wrapping(I16F16::from_num(-12.25)).int(), Wrapping(I16F16::from_num(-13)));
    /// ```
    ///
    /// [`I0F16`]: types/type.I0F16.html
    /// [`Wrapping`]: struct.Wrapping.html
    #[inline]
    pub fn int(self) -> Wrapping<F> {
        Wrapping(self.0.int())
    }

    /// Returns the fractional part.
    ///
    /// Note that since the numbers are stored in two’s complement,
    /// the returned fraction will be non-negative for negative
    /// numbers, except in the case where there are no integer bits,
    /// for example for the type
    /// <code>[Wrapping][`Wrapping`]&lt;[I0F16][`I0F16`]&gt;</code>,
    /// where the return value is always equal to `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping(I16F16::from_num(12.25)).frac(), Wrapping(I16F16::from_num(0.25)));
    /// assert_eq!(Wrapping(I16F16::from_num(-12.25)).frac(), Wrapping(I16F16::from_num(0.75)));
    /// ```
    ///
    /// [`I0F16`]: types/type.I0F16.html
    /// [`Wrapping`]: struct.Wrapping.html
    #[inline]
    pub fn frac(self) -> Wrapping<F> {
        Wrapping(self.0.frac())
    }

    /// Rounds to the next integer towards 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let three = Wrapping(I16F16::from_num(3));
    /// assert_eq!(Wrapping(I16F16::from_num(3.9)).round_to_zero(), three);
    /// assert_eq!(Wrapping(I16F16::from_num(-3.9)).round_to_zero(), -three);
    /// ```
    #[inline]
    pub fn round_to_zero(self) -> Wrapping<F> {
        Wrapping(self.0.round_to_zero())
    }

    /// Wrapping ceil. Rounds to the next integer towards +∞, wrapping
    /// on overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let two_half = Wrapping(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.ceil(), Wrapping(I16F16::from_num(3)));
    /// assert_eq!(Wrapping(I16F16::max_value()).ceil(), Wrapping(I16F16::min_value()));
    /// ```
    #[inline]
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
    /// use substrate_fixed::{
    ///     types::{I0F32, I16F16},
    ///     Wrapping,
    /// };
    /// let two_half = Wrapping(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.floor(), Wrapping(I16F16::from_num(2)));
    /// assert_eq!(Wrapping(I0F32::min_value()).floor(), Wrapping(I0F32::from_num(0)));
    /// ```
    #[inline]
    pub fn floor(self) -> Wrapping<F> {
        Wrapping(self.0.wrapping_floor())
    }

    /// Wrapping round. Rounds to the next integer to the nearest,
    /// with ties rounded away from zero, and wrapping on overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let two_half = Wrapping(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.round(), Wrapping(I16F16::from_num(3)));
    /// assert_eq!((-two_half).round(), Wrapping(I16F16::from_num(-3)));
    /// assert_eq!(Wrapping(I16F16::max_value()).round(), Wrapping(I16F16::min_value()));
    /// ```
    #[inline]
    pub fn round(self) -> Wrapping<F> {
        Wrapping(self.0.wrapping_round())
    }

    /// Wrapping round. Rounds to the next integer to the nearest,
    /// with ties rounded to even, and wrapping on overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let two_half = Wrapping(I16F16::from_num(2.5));
    /// assert_eq!(two_half.round_ties_to_even(), Wrapping(I16F16::from_num(2)));
    /// let three_half = Wrapping(I16F16::from_num(3.5));
    /// assert_eq!(three_half.round_ties_to_even(), Wrapping(I16F16::from_num(4)));
    /// let max = Wrapping(I16F16::max_value());
    /// assert_eq!(max.round_ties_to_even(), Wrapping(I16F16::min_value()));
    /// ```
    #[inline]
    pub fn round_ties_to_even(self) -> Wrapping<F> {
        Wrapping(self.0.wrapping_round_ties_to_even())
    }

    /// Returns the number of ones in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let w = Wrapping(I16F16::from_bits(0x00FF_FF00));
    /// assert_eq!(w.count_ones(), w.0.count_ones());
    /// ```
    #[inline]
    pub fn count_ones(self) -> u32 {
        self.0.count_ones()
    }

    /// Returns the number of zeros in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let w = Wrapping(I16F16::from_bits(0x00FF_FF00));
    /// assert_eq!(w.count_zeros(), w.0.count_zeros());
    /// ```
    #[inline]
    pub fn count_zeros(self) -> u32 {
        self.0.count_zeros()
    }

    /// Returns the number of leading zeros in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let w = Wrapping(I16F16::from_bits(0x00FF_FF00));
    /// assert_eq!(w.leading_zeros(), w.0.leading_zeros());
    /// ```
    #[inline]
    pub fn leading_zeros(self) -> u32 {
        self.0.leading_zeros()
    }

    /// Returns the number of trailing zeros in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let w = Wrapping(I16F16::from_bits(0x00FF_FF00));
    /// assert_eq!(w.trailing_zeros(), w.0.trailing_zeros());
    /// ```
    #[inline]
    pub fn trailing_zeros(self) -> u32 {
        self.0.trailing_zeros()
    }

    /// Shifts to the left by `n` bits, wrapping the truncated bits to the right end.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let i = I16F16::from_bits(0x00FF_FF00);
    /// assert_eq!(Wrapping(i).rotate_left(12), Wrapping(i.rotate_left(12)));
    /// ```
    #[inline]
    pub fn rotate_left(self, n: u32) -> Wrapping<F> {
        Wrapping(self.0.rotate_left(n))
    }

    /// Shifts to the right by `n` bits, wrapping the truncated bits to the left end.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let i = I16F16::from_bits(0x00FF_FF00);
    /// assert_eq!(Wrapping(i).rotate_right(12), Wrapping(i.rotate_right(12)));
    /// ```
    #[inline]
    pub fn rotate_right(self, n: u32) -> Wrapping<F> {
        Wrapping(self.0.rotate_right(n))
    }

    /// Euclidean division.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let num = Wrapping(I16F16::from_num(7.5));
    /// let den = Wrapping(I16F16::from_num(2));
    /// assert_eq!(num.div_euclid(den), Wrapping(I16F16::from_num(3)));
    /// let quarter = Wrapping(I16F16::from_num(0.25));
    /// let check = (Wrapping::max_value() * 4i32).round_to_zero();
    /// assert_eq!(Wrapping::max_value().div_euclid(quarter), check);
    /// ```
    #[inline]
    pub fn div_euclid(self, divisor: Wrapping<F>) -> Wrapping<F> {
        Wrapping(self.0.wrapping_div_euclid(divisor.0))
    }

    /// Remainder for Euclidean division.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let num = Wrapping(I16F16::from_num(7.5));
    /// let den = Wrapping(I16F16::from_num(2));
    /// assert_eq!(num.rem_euclid(den), Wrapping(I16F16::from_num(1.5)));
    /// assert_eq!((-num).rem_euclid(den), Wrapping(I16F16::from_num(0.5)));
    /// ```
    #[inline]
    pub fn rem_euclid(self, divisor: Wrapping<F>) -> Wrapping<F> {
        Wrapping(self.0.rem_euclid(divisor.0))
    }

    /// Euclidean division by an integer.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let num = Wrapping(I16F16::from_num(7.5));
    /// assert_eq!(num.div_euclid_int(2), Wrapping(I16F16::from_num(3)));
    /// let min = Wrapping(I16F16::min_value());
    /// assert_eq!(min.div_euclid_int(-1), min);
    /// ```
    #[inline]
    pub fn div_euclid_int(self, divisor: F::Bits) -> Wrapping<F> {
        Wrapping(self.0.wrapping_div_euclid_int(divisor))
    }

    /// Remainder for Euclidean division.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// let num = Wrapping(I16F16::from_num(7.5));
    /// assert_eq!(num.rem_euclid_int(2), Wrapping(I16F16::from_num(1.5)));
    /// assert_eq!((-num).rem_euclid_int(2), Wrapping(I16F16::from_num(0.5)));
    /// ```
    #[inline]
    pub fn rem_euclid_int(self, divisor: F::Bits) -> Wrapping<F> {
        Wrapping(self.0.wrapping_rem_euclid_int(divisor))
    }
}

impl<F: FixedSigned> Wrapping<F> {
    /// Returns [`true`][`bool`] if the number is > 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert!(Wrapping(I16F16::from_num(4.3)).is_positive());
    /// assert!(!Wrapping(I16F16::from_num(0)).is_positive());
    /// assert!(!Wrapping(I16F16::from_num(-4.3)).is_positive());
    /// ```
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    pub fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Returns [`true`][`bool`] if the number is < 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert!(!Wrapping(I16F16::from_num(4.3)).is_negative());
    /// assert!(!Wrapping(I16F16::from_num(0)).is_negative());
    /// assert!(Wrapping(I16F16::from_num(-4.3)).is_negative());
    /// ```
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    pub fn is_negative(self) -> bool {
        self.0.is_negative()
    }

    /// Wrapping absolute value. Returns the absolute value, wrapping
    /// on overflow.
    ///
    /// Overflow can only occur when trying to find the absolute value
    /// of the minimum value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping(I16F16::from_num(-5)).abs(), Wrapping(I16F16::from_num(5)));
    /// assert_eq!(Wrapping(I16F16::min_value()).abs(), Wrapping(I16F16::min_value()));
    /// ```
    #[inline]
    pub fn abs(self) -> Wrapping<F> {
        Wrapping(self.0.wrapping_abs())
    }

    /// Returns a number representing the sign of `self`.
    ///
    /// # Warning
    ///
    /// Using this method when 1 and −1 cannot be represented is
    /// almost certainly a bug, however, this is allowed and gives the
    /// following wrapped results.
    ///
    ///   * When there are no integer bits, for example for the type
    ///     <code>[Wrapping][`Wrapping`]&lt;[I0F16][`I0F16`]&gt;</code>,
    ///     the return value is always zero.
    ///   * When there is one integer bit, for example for the type
    ///     <code>[Wrapping][`Wrapping`]&lt;[I1F15][`I1F15`]&gt;</code>,
    ///     the return value is zero when `self` is zero, and −1
    ///     otherwise. This means that for a positive number, −1 is
    ///     returned, because +1 does not fit and is wrapped to −1.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::I16F16, Wrapping};
    /// assert_eq!(Wrapping(<I16F16>::from_num(-3.9)).signum(), Wrapping(I16F16::from_num(-1)));
    /// assert_eq!(Wrapping(<I16F16>::from_num(0)).signum(), Wrapping(I16F16::from_num(0)));
    /// assert_eq!(Wrapping(<I16F16>::from_num(3.9)).signum(), Wrapping(I16F16::from_num(1)));
    /// ```
    ///
    /// [`I0F16`]: types/type.I0F16.html
    /// [`I1F15`]: types/type.I1F15.html
    /// [`Wrapping`]: struct.Wrapping.html
    #[inline]
    pub fn signum(self) -> Wrapping<F> {
        if self.is_positive() {
            Self::from_num(1)
        } else if self.is_negative() {
            Self::from_num(-1)
        } else {
            Self::from_num(0)
        }
    }
}

impl<F: FixedUnsigned> Wrapping<F> {
    /// Returns [`true`][`bool`] if the fixed-point number is
    /// 2<sup><i>k</i></sup> for some integer <i>k</i>.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::U16F16, Wrapping};
    /// assert!(Wrapping(U16F16::from_num(0.5)).is_power_of_two());
    /// assert!(Wrapping(U16F16::from_num(4)).is_power_of_two());
    /// assert!(!Wrapping(U16F16::from_num(5)).is_power_of_two());
    /// ```
    ///
    /// [`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    pub fn is_power_of_two(self) -> bool {
        self.0.is_power_of_two()
    }

    /// Returns the smallest power of two that is ≥ `self`.
    ///
    /// If the next power of two is too large to fit, it is wrapped to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use substrate_fixed::{types::U16F16, Wrapping};
    /// let half = Wrapping(U16F16::from_num(0.5));
    /// assert_eq!(Wrapping(U16F16::from_num(0.3)).next_power_of_two(), half);
    /// let four = Wrapping(U16F16::from_num(4));
    /// assert_eq!(Wrapping(U16F16::from_num(4)).next_power_of_two(), four);
    /// let zero = Wrapping(U16F16::from_num(0));
    /// assert_eq!(Wrapping(U16F16::max_value()).next_power_of_two(), zero);
    /// ```
    #[inline]
    pub fn next_power_of_two(self) -> Wrapping<F> {
        Wrapping(self.0.checked_next_power_of_two().unwrap_or_default())
    }
}

impl<F: Fixed> Display for Wrapping<F> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self.0, f)
    }
}

impl<F: Fixed> From<F> for Wrapping<F> {
    /// Wraps a fixed-point number.
    #[inline]
    fn from(src: F) -> Wrapping<F> {
        Wrapping(src)
    }
}

impl<F: Fixed> FromStr for Wrapping<F> {
    type Err = ParseFixedError;
    /// Parses a string slice containing decimal digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
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

macro_rules! op_bitwise {
    ($Op:ident $op:ident, $OpAssign:ident $op_assign:ident) => {
        impl<F> $Op<Wrapping<F>> for Wrapping<F>
        where
            F: $Op<F, Output = F>,
        {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: Wrapping<F>) -> Wrapping<F> {
                Wrapping((self.0).$op(other.0))
            }
        }
        impl<'a, F> $Op<Wrapping<F>> for &'a Wrapping<F>
        where
            &'a F: $Op<F, Output = F>,
        {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: Wrapping<F>) -> Wrapping<F> {
                Wrapping((self.0).$op(other.0))
            }
        }
        impl<'a, F> $Op<&'a Wrapping<F>> for Wrapping<F>
        where
            F: $Op<&'a F, Output = F>,
        {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: &'a Wrapping<F>) -> Wrapping<F> {
                Wrapping((self.0).$op(&other.0))
            }
        }
        impl<'a, 'b, F> $Op<&'a Wrapping<F>> for &'b Wrapping<F>
        where
            &'b F: $Op<&'a F, Output = F>,
        {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: &'a Wrapping<F>) -> Wrapping<F> {
                Wrapping((self.0).$op(&other.0))
            }
        }
        impl<F> $OpAssign<Wrapping<F>> for Wrapping<F>
        where
            F: $OpAssign<F>,
        {
            #[inline]
            fn $op_assign(&mut self, other: Wrapping<F>) {
                (self.0).$op_assign(other.0);
            }
        }
        impl<'a, F> $OpAssign<&'a Wrapping<F>> for Wrapping<F>
        where
            F: $OpAssign<&'a F>,
        {
            #[inline]
            fn $op_assign(&mut self, other: &'a Wrapping<F>) {
                (self.0).$op_assign(&other.0);
            }
        }
    };
}

macro_rules! op_shift {
    (
        $Op:ident $op:ident, $OpAssign:ident $op_assign:ident;
        $($Rhs:ident),*
    ) => { $(
        impl<F> $Op<$Rhs> for Wrapping<F>
        where
            F: $Op<u32, Output = F>,
        {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: $Rhs) -> Wrapping<F> {
                let nbits = mem::size_of::<F>() as u32 * 8;
                Wrapping((self.0).$op(other as u32 % nbits))
            }
        }
        impl<'a, F> $Op<$Rhs> for &'a Wrapping<F>
        where
            &'a F: $Op<u32, Output = F>,
        {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: $Rhs) -> Wrapping<F> {
                let nbits = mem::size_of::<F>() as u32 * 8;
                Wrapping((self.0).$op(other as u32 % nbits))
            }
        }
        impl<'a, F> $Op<&'a $Rhs> for Wrapping<F>
        where
            F: $Op<u32, Output = F>,
        {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: &$Rhs) -> Wrapping<F> {
                let nbits = mem::size_of::<F>() as u32 * 8;
                Wrapping((self.0).$op(*other as u32 % nbits))
            }
        }
        impl<'a, 'b, F> $Op<&'a $Rhs> for &'b Wrapping<F>
        where
            &'b F: $Op<u32, Output = F>,
        {
            type Output = Wrapping<F>;
            #[inline]
            fn $op(self, other: &$Rhs) -> Wrapping<F> {
                let nbits = mem::size_of::<F>() as u32 * 8;
                Wrapping((self.0).$op(*other as u32 % nbits))
            }
        }
        impl<F> $OpAssign<$Rhs> for Wrapping<F>
        where
            F: $OpAssign<u32>,
        {
            #[inline]
            fn $op_assign(&mut self, other: $Rhs) {
                let nbits = mem::size_of::<F>() as u32 * 8;
                (self.0).$op_assign(other as u32 % nbits);
            }
        }
        impl<'a, F> $OpAssign<&'a $Rhs> for Wrapping<F>
        where
            F: $OpAssign<u32>,
        {
            #[inline]
            fn $op_assign(&mut self, other: &$Rhs) {
                let nbits = mem::size_of::<F>() as u32 * 8;
                (self.0).$op_assign(*other as u32 % nbits);
            }
        }
    )* };
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
op! { rem, Rem rem, RemAssign rem_assign }

impl<F> Not for Wrapping<F>
where
    F: Not<Output = F>,
{
    type Output = Wrapping<F>;
    #[inline]
    fn not(self) -> Wrapping<F> {
        Wrapping((self.0).not())
    }
}
impl<'a, F> Not for &'a Wrapping<F>
where
    &'a F: Not<Output = F>,
{
    type Output = Wrapping<F>;
    #[inline]
    fn not(self) -> Wrapping<F> {
        Wrapping((self.0).not())
    }
}
op_bitwise! { BitAnd bitand, BitAndAssign bitand_assign }
op_bitwise! { BitOr bitor, BitOrAssign bitor_assign }
op_bitwise! { BitXor bitxor, BitXorAssign bitxor_assign }

op_shift! {
    Shl shl, ShlAssign shl_assign;
    i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
}
op_shift! {
    Shr shr, ShrAssign shr_assign;
    i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
}

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
// otherwise there will be a conflicting implementation error. For
// example we cannot implement both these without triggering E0119:
//
//     impl<F: Fixed> Op<F::Bits> for Wrapping<F> { /* ... */ }
//     impl<'a, F: Fixed> Op<&'a F::Bits> for Wrapping<F> { /* ... */ }
//
// To work around this, we provide implementations like this:
//
//     impl<Frac> Op<i8> for Wrapping<FixedI8<Frac>> { /* ... */ }
//     impl<'a, Frac> Op<&'a i8> for Wrapping<FixedI8<Frac>> { /* ... */ }
//     impl<Frac> Op<i16> for Wrapping<FixedI16<Frac>> { /* ... */ }
//     impl<'a, Frac> Op<&'a i16> for Wrapping<FixedI16<Frac>> { /* ... */ }
//     ...

macro_rules! op_bits {
    (
        $Fixed:ident($Bits:ident $(, $LeEqU:ident)*)::$wrapping:ident,
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac $(: $LeEqU)*> $Op<$Bits> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, Frac $(: $LeEqU)*> $Op<$Bits> for &'a Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(other))
            }
        }
        impl<'a, Frac $(: $LeEqU)*> $Op<&'a $Bits> for Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<'a, 'b, Frac $(: $LeEqU)*> $Op<&'a $Bits> for &'b Wrapping<$Fixed<Frac>> {
            type Output = Wrapping<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Wrapping<$Fixed<Frac>> {
                Wrapping((self.0).$wrapping(*other))
            }
        }
        impl<Frac $(: $LeEqU)*> $OpAssign<$Bits> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: $Bits) {
                self.0 = (self.0).$wrapping(other);
            }
        }
        impl<'a, Frac $(: $LeEqU)*> $OpAssign<&'a $Bits> for Wrapping<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: &$Bits) {
                self.0 = (self.0).$wrapping(*other);
            }
        }
    };
}

macro_rules! ops {
    ($Fixed:ident($Bits:ident, $LeEqU:ident)) => {
        op_bits! { $Fixed($Bits)::wrapping_mul_int, Mul mul, MulAssign mul_assign }
        op_bits! { $Fixed($Bits)::wrapping_div_int, Div div, DivAssign div_assign }
        op_bits! { $Fixed($Bits, $LeEqU)::rem, Rem rem, RemAssign rem_assign }
    };
}
ops! { FixedI8(i8, LeEqU8) }
ops! { FixedI16(i16, LeEqU16) }
ops! { FixedI32(i32, LeEqU32) }
ops! { FixedI64(i64, LeEqU64) }
ops! { FixedI128(i128, LeEqU128) }
ops! { FixedU8(u8, LeEqU8) }
ops! { FixedU16(u16, LeEqU16) }
ops! { FixedU32(u32, LeEqU32) }
ops! { FixedU64(u64, LeEqU64) }
ops! { FixedU128(u128, LeEqU128) }
