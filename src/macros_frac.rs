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

macro_rules! fixed_frac {
    (
        $description:expr,
        $Fixed:ident[$s_fixed:expr]($Inner:ty[$s_inner:expr], $LeEqU:tt, $s_nbits:expr),
        $UInner:ty, $Signedness:tt
    ) => {
        impl<Frac: $LeEqU> $Fixed<Frac> {
            comment! {
                "The number of integer bits.

# Examples

```rust
use fixed::{types::extra::U6, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U6>;
assert_eq!(Fix::INT_NBITS, ", $s_nbits, " - 6);
```
";
                pub const INT_NBITS: u32 = mem::size_of::<$Inner>() as u32 * 8 - Self::FRAC_NBITS;
            }

            comment! {
                "The number of fractional bits.

# Examples

```rust
use fixed::{types::extra::U6, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U6>;
assert_eq!(Fix::FRAC_NBITS, 6);
```
";
                pub const FRAC_NBITS: u32 = Frac::U32;
            }

            // some other useful constants for internal use:

            const INT_MASK: $Inner =
                !0 << (Self::FRAC_NBITS / 2) << (Self::FRAC_NBITS - Self::FRAC_NBITS / 2);
            const FRAC_MASK: $Inner = !Self::INT_MASK;

            // 0 when FRAC_NBITS = 0
            const INT_LSB: $Inner = Self::INT_MASK ^ (Self::INT_MASK << 1);

            // 0 when INT_NBITS = 0
            const FRAC_MSB: $Inner =
                Self::FRAC_MASK ^ ((Self::FRAC_MASK as $UInner) >> 1) as $Inner;

            comment! {
                "Returns the number of integer bits.

# Examples

```rust
use fixed::{types::extra::U6, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U6>;
assert_eq!(Fix::int_nbits(), ", $s_nbits, " - 6);
```
";
                #[inline]
                pub fn int_nbits() -> u32 {
                    Self::INT_NBITS
                }
            }

            comment! {
                "Returns the number of fractional bits.

# Examples

```rust
use fixed::{types::extra::U6, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U6>;
assert_eq!(Fix::frac_nbits(), 6);
```
";
                #[inline]
                pub fn frac_nbits() -> u32 {
                    Self::FRAC_NBITS
                }
            }

            fixed_from_to! { $Fixed[$s_fixed]($Inner[$s_inner], $s_nbits), $Signedness }
            fixed_round! { $Fixed[$s_fixed]($s_nbits), $Signedness }

            if_signed! {
                $Signedness;
                comment! {
                    "Returns a number representing the sign of `self`.

# Panics

When debug assertions are enabled, this method panics
  * if the value is positive and the fixed-point number has zero
    or one integer bits such that it cannot hold the value 1.
  * if the value is negative and the fixed-point number has zero
    integer bits, such that it cannot hold the value −1.

When debug assertions are not enabled, the wrapped value can be
returned in those cases, but it is not considered a breaking change if
in the future it panics; using this method when 1 and −1 cannot be
represented is almost certainly a bug.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(5).signum(), 1);
assert_eq!(Fix::from_num(0).signum(), 0);
assert_eq!(Fix::from_num(-5).signum(), -1);
```
";
                    #[inline]
                    pub fn signum(self) -> $Fixed<Frac> {
                        match self.to_bits().cmp(&0) {
                            Ordering::Equal => Self::from_bits(0),
                            Ordering::Greater => Self::from_num(1),
                            Ordering::Less => Self::from_num(-1),
                        }
                    }
                }
            }

            comment! {
                "Checked multiplication. Returns the product, or [`None`] on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::max_value().checked_mul(Fix::from_num(1)), Some(Fix::max_value()));
assert_eq!(Fix::max_value().checked_mul(Fix::from_num(2)), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
                #[inline]
                pub fn checked_mul(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                    let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                    match dir {
                        Ordering::Equal => Some(Self::from_bits(ans)),
                        _ => None,
                    }
                }
            }

            comment! {
                "Checked division. Returns the quotient, or [`None`] if
the divisor is zero or on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::max_value().checked_div(Fix::from_num(1)), Some(Fix::max_value()));
assert_eq!(Fix::max_value().checked_div(Fix::from_num(1) / 2), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
                #[inline]
                pub fn checked_div(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                    if rhs.to_bits() == 0 {
                        return None;
                    }
                    let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                    match dir {
                        Ordering::Equal => Some(Self::from_bits(ans)),
                        _ => None,
                    }
                }
            }

            comment! {
                "Saturating multiplication. Returns the product, saturating on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).saturating_mul(Fix::from_num(2)), Fix::from_num(6));
assert_eq!(Fix::max_value().saturating_mul(Fix::from_num(2)), Fix::max_value());
```
";
                #[inline]
                pub fn saturating_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                    match dir {
                        Ordering::Equal => Self::from_bits(ans),
                        Ordering::Less => Self::max_value(),
                        Ordering::Greater => Self::min_value(),
                    }
                }
            }

            comment! {
                "Saturating division. Returns the quotient, saturating on overflow.

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one_half = Fix::from_num(1) / 2;
assert_eq!(Fix::from_num(1).saturating_div(Fix::from_num(2)), one_half);
assert_eq!(Fix::max_value().saturating_div(one_half), Fix::max_value());
```
";
                #[inline]
                pub fn saturating_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                    match dir {
                        Ordering::Equal => Self::from_bits(ans),
                        Ordering::Less => Self::max_value(),
                        Ordering::Greater => Self::min_value(),
                    }
                }
            }

            comment! {
                "Wrapping multiplication. Returns the product, wrapping on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).wrapping_mul(Fix::from_num(2)), Fix::from_num(6));
let wrapped = Fix::from_bits(!0 << 2);
assert_eq!(Fix::max_value().wrapping_mul(Fix::from_num(4)), wrapped);
```
";
                #[inline]
                pub fn wrapping_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    let (ans, _) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                    Self::from_bits(ans)
                }
            }

            comment! {
                "Wrapping division. Returns the quotient, wrapping on overflow.

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one_point_5 = Fix::from_bits(0b11 << (4 - 1));
assert_eq!(Fix::from_num(3).wrapping_div(Fix::from_num(2)), one_point_5);
let quarter = Fix::from_num(1) / 4;
let wrapped = Fix::from_bits(!0 << 2);
assert_eq!(Fix::max_value().wrapping_div(quarter), wrapped);
```
";
                #[inline]
                pub fn wrapping_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    let (ans, _) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                    Self::from_bits(ans)
                }
            }

            comment! {
                "Overflowing multiplication.

Returns a [tuple] of the product and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).overflowing_mul(Fix::from_num(2)), (Fix::from_num(6), false));
let wrapped = Fix::from_bits(!0 << 2);
assert_eq!(Fix::max_value().overflowing_mul(Fix::from_num(4)), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub fn overflowing_mul(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                    let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                    (Self::from_bits(ans), dir != Ordering::Equal)
                }
            }

            comment! {
                "Overflowing division.

Returns a [tuple] of the quotient and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one_point_5 = Fix::from_bits(0b11 << (4 - 1));
assert_eq!(Fix::from_num(3).overflowing_div(Fix::from_num(2)), (one_point_5, false));
let quarter = Fix::from_num(1) / 4;
let wrapped = Fix::from_bits(!0 << 2);
assert_eq!(Fix::max_value().overflowing_div(quarter), (wrapped, true));
```
";
                #[inline]
                pub fn overflowing_div(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                    let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                    (Self::from_bits(ans), dir != Ordering::Equal)
                }
            }

            /// Creates a fixed-point number from another number.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `from_num`")]
            pub fn from_fixed<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::from_num(src)
            }

            /// Converts a fixed-point number to another number.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `to_num`")]
            pub fn to_fixed<Dst: FromFixed>(self) -> Dst {
                self.to_num()
            }

            /// Creates a fixed-point number from another number.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `from_num`")]
            pub fn from_int<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::from_num(src)
            }

            /// Converts a fixed-point number to another number.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `to_num`")]
            pub fn to_int<Dst: FromFixed>(self) -> Dst {
                self.to_num()
            }

            /// Creates a fixed-point number from another number.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `from_num`")]
            pub fn from_float<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::from_num(src)
            }

            /// Converts a fixed-point number to another number.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `to_num`")]
            pub fn to_float<Dst: FromFixed>(self) -> Dst {
                self.to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `checked_from_num`")]
            pub fn checked_from_fixed<Src: ToFixed>(src: Src) -> Option<$Fixed<Frac>> {
                Self::checked_from_num(src)
            }

            /// Converts a fixed-point number to another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `checked_to_num`")]
            pub fn checked_to_fixed<Dst: FromFixed>(self) -> Option<Dst> {
                self.checked_to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `checked_from_num`")]
            pub fn checked_from_int<Src: ToFixed>(src: Src) -> Option<$Fixed<Frac>> {
                Self::checked_from_num(src)
            }

            /// Converts a fixed-point number to another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `checked_to_num`")]
            pub fn checked_to_int<Dst: FromFixed>(self) -> Option<Dst> {
                self.checked_to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `checked_from_num`")]
            pub fn checked_from_float<Src: ToFixed>(src: Src) -> Option<$Fixed<Frac>> {
                Self::checked_from_num(src)
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `saturating_from_num`")]
            pub fn saturating_from_fixed<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::saturating_from_num(src)
            }

            /// Converts a fixed-point number to another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `saturating_to_num`")]
            pub fn saturating_to_fixed<Dst: FromFixed>(self) -> Dst {
                self.saturating_to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `saturating_from_num`")]
            pub fn saturating_from_int<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::saturating_from_num(src)
            }

            /// Converts a fixed-point number to another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `saturating_to_num`")]
            pub fn saturating_to_int<Dst: FromFixed>(self) -> Dst {
                self.saturating_to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `saturating_from_num`")]
            pub fn saturating_from_float<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::saturating_from_num(src)
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `wrapping_from_num`")]
            pub fn wrapping_from_fixed<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::wrapping_from_num(src)
            }

            /// Converts a fixed-point number to another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `wrapping_to_num`")]
            pub fn wrapping_to_fixed<Dst: FromFixed>(self) -> Dst {
                self.wrapping_to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `wrapping_from_num`")]
            pub fn wrapping_from_int<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::wrapping_from_num(src)
            }

            /// Converts a fixed-point number to another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `wrapping_to_num`")]
            pub fn wrapping_to_int<Dst: FromFixed>(self) -> Dst {
                self.wrapping_to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `wrapping_from_num`")]
            pub fn wrapping_from_float<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                Self::wrapping_from_num(src)
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `overflowing_from_num`")]
            pub fn overflowing_from_fixed<Src: ToFixed>(src: Src) -> ($Fixed<Frac>, bool) {
                Self::overflowing_from_num(src)
            }

            /// Converts a fixed-point number to another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `overflowing_to_num`")]
            pub fn overflowing_to_fixed<Dst: FromFixed>(self) -> (Dst, bool) {
                self.overflowing_to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `overflowing_from_num`")]
            pub fn overflowing_from_int<Src: ToFixed>(src: Src) -> ($Fixed<Frac>, bool) {
                Self::overflowing_from_num(src)
            }

            /// Converts a fixed-point number to another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `overflowing_to_num`")]
            pub fn overflowing_to_int<Dst: FromFixed>(self) -> (Dst, bool) {
                self.overflowing_to_num()
            }

            /// Creates a fixed-point number from another number if it fits.
            #[inline]
            #[deprecated(since = "0.4.2", note = "replaced by `overflowing_from_num`")]
            pub fn overflowing_from_float<Src: ToFixed>(src: Src) -> ($Fixed<Frac>, bool) {
                Self::overflowing_from_num(src)
            }
        }
    };
}
