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

macro_rules! fixed_checked_arith {
    ($Fixed:ident[$s_fixed:expr]($Inner:ty, $s_nbits:expr), $Signedness:tt) => {
        comment!(
            "Checked negation. Returns the negated value, or [`None`] on overflow.

",
            if_signed_unsigned!(
                $Signedness,
                "Overflow can only occur when negating the minimum value.",
                "Only zero can be negated without overflow.",
            ),
            "

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
            if_signed_unsigned!(
                $Signedness,
                "assert_eq!(Fix::from_num(5).checked_neg(), Some(Fix::from_num(-5)));
assert_eq!(Fix::min_value().checked_neg(), None);",
                "assert_eq!(Fix::from_num(0).checked_neg(), Some(Fix::from_num(0)));
assert_eq!(Fix::from_num(5).checked_neg(), None);",
            ),
            "
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_neg(self) -> Option<$Fixed<Frac>> {
                self.to_bits().checked_neg().map(Self::from_bits)
            }
        );

        comment!(
            "Checked addition. Returns the sum, or [`None`] on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
assert_eq!((Fix::max_value() - one).checked_add(one), Some(Fix::max_value()));
assert_eq!(Fix::max_value().checked_add(one), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_add(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                self.to_bits().checked_add(rhs.to_bits()).map(Self::from_bits)
            }
        );

        comment!(
            "Checked subtraction. Returns the difference, or [`None`] on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
assert_eq!((Fix::min_value() + one).checked_sub(one), Some(Fix::min_value()));
assert_eq!(Fix::min_value().checked_sub(one), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_sub(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                self.to_bits().checked_sub(rhs.to_bits()).map(Self::from_bits)
            }
        );

        comment!(
            "Checked multiplication. Returns the product, or [`None`] on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
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
        );

        comment!(
            "Checked division. Returns the quotient, or [`None`] if
the divisor is zero or on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
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
        );

        comment!(
            "Checked multiplication by an integer. Returns the
product, or [`None`] on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::max_value().checked_mul_int(1), Some(Fix::max_value()));
assert_eq!(Fix::max_value().checked_mul_int(2), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_mul_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                self.to_bits().checked_mul(rhs).map(Self::from_bits)
            }
        );

        comment!(
            "Checked division by an integer. Returns the quotient, or
[`None`] if the divisor is zero",
            if_signed_unsigned!(
                $Signedness,
                " or if the division results in overflow.",
                ".",
            ),
            "

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::max_value().checked_div_int(1), Some(Fix::max_value()));
assert_eq!(Fix::from_num(1).checked_div_int(0), None);
",
            if_signed_else_empty_str!(
                $Signedness,
                "assert_eq!(Fix::min_value().checked_div_int(-1), None);
",
            ),
            "```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_div_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                self.to_bits().checked_div(rhs).map(Self::from_bits)
            }
        );

        comment!(
            "Checked fixed-point remainder for division by an integer.
Returns the remainder, or [`None`] if the divisor is zero",
            if_signed_unsigned!(
                $Signedness,
                " or if the division results in overflow.",
                ".",
            ),
            "

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// binary 1.0101 / 8 = binary 0.0010 remainder 0.0101
assert_eq!(Fix::from_bits(0b10101).checked_rem_int(8), Some(Fix::from_bits(0b101)));
assert_eq!(Fix::from_num(1).checked_rem_int(0), None);
",
            if_signed_else_empty_str!(
                $Signedness,
                "assert_eq!(Fix::min_value().checked_rem_int(-1), None);
",
            ),
            "```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_rem_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                self.to_bits().checked_rem(rhs).map(Self::from_bits)
            }
        );

        comment!(
            "Checked shift left. Returns the shifted number,
or [`None`] if `rhs` ≥ ", $s_nbits, ".

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(1) / 2).checked_shl(3), Some(Fix::from_num(4)));
assert_eq!((Fix::from_num(1) / 2).checked_shl(", $s_nbits, "), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_shl(self, rhs: u32) -> Option<$Fixed<Frac>> {
                self.to_bits().checked_shl(rhs).map(Self::from_bits)
            }
        );

        comment!(
            "Checked shift right. Returns the shifted number,
or [`None`] if `rhs` ≥ ", $s_nbits, ".

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(4).checked_shr(3), Some(Fix::from_num(1) / 2));
assert_eq!(Fix::from_num(4).checked_shr(", $s_nbits, "), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_shr(self, rhs: u32) -> Option<$Fixed<Frac>> {
                self.to_bits().checked_shr(rhs).map(Self::from_bits)
            }
        );

        if_signed! {
            $Signedness;
            comment!(
                "Checked absolute value. Returns the absolute value, or [`None`] on overflow.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).checked_abs(), Some(Fix::from_num(5)));
assert_eq!(Fix::min_value().checked_abs(), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
                #[inline]
                pub fn checked_abs(self) -> Option<$Fixed<Frac>> {
                    self.to_bits().checked_abs().map(Self::from_bits)
                }
            );
        }

        comment!(
            "Saturating negation. Returns the negated value, saturating on overflow.

",
            if_signed_unsigned!(
                $Signedness,
                "Overflow can only occur when negating the minimum value.",
                "This method always returns zero.",
            ),
            "

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
            if_signed_unsigned!(
                $Signedness,
                "assert_eq!(Fix::from_num(5).saturating_neg(), Fix::from_num(-5));
assert_eq!(Fix::min_value().saturating_neg(), Fix::max_value());",
                "assert_eq!(Fix::from_num(0).saturating_neg(), Fix::from_num(0));
assert_eq!(Fix::from_num(5).saturating_neg(), Fix::from_num(0));",
            ),
            "
```
";
            #[inline]
            pub fn saturating_neg(self) -> $Fixed<Frac> {
                if_signed_unsigned!(
                    $Signedness,
                    self.checked_neg().unwrap_or(Self::max_value()),
                    Self::from_bits(0),
                )
            }
        );

        delegate!(
            "Saturating addition. Returns the sum, saturating on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).saturating_add(Fix::from_num(2)), Fix::from_num(5));
assert_eq!(Fix::max_value().saturating_add(Fix::from_num(1)), Fix::max_value());
```
";
            $Fixed => fn saturating_add(self, rhs)
        );

        delegate!(
            "Saturating subtraction. Returns the difference, saturating on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
            if_signed_unsigned!(
                $Signedness,
                "assert_eq!(Fix::from_num(1).saturating_sub(Fix::from_num(3)), Fix::from_num(-2));
assert_eq!(Fix::min_value().saturating_sub(Fix::from_num(1)), Fix::min_value());",
                "assert_eq!(Fix::from_num(5).saturating_sub(Fix::from_num(3)), Fix::from_num(2));
assert_eq!(Fix::from_num(0).saturating_sub(Fix::from_num(1)), Fix::from_num(0));",
            ),
            "
```
";
            $Fixed => fn saturating_sub(self, rhs)
        );

        comment!(
            "Saturating multiplication. Returns the product, saturating on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
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
        );

        comment!(
            "Saturating division. Returns the quotient, saturating on overflow.

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
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
        );

        comment!(
            "Saturating multiplication by an integer. Returns the product, saturating on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).saturating_mul_int(2), Fix::from_num(6));
assert_eq!(Fix::max_value().saturating_mul_int(2), Fix::max_value());
```
";
            #[inline]
            pub fn saturating_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().saturating_mul(rhs))
            }
        );

        if_signed! {
            $Signedness;
            comment!(
                "Saturating absolute value. Returns the absolute value, saturating on overflow.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).saturating_abs(), Fix::from_num(5));
assert_eq!(Fix::min_value().saturating_abs(), Fix::max_value());
```
";
                #[inline]
                pub fn saturating_abs(self) -> $Fixed<Frac> {
                    self.checked_abs().unwrap_or(Self::max_value())
                }
            );
        }

        delegate!(
            "Wrapping negation. Returns the negated value, wrapping on overflow.

",
            if_signed_unsigned!(
                $Signedness,
                "Overflow can only occur when negating the minimum value.",
                "Only zero can be negated without overflow.",
            ),
            "

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
            if_signed_unsigned!(
                $Signedness,
                "assert_eq!(Fix::from_num(5).wrapping_neg(), Fix::from_num(-5));
assert_eq!(Fix::min_value().wrapping_neg(), Fix::min_value());",
                "assert_eq!(Fix::from_num(0).wrapping_neg(), Fix::from_num(0));
assert_eq!(Fix::from_num(5).wrapping_neg(), Fix::wrapping_from_num(-5));
let neg_five_bits = !Fix::from_num(5).to_bits() + 1;
assert_eq!(Fix::from_num(5).wrapping_neg(), Fix::from_bits(neg_five_bits));",
            ),
            "
```
";
            $Fixed => fn wrapping_neg(self)
        );

        delegate!(
            "Wrapping addition. Returns the sum, wrapping on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
let one_minus_bit = one - Fix::from_bits(1);
assert_eq!(Fix::from_num(3).wrapping_add(Fix::from_num(2)), Fix::from_num(5));
assert_eq!(Fix::max_value().wrapping_add(one), ",
            if_signed_else_empty_str!($Signedness, "Fix::min_value() + "),
            "one_minus_bit);
```
";
            $Fixed => fn wrapping_add(self, rhs)
        );

        delegate!(
            "Wrapping subtraction. Returns the difference, wrapping on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
let one_minus_bit = one - Fix::from_bits(1);
",
            if_signed_unsigned!(
                $Signedness,
                "assert_eq!(Fix::from_num(3).wrapping_sub(Fix::from_num(5)), Fix::from_num(-2));
assert_eq!(Fix::min_value()",
                "assert_eq!(Fix::from_num(5).wrapping_sub(Fix::from_num(3)), Fix::from_num(2));
assert_eq!(Fix::from_num(0)",
            ),
            ".wrapping_sub(one), Fix::max_value() - one_minus_bit);
```
";
            $Fixed => fn wrapping_sub(self, rhs)
        );

        comment!(
            "Wrapping multiplication. Returns the product, wrapping on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
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
        );

        comment!(
            "Wrapping division. Returns the quotient, wrapping on overflow.

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
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
        );

        comment!(
            "Wrapping multiplication by an integer. Returns the product, wrapping on overflow.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).wrapping_mul_int(2), Fix::from_num(6));
let wrapped = Fix::from_bits(!0 << 2);
assert_eq!(Fix::max_value().wrapping_mul_int(4), wrapped);
```
";
            #[inline]
            pub fn wrapping_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().wrapping_mul(rhs))
            }
        );

        comment!(
            "Wrapping division by an integer. Returns the quotient",
            if_signed_unsigned!(
                $Signedness,
                ", wrapping on overflow.

Overflow can only occur when dividing the minimum value by −1.",
                ".

Can never overflow for unsigned values.",
            ),
            "

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 1.5 is binary 1.1
let one_point_5 = Fix::from_bits(0b11 << (4 - 1));
assert_eq!(Fix::from_num(3).wrapping_div_int(2), one_point_5);
",
            if_signed_else_empty_str!(
                $Signedness,
                "assert_eq!(Fix::min_value().wrapping_div_int(-1), Fix::min_value());
",
            ),
            "```
";
            #[inline]
            pub fn wrapping_div_int(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().wrapping_div(rhs))
            }
        );

        comment!(
            "Wrapping fixed-point remainder for division by an integer. Returns the remainder",
            if_signed_unsigned!(
                $Signedness,
                ", wrapping on overflow.

Overflow can only occur when dividing the minimum value by −1.",
                ".

Can never overflow for unsigned values.",
            ),
            "

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// binary 1.0101 / 8 = binary 0.0010 remainder 0.0101
assert_eq!(Fix::from_bits(0b10101).wrapping_rem_int(8), Fix::from_bits(0b101));
",
            if_signed_else_empty_str!(
                $Signedness,
                "assert_eq!(Fix::min_value().wrapping_rem_int(-1), 0);
",
            ),
            "```
";
            #[inline]
            pub fn wrapping_rem_int(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits().wrapping_rem(rhs))
            }
        );

        delegate!(
            "Wrapping shift left. Wraps `rhs` if `rhs` ≥ ", $s_nbits, ",
then shifts and returns the number.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(1) / 2).wrapping_shl(3), Fix::from_num(4));
assert_eq!((Fix::from_num(1) / 2).wrapping_shl(3 + ", $s_nbits, "), Fix::from_num(4));
```
";
            $Fixed => fn wrapping_shl(self, rhs: u32)
        );

        delegate!(
            "Wrapping shift right. Wraps `rhs` if `rhs` ≥ ", $s_nbits, ",
then shifts and returns the number.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(4)).wrapping_shr(3), Fix::from_num(1) / 2);
assert_eq!((Fix::from_num(4)).wrapping_shr(3 + ", $s_nbits, "), Fix::from_num(1) / 2);
```
";
            $Fixed => fn wrapping_shr(self, rhs: u32)
        );

        if_signed! {
            $Signedness;
            delegate!(
                "Wrapping absolute value. Returns the absolute value, wrapping on overflow.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).wrapping_abs(), Fix::from_num(5));
assert_eq!(Fix::min_value().wrapping_abs(), Fix::min_value());
```
";
                $Fixed => fn wrapping_abs(self)
            );
        }

        comment!(
            "Overflowing negation.

Returns a [tuple] of the negated value and a [`bool`] indicating whether
an overflow has occurred. On overflow, the wrapped value is returned.

",
            if_signed_unsigned!(
                $Signedness,
                "Overflow can only occur when negating the minimum value.",
                "Only zero can be negated without overflow.",
            ),
            "

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
            if_signed_unsigned!(
                $Signedness,
                "assert_eq!(Fix::from_num(5).overflowing_neg(), (Fix::from_num(-5), false));
assert_eq!(Fix::min_value().overflowing_neg(), (Fix::min_value(), true));",
                "assert_eq!(Fix::from_num(0).overflowing_neg(), (Fix::from_num(0), false));
assert_eq!(Fix::from_num(5).overflowing_neg(), Fix::overflowing_from_num(-5));
let neg_five_bits = !Fix::from_num(5).to_bits() + 1;
assert_eq!(Fix::from_num(5).overflowing_neg(), (Fix::from_bits(neg_five_bits), true));",
            ),
            "
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_neg(self) -> ($Fixed<Frac>, bool) {
                let (ans, o) = self.to_bits().overflowing_neg();
                (Self::from_bits(ans), o)
            }
        );

        comment!(
            "Overflowing addition.

Returns a [tuple] of the sum and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
let one_minus_bit = one - Fix::from_bits(1);
assert_eq!(Fix::from_num(3).overflowing_add(Fix::from_num(2)), (Fix::from_num(5), false));
assert_eq!(Fix::max_value().overflowing_add(one), (",
            if_signed_else_empty_str!($Signedness, "Fix::min_value() + "),
            "one_minus_bit, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_add(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, o) = self.to_bits().overflowing_add(rhs.to_bits());
                (Self::from_bits(ans), o)
            }
        );

        comment!(
            "Overflowing subtraction.

Returns a [tuple] of the difference and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
let one_minus_bit = one - Fix::from_bits(1);
",
            if_signed_unsigned!(
                $Signedness,
                "assert_eq!(Fix::from_num(3).overflowing_sub(Fix::from_num(5)), (Fix::from_num(-2), false));
assert_eq!(Fix::min_value()",
                "assert_eq!(Fix::from_num(5).overflowing_sub(Fix::from_num(3)), (Fix::from_num(2), false));
assert_eq!(Fix::from_num(0)",
            ),
            ".overflowing_sub(one), (Fix::max_value() - one_minus_bit, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_sub(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, o) = self.to_bits().overflowing_sub(rhs.to_bits());
                (Self::from_bits(ans), o)
            }
        );

        comment!(
            "Overflowing multiplication.

Returns a [tuple] of the product and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
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
        );

        comment!(
            "Overflowing division.

Returns a [tuple] of the quotient and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
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
        );

        comment!(
            "Overflowing multiplication by an integer.

Returns a [tuple] of the product and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).overflowing_mul_int(2), (Fix::from_num(6), false));
let wrapped = Fix::from_bits(!0 << 2);
assert_eq!(Fix::max_value().overflowing_mul_int(4), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_mul_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = self.to_bits().overflowing_mul(rhs);
                (Self::from_bits(ans), o)
            }
        );

        comment!(
            "Overflowing division by an integer.

Returns a [tuple] of the quotient and ",
            if_signed_unsigned!(
                $Signedness,
                "a [`bool`] indicating whether an overflow has
occurred. On overflow, the wrapped value is returned. Overflow can
only occur when dividing the minimum value by −1.",
                "[`false`][`bool`], as the division can never overflow for unsigned values.",
            ),
            "

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 1.5 is binary 1.1
let one_point_5 = Fix::from_bits(0b11 << (4 - 1));
assert_eq!(Fix::from_num(3).overflowing_div_int(2), (one_point_5, false));
",
            if_signed_else_empty_str!(
                $Signedness,
                "assert_eq!(Fix::min_value().overflowing_div_int(-1), (Fix::min_value(), true));
",
            ),
            "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_div_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = self.to_bits().overflowing_div(rhs);
                (Self::from_bits(ans), o)
            }
        );

        comment!(
            "Overflowing fixed-point remainder for division by an integer.

Returns a [tuple] of the remainder and ",
            if_signed_unsigned!(
                $Signedness,
                "a [`bool`] indicating whether an overflow has
occurred. On overflow, the wrapped value is returned. Overflow can
only occur when dividing the minimum value by −1.",
                "[`false`][`bool`], as the division can never overflow for unsigned values.",
            ),
            "

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// binary 1.0101 / 8 = binary 0.0010 remainder 0.0101
assert_eq!(Fix::from_bits(0b10101).overflowing_rem_int(8), (Fix::from_bits(0b101), false));
",
            if_signed_else_empty_str!(
                $Signedness,
                "assert_eq!(Fix::min_value().overflowing_rem_int(-1), (Fix::from_num(0), true));
",
            ),
            "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_rem_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = self.to_bits().overflowing_rem(rhs);
                (Self::from_bits(ans), o)
            }
        );

        comment!(
            "Overflowing shift left.

Returns a [tuple] of the shifted value and a [`bool`] indicating whether
an overflow has occurred. Overflow occurs when `rhs` ≥ ", $s_nbits, ".
On overflow `rhs` is wrapped before the shift operation.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(1) / 2).overflowing_shl(3), (Fix::from_num(4), false));
assert_eq!((Fix::from_num(1) / 2).overflowing_shl(3 + ", $s_nbits, "), (Fix::from_num(4), true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_shl(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                let (ans, o) = self.to_bits().overflowing_shl(rhs);
                (Self::from_bits(ans), o)
            }
        );

        comment!(
            "Overflowing shift right.

Returns a [tuple] of the shifted value and a [`bool`] indicating whether
an overflow has occurred. Overflow occurs when `rhs` ≥ ", $s_nbits, ".
On overflow `rhs` is wrapped before the shift operation.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(4)).overflowing_shr(3), (Fix::from_num(1) / 2, false));
assert_eq!((Fix::from_num(4)).overflowing_shr(3 + ", $s_nbits, "), (Fix::from_num(1) / 2, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_shr(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                let (ans, o) = self.to_bits().overflowing_shr(rhs);
                (Self::from_bits(ans), o)
            }
        );

        if_signed! {
            $Signedness;
            comment!(
                "Overflowing absolute value.

Returns a [tuple] of the absolute value and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
use fixed::{frac::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).overflowing_abs(), (Fix::from_num(5), false));
assert_eq!(Fix::min_value().overflowing_abs(), (Fix::min_value(), true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub fn overflowing_abs(self) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = self.to_bits().overflowing_abs();
                    (Self::from_bits(ans), o)
                }
            );
        }
    };
}
