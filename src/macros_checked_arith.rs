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
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
",
            if_signed_unsigned!(
                $Signedness,
                "assert_eq!(Fix::from_int(5).checked_neg(), Some(Fix::from_int(-5)));
assert_eq!(Fix::min_value().checked_neg(), None);",
                "assert_eq!(Fix::from_int(0).checked_neg(), Some(Fix::from_int(0)));
assert_eq!(Fix::from_int(5).checked_neg(), None);",
            ),
            "
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_neg(self) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_neg(self.to_bits()).map(Self::from_bits)
            }
        );

        comment!(
            "Checked addition. Returns the sum, or [`None`] on overflow.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
let one = Fix::from_int(1);
assert_eq!((Fix::max_value() - one).checked_add(one), Some(Fix::max_value()));
assert_eq!(Fix::max_value().checked_add(one), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_add(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_add(self.to_bits(), rhs.to_bits()).map(Self::from_bits)
            }
        );

        comment!(
            "Checked subtraction. Returns the difference, or [`None`] on overflow.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
let one = Fix::from_int(1);
assert_eq!((Fix::min_value() + one).checked_sub(one), Some(Fix::min_value()));
assert_eq!(Fix::min_value().checked_sub(one), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_sub(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_sub(self.to_bits(), rhs.to_bits()).map(Self::from_bits)
            }
        );

        comment!(
            "Checked multiplication. Returns the product, or [`None`] on overflow.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::max_value().checked_mul(Fix::from_int(1)), Some(Fix::max_value()));
assert_eq!(Fix::max_value().checked_mul(Fix::from_int(2)), None);
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
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::max_value().checked_div(Fix::from_int(1)), Some(Fix::max_value()));
assert_eq!(Fix::max_value().checked_div(Fix::from_int(1) / 2), None);
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
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::max_value().checked_mul_int(1), Some(Fix::max_value()));
assert_eq!(Fix::max_value().checked_mul_int(2), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_mul_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_mul(self.to_bits(), rhs).map(Self::from_bits)
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
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::max_value().checked_div_int(1), Some(Fix::max_value()));
assert_eq!(Fix::from_int(1).checked_div_int(0), None);
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
                <$Inner>::checked_div(self.to_bits(), rhs).map(Self::from_bits)
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
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// binary 1.0101 / 8 = binary 0.0010 remainder 0.0101
assert_eq!(Fix::from_bits(0b10101).checked_rem_int(8), Some(Fix::from_bits(0b101)));
assert_eq!(Fix::from_int(1).checked_rem_int(0), None);
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
                <$Inner>::checked_rem(self.to_bits(), rhs).map(Self::from_bits)
            }
        );

        comment!(
            "Checked shift left. Returns the shifted number, or [`None`] if `rhs` ≥ ",
            $s_nbits,
            ".

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!((Fix::from_int(1) / 2).checked_shl(3), Some(Fix::from_int(4)));
assert_eq!((Fix::from_int(1) / 2).checked_shl(",
            $s_nbits,
            "), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_shl(self, rhs: u32) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_shl(self.to_bits(), rhs).map(Self::from_bits)
            }
        );

        comment!(
            "Checked shift right. Returns the shifted number, or [`None`] if `rhs` ≥ ",
            $s_nbits,
            ".

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::from_int(4).checked_shr(3), Some(Fix::from_int(1) / 2));
assert_eq!(Fix::from_int(4).checked_shr(",
            $s_nbits,
            "), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_shr(self, rhs: u32) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_shr(self.to_bits(), rhs).map(Self::from_bits)
            }
        );

        if_signed! {
            $Signedness;
            comment!(
                "Checked absolute value. Returns the absolute value, or [`None`] on overflow.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
assert_eq!(Fix::from_int(-5).checked_abs(), Some(Fix::from_int(5)));
assert_eq!(Fix::min_value().checked_abs(), None);
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
                #[inline]
                pub fn checked_abs(self) -> Option<$Fixed<Frac>> {
                    <$Inner>::checked_abs(self.to_bits()).map(Self::from_bits)
                }
            );
        }

        /// Saturating fixed-point addition.
        #[inline]
        pub fn saturating_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::saturating_add(self.to_bits(), rhs.to_bits()))
        }

        /// Saturating fixed-point subtraction.
        #[inline]
        pub fn saturating_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::saturating_sub(self.to_bits(), rhs.to_bits()))
        }

        /// Saturating fixed-point multiplication.
        #[inline]
        pub fn saturating_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
            let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
            match dir {
                Ordering::Equal => Self::from_bits(ans),
                Ordering::Less => Self::max_value(),
                Ordering::Greater => Self::min_value(),
            }
        }

        /// Saturating fixed-point division.
        #[inline]
        pub fn saturating_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
            let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
            match dir {
                Ordering::Equal => Self::from_bits(ans),
                Ordering::Less => Self::max_value(),
                Ordering::Greater => Self::min_value(),
            }
        }

        /// Saturating fixed-point multiplication by integer.
        #[inline]
        pub fn saturating_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::saturating_mul(self.to_bits(), rhs))
        }

        /// Wrapping negation.
        #[inline]
        pub fn wrapping_neg(self) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::wrapping_neg(self.to_bits()))
        }

        /// Wrapping fixed-point addition.
        #[inline]
        pub fn wrapping_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::wrapping_add(self.to_bits(), rhs.to_bits()))
        }

        /// Wrapping fixed-point subtraction.
        #[inline]
        pub fn wrapping_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::wrapping_sub(self.to_bits(), rhs.to_bits()))
        }

        /// Wrapping fixed-point multiplication.
        #[inline]
        pub fn wrapping_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
            let (ans, _) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
            Self::from_bits(ans)
        }

        /// Wrapping fixed-point division.
        #[inline]
        pub fn wrapping_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
            let (ans, _) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
            Self::from_bits(ans)
        }

        /// Wrapping fixed-point multiplication by integer.
        #[inline]
        pub fn wrapping_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::wrapping_mul(self.to_bits(), rhs))
        }

        /// Wrapping fixed-point division by integer.
        #[inline]
        pub fn wrapping_div_int(self, rhs: $Inner) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::wrapping_div(self.to_bits(), rhs))
        }

        /// Wrapping fixed-point remainder for division by integer.
        #[inline]
        pub fn wrapping_rem_int(self, rhs: $Inner) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::wrapping_rem(self.to_bits(), rhs))
        }

        /// Wrapping fixed-point left shift.
        #[inline]
        pub fn wrapping_shl(self, rhs: u32) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::wrapping_shl(self.to_bits(), rhs))
        }

        /// Wrapping fixed-point right shift.
        #[inline]
        pub fn wrapping_shr(self, rhs: u32) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::wrapping_shr(self.to_bits(), rhs))
        }

        if_signed! {
            $Signedness;
            /// Wrapping absolute value.
            #[inline]
            pub fn wrapping_abs(self) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_abs(self.to_bits()))
            }
        }

        /// Overflowing negation.
        #[inline]
        pub fn overflowing_neg(self) -> ($Fixed<Frac>, bool) {
            let (ans, o) = <$Inner>::overflowing_neg(self.to_bits());
            (Self::from_bits(ans), o)
        }

        /// Overflowing fixed-point addition.
        #[inline]
        pub fn overflowing_add(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
            let (ans, o) = <$Inner>::overflowing_add(self.to_bits(), rhs.to_bits());
            (Self::from_bits(ans), o)
        }

        /// Overflowing fixed-point subtraction.
        #[inline]
        pub fn overflowing_sub(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
            let (ans, o) = <$Inner>::overflowing_sub(self.to_bits(), rhs.to_bits());
            (Self::from_bits(ans), o)
        }

        /// Overflowing fixed-point multiplication.
        #[inline]
        pub fn overflowing_mul(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
            let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
            (Self::from_bits(ans), dir != Ordering::Equal)
        }

        /// Overflowing fixed-point division.
        #[inline]
        pub fn overflowing_div(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
            let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
            (Self::from_bits(ans), dir != Ordering::Equal)
        }

        /// Overflowing fixed-point multiplication by integer.
        #[inline]
        pub fn overflowing_mul_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
            let (ans, o) = <$Inner>::overflowing_mul(self.to_bits(), rhs);
            (Self::from_bits(ans), o)
        }

        /// Overflowing fixed-point division by integer.
        #[inline]
        pub fn overflowing_div_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
            let (ans, o) = <$Inner>::overflowing_div(self.to_bits(), rhs);
            (Self::from_bits(ans), o)
        }

        /// Overflowing fixed-point remainder for division by integer.
        #[inline]
        pub fn overflowing_rem_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
            let (ans, o) = <$Inner>::overflowing_rem(self.to_bits(), rhs);
            (Self::from_bits(ans), o)
        }

        /// Overflowing fixed-point left shift.
        #[inline]
        pub fn overflowing_shl(self, rhs: u32) -> ($Fixed<Frac>, bool) {
            let (ans, o) = <$Inner>::overflowing_shl(self.to_bits(), rhs);
            (Self::from_bits(ans), o)
        }

        /// Overflowing fixed-point right shift.
        #[inline]
        pub fn overflowing_shr(self, rhs: u32) -> ($Fixed<Frac>, bool) {
            let (ans, o) = <$Inner>::overflowing_shr(self.to_bits(), rhs);
            (Self::from_bits(ans), o)
        }

        if_signed! {
            $Signedness;
            /// Overflowing absolute value.
            #[inline]
            pub fn overflowing_abs(self) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_abs(self.to_bits());
                (Self::from_bits(ans), o)
            }
        }
    };
}
