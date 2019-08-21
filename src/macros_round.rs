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

macro_rules! fixed_round {
    ($Fixed:ident[$s_fixed:expr]($s_nbits:expr), $Signedness:tt) => {
        comment! {
            "Returns the integer part.

",
            if_signed_else_empty_str! {
                $Signedness,
                "Note that since the numbers are stored in two’s
complement, negative numbers with non-zero fractional parts will be
rounded towards −∞, except in the case where there are no integer
bits, that is `", $s_fixed, "<U", $s_nbits, ">`, where the return value is always zero.

",
            },
            "# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 0010.0000
let two = Fix::from_num(2);
// 0010.0100
let two_and_quarter = two + two / 8;
assert_eq!(two_and_quarter.int(), two);
",
            if_signed_else_empty_str! {
                $Signedness,
                "// 1101.0000
let three = Fix::from_num(3);
// 1101.1100
assert_eq!((-two_and_quarter).int(), -three);
",
            },
            "```
";
            #[inline]
            pub fn int(self) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits() & Self::INT_MASK)
            }
        }

        comment! {
            "Returns the fractional part.

",
            if_signed_else_empty_str! {
                $Signedness,
                "Note that since the numbers are stored in two’s
complement, the returned fraction will be non-negative for negative
numbers, except in the case where there are no integer bits, that is
`", $s_fixed, "<U", $s_nbits, ">` where the return value is always equal to
`self`.

",
            },
            "# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 0000.0100
let quarter = Fix::from_num(1) / 4;
// 0010.0100
let two_and_quarter = quarter * 9;
assert_eq!(two_and_quarter.frac(), quarter);
",
            if_signed_else_empty_str! {
                $Signedness,
                "// 0000.1100
let three_quarters = quarter * 3;
// 1101.1100
assert_eq!((-two_and_quarter).frac(), three_quarters);
",
            },
            "```
";
            #[inline]
            pub fn frac(self) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits() & Self::FRAC_MASK)
            }
        }

        comment! {
            "Rounds to the next integer towards +∞.

# Panics

When debug assertions are enabled, panics if the result does not fit.
When debug assertions are not enabled, the wrapped result can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_ceil`] instead.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.ceil(), Fix::from_num(3));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).ceil(), Fix::from_num(-2));
",
            },
            "```

[`wrapping_ceil`]: #method.wrapping_ceil
";
            #[inline]
            pub fn ceil(self) -> $Fixed<Frac> {
                let (ceil, overflow) = self.overflowing_ceil();
                debug_assert!(!overflow, "overflow");
                let _ = overflow;
                ceil
            }
        }

        comment! {
            "Rounds to the next integer towards −∞.

",
            if_signed_else_empty_str! {
                $Signedness,
                "# Panics

When debug assertions are enabled, panics if the result does not fit.
When debug assertions are not enabled, the wrapped result can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_floor`] instead.

Overflow can only occur when there are zero integer bits.

",
            },
            "# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.floor(), Fix::from_num(2));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).floor(), Fix::from_num(-3));
",
            },
            "```

[`wrapping_floor`]: #method.wrapping_floor
";
            #[inline]
            pub fn floor(self) -> $Fixed<Frac> {
                let (floor, overflow) = self.overflowing_floor();
                debug_assert!(!overflow, "overflow");
                let _ = overflow;
                floor
            }
        }

        comment! {
            "Rounds to the nearest integer, with ties rounded away
from zero.

# Panics

When debug assertions are enabled, panics if the result does not fit.
When debug assertions are not enabled, the wrapped result can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_round`] instead.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.round(), Fix::from_num(3));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).round(), Fix::from_num(-3));
",
            },
            "```

[`wrapping_round`]: #method.wrapping_round
";
            #[inline]
            pub fn round(self) -> $Fixed<Frac> {
                let (round, overflow) = self.overflowing_round();
                debug_assert!(!overflow, "overflow");
                let _ = overflow;
                round
            }
        }

        comment! {
            "Checked ceil. Rounds to the next integer towards +∞,
returning [`None`] on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.checked_ceil(), Some(Fix::from_num(3)));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).checked_ceil(), Some(Fix::from_num(-2)));
",
            },
            "assert!(Fix::max_value().checked_ceil().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_ceil(self) -> Option<$Fixed<Frac>> {
                let (ceil, overflow) = self.overflowing_ceil();
                if overflow { None } else { Some(ceil) }
            }
        }

        comment! {
            "Checked floor. Rounds to the next integer towards −∞.",
            if_signed_unsigned! {
                $Signedness,
                "Returns [`None`] on overflow.

Overflow can only occur when there are zero integer bits.",
                "Always returns [`Some`] for unsigned values.",
            },
            "

# Examples

```rust
use fixed::{",
            if_signed_unsigned! {
                $Signedness,
                concat!(
                    "
    types::extra::{U4, U", $s_nbits, "},
    ", $s_fixed, ",
",
                ),
                concat!("types::extra::U4, ", $s_fixed),
            },
            "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.checked_floor(), Some(Fix::from_num(2)));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).checked_floor(), Some(Fix::from_num(-3)));
type AllFrac = ", $s_fixed, "<U", $s_nbits, ">;
assert!(AllFrac::min_value().checked_floor().is_none());
",
            },
            "```
",
            if_signed_unsigned! {
                $Signedness,
                "
[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None",
                "
[`Some`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.Some",
            },
            "
";
            #[inline]
            pub fn checked_floor(self) -> Option<$Fixed<Frac>> {
                let (floor, overflow) = self.overflowing_floor();
                if overflow { None } else { Some(floor) }
            }
        }

        comment! {
            "Checked round. Rounds to the nearest integer, with ties
rounded away from zero, returning [`None`] on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.checked_round(), Some(Fix::from_num(3)));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).checked_round(), Some(Fix::from_num(-3)));
",
            },
            "assert!(Fix::max_value().checked_round().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_round(self) -> Option<$Fixed<Frac>> {
                let (round, overflow) = self.overflowing_round();
                if overflow { None } else { Some(round) }
            }
        }

        comment! {
            "Saturating ceil. Rounds to the next integer towards +∞,
saturating on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.saturating_ceil(), Fix::from_num(3));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).saturating_ceil(), Fix::from_num(-2));
",
            },
            "assert_eq!(Fix::max_value().saturating_ceil(), Fix::max_value());
```
";
            #[inline]
            pub fn saturating_ceil(self) -> $Fixed<Frac> {
                let (ceil, overflow) = self.overflowing_ceil();
                if overflow { Self::max_value() } else { ceil }
            }
        }

        comment! {
            "Saturating floor. Rounds to the next integer towards −∞",
            if_signed_unsigned! {
                $Signedness,
                ", saturating on overflow.

Overflow can only occur when there are zero integer bits.",
                ". Cannot overflow for unsigned values.",
            },
            "

# Examples

```rust
use fixed::{",
            if_signed_unsigned! {
                $Signedness,
                concat!(
                    "
    types::extra::{U4, U", $s_nbits, "},
    ", $s_fixed, ",
",
                ),
                concat!("types::extra::U4, ", $s_fixed),
            },
            "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.saturating_floor(), Fix::from_num(2));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).saturating_floor(), Fix::from_num(-3));
type AllFrac = ", $s_fixed, "<U", $s_nbits, ">;
assert_eq!(AllFrac::min_value().saturating_floor(), AllFrac::min_value());
",
            },
            "```
";
            #[inline]
            pub fn saturating_floor(self) -> $Fixed<Frac> {
                let (floor, overflow) = self.overflowing_floor();
                if overflow { Self::min_value() } else { floor }
            }
        }

        comment! {
            "Saturating round. Rounds to the nearest integer, with
ties rounded away from zero, and saturating on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.saturating_round(), Fix::from_num(3));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).saturating_round(), Fix::from_num(-3));
",
            },
            "assert_eq!(Fix::max_value().saturating_round(), Fix::max_value());
```
";
            #[inline]
            pub fn saturating_round(self) -> $Fixed<Frac> {
                let saturated = if self.to_bits() > 0 {
                    $Fixed::max_value()
                } else {
                    $Fixed::min_value()
                };
                let (round, overflow) = self.overflowing_round();
                if overflow { saturated } else { round }
            }
        }

        comment! {
            "Wrapping ceil. Rounds to the next integer towards +∞,
wrapping on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.wrapping_ceil(), Fix::from_num(3));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).wrapping_ceil(), Fix::from_num(-2));
",
            },
            "assert_eq!(Fix::max_value().wrapping_ceil(), Fix::min_value());
```
";
            #[inline]
            pub fn wrapping_ceil(self) -> $Fixed<Frac> {
                self.overflowing_ceil().0
            }
        }

        comment! {
            "Wrapping floor. Rounds to the next integer towards −∞",
            if_signed_unsigned! {
                $Signedness,
                ", wrapping on overflow.

Overflow can only occur when there are zero integer bits.",
                ". Cannot overflow for unsigned values.",
            },
            "

# Examples

```rust
use fixed::{",
            if_signed_unsigned! {
                $Signedness,
                concat!(
                    "
    types::extra::{U4, U", $s_nbits, "},
    ", $s_fixed, ",
",
                ),
                concat!("types::extra::U4, ", $s_fixed),
            },
            "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.wrapping_floor(), Fix::from_num(2));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).wrapping_floor(), Fix::from_num(-3));
type AllFrac = ", $s_fixed, "<U", $s_nbits, ">;
assert_eq!(AllFrac::min_value().wrapping_floor(), AllFrac::from_num(0));
",
            },
            "```
";
            #[inline]
            pub fn wrapping_floor(self) -> $Fixed<Frac> {
                self.overflowing_floor().0
            }
        }

        comment! {
            "Wrapping round. Rounds to the next integer to the
nearest, with ties rounded away from zero, and wrapping on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.wrapping_round(), Fix::from_num(3));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).wrapping_round(), Fix::from_num(-3));
",
            },
            "assert_eq!(Fix::max_value().wrapping_round(), Fix::min_value());
```
";
            #[inline]
            pub fn wrapping_round(self) -> $Fixed<Frac> {
                self.overflowing_round().0
            }
        }

        comment! {
            "Overflowing ceil. Rounds to the next integer towards +∞.

Returns a [tuple] of the fixed-point number and a [`bool`], indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.overflowing_ceil(), (Fix::from_num(3), false));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).overflowing_ceil(), (Fix::from_num(-2), false));
"
            },
            "assert_eq!(Fix::max_value().overflowing_ceil(), (Fix::min_value(), true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_ceil(self) -> ($Fixed<Frac>, bool) {
                let int = self.int();
                if self.frac() == 0 {
                    return (int, false);
                }
                if Self::INT_NBITS == 0 {
                    return (int, self.to_bits() > 0);
                }
                let increment = Self::from_bits(Self::INT_LSB);
                if_signed! {
                    $Signedness;
                    if Self::INT_NBITS == 1 {
                        return int.overflowing_sub(increment);
                    }
                }
                int.overflowing_add(increment)
            }
        }

        comment! {
            "Overflowing floor. Rounds to the next integer towards −∞.

Returns a [tuple] of the fixed-point number and
",
            if_signed_unsigned! {
                $Signedness,
                "a [`bool`], indicating whether an overflow has
occurred. On overflow, the wrapped value isreturned. Overflow can only
occur when there are zero integer bits.",
                "[`false`][`bool`].",
            },
            "

# Examples

```rust
use fixed::{",
            if_signed_unsigned! {
                $Signedness,
                concat!(
                    "
    types::extra::{U4, U", $s_nbits, "},
    ", $s_fixed, ",
",
                ),
                concat!("types::extra::U4, ", $s_fixed),
            },
            "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.overflowing_floor(), (Fix::from_num(2), false));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).overflowing_floor(), (Fix::from_num(-3), false));
type AllFrac = ", $s_fixed, "<U", $s_nbits, ">;
assert_eq!(AllFrac::min_value().overflowing_floor(), (AllFrac::from_num(0), true));
",
            },
            "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_floor(self) -> ($Fixed<Frac>, bool) {
                let int = self.int();
                if_signed! {
                    $Signedness;
                    if Self::INT_NBITS == 0 {
                        return (int, self.to_bits() < 0);
                    }
                }
                (int, false)
            }
        }

        comment! {
            "Overflowing round. Rounds to the next integer to the
nearest, with ties rounded away from zero.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let two_half = Fix::from_num(5) / 2;
assert_eq!(two_half.overflowing_round(), (Fix::from_num(3), false));
",
            if_signed_else_empty_str! {
                $Signedness,
                "assert_eq!((-two_half).overflowing_round(), (Fix::from_num(-3), false));
",
            },
            "assert_eq!(Fix::max_value().overflowing_round(), (Fix::min_value(), true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_round(self) -> ($Fixed<Frac>, bool) {
                let int = self.int();
                if (self.to_bits() & Self::FRAC_MSB) == 0 {
                    return (int, false);
                }
                let increment = Self::from_bits(Self::INT_LSB);
                if_signed! {
                    $Signedness;
                    let tie = self.frac().to_bits() == Self::FRAC_MSB;
                    if Self::INT_NBITS == 0 {
                        // if num is .100...00 = -0.5, we have overflow
                        // otherwise .100...01, 0 < x < -0.5,  no overflow
                        return (int, tie);
                    }
                    // If num is −int.100...00 = (-int) + 0.5, we simply truncate to move to −∞.
                    // If num is −int.100...01 = (-int) + 0.6, we add 1 to −int.
                    // If num is +int.100...00 = (+int) + 0.5, we add 1 to +int.
                    // If num is +int.100...01 = (+int) + 0.6, we add 1 to +int.
                    if tie && self.to_bits() < 0 {
                        return (int, false);
                    }
                    if Self::INT_NBITS == 1 {
                        return int.overflowing_sub(increment);
                    }
                    int.overflowing_add(increment)
                }
                if_unsigned! {
                    $Signedness;
                    if Self::INT_NBITS == 0 {
                        return (int, true);
                    }
                    int.overflowing_add(increment)
                }
            }
        }
    };
}
