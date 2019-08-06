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

macro_rules! fixed_from_to {
    ($Fixed:ident[$s_fixed:expr]($Inner:ty[$s_inner:expr], $s_nbits:expr), $Signedness:tt) => {
        comment!(
            "Creates a fixed-point number that has a bitwise
representation identical to the given integer.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 0010.0000 == 2
assert_eq!(Fix::from_bits(0b10_0000), 2);
```
";
            #[inline]
            pub fn from_bits(bits: $Inner) -> $Fixed<Frac> {
                $Fixed {
                    bits,
                    phantom: PhantomData,
                }
            }
        );

        comment!(
            "Creates an integer that has a bitwise representation
identical to the given fixed-point number.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 2 is 0010.0000
assert_eq!(Fix::from_int(2).to_bits(), 0b10_0000);
```
";
            #[inline]
            pub fn to_bits(self) -> $Inner {
                self.bits
            }
        );

        comment!(
            "Creates a fixed-point number from another fixed-point
number which can have a different type.

Any extra fractional bits are truncated.

# Panics

When debug assertions are enabled, panics if the value does not fit.
When debug assertions are not enabled, the wrapped value can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_from_fixed`]
instead.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::from_fixed(src), Dst::from_bits(0b111 << (4 - 2)));
// src >> 4 is 0.000111, which for Dst is truncated to 0.0001
assert_eq!(Dst::from_fixed(src >> 4), Dst::from_bits(1));
```

[`wrapping_from_fixed`]: #method.wrapping_from_fixed
";
            #[inline]
            pub fn from_fixed<F>(val: F) -> $Fixed<Frac>
            where
                F: Fixed,
            {
                SealedFixed::from_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to another fixed-point
number which can have a different type.

Any extra fractional bits are truncated.

# Panics

When debug assertions are enabled, panics if the value does not fit.
When debug assertions are not enabled, the wrapped value can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_to_fixed`] instead.

# Examples

```rust
type Src = fixed::",
            $s_fixed,
            "<fixed::frac::U6>;
type Dst = fixed::FixedI32<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (6 - 2));
assert_eq!(src.to_fixed::<Dst>(), Dst::from_bits(0b111 << (4 - 2)));
// src >> 4 is 0.000111, which for Dst is truncated to 0.0001
assert_eq!((src >> 4u32).to_fixed::<Dst>(), Dst::from_bits(1));
```

[`wrapping_to_fixed`]: #method.wrapping_to_fixed
";
            #[inline]
            pub fn to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedFixed::from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from an integer.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

# Panics

When debug assertions are enabled, panics if the value does not fit.
When debug assertions are not enabled, the wrapped value can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_from_int`] instead.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::from_int(3i32), Fix::from_bits(3 << 4));
assert_eq!(Fix::from_int(",
            if_signed_unsigned!(
                $Signedness,
                "-3i64), Fix::from_bits(-",
                "3i64), Fix::from_bits(",
            ),
            "3 << 4));
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[`wrapping_from_int`]: #method.wrapping_from_int
";
            #[inline]
            pub fn from_int<I>(val: I) -> $Fixed<Frac>
            where
                I: Int,
            {
                SealedInt::to_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number of type to an integer.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

Any fractional bits are truncated.

# Panics

When debug assertions are enabled, panics if the value does not fit.
When debug assertions are not enabled, the wrapped value can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_to_int`] instead.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.to_int::<i32>(), 2);
assert_eq!(",
            if_signed_unsigned!(
                $Signedness,
                "(-two_point_5).to_int::<i64>(), -3",
                "two_point_5.to_int::<i64>(), 2",
            ),
            ");
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[`wrapping_to_int`]: #method.wrapping_to_int
";
            #[inline]
            pub fn to_int<I>(self) -> I
            where
                I: Int,
            {
                SealedInt::from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from a floating-point
number.

The floating-point number can be of type [`f32`] or [`f64`]. If the
[`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Panics

Panics if the value is not [finite].

When debug assertions are enabled, panics if the value does not fit.
When debug assertions are not enabled, the wrapped value can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_from_float`]
instead.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
assert_eq!(Fix::from_float(1.75f32), Fix::from_bits(0b111 << (4 - 2)));
assert_eq!(Fix::from_float(",
            if_signed_unsigned!(
                $Signedness,
                "-1.75f64), Fix::from_bits(-",
                "1.75f64), Fix::from_bits(",
            ),
            "0b111 << (4-2)));
```

[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`wrapping_from_float`]: #method.wrapping_from_float
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
";
            #[inline]
            pub fn from_float<F>(val: F) -> $Fixed<Frac>
            where
                F: Float,
            {
                SealedFloat::to_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to a floating-point number.

The floating-point number can be of type [`f32`] or [`f64`].
If the [`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.625 is 1.101 in binary
assert_eq!(Fix::from_bits(0b1101 << (4 - 3)).to_float::<f32>(), 1.625f32);
assert_eq!(Fix::from_bits(",
            if_signed_unsigned!(
                $Signedness,
                "-0b1101 << (4 - 3)).to_float::<f64>(), -",
                "0b1101 << (4 - 3)).to_float::<f64>(), "
            ),
            "1.625f64);
let max_fixed = fixed::FixedU128::<fixed::frac::U0>::max_value();
assert_eq!(max_fixed.to_float::<f32>(), std::f32::INFINITY);
```

[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
";
            pub fn to_float<F>(self) -> F
            where
                F: Float,
            {
                SealedFixed::to_float(self)
            }
        );

        comment!(
            "Creates a fixed-point number from another fixed-point
number if it fits, otherwise returns [`None`].

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::checked_from_fixed(src), Some(Dst::from_bits(0b111 << (4 - 2))));
let too_large = fixed::",
            $s_fixed,
            "::<fixed::frac::U2>::max_value();
assert!(Dst::checked_from_fixed(too_large).is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_from_fixed<F>(val: F) -> Option<$Fixed<Frac>>
            where
                F: Fixed,
            {
                SealedFixed::checked_from_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to another fixed-point
number if it fits, otherwise returns [`None`].

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
type Dst = fixed::FixedI32<fixed::frac::U16>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (4 - 2));
let expected = Dst::from_bits(0b111 << (16 - 2));
assert_eq!(src.checked_to_fixed::<Dst>(), Some(expected));
type TooFewIntBits = fixed::",
            $s_fixed,
            "<fixed::frac::U6>;
assert!(Src::max_value().checked_to_fixed::<TooFewIntBits>().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
            #[inline]
            pub fn checked_to_fixed<F>(self) -> Option<F>
            where
                F: Fixed,
            {
                SealedFixed::checked_from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from an integer if it fits,
otherwise returns [`None`].

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::checked_from_int(3), Some(Fix::from_bits(3 << 4)));
let too_large = ",
            $s_inner,
            "::max_value();
assert!(Fix::checked_from_int(too_large).is_none());
let too_small = ",
            if_signed_unsigned!(
                $Signedness,
                concat!($s_inner, "::min_value()"),
                "-1",
            ),
            ";
assert!(Fix::checked_from_int(too_small).is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn checked_from_int<I>(val: I) -> Option<$Fixed<Frac>>
            where
                I: Int,
            {
                SealedInt::checked_to_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to an integer if it fits,
otherwise returns [`None`].

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

Any fractional bits are truncated.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.checked_to_int::<i32>(), Some(2));
assert_eq!(",
            if_signed_unsigned!(
                $Signedness,
                "(-two_point_5).checked_to_int::<i64>(), Some(-3",
                "two_point_5.checked_to_int::<i64>(), Some(2",
            ),
            "));
type AllInt = fixed::",
            $s_fixed,
            "<fixed::frac::U0>;
assert!(AllInt::",
            if_signed_unsigned!(
                $Signedness,
                "from_bits(-1).checked_to_int::<u",
                "max_value().checked_to_int::<i",
            ),
            $s_nbits,
            ">().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn checked_to_int<I>(self) -> Option<I>
            where
                I: Int,
            {
                SealedInt::checked_from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from a floating-point number
if it fits, otherwise returns [`None`].

The floating-point number can be of type [`f32`] or [`f64`]. If the
[`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let expected = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::checked_from_float(1.75f32), Some(expected));
assert_eq!(Fix::checked_from_float(",
            if_signed_unsigned!(
                $Signedness,
                "-1.75f64), Some(-",
                "1.75f64), Some(",
            ),
            "expected));
assert!(Fix::checked_from_float(2e38).is_none());
assert!(Fix::checked_from_float(std::f64::NAN).is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
";
            #[inline]
            pub fn checked_from_float<F>(val: F) -> Option<$Fixed<Frac>>
            where
                F: Float,
            {
                SealedFloat::checked_to_fixed(val)
            }
        );

        comment!(
            "Creates a fixed-point number from another fixed-point
number, saturating the value if it does not fit.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::saturating_from_fixed(src), Dst::from_bits(0b111 << (4 - 2)));
let too_large = fixed::",
            $s_fixed,
            "::<fixed::frac::U2>::max_value();
assert_eq!(Dst::saturating_from_fixed(too_large), Dst::max_value());
let too_small = ",
            if_signed_unsigned!(
                $Signedness,
                concat!("fixed::", $s_fixed, "::<fixed::frac::U2>::min_value()"),
                "Src::from_bits(-1)"
            ),
            ";
assert_eq!(Dst::saturating_from_fixed(too_small), Dst::min_value());
```
";
            #[inline]
            pub fn saturating_from_fixed<F>(val: F) -> $Fixed<Frac>
            where
                F: Fixed,
            {
                SealedFixed::saturating_from_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to another fixed-point
number, saturating the value if it does not fit.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
type Dst = fixed::FixedI32<fixed::frac::U16>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (4 - 2));
assert_eq!(src.saturating_to_fixed::<Dst>(), Dst::from_bits(0b111 << (16 - 2)));
type TooFewIntBits = fixed::",
            $s_fixed,
            "<fixed::frac::U6>;
let saturated = Src::max_value().saturating_to_fixed::<TooFewIntBits>();
assert_eq!(saturated, TooFewIntBits::max_value());
```
";
            #[inline]
            pub fn saturating_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedFixed::saturating_from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from an integer, saturating
the value if it does not fit.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::saturating_from_int(3), Fix::from_bits(3 << 4));
let too_large = ",
            $s_inner,
            "::max_value();
assert_eq!(Fix::saturating_from_int(too_large), Fix::max_value());
let too_small = ",
            if_signed_unsigned!(
                $Signedness,
                concat!($s_inner, "::min_value()"),
                "-1",
            ),
            ";
assert_eq!(Fix::saturating_from_int(too_small), Fix::min_value());
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn saturating_from_int<I>(val: I) -> $Fixed<Frac>
            where
                I: Int,
            {
                SealedInt::saturating_to_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to an integer, saturating
the value if it does not fit.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

Any fractional bits are truncated.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.saturating_to_int::<i32>(), 2);
assert_eq!(",
            if_signed_unsigned!(
                $Signedness,
                "(-two_point_5).saturating_to_int::<i64>(), -3",
                "two_point_5.saturating_to_int::<i64>(), 2",
            ),
            ");
type AllInt = fixed::",
            $s_fixed,
            "<fixed::frac::U0>;
assert_eq!(",
            if_signed_unsigned!(
                $Signedness,
                concat!(
                    "AllInt::from_bits(-1).saturating_to_int::<u",
                    $s_nbits,
                    ">(), 0",
                ),
                concat!(
                    "AllInt::max_value().saturating_to_int::<i",
                    $s_nbits,
                    ">(), i",
                    $s_nbits,
                    "::max_value()",
                ),
            ),
            ");
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn saturating_to_int<I>(self) -> I
            where
                I: Int,
            {
                SealedInt::saturating_from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from a floating-point
number, saturating the value if it does not fit.

The floating-point value can be of type [`f32`] or [`f64`].
If the [`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Panics

This method panics if the value is [NaN].

# Examples

```rust
use std::f64;
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.625 is 1.101 in binary
let one_point_625 = Fix::from_bits(0b1101 << (4 - 3));
assert_eq!(Fix::saturating_from_float(1.625f32), one_point_625);
assert_eq!(Fix::saturating_from_float(2e38), Fix::max_value());
assert_eq!(Fix::saturating_from_float(f64::NEG_INFINITY), Fix::min_value());
```

[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[NaN]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_nan
";
            #[inline]
            pub fn saturating_from_float<F>(val: F) -> $Fixed<Frac>
            where
                F: Float,
            {
                SealedFloat::saturating_to_fixed(val)
            }
        );

        comment!(
            "Creates a fixed-point number from another fixed-point
number, wrapping the value on overflow.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
let expected = Dst::from_bits(0b111 << (4 - 2));
assert_eq!(Dst::wrapping_from_fixed(src), expected);
// integer 0b1101 << (",
            $s_nbits,
            " - 7) will wrap to fixed-point 1010...
let too_large = fixed::",
            $s_fixed,
            "::<fixed::frac::U0>::from_bits(0b1101 << (",
            $s_nbits,
            " - 7));
let wrapped = Dst::from_bits(0b1010 << (",
            $s_nbits,
            " - 4));
assert_eq!(Dst::wrapping_from_fixed(too_large), wrapped);
```
";
            #[inline]
            pub fn wrapping_from_fixed<F>(val: F) -> $Fixed<Frac>
            where
                F: Fixed,
            {
                SealedFixed::wrapping_from_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to another fixed-point
number, wrapping the value on overflow.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
type Dst = fixed::FixedI32<fixed::frac::U16>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (4 - 2));
let expected = Dst::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::wrapping_from_fixed(src), expected);
type TooFewIntBits = fixed::",
            $s_fixed,
            "<fixed::frac::U6>;
let wrapped = TooFewIntBits::from_bits(Src::max_value().to_bits() << 2);
assert_eq!(Src::max_value().wrapping_to_fixed::<TooFewIntBits>(), wrapped);
```
";
            #[inline]
            pub fn wrapping_to_fixed<F>(self) -> F
            where
                F: Fixed,
            {
                SealedFixed::wrapping_from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from an integer, wrapping
the value on overflow.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::wrapping_from_int(3), Fix::from_bits(3 << 4));
// integer 0b1101 << (",
            $s_nbits,
            " - 7) will wrap to fixed-point 1010...
let large: ",
            $s_inner,
            " = 0b1101 << (",
            $s_nbits,
            " - 7);
let wrapped = Fix::from_bits(0b1010 << (",
            $s_nbits,
            " - 4));
assert_eq!(Fix::wrapping_from_int(large), wrapped);
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn wrapping_from_int<I>(val: I) -> $Fixed<Frac>
            where
                I: Int,
            {
                SealedInt::wrapping_to_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to an integer, wrapping the
value on overflow.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

Any fractional bits are truncated.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.wrapping_to_int::<i32>(), 2);
assert_eq!(",
            if_signed_unsigned!(
                $Signedness,
                "(-two_point_5).wrapping_to_int::<i64>(), -3",
                "two_point_5.wrapping_to_int::<i64>(), 2",
            ),
            ");
type AllInt = fixed::",
            $s_fixed,
            "<fixed::frac::U0>;
assert_eq!(",
            if_signed_unsigned!(
                $Signedness,
                concat!(
                    "AllInt::from_bits(-1).wrapping_to_int::<u",
                    $s_nbits,
                    ">(), u",
                    $s_nbits,
                    "::max_value()",
                ),
                concat!(
                    "AllInt::max_value().wrapping_to_int::<i",
                    $s_nbits,
                    ">(), -1",
                ),
            ),
            ");
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn wrapping_to_int<I>(self) -> I
            where
                I: Int,
            {
                SealedInt::wrapping_from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from a floating-point
number, wrapping the value on overflow.

The floating-point value can be of type [`f32`] or [`f64`].
If the [`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Panics

This method panics if the value is not [finite].

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let from_bits = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::wrapping_from_float(1.75f32), from_bits);
assert_eq!(Fix::wrapping_from_float(",
            if_signed_unsigned!($Signedness, "-1.75f64), -", "1.75f64), "),
            "from_bits);
// 1.75 << (",
            $s_nbits,
            " - 4) wraps to binary 11000...
let large = 1.75 * 2f32.powi(",
            $s_nbits,
            " - 4);
let wrapped = Fix::from_bits(0b1100 << (",
            $s_nbits,
            " - 4));
assert_eq!(Fix::wrapping_from_float(large), wrapped);
```

[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
";
            #[inline]
            pub fn wrapping_from_float<F>(val: F) -> $Fixed<Frac>
            where
                F: Float,
            {
                SealedFloat::wrapping_to_fixed(val)
            }
        );

        comment!(
            "Creates a fixed-point number from another fixed-point
number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
let expected = Dst::from_bits(0b111 << (4 - 2));
assert_eq!(Dst::overflowing_from_fixed(src), (expected, false));
// integer 0b1101 << (",
            $s_nbits,
            " - 7) will wrap to fixed-point 1010...
let too_large = fixed::",
            $s_fixed,
            "::<fixed::frac::U0>::from_bits(0b1101 << (",
            $s_nbits,
            " - 7));
let wrapped = Dst::from_bits(0b1010 << (",
            $s_nbits,
            " - 4));
assert_eq!(Dst::overflowing_from_fixed(too_large), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_from_fixed<F>(val: F) -> ($Fixed<Frac>, bool)
            where
                F: Fixed,
            {
                SealedFixed::overflowing_from_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to another fixed-point
number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
type Dst = fixed::FixedI32<fixed::frac::U16>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (4 - 2));
let expected = Dst::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::overflowing_from_fixed(src), (expected, false));
type TooFewIntBits = fixed::",
            $s_fixed,
            "<fixed::frac::U6>;
let wrapped = TooFewIntBits::from_bits(Src::max_value().to_bits() << 2);
assert_eq!(Src::max_value().overflowing_to_fixed::<TooFewIntBits>(), (wrapped, true));
```
";
            #[inline]
            pub fn overflowing_to_fixed<F>(self) -> (F, bool)
            where
                F: Fixed,
            {
                SealedFixed::overflowing_from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from an integer.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
assert_eq!(Fix::overflowing_from_int(3), (Fix::from_bits(3 << 4), false));
// integer 0b1101 << (",
            $s_nbits,
            " - 7) will wrap to fixed-point 1010...
let large: ",
            $s_inner,
            " = 0b1101 << (",
            $s_nbits,
            " - 7);
let wrapped = Fix::from_bits(0b1010 << (",
            $s_nbits,
            " - 4));
assert_eq!(Fix::overflowing_from_int(large), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_from_int<I>(val: I) -> ($Fixed<Frac>, bool)
            where
                I: Int,
            {
                SealedInt::overflowing_to_fixed(val)
            }
        );

        comment!(
            "Converts a fixed-point number to an integer.

Returns a [tuple] of the integer and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and
[`usize`].

Any fractional bits are truncated.

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.overflowing_to_int::<i32>(), (2, false));
assert_eq!(",
            if_signed_unsigned!(
                $Signedness,
                "(-two_point_5).overflowing_to_int::<i64>(), (-3",
                "two_point_5.overflowing_to_int::<i64>(), (2",
            ),
            ", false));
let does_not_fit = fixed::",
            $s_fixed,
            "::<fixed::frac::U0>::",
            if_signed_unsigned!($Signedness, "from_bits(-1)", "max_value()"),
            ";
let wrapped = ",
            if_signed_unsigned!(
                $Signedness,
                concat!("1u", $s_nbits, ".wrapping_neg()"),
                concat!("-1i", $s_nbits),
            ),
            ";
assert_eq!(does_not_fit.overflowing_to_int::<",
            if_signed_unsigned!($Signedness, "u", "i"),
            $s_nbits,
            ">(), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_to_int<I>(self) -> (I, bool)
            where
                I: Int,
            {
                SealedInt::overflowing_from_fixed(self)
            }
        );

        comment!(
            "Creates a fixed-point number from a floating-point
number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating whether
an overflow has occurred. On overflow, the wrapped value is returned.

The floating-point value can be of type [`f32`] or [`f64`].
If the [`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Panics

This method panics if the value is not [finite].

# Examples

```rust
type Fix = fixed::",
            $s_fixed,
            "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let from_bits = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::overflowing_from_float(1.75f32), (from_bits, false));
assert_eq!(Fix::overflowing_from_float(",
            if_signed_unsigned!($Signedness, "-1.75f64), (-", "1.75f64), ("),
            "from_bits, false));
// 1.75 << (",
            $s_nbits,
            " - 4) wraps to binary 11000...
let large = 1.75 * 2f32.powi(",
            $s_nbits,
            " - 4);
let wrapped = Fix::from_bits(0b1100 << (",
            $s_nbits,
            " - 4));
assert_eq!(Fix::overflowing_from_float(large), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_from_float<F>(val: F) -> ($Fixed<Frac>, bool)
            where
                F: Float,
            {
                SealedFloat::overflowing_to_fixed(val)
            }
        );
    };
}
