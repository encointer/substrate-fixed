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
        comment! {
            "Creates a fixed-point number from another number.

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`].
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other number `src` for which [`ToFixed`] is implemented, in
    which case this method returns [`src.to_fixed()`][`to_fixed`].

# Panics

For floating-point numbers, panics if the value is not [finite].

When debug assertions are enabled, panics if the value does not fit.
When debug assertions are not enabled, the wrapped value can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_from_num`] instead.

# Examples

```rust
use substrate_fixed::{types::extra::U4, types::I16F16, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = I16F16::from_bits(0b111 << (16 - 2));
assert_eq!(Fix::from_num(src), Fix::from_bits(0b111 << (4 - 2)));

assert_eq!(Fix::from_num(3i32), Fix::from_bits(3 << 4));
assert_eq!(Fix::from_num(",
            if_signed_unsigned! {
                $Signedness,
                "-3i64), Fix::from_bits(-",
                "3i64), Fix::from_bits(",
            },
            "3 << 4));

assert_eq!(Fix::from_num(1.75f32), Fix::from_bits(0b111 << (4 - 2)));
assert_eq!(Fix::from_num(",
            if_signed_unsigned! {
                $Signedness,
                "-1.75f64), Fix::from_bits(-",
                "1.75f64), Fix::from_bits(",
            },
            "0b111 << (4-2)));
```

[`ToFixed`]: traits/trait.ToFixed.html
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`to_fixed`]: traits/trait.ToFixed.html#tymethod.to_fixed
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[`wrapping_from_num`]: #method.wrapping_from_num
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
";
            #[inline]
            pub fn from_num<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                src.to_fixed()
            }
        }

        comment! {
            "Converts a fixed-point number to another number.

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`]. Any fractional bits are truncated.
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other type `Dst` for which [`FromFixed`] is implemented, in
    which case this method returns
    [`Dst::from_fixed(self)`][`from_fixed`].

# Panics

When debug assertions are enabled, panics if the value does not fit.
When debug assertions are not enabled, the wrapped value can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_to_num`] instead.

# Examples

```rust
use substrate_fixed::{types::extra::U4, types::I30F2, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(src.to_num::<I30F2>(), I30F2::from_bits(0b111));
// src >> 2 is 0.0111, which for I30F2 is truncated to 0.01
assert_eq!((src >> 2u32).to_num::<I30F2>(), I30F2::from_bits(1));

// 2.5 is 10.1 in binary
let two_point_5 = Fix::from_bits(0b101 << (4 - 1));
assert_eq!(two_point_5.to_num::<i32>(), 2);
assert_eq!(",
            if_signed_unsigned! {
                $Signedness,
                "(-two_point_5).to_num::<i64>(), -3",
                "two_point_5.to_num::<i64>(), 2",
            },
            ");

// 1.625 is 1.101 in binary
let one_point_625 = Fix::from_bits(0b1101 << (4 - 3));
assert_eq!(one_point_625.to_num::<f32>(), 1.625f32);
assert_eq!(",
            if_signed_unsigned! {
                $Signedness,
                "(-one_point_625).to_num::<f64>(), -",
                "one_point_625.to_num::<f64>(), "
            },
            "1.625f64);
```

[`FromFixed`]: traits/trait.FromFixed.html
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`from_fixed`]: traits/trait.FromFixed.html#tymethod.from_fixed
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
[`wrapping_to_num`]: #method.wrapping_to_num
";
            #[inline]
            pub fn to_num<Dst: FromFixed>(self) -> Dst {
                Dst::from_fixed(self)
            }
        }

        comment! {
            "Creates a fixed-point number from another number if it
fits, otherwise returns [`None`].

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`].
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other number `src` for which [`ToFixed`] is implemented, in
    which case this method returns [`src.checked_to_fixed()`][`checked_to_fixed`].

# Examples

```rust
use substrate_fixed::{
    types::extra::{U2, U4},
    types::I16F16,
    ", $s_fixed, ",
};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = I16F16::from_bits(0b111 << (16 - 2));
assert_eq!(Fix::checked_from_num(src), Some(Fix::from_bits(0b111 << (4 - 2))));
let too_large = ", $s_fixed, "::<U2>::max_value();
assert!(Fix::checked_from_num(too_large).is_none());

assert_eq!(Fix::checked_from_num(3), Some(Fix::from_bits(3 << 4)));
let too_large = ", $s_inner, "::max_value();
assert!(Fix::checked_from_num(too_large).is_none());
let too_small = ",
            if_signed_unsigned! {
                $Signedness,
                concat!($s_inner, "::min_value()"),
                "-1",
            },
            ";
assert!(Fix::checked_from_num(too_small).is_none());

// 1.75 is 1.11 in binary
let expected = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::checked_from_num(1.75f32), Some(expected));
assert_eq!(Fix::checked_from_num(",
            if_signed_unsigned! {
                $Signedness,
                "-1.75f64), Some(-",
                "1.75f64), Some(",
            },
            "expected));
assert!(Fix::checked_from_num(2e38).is_none());
assert!(Fix::checked_from_num(std::f64::NAN).is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
[`ToFixed`]: traits/trait.ToFixed.html
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`checked_to_fixed`]: traits/trait.ToFixed.html#tymethod.checked_to_fixed
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn checked_from_num<Src: ToFixed>(src: Src) -> Option<$Fixed<Frac>> {
                src.checked_to_fixed()
            }
        }

        comment! {
            "Converts a fixed-point number to another number if it
fits, otherwise returns [`None`].

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`]. Any fractional bits are truncated.
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other type `Dst` for which [`FromFixed`] is implemented, in
    which case this method returns
    [`Dst::checked_from_fixed(self)`][`checked_from_fixed`].

# Examples

```rust
use substrate_fixed::{
    types::extra::{U0, U4, U6},
    types::I16F16,
    ", $s_fixed, ",
};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = Fix::from_bits(0b111 << (4 - 2));
let expected = I16F16::from_bits(0b111 << (16 - 2));
assert_eq!(src.checked_to_num::<I16F16>(), Some(expected));
type TooFewIntBits = ", $s_fixed, "<U6>;
assert!(Fix::max_value().checked_to_num::<TooFewIntBits>().is_none());

// 2.5 is 10.1 in binary
let two_point_5 = Fix::from_bits(0b101 << (4 - 1));
assert_eq!(two_point_5.checked_to_num::<i32>(), Some(2));
assert_eq!(",
            if_signed_unsigned! {
                $Signedness,
                "(-two_point_5).checked_to_num::<i64>(), Some(-3",
                "two_point_5.checked_to_num::<i64>(), Some(2",
            },
            "));
type AllInt = ", $s_fixed, "<U0>;
assert!(AllInt::",
            if_signed_unsigned! {
                $Signedness,
                "from_bits(-1).checked_to_num::<u",
                "max_value().checked_to_num::<i",
            },
            $s_nbits, ">().is_none());

// 1.625 is 1.101 in binary
let one_point_625 = Fix::from_bits(0b1101 << (4 - 3));
assert_eq!(one_point_625.checked_to_num::<f32>(), Some(1.625f32));
```

[`FromFixed`]: traits/trait.FromFixed.html
[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`checked_from_fixed`]: traits/trait.FromFixed.html#tymethod.checked_from_fixed
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
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
            pub fn checked_to_num<Dst: FromFixed>(self) -> Option<Dst> {
                Dst::checked_from_fixed(self)
            }
        }

        comment! {
            "Creates a fixed-point number from another number,
saturating if it does not fit.

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`].
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other number `src` for which [`ToFixed`] is implemented, in
    which case this method returns
    [`src.saturating_to_fixed()`][`saturating_to_fixed`].

# Panics

This method panics if the value is a floating-point [NaN].

# Examples

```rust
use substrate_fixed::{
    types::extra::{U2, U4},
    types::I16F16,
    ", $s_fixed, ",
};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = I16F16::from_bits(0b111 << (16 - 2));
assert_eq!(Fix::saturating_from_num(src), Fix::from_bits(0b111 << (4 - 2)));
let too_large = ", $s_fixed, "::<U2>::max_value();
assert_eq!(Fix::saturating_from_num(too_large), Fix::max_value());

assert_eq!(Fix::saturating_from_num(3), Fix::from_bits(3 << 4));
let too_small = ",
            if_signed_unsigned! {
                $Signedness,
                concat!($s_inner, "::min_value()"),
                "-1",
            },
            ";
assert_eq!(Fix::saturating_from_num(too_small), Fix::min_value());

// 1.75 is 1.11 in binary
let expected = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::saturating_from_num(1.75f32), expected);
assert_eq!(Fix::saturating_from_num(",
            if_signed_unsigned! {
                $Signedness,
                "-1.75f64), -",
                "1.75f64), ",
            },
            "expected);
assert_eq!(Fix::saturating_from_num(2e38), Fix::max_value());
assert_eq!(Fix::saturating_from_num(std::f64::NEG_INFINITY), Fix::min_value());
```

[NaN]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_nan
[`ToFixed`]: traits/trait.ToFixed.html
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`saturating_to_fixed`]: traits/trait.ToFixed.html#tymethod.saturating_to_fixed
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn saturating_from_num<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                src.saturating_to_fixed()
            }
        }

        comment! {
            "Converts a fixed-point number to another number,
saturating the value if it does not fit.

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`]. Any fractional bits are truncated.
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other type `Dst` for which [`FromFixed`] is implemented, in
    which case this method returns
    [`Dst::saturating_from_fixed(self)`][`saturating_from_fixed`].

# Examples

```rust
use substrate_fixed::{
    types::extra::{U0, U4, U6},
    types::I16F16,
    ", $s_fixed, ",
};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = Fix::from_bits(0b111 << (4 - 2));
let expected = I16F16::from_bits(0b111 << (16 - 2));
assert_eq!(src.saturating_to_num::<I16F16>(), expected);
type TooFewIntBits = ", $s_fixed, "<U6>;
let saturated = Fix::max_value().saturating_to_num::<TooFewIntBits>();
assert_eq!(saturated, TooFewIntBits::max_value());

// 2.5 is 10.1 in binary
let two_point_5 = Fix::from_bits(0b101 << (4 - 1));
assert_eq!(two_point_5.saturating_to_num::<i32>(), 2);
type AllInt = ", $s_fixed, "<U0>;
assert_eq!(",
            if_signed_unsigned! {
                $Signedness,
                concat!("AllInt::from_bits(-1).saturating_to_num::<u", $s_nbits, ">(), 0"),
                concat!(
                    "AllInt::max_value().saturating_to_num::<i", $s_nbits, ">(), ",
                    "i", $s_nbits, "::max_value()",
                ),
            },
            ");

// 1.625 is 1.101 in binary
let one_point_625 = Fix::from_bits(0b1101 << (4 - 3));
assert_eq!(one_point_625.saturating_to_num::<f32>(), 1.625f32);
```

[`FromFixed`]: traits/trait.FromFixed.html
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`saturating_from_fixed`]: traits/trait.FromFixed.html#tymethod.saturating_from_fixed
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
";
            #[inline]
            pub fn saturating_to_num<Dst: FromFixed>(self) -> Dst {
                Dst::saturating_from_fixed(self)
            }
        }

        comment! {
            "Creates a fixed-point number from another number,
wrapping the value on overflow.

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`].
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other number `src` for which [`ToFixed`] is implemented, in
    which case this method returns [`src.wrapping_to_fixed()`][`wrapping_to_fixed`].

# Panics

For floating-point numbers, panics if the value is not [finite].

# Examples

```rust
use substrate_fixed::{
    types::extra::{U0, U4},
    types::I16F16,
    ", $s_fixed, ",
};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = I16F16::from_bits(0b111 << (16 - 2));
assert_eq!(Fix::wrapping_from_num(src), Fix::from_bits(0b111 << (4 - 2)));
// integer 0b1101 << (", $s_nbits, " - 7) will wrap to fixed-point 1010...
let too_large = ", $s_fixed, "::<U0>::from_bits(0b1101 << (", $s_nbits, " - 7));
let wrapped = Fix::from_bits(0b1010 << (", $s_nbits, " - 4));
assert_eq!(Fix::wrapping_from_num(too_large), wrapped);

// integer 0b1101 << (", $s_nbits, " - 7) will wrap to fixed-point 1010...
let large: ", $s_inner, " = 0b1101 << (", $s_nbits, " - 7);
let wrapped = Fix::from_bits(0b1010 << (", $s_nbits, " - 4));
assert_eq!(Fix::wrapping_from_num(large), wrapped);

// 1.75 is 1.11 in binary
let expected = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::wrapping_from_num(1.75f32), expected);
// 1.75 << (", $s_nbits, " - 4) wraps to binary 11000...
let large = 1.75 * 2f32.powi(", $s_nbits, " - 4);
let wrapped = Fix::from_bits(0b1100 << (", $s_nbits, " - 4));
assert_eq!(Fix::wrapping_from_num(large), wrapped);
```

[`ToFixed`]: traits/trait.ToFixed.html
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`wrapping_to_fixed`]: traits/trait.ToFixed.html#tymethod.wrapping_to_fixed
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
";
            #[inline]
            pub fn wrapping_from_num<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
                src.wrapping_to_fixed()
            }
        }

        comment! {
            "Converts a fixed-point number to another number,
wrapping the value on overflow.

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`]. Any fractional bits are truncated.
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other type `Dst` for which [`FromFixed`] is implemented, in
    which case this method returns
    [`Dst::wrapping_from_fixed(self)`][`wrapping_from_fixed`].

# Examples

```rust
use substrate_fixed::{
    types::extra::{U0, U4, U6},
    types::I16F16,
    ", $s_fixed, ",
};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = Fix::from_bits(0b111 << (4 - 2));
let expected = I16F16::from_bits(0b111 << (16 - 2));
assert_eq!(src.wrapping_to_num::<I16F16>(), expected);
type TooFewIntBits = ", $s_fixed, "<U6>;
let wrapped = TooFewIntBits::from_bits(Fix::max_value().to_bits() << 2);
assert_eq!(Fix::max_value().wrapping_to_num::<TooFewIntBits>(), wrapped);

// 2.5 is 10.1 in binary
let two_point_5 = Fix::from_bits(0b101 << (4 - 1));
assert_eq!(two_point_5.wrapping_to_num::<i32>(), 2);
type AllInt = ", $s_fixed, "<U0>;
assert_eq!(",
            if_signed_unsigned! {
                $Signedness,
                concat!(
                    "AllInt::from_bits(-1).wrapping_to_num::<u", $s_nbits, ">(), ",
                    "u", $s_nbits, "::max_value()",
                ),
                concat!("AllInt::max_value().wrapping_to_num::<i", $s_nbits, ">(), -1"),
            },
            ");

// 1.625 is 1.101 in binary
let one_point_625 = Fix::from_bits(0b1101 << (4 - 3));
assert_eq!(one_point_625.wrapping_to_num::<f32>(), 1.625f32);
```

[`FromFixed`]: traits/trait.FromFixed.html
[`wrapping_from_fixed`]: traits/trait.FromFixed.html#tymethod.wrapping_from_fixed
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
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
            pub fn wrapping_to_num<Dst: FromFixed>(self) -> Dst {
                Dst::wrapping_from_fixed(self)
            }
        }

        comment! {
            "Creates a fixed-point number from another number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`].
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`]. For this
    conversion, the method rounds to the nearest, with ties rounding
    to even.
  * Any other number `src` for which [`ToFixed`] is implemented, in
    which case this method returns [`src.overflowing_to_fixed()`][`overflowing_to_fixed`].

# Panics

For floating-point numbers, panics if the value is not [finite].

# Examples

```rust
use substrate_fixed::{
    types::extra::{U0, U4},
    types::I16F16,
    ", $s_fixed, ",
};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = I16F16::from_bits(0b111 << (16 - 2));
let expected = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::overflowing_from_num(src), (expected, false));
// integer 0b1101 << (", $s_nbits, " - 7) will wrap to fixed-point 1010...
let too_large = ", $s_fixed, "::<U0>::from_bits(0b1101 << (", $s_nbits, " - 7));
let wrapped = Fix::from_bits(0b1010 << (", $s_nbits, " - 4));
assert_eq!(Fix::overflowing_from_num(too_large), (wrapped, true));

assert_eq!(Fix::overflowing_from_num(3), (Fix::from_bits(3 << 4), false));
// integer 0b1101 << (", $s_nbits, " - 7) will wrap to fixed-point 1010...
let large: ", $s_inner, " = 0b1101 << (", $s_nbits, " - 7);
let wrapped = Fix::from_bits(0b1010 << (", $s_nbits, " - 4));
assert_eq!(Fix::overflowing_from_num(large), (wrapped, true));

// 1.75 is 1.11 in binary
let expected = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::overflowing_from_num(1.75f32), (expected, false));
// 1.75 << (", $s_nbits, " - 4) wraps to binary 11000...
let large = 1.75 * 2f32.powi(", $s_nbits, " - 4);
let wrapped = Fix::from_bits(0b1100 << (", $s_nbits, " - 4));
assert_eq!(Fix::overflowing_from_num(large), (wrapped, true));
```

[`ToFixed`]: traits/trait.ToFixed.html
[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`overflowing_to_fixed`]: traits/trait.ToFixed.html#tymethod.overflowing_to_fixed
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_from_num<Src: ToFixed>(src: Src) -> ($Fixed<Frac>, bool) {
                src.overflowing_to_fixed()
            }
        }

        comment! {
            "Converts a fixed-point number to another number.

Returns a [tuple] of the number and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

The other number can be:

  * Another fixed-point number. Any extra fractional bits are truncated.
  * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    [`usize`]. Any fractional bits are truncated.
  * A floating-point number of type [`f32`] or [`f64`]. If the [`f16`
    feature] is enabled, it can also be of type [`f16`] or [`bf16`].
    For this conversion, the method rounds to the nearest, with ties
    rounding to even.
  * Any other type `Dst` for which [`FromFixed`] is implemented, in
    which case this method returns
    [`Dst::overflowing_from_fixed(self)`][`overflowing_from_fixed`].

# Examples

```rust
use substrate_fixed::{
    types::extra::{U0, U4, U6},
    types::I16F16,
    ", $s_fixed, ",
};
type Fix = ", $s_fixed, "<U4>;

// 1.75 is 1.11 in binary
let src = Fix::from_bits(0b111 << (4 - 2));
let expected = I16F16::from_bits(0b111 << (16 - 2));
assert_eq!(src.overflowing_to_num::<I16F16>(), (expected, false));
type TooFewIntBits = ", $s_fixed, "<U6>;
let wrapped = TooFewIntBits::from_bits(Fix::max_value().to_bits() << 2);
assert_eq!(Fix::max_value().overflowing_to_num::<TooFewIntBits>(), (wrapped, true));

// 2.5 is 10.1 in binary
let two_point_5 = Fix::from_bits(0b101 << (4 - 1));
assert_eq!(two_point_5.overflowing_to_num::<i32>(), (2, false));
let does_not_fit = ", $s_fixed, "::<U0>::",
            if_signed_unsigned! { $Signedness, "from_bits(-1)", "max_value()" },
            ";
let wrapped = ",
            if_signed_unsigned! {
                $Signedness,
                concat!("1u", $s_nbits, ".wrapping_neg()"),
                concat!("-1i", $s_nbits),
            },
            ";
assert_eq!(does_not_fit.overflowing_to_num::<",
            if_signed_unsigned! { $Signedness, "u", "i" },
            $s_nbits, ">(), (wrapped, true));

// 1.625 is 1.101 in binary
let one_point_625 = Fix::from_bits(0b1101 << (4 - 3));
assert_eq!(one_point_625.overflowing_to_num::<f32>(), (1.625f32, false));
```

[`FromFixed`]: traits/trait.FromFixed.html
[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`overflowing_from_fixed`]: traits/trait.FromFixed.html#tymethod.overflowing_from_fixed
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_to_num<Dst: FromFixed>(self) -> (Dst, bool) {
                Dst::overflowing_from_fixed(self)
            }
        }

        comment! {
            "Parses a string slice containing binary digits to return a fixed-point number.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
use substrate_fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 1.75 is 1.11 in binary
let f = Fix::from_str_binary(\"1.11\");
let check = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(f, Ok(check));
",
            if_signed_else_empty_str! {
                $Signedness,
                "let neg = Fix::from_str_binary(\"-1.11\");
assert_eq!(neg, Ok(-check));
",
            },
            "```
";
            #[inline]
            pub fn from_str_binary(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::from_str_radix(src, 2)
            }
        }

        comment! {
            "Parses a string slice containing octal digits to return a fixed-point number.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
use substrate_fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 1.75 is 1.11 in binary, 1.6 in octal
let f = Fix::from_str_octal(\"1.6\");
let check = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(f, Ok(check));
",
            if_signed_else_empty_str! {
                $Signedness,
                "let neg = Fix::from_str_octal(\"-1.6\");
assert_eq!(neg, Ok(-check));
",
            },
            "```
";
            #[inline]
            pub fn from_str_octal(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::from_str_radix(src, 8)
            }
        }

        comment! {
            "Parses a string slice containing hexadecimal digits to return a fixed-point number.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
use substrate_fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 1.75 is 1.11 in binary, 1.C in hexadecimal
let f = Fix::from_str_hex(\"1.C\");
let check = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(f, Ok(check));
",
            if_signed_else_empty_str! {
                $Signedness,
                "let neg = Fix::from_str_hex(\"-1.C\");
assert_eq!(neg, Ok(-check));
",
            },
            "```
";
            #[inline]
            pub fn from_str_hex(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::from_str_radix(src, 16)
            }
        }

        comment! {
            "Parses a string slice containing decimal digits to return a fixed-point number,
saturating on overflow.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
assert_eq!(I8F8::saturating_from_str(\"9999\"), Ok(I8F8::max_value()));
assert_eq!(I8F8::saturating_from_str(\"-9999\"), Ok(I8F8::min_value()));
",
                "use substrate_fixed::types::U8F8;
assert_eq!(U8F8::saturating_from_str(\"9999\"), Ok(U8F8::max_value()));
assert_eq!(U8F8::saturating_from_str(\"-1\"), Ok(U8F8::from_num(0)));
",
            },
            "```
";
            #[inline]
            pub fn saturating_from_str(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::saturating_from_str_radix(src, 10)
            }
        }

        comment! {
            "Parses a string slice containing binary digits to return a fixed-point number,
saturating on overflow.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
assert_eq!(I8F8::saturating_from_str_binary(\"101100111000\"), Ok(I8F8::max_value()));
assert_eq!(I8F8::saturating_from_str_binary(\"-101100111000\"), Ok(I8F8::min_value()));
",
                "use substrate_fixed::types::U8F8;
assert_eq!(U8F8::saturating_from_str_binary(\"101100111000\"), Ok(U8F8::max_value()));
assert_eq!(U8F8::saturating_from_str_binary(\"-1\"), Ok(U8F8::from_num(0)));
",
            },
            "```
";
            #[inline]
            pub fn saturating_from_str_binary(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::saturating_from_str_radix(src, 2)
            }
        }

        comment! {
            "Parses a string slice containing octal digits to return a fixed-point number,
saturating on overflow.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
assert_eq!(I8F8::saturating_from_str_octal(\"7777\"), Ok(I8F8::max_value()));
assert_eq!(I8F8::saturating_from_str_octal(\"-7777\"), Ok(I8F8::min_value()));
",
                "use substrate_fixed::types::U8F8;
assert_eq!(U8F8::saturating_from_str_octal(\"7777\"), Ok(U8F8::max_value()));
assert_eq!(U8F8::saturating_from_str_octal(\"-1\"), Ok(U8F8::from_num(0)));
",
            },
            "```
";
            #[inline]
            pub fn saturating_from_str_octal(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::saturating_from_str_radix(src, 8)
            }
        }

        comment! {
            "Prases a string slice containing hexadecimal digits to return a fixed-point number,
saturating on overflow.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
assert_eq!(I8F8::saturating_from_str_hex(\"FFFF\"), Ok(I8F8::max_value()));
assert_eq!(I8F8::saturating_from_str_hex(\"-FFFF\"), Ok(I8F8::min_value()));
",
                "use substrate_fixed::types::U8F8;
assert_eq!(U8F8::saturating_from_str_hex(\"FFFF\"), Ok(U8F8::max_value()));
assert_eq!(U8F8::saturating_from_str_hex(\"-1\"), Ok(U8F8::from_num(0)));
",
            },
            "```
";
            #[inline]
            pub fn saturating_from_str_hex(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::saturating_from_str_radix(src, 16)
            }
        }

        comment! {
            "Parses a string slice containing decimal digits to return a fixed-point number,
wrapping on overflow.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
// 9999.5 = 15.5 + 256 × n
assert_eq!(I8F8::wrapping_from_str(\"9999.5\"), Ok(I8F8::from_num(15.5)));
assert_eq!(I8F8::wrapping_from_str(\"-9999.5\"), Ok(I8F8::from_num(-15.5)));
",
                "use substrate_fixed::types::U8F8;
// 9999.5 = 15.5 + 256 × n
assert_eq!(U8F8::wrapping_from_str(\"9999.5\"), Ok(U8F8::from_num(15.5)));
assert_eq!(U8F8::wrapping_from_str(\"-9999.5\"), Ok(U8F8::from_num(240.5)));
",
            },
            "```
";
            #[inline]
            pub fn wrapping_from_str(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::wrapping_from_str_radix(src, 10)
            }
        }

        comment! {
            "Parses a string slice containing binary digits to return a fixed-point number,
wrapping on overflow.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
let check = I8F8::from_bits(0b1110001 << (8 - 1));
assert_eq!(I8F8::wrapping_from_str_binary(\"101100111000.1\"), Ok(check));
assert_eq!(I8F8::wrapping_from_str_binary(\"-101100111000.1\"), Ok(-check));
",
                "use substrate_fixed::types::U8F8;
let check = U8F8::from_bits(0b1110001 << (8 - 1));
assert_eq!(U8F8::wrapping_from_str_binary(\"101100111000.1\"), Ok(check));
assert_eq!(U8F8::wrapping_from_str_binary(\"-101100111000.1\"), Ok(check.wrapping_neg()));
",
            },
            "```
";
            #[inline]
            pub fn wrapping_from_str_binary(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::wrapping_from_str_radix(src, 2)
            }
        }

        comment! {
            "Parses a string slice containing octal digits to return a fixed-point number,
wrapping on overflow.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
let check = I8F8::from_bits(0o1654 << (8 - 3));
assert_eq!(I8F8::wrapping_from_str_octal(\"7165.4\"), Ok(check));
assert_eq!(I8F8::wrapping_from_str_octal(\"-7165.4\"), Ok(-check));
",
                "use substrate_fixed::types::U8F8;
let check = U8F8::from_bits(0o1654 << (8 - 3));
assert_eq!(U8F8::wrapping_from_str_octal(\"7165.4\"), Ok(check));
assert_eq!(U8F8::wrapping_from_str_octal(\"-7165.4\"), Ok(check.wrapping_neg()));
",
            },
            "```
";
            #[inline]
            pub fn wrapping_from_str_octal(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::wrapping_from_str_radix(src, 8)
            }
        }

        comment! {
            "Parses a string slice containing hexadecimal digits to return a fixed-point number,
wrapping on overflow.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
let check = I8F8::from_bits(0xFFE);
assert_eq!(I8F8::wrapping_from_str_hex(\"C0F.FE\"), Ok(check));
assert_eq!(I8F8::wrapping_from_str_hex(\"-C0F.FE\"), Ok(-check));
",
                "use substrate_fixed::types::U8F8;
let check = U8F8::from_bits(0xFFE);
assert_eq!(U8F8::wrapping_from_str_hex(\"C0F.FE\"), Ok(check));
assert_eq!(U8F8::wrapping_from_str_hex(\"-C0F.FE\"), Ok(check.wrapping_neg()));
",
            },
            "```
";
            #[inline]
            pub fn wrapping_from_str_hex(src: &str) -> Result<$Fixed<Frac>, ParseFixedError> {
                FromStrRadix::wrapping_from_str_radix(src, 16)
            }
        }

        comment! {
            "Parses a string slice containing decimal digits to return a fixed-point number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
assert_eq!(I8F8::overflowing_from_str(\"99.5\"), Ok((I8F8::from_num(99.5), false)));
// 9999.5 = 15.5 + 256 × n
assert_eq!(I8F8::overflowing_from_str(\"-9999.5\"), Ok((I8F8::from_num(-15.5), true)));
",
                "use substrate_fixed::types::U8F8;
assert_eq!(U8F8::overflowing_from_str(\"99.5\"), Ok((U8F8::from_num(99.5), false)));
// 9999.5 = 15.5 + 256 × n
assert_eq!(U8F8::overflowing_from_str(\"9999.5\"), Ok((U8F8::from_num(15.5), true)));
",
            },
            "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_from_str(
                src: &str,
            ) -> Result<($Fixed<Frac>, bool), ParseFixedError> {
                FromStrRadix::overflowing_from_str_radix(src, 10)
            }
        }

        comment! {
            "Parses a string slice containing binary digits to return a fixed-point number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
let check = I8F8::from_bits(0b1110001 << (8 - 1));
assert_eq!(I8F8::overflowing_from_str_binary(\"111000.1\"), Ok((check, false)));
assert_eq!(I8F8::overflowing_from_str_binary(\"-101100111000.1\"), Ok((-check, true)));
",
                "use substrate_fixed::types::U8F8;
let check = U8F8::from_bits(0b1110001 << (8 - 1));
assert_eq!(U8F8::overflowing_from_str_binary(\"111000.1\"), Ok((check, false)));
assert_eq!(U8F8::overflowing_from_str_binary(\"101100111000.1\"), Ok((check, true)));
",
            },
            "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_from_str_binary(
                src: &str,
            ) -> Result<($Fixed<Frac>, bool), ParseFixedError> {
                FromStrRadix::overflowing_from_str_radix(src, 2)
            }
        }

        comment! {
            "Parses a string slice containing octal digits to return a fixed-point number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
let check = I8F8::from_bits(0o1654 << (8 - 3));
assert_eq!(I8F8::overflowing_from_str_octal(\"165.4\"), Ok((check, false)));
assert_eq!(I8F8::overflowing_from_str_octal(\"-7165.4\"), Ok((-check, true)));
",
                "use substrate_fixed::types::U8F8;
let check = U8F8::from_bits(0o1654 << (8 - 3));
assert_eq!(U8F8::overflowing_from_str_octal(\"165.4\"), Ok((check, false)));
assert_eq!(U8F8::overflowing_from_str_octal(\"7165.4\"), Ok((check, true)));
",
            },
            "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_from_str_octal(
                src: &str,
            ) -> Result<($Fixed<Frac>, bool), ParseFixedError> {
                FromStrRadix::overflowing_from_str_radix(src, 8)
            }
        }

        comment! {
            "Parses a string slice containing hexadecimal digits to return a fixed-point number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Rounding is to the nearest, with ties rounded to even.

# Examples

```rust
",
            if_signed_unsigned! {
                $Signedness,
                "use substrate_fixed::types::I8F8;
let check = I8F8::from_bits(0xFFE);
assert_eq!(I8F8::overflowing_from_str_hex(\"F.FE\"), Ok((check, false)));
assert_eq!(I8F8::overflowing_from_str_hex(\"-C0F.FE\"), Ok((-check, true)));
",
                "use substrate_fixed::types::U8F8;
let check = U8F8::from_bits(0xFFE);
assert_eq!(U8F8::overflowing_from_str_hex(\"F.FE\"), Ok((check, false)));
assert_eq!(U8F8::overflowing_from_str_hex(\"C0F.FE\"), Ok((check, true)));
",
            },
            "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
            #[inline]
            pub fn overflowing_from_str_hex(
                src: &str,
            ) -> Result<($Fixed<Frac>, bool), ParseFixedError> {
                FromStrRadix::overflowing_from_str_radix(src, 16)
            }
        }
    };
}
