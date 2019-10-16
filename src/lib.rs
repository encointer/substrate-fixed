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

/*!
# Fixed-point numbers

The [*fixed* crate] provides fixed-point numbers.

  * [`FixedI8`] and [`FixedU8`] are eight-bit fixed-point numbers.
  * [`FixedI16`] and [`FixedU16`] are 16-bit fixed-point numbers.
  * [`FixedI32`] and [`FixedU32`] are 32-bit fixed-point numbers.
  * [`FixedI64`] and [`FixedU64`] are 64-bit fixed-point numbers.
  * [`FixedI128`] and [`FixedU128`] are 128-bit fixed-point numbers.

These types can have `Frac` fractional bits, where
0 ≤ `Frac` ≤ <i>n</i> and <i>n</i> is the total number of bits. When
`Frac` = 0, the fixed-point number behaves like an <i>n</i>-bit
integer. When `Frac` = <i>n</i>, the value <i>x</i> lies in the range
−0.5 ≤ <i>x</i> < 0.5 for signed numbers, and in the range
0 ≤ <i>x</i> < 1 for unsigned numbers.

Currently the [*typenum* crate] is used for the fractional bit count
`Frac`; it is planned to move to [const generics] when they are
supported by the Rust compiler.

The main features are

  * Representation of fixed-point numbers up to 128 bits wide.
  * Conversions between fixed-point numbers and numeric primitives.
  * Comparisons between fixed-point numbers and numeric primitives.
  * Parsing from strings in decimal, binary, octal and hexadecimal.
  * Display as decimal, binary, octal and hexadecimal.
  * Arithmetic and logic operations.

This crate does *not* provide general analytic functions.

  * No algebraic functions are provided, for example no `sqrt` or
    `pow`.
  * No trigonometric functions are provided, for example no `sin` or
    `cos`.
  * No other transcendental functions are provided, for example no
    `log` or `exp`.

The conversions supported cover the following cases.

  * Infallible lossless conversions between fixed-point numbers and
    numeric primitives are provided using [`From`] and [`Into`]. These
    never fail (infallible) and do not lose any bits (lossless).
  * Infallible lossy conversions between fixed-point numbers and
    numeric primitives are provided using the [`LossyFrom`] and
    [`LossyInto`] traits. The source can have more fractional bits
    than the destination.
  * Checked conversions between fixed-point numbers and numeric
    primitives are provided using the [`FromFixed`] and [`ToFixed`]
    traits, or using the [`from_num`] and [`to_num`] methods and
    [their checked versions][`checked_from_num`].
  * Fixed-point numbers can be parsed from decimal strings using
    [`FromStr`], and from binary, octal and hexadecimal strings using
    the [`from_str_binary`], [`from_str_octal`] and [`from_str_hex`]
    methods. The result is rounded to the nearest, with ties rounded
    to even.
  * Fixed-point numbers can be converted to strings using [`Display`],
    [`Binary`], [`Octal`], [`LowerHex`] and [`UpperHex`]. The output
    is rounded to the nearest, with ties rounded to even.

## Quick examples

```rust
use fixed::types::I20F12;

// 19/3 = 6 1/3
let six_and_third = I20F12::from_num(19) / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// find the ceil and convert to i32
assert_eq!(six_and_third.ceil().to_num::<i32>(), 7);
// we can also compare directly to integers
assert_eq!(six_and_third.ceil(), 7);
```

The type [`I20F12`] is a 32-bit fixed-point signed number with 20
integer bits and 12 fractional bits. It is an alias to
<code>[FixedI32][`FixedI32`]&lt;[U12][`U12`]&gt;</code>. The unsigned
counterpart would be [`U20F12`]. Aliases are provided for all
combinations of integer and fractional bits adding up to a total of
eight, 16, 32, 64 or 128 bits.

```rust
use fixed::types::{I4F4, I4F12};

// −8 ≤ I4F4 < 8 with steps of 1/16 (~0.06)
let a = I4F4::from_num(1);
// multiplication and division by integers are possible
let ans1 = a / 5 * 17;
// 1 / 5 × 17 = 3 2/5 (3.4), but we get 3 3/16 (~3.2)
assert_eq!(ans1, I4F4::from_bits((3 << 4) + 3));
assert_eq!(ans1.to_string(), "3.2");

// −8 ≤ I4F12 < 8 with steps of 1/4096 (~0.0002)
let wider_a = I4F12::from(a);
let wider_ans = wider_a / 5 * 17;
let ans2 = I4F4::from_num(wider_ans);
// now the answer is the much closer 3 6/16 (~3.4)
assert_eq!(ans2, I4F4::from_bits((3 << 4) + 6));
assert_eq!(ans2.to_string(), "3.4");
```

The second example shows some precision and conversion issues. The low
precision of `a` means that `a / 5` is 3⁄16 instead of 1⁄5, leading to
an inaccurate result `ans1` = 3 3⁄16 (~3.2). With a higher precision,
we get `wider_a / 5` equal to 819⁄4096, leading to a more accurate
intermediate result `wider_ans` = 3 1635⁄4096. When we convert back to
four fractional bits, we get `ans2` = 3 6⁄16 (~3.4).

Note that we can convert from [`I4F4`] to [`I4F12`] using [`From`], as
the target type has the same number of integer bits and a larger
number of fractional bits. Converting from [`I4F12`] to [`I4F4`]
cannot use [`From`] as we have less fractional bits, so we use
[`from_num`] instead.

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.4.6"
```

The *fixed* crate requires rustc version 1.34.0 or later.

## Optional features

The *fixed* crate has three optional feature:

 1. `az`, disabled by default. This implements the cast traits
    provided by the [*az* crate].
 2. `f16`, disabled by default. This provides conversion to/from
    [`f16`] and [`bf16`]. This features requires the [*half* crate].
 3. `serde`, disabled by default. This provides serialization support
    for the fixed-point types. This feature requires the
    [*serde* crate].

To enable features, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.fixed]
version = "0.4.6"
features = ["f16", "serde"]
```

## License

This crate is free software: you can redistribute it and/or modify it
under the terms of either

  * the [Apache License, Version 2.0][LICENSE-APACHE] or
  * the [MIT License][LICENSE-MIT]

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache
License, Version 2.0, shall be dual licensed as above, without any
additional terms or conditions.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*az* crate]: https://crates.io/crates/az
[*fixed* crate]: https://crates.io/crates/fixed
[*half* crate]: https://crates.io/crates/half
[*serde* crate]: https://crates.io/crates/serde
[*typenum* crate]: https://crates.io/crates/typenum
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`Binary`]: https://doc.rust-lang.org/nightly/std/fmt/trait.Binary.html
[`Display`]: https://doc.rust-lang.org/nightly/std/fmt/trait.Display.html
[`FixedI128`]: struct.FixedI128.html
[`FixedI16`]: struct.FixedI16.html
[`FixedI32`]: struct.FixedI32.html
[`FixedI64`]: struct.FixedI64.html
[`FixedI8`]: struct.FixedI8.html
[`FixedU128`]: struct.FixedU128.html
[`FixedU16`]: struct.FixedU16.html
[`FixedU32`]: struct.FixedU32.html
[`FixedU64`]: struct.FixedU64.html
[`FixedU8`]: struct.FixedU8.html
[`FromFixed`]: traits/trait.FromFixed.html
[`FromStr`]: https://doc.rust-lang.org/nightly/std/str/trait.FromStr.html
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`I20F12`]: types/type.I20F12.html
[`I4F12`]: types/type.I4F12.html
[`I4F4`]: types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`LossyFrom`]: traits/trait.LossyFrom.html
[`LossyInto`]: traits/trait.LossyInto.html
[`LowerHex`]: https://doc.rust-lang.org/nightly/std/fmt/trait.LowerHex.html
[`Octal`]: https://doc.rust-lang.org/nightly/std/fmt/trait.Octal.html
[`ToFixed`]: traits/trait.ToFixed.html
[`U12`]: types/extra/type.U12.html
[`U20F12`]: types/type.U20F12.html
[`UpperHex`]: https://doc.rust-lang.org/nightly/std/fmt/trait.UpperHex.html
[`bf16`]: https://docs.rs/half/^1/half/struct.bf16.html
[`checked_from_num`]: struct.FixedI32.html#method.checked_from_num
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`from_num`]: struct.FixedI32.html#method.from_num
[`from_str_binary`]: struct.FixedI32.html#method.from_str_binary
[`from_str_hex`]: struct.FixedI32.html#method.from_str_hex
[`from_str_octal`]: struct.FixedI32.html#method.from_str_octal
[`to_num`]: struct.FixedI32.html#method.to_num
[const generics]: https://github.com/rust-lang/rust/issues/44580
*/
#![no_std]
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/fixed/0.4.6")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]
#![allow(clippy::type_repetition_in_bounds)]

#[cfg(test)]
extern crate std;

#[macro_use]
mod macros;

mod arith;
#[cfg(feature = "az")]
mod cast;
mod cmp;
pub mod consts;
mod convert;
mod display;
mod float_helper;
pub mod frac;
mod from_str;
mod helpers;
mod int_helper;
pub mod sealed;
#[cfg(feature = "serde")]
mod serdeize;
pub mod traits;
pub mod types;
mod wide_div;
mod wrapping;
use crate::{
    arith::MulDivDir,
    from_str::FromStrRadix,
    helpers::IntHelper,
    traits::{FromFixed, ToFixed},
    types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
};
pub use crate::{from_str::ParseFixedError, wrapping::Wrapping};
use core::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem,
};

/// A prelude for users of the *fixed* crate.
///
/// This prelude is similar to the [standard library’s
/// prelude][prelude] in that you’ll almost always want to import its
/// entire contents, but unlike the standard library’s prelude you’ll
/// have to do so manually:
///
/// ```
/// # #[allow(unused_imports)]
/// use fixed::prelude::*;
/// ```
///
/// The prelude may grow over time as additional items see ubiquitous use.
///
/// [prelude]: https://doc.rust-lang.org/nightly/std/prelude/index.html
pub mod prelude {
    pub use crate::traits::{FromFixed, ToFixed};
}

#[macro_use]
mod macros_from_to;
#[macro_use]
mod macros_round;
#[macro_use]
mod macros_no_frac;
#[macro_use]
mod macros_frac;

macro_rules! fixed {
    (
        $description:expr,
        $Fixed:ident($Inner:ty, $LeEqU:tt, $s_nbits:expr),
        $UInner:ty, $Signedness:tt
    ) => {
        fixed! {
            $description,
            $Fixed[stringify!($Fixed)]($Inner[stringify!($Inner)], $LeEqU, $s_nbits),
            $UInner, $Signedness
        }
    };
    (
        $description:expr,
        $Fixed:ident[$s_fixed:expr]($Inner:ty[$s_inner:expr], $LeEqU:tt, $s_nbits:expr),
        $UInner:ty, $Signedness:tt
    ) => {
        comment! {
            $description,
            " number with `Frac` fractional bits.

Currently `Frac` is an [`Unsigned`] as provided by the
[typenum crate]; it is planned to move to [const generics] when they
are implemented by the Rust compiler.

# Examples

```rust
use fixed::{types::extra::U3, ", $s_fixed, "};
let eleven = ", $s_fixed, "::<U3>::from_num(11);
assert_eq!(eleven, ", $s_fixed, "::<U3>::from_bits(11 << 3));
assert_eq!(eleven, 11);
assert_eq!(eleven.to_string(), \"11\");
let two_point_75 = eleven / 4;
assert_eq!(two_point_75, ", $s_fixed, "::<U3>::from_bits(11 << 1));
assert_eq!(two_point_75, 2.75);
assert_eq!(two_point_75.to_string(), \"2.8\");
```

[`Unsigned`]: https://docs.rs/typenum/^1.3/typenum/marker_traits/trait.Unsigned.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
[typenum crate]: https://crates.io/crates/typenum
";
            #[repr(transparent)]
            pub struct $Fixed<Frac> {
                bits: $Inner,
                phantom: PhantomData<Frac>,
            }
        }

        impl<Frac> Clone for $Fixed<Frac> {
            #[inline]
            fn clone(&self) -> $Fixed<Frac> {
                $Fixed {
                    bits: self.bits,
                    phantom: PhantomData,
                }
            }
        }

        impl<Frac> Copy for $Fixed<Frac> {}

        impl<Frac> Default for $Fixed<Frac> {
            #[inline]
            fn default() -> Self {
                $Fixed {
                    bits: Default::default(),
                    phantom: PhantomData,
                }
            }
        }

        impl<Frac> Hash for $Fixed<Frac> {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.bits.hash(state);
            }
        }

        // inherent methods that do not require Frac bounds, some of which can thus be const
        fixed_no_frac! {
            $description,
            $Fixed[$s_fixed]($Inner[$s_inner], $s_nbits),
            $UInner, $Signedness
        }
        // inherent methods that require Frac bounds, and cannot be const
        fixed_frac! {
            $description,
            $Fixed[$s_fixed]($Inner[$s_inner], $LeEqU, $s_nbits),
            $UInner, $Signedness
        }
    };
}

fixed! { "An eight-bit fixed-point unsigned", FixedU8(u8, LeEqU8, "8"), u8, Unsigned }
fixed! { "A 16-bit fixed-point unsigned", FixedU16(u16, LeEqU16, "16"), u16, Unsigned }
fixed! { "A 32-bit fixed-point unsigned", FixedU32(u32, LeEqU32, "32"), u32, Unsigned }
fixed! { "A 64-bit fixed-point unsigned", FixedU64(u64, LeEqU64, "64"), u64, Unsigned }
fixed! { "A 128-bit fixed-point unsigned", FixedU128(u128, LeEqU128, "128"), u128, Unsigned }
fixed! { "An eight-bit fixed-point signed", FixedI8(i8, LeEqU8, "8"), u8, Signed }
fixed! { "A 16-bit fixed-point signed", FixedI16(i16, LeEqU16, "16"), u16, Signed }
fixed! { "A 32-bit fixed-point signed", FixedI32(i32, LeEqU32, "32"), u32, Signed }
fixed! { "A 64-bit fixed-point signed", FixedI64(i64, LeEqU64, "64"), u64, Signed }
fixed! { "A 128-bit fixed-point signed", FixedI128(i128, LeEqU128, "128"), u128, Signed }

#[cfg(test)]
#[allow(clippy::cognitive_complexity)]
mod tests {
    use crate::types::{I0F32, I16F16, I1F31, U0F32, U16F16};

    #[test]
    fn rounding_signed() {
        // -0.5
        let f = I0F32::from_bits(-1 << 31);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::from_num(0), false));
        assert_eq!(f.overflowing_floor(), (I0F32::from_num(0), true));
        assert_eq!(f.overflowing_round(), (I0F32::from_num(0), true));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I0F32::from_num(0), false)
        );

        // -0.5 + Δ
        let f = I0F32::from_bits((-1 << 31) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::from_num(0), false));
        assert_eq!(f.overflowing_floor(), (I0F32::from_num(0), true));
        assert_eq!(f.overflowing_round(), (I0F32::from_num(0), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I0F32::from_num(0), false)
        );

        // 0.5 - Δ
        let f = I0F32::from_bits((1 << 30) - 1 + (1 << 30));
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::from_num(0), true));
        assert_eq!(f.overflowing_floor(), (I0F32::from_num(0), false));
        assert_eq!(f.overflowing_round(), (I0F32::from_num(0), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I0F32::from_num(0), false)
        );

        // -0.5 - Δ
        let f = I1F31::from_bits(((-1) << 30) - 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::from_num(0), false));
        assert_eq!(f.overflowing_floor(), (I1F31::from_num(-1), false));
        assert_eq!(f.overflowing_round(), (I1F31::from_num(-1), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I1F31::from_num(-1), false)
        );

        // -0.5
        let f = I1F31::from_bits((-1) << 30);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::from_num(0), false));
        assert_eq!(f.overflowing_floor(), (I1F31::from_num(-1), false));
        assert_eq!(f.overflowing_round(), (I1F31::from_num(-1), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I1F31::from_num(0), false)
        );

        // -0.5 + Δ
        let f = I1F31::from_bits(((-1) << 30) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::from_num(0), false));
        assert_eq!(f.overflowing_floor(), (I1F31::from_num(-1), false));
        assert_eq!(f.overflowing_round(), (I1F31::from_num(0), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I1F31::from_num(0), false)
        );

        // 0.5 - Δ
        let f = I1F31::from_bits((1 << 30) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::from_num(-1), true));
        assert_eq!(f.overflowing_floor(), (I1F31::from_num(0), false));
        assert_eq!(f.overflowing_round(), (I1F31::from_num(0), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I1F31::from_num(0), false)
        );

        // 0.5
        let f = I1F31::from_bits(1 << 30);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::from_num(-1), true));
        assert_eq!(f.overflowing_floor(), (I1F31::from_num(0), false));
        assert_eq!(f.overflowing_round(), (I1F31::from_num(-1), true));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I1F31::from_num(0), false)
        );

        // 0.5 + Δ
        let f = I1F31::from_bits((1 << 30) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::from_num(-1), true));
        assert_eq!(f.overflowing_floor(), (I1F31::from_num(0), false));
        assert_eq!(f.overflowing_round(), (I1F31::from_num(-1), true));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I1F31::from_num(-1), true)
        );

        // -3.5 - Δ
        let f = I16F16::from_bits(((-7) << 15) - 1);
        assert_eq!(f.to_num::<i32>(), -4);
        assert_eq!(f.round_to_zero(), -3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-4), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(-4), false)
        );

        // -3.5
        let f = I16F16::from_bits((-7) << 15);
        assert_eq!(f.to_num::<i32>(), -4);
        assert_eq!(f.round_to_zero(), -3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-4), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(-4), false)
        );

        // -3.5 + Δ
        let f = I16F16::from_bits(((-7) << 15) + 1);
        assert_eq!(f.to_num::<i32>(), -4);
        assert_eq!(f.round_to_zero(), -3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(-3), false)
        );

        // -2.5 - Δ
        let f = I16F16::from_bits(((-5) << 15) - 1);
        assert_eq!(f.to_num::<i32>(), -3);
        assert_eq!(f.round_to_zero(), -2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-2), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(-3), false)
        );

        // -2.5
        let f = I16F16::from_bits((-5) << 15);
        assert_eq!(f.to_num::<i32>(), -3);
        assert_eq!(f.round_to_zero(), -2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-2), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(-2), false)
        );

        // -2.5 + Δ
        let f = I16F16::from_bits(((-5) << 15) + 1);
        assert_eq!(f.to_num::<i32>(), -3);
        assert_eq!(f.round_to_zero(), -2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-2), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-2), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(-2), false)
        );

        // -0.5 - Δ
        let f = I16F16::from_bits(((-1) << 15) - 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-1), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(-1), false)
        );

        // -0.5
        let f = I16F16::from_bits((-1) << 15);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-1), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(0), false)
        );

        // -0.5 + Δ
        let f = I16F16::from_bits(((-1) << 15) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(0), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(0), false)
        );

        // 0.5 - Δ
        let f = I16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(0), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(0), false)
        );

        // 0.5
        let f = I16F16::from_bits(1 << 15);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(1), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(0), false)
        );

        // 0.5 + Δ
        let f = I16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(1), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(1), false)
        );

        // 2.5 - Δ
        let f = I16F16::from_bits((5 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(2), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(2), false)
        );

        // 2.5
        let f = I16F16::from_bits(5 << 15);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(2), false)
        );

        // 2.5 + Δ
        let f = I16F16::from_bits((5 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(3), false)
        );

        // 3.5 - Δ
        let f = I16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(3), false)
        );

        // 3.5
        let f = I16F16::from_bits(7 << 15);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(4), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(4), false)
        );

        // 3.5 + Δ
        let f = I16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(4), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(4), false)
        );
    }

    #[test]
    fn rounding_unsigned() {
        // 0.5 - Δ
        let f = U0F32::from_bits((1 << 31) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_num(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_num(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_num(0), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U0F32::from_num(0), false)
        );

        // 0.5
        let f = U0F32::from_bits(1 << 31);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_num(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_num(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_num(0), true));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U0F32::from_num(0), false)
        );

        // 0.5 + Δ
        let f = U0F32::from_bits((1 << 31) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_num(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_num(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_num(0), true));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U0F32::from_num(0), true)
        );

        // 0.5 - Δ
        let f = U16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(0), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(0), false)
        );

        // 0.5
        let f = U16F16::from_bits(1 << 15);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(1), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(0), false)
        );

        // 0.5 + Δ
        let f = U16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(1), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(1), false)
        );

        // 2.5 - Δ
        let f = U16F16::from_bits((5 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(2), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(2), false)
        );

        // 2.5
        let f = U16F16::from_bits(5 << 15);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(2), false)
        );

        // 2.5 + Δ
        let f = U16F16::from_bits((5 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(3), false)
        );

        // 3.5 - Δ
        let f = U16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(3), false)
        );

        // 3.5
        let f = U16F16::from_bits(7 << 15);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(4), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(4), false)
        );

        // 3.5 + Δ
        let f = U16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(4), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
            (U16F16::from_num(4), false)
        );
    }
}
