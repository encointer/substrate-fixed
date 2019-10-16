<!-- Copyright © 2018–2019 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

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

## What’s new

### Version 0.4.6 news (2019-10-16)

  * Conversions to/from [`bf16`] are now provided when the `f16`
    option is enabled.
  * The following methods are now `const` functions:
    [`saturating_neg`], [`saturating_add`], [`saturating_sub`],
    [`saturating_mul_int`], [`saturating_abs`]
  * Support for casts using the [*az* crate] was added.

[`saturating_abs`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.saturating_abs
[`saturating_add`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.saturating_add
[`saturating_mul_int`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.saturating_mul_int
[`saturating_sub`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.saturating_sub
[`saturating_neg`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.saturating_neg

### Version 0.4.5 news (2019-08-30)

  * Bug fix: display of many decimal numbers was panicking in debug
    mode or including a leading zero in release mode.
  * Many methods were added to [`Wrapping`] for convenience, even if
    they do not involve wrapping.

[`Wrapping`]: https://docs.rs/fixed/0.4.6/fixed/struct.Wrapping.html

### Version 0.4.4 news (2019-08-24)

  * Bug fix: rounding could produce bad output for [`Binary`],
    [`Octal`], [`LowerHex`] and [`UpperHex`].
  * The following methods are now `const` functions:
    [`is_power_of_two`], [`abs`], [`wrapping_abs`],
    [`overflowing_abs`]
  * The method [`round_to_zero`] was added.
  * The method [`round_ties_to_even`] and its checked versions were
    added.

[`abs`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.abs
[`is_power_of_two`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedU32.html#method.is_power_of_two
[`overflowing_abs`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.overflowing_abs
[`round_ties_to_even`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.round_ties_to_even
[`round_to_zero`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.round_to_zero
[`wrapping_abs`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.wrapping_abs

### Other releases

Details on other releases can be found in [*RELEASES.md*].

[*RELEASES.md*]: https://gitlab.com/tspiteri/fixed/blob/master/RELEASES.md

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
[`FixedI128`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedU8.html
[`FromFixed`]: https://docs.rs/fixed/0.4.6/fixed/traits/trait.FromFixed.html
[`FromStr`]: https://doc.rust-lang.org/nightly/std/str/trait.FromStr.html
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`I20F12`]: https://docs.rs/fixed/0.4.6/fixed/types/type.I20F12.html
[`I4F12`]: https://docs.rs/fixed/0.4.6/fixed/types/type.I4F12.html
[`I4F4`]: https://docs.rs/fixed/0.4.6/fixed/types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`LossyFrom`]: https://docs.rs/fixed/0.4.6/fixed/traits/trait.LossyFrom.html
[`LossyInto`]: https://docs.rs/fixed/0.4.6/fixed/traits/trait.LossyInto.html
[`LowerHex`]: https://doc.rust-lang.org/nightly/std/fmt/trait.LowerHex.html
[`Octal`]: https://doc.rust-lang.org/nightly/std/fmt/trait.Octal.html
[`ToFixed`]: https://docs.rs/fixed/0.4.6/fixed/traits/trait.ToFixed.html
[`U12`]: https://docs.rs/fixed/0.4.6/fixed/types/extra/type.U12.html
[`U20F12`]: https://docs.rs/fixed/0.4.6/fixed/types/type.U20F12.html
[`UpperHex`]: https://doc.rust-lang.org/nightly/std/fmt/trait.UpperHex.html
[`bf16`]: https://docs.rs/half/^1/half/struct.bf16.html
[`checked_from_num`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.checked_from_num
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`from_num`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.from_num
[`from_str_binary`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.from_str_binary
[`from_str_hex`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.from_str_hex
[`from_str_octal`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.from_str_octal
[`to_num`]: https://docs.rs/fixed/0.4.6/fixed/struct.FixedI32.html#method.to_num
[const generics]: https://github.com/rust-lang/rust/issues/44580
