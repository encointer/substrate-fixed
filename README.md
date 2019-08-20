<!-- Copyright © 2018–2019 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

# Fixed-point numbers

The [*fixed* crate] provides fixed-point numbers. Currently it uses
the [*typenum* crate] for the fractional bit count; it is planned to
move to [const generics] when they are implemented by the Rust
compiler.

The crate provides the following types:

  * [`FixedI8`] is a signed eight-bit fixed-point number,
  * [`FixedI16`] is a signed 16-bit fixed-point number,
  * [`FixedI32`] is a signed 32-bit fixed-point number,
  * [`FixedI64`] is a signed 64-bit fixed-point number,
  * [`FixedI128`] is a signed 128-bit fixed-point number,
  * [`FixedU8`] is an unsigned eight-bit fixed-point number,
  * [`FixedU16`] is an unsigned 16-bit fixed-point number,
  * [`FixedU32`] is an unsigned 32-bit fixed-point number,
  * [`FixedU64`] is an unsigned 64-bit fixed-point number, and
  * [`FixedU128`] is an unsigned 128-bit fixed-point number.

All fixed-point numbers can have `Frac` fractional bits, where `Frac`
can have any value from 0 up to and including the size of the number
in bits. When `Frac` is 0, the fixed-point number behaves like an
integer. When `Frac` is equal to the number of bits, the value of the
fixed-point number lies in the range −0.5 ≤ *x* < 0.5 for signed
fixed-point numbers, and in the range 0 ≤ *x* < 1 for unsigned
fixed-point numbers.

Various conversion methods are available:

  * All lossless infallible conversions between fixed-point numbers
    and numeric primitives are implemented. You can use [`From`] or
    [`Into`] for conversions that always work without losing any bits.
  * For lossy infallible conversions between fixed-point numbers and
    numeric primitives, where the source type may have more fractional
    bits than the destination type, the [`LossyFrom`] and
    [`LossyInto`] traits can be used. Excess fractional bits are
    truncated.
  * Checked conversions are provided between fixed-point numbers and
    numeric primitives using the [`FromFixed`] and [`ToFixed`] traits,
    or using the [`from_num`] and [`to_num`] methods and their checked
    versions.
  * Fixed-point numbers can be parsed from decimal strings using
    [`FromStr`], or from binary, octal or hexadecimal using the
    [`from_str_binary`], [`from_str_octal`] or [`from_str_hex`]
    methods. The result is rounded to the nearest, with ties rounded
    to even.
  * Fixed-point numbers can be converted to strings using [`Display`],
    [`Binary`], [`Octal`], [`LowerHex`] and [`UpperHex`]. The output
    is rounded to the nearest, with ties rounded to even.

## What’s new

### Version 0.4.3 news (2019-08-20)

  * The [*fixed* crate] now requires rustc version 1.34.0 or later.
  * The precision argument is no longer ignored when formatting
    fixed-point numbers; precision should now be handled the same as
    for primitive floating-point numbers in the standard library.
  * Parsing strings now rounds to the nearest with ties rounded to
    even.
  * Checked versions of string parsing methods are now available as
    inherent methods to all fixed-point numbers, and as methods in the
    [`Fixed`] trait.
  * [`Wrapping`] now has methods for parsing with wrapping, including
    an implementation of [`FromStr`].
  * The following methods are now `const` functions:
      * [`min_value`], [`max_value`], [`from_bits`], [`to_bits`]
	  * [`count_ones`], [`count_zeros`], [`leading_zeros`],
        [`trailing_zeros`] [`rotate_left`], [`rotate_right`]
	  * [`wrapping_neg`], [`wrapping_add`], [`wrapping_sub`],
        [`wrapping_mul_int`], [`wrapping_shl`], [`wrapping_shr`]
	  * [`overflowing_neg`], [`overflowing_add`], [`overflowing_sub`],
        [`overflowing_mul_int`], [`overflowing_shl`],
        [`overflowing_shr`]
      * [`is_positive`], [`is_negative`]
  * The associated constants [`INT_NBITS`] and [`FRAC_NBITS`] were added.
  * The reexports in the `frac` module and the `LeEqU*` traits were
    moved into the new [`types::extra`] module.

[`FRAC_NBITS`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#associatedconstant.FRAC_NBITS
[`Fixed`]: https://docs.rs/fixed/0.4.3/fixed/traits/trait.Fixed.html
[`INT_NBITS`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#associatedconstant.INT_NBITS
[`Wrapping`]: https://docs.rs/fixed/0.4.3/fixed/struct.Wrapping.html
[`count_ones`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.count_ones
[`count_zeros`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.count_zeros
[`from_bits`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.from_bits
[`is_negative`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.is_negative
[`is_positive`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.is_positive
[`leading_zeros`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.leading_zeros
[`max_value`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.max_value
[`min_value`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.min_value
[`overflowing_add`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.overflowing_add
[`overflowing_mul_int`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.overflowing_mul_int
[`overflowing_neg`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.overflowing_neg
[`overflowing_shl`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.overflowing_shl
[`overflowing_shr`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.overflowing_shr
[`overflowing_sub`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.overflowing_sub
[`rotate_left`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.rotate_left
[`rotate_right`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.rotate_right
[`to_bits`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.to_bits
[`trailing_zeros`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.trailing_zeros
[`types::extra`]: https://docs.rs/fixed/0.4.3/fixed/types/extra/index.html
[`wrapping_add`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.wrapping_add
[`wrapping_mul_int`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.wrapping_mul_int
[`wrapping_neg`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.wrapping_neg
[`wrapping_shl`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.wrapping_shl
[`wrapping_shr`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.wrapping_shr
[`wrapping_sub`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.wrapping_sub

### Version 0.4.2 news (2019-08-16)

  * The new methods [`from_num`] and [`to_num`] together with their
    checked versions were added to all fixed-point numbers.
  * The methods `from_fixed`, `to_fixed`, `from_int`, `to_int`,
    `from_float`, and `to_float`, and their checked versions, were
    deprecated.
  * The new method [`from_num`][`Wrapping::from_num`] was added to the
    [`Wrapping`] wrapper.
  * Bug fix: parsing of decimal fractions was fixed to give correctly
    rounded results for long decimal fraction strings, for example
    with four fractional bits, 0.96874999… (just below 31⁄32) and
    0.96875 (31⁄32) are now parsed correctly as 0.9375 (15⁄16) and 1.0.

[`Wrapping::from_num`]: https://docs.rs/fixed/0.4.3/fixed/struct.Wrapping.html#method.from_num
[`Wrapping`]: https://docs.rs/fixed/0.4.3/fixed/struct.Wrapping.html

### Version 0.4.1 news (2019-08-12)

  * All fixed-point types now implement [`FromStr`].
  * The methods [`from_str_binary`], [`from_str_octal`] and
    [`from_str_hex`] were added.

### Version 0.4.0 news (2019-08-08)

  * The [*fixed* crate] now requires rustc version 1.31.0 or later.
  * The [`traits`] module was added, with its traits [`Fixed`],
    [`FixedSigned`], [`FixedUnsigned`], [`FromFixed`], [`ToFixed`],
    [`LossyFrom`] and [`LossyInto`].
  * The [`saturating_neg`] method was added to all fixed-point
    numbers, and the [`saturating_abs`] method was added to signed
    fixed-point numbers.
  * The [`consts`] module was added.
  * The [`signum`] method now wraps instead of panics in release mode.

#### Incompatible changes

  * The sealed traits [`Int`] and [`Float`] now have no provided
    methods; the methods in the old implementation are new provided by
    [`FromFixed`] and [`ToFixed`].
  * Deprecated methods were removed.

#### Contributors

  * [@jean-airoldie](https://gitlab.com/jean-airoldie)
  * [@tspiteri](https://gitlab.com/tspiteri)

[`FixedSigned`]: https://docs.rs/fixed/0.4.3/fixed/traits/trait.FixedSigned.html
[`FixedUnsigned`]: https://docs.rs/fixed/0.4.3/fixed/traits/trait.FixedUnsigned.html
[`Fixed`]: https://docs.rs/fixed/0.4.3/fixed/traits/trait.Fixed.html
[`Float`]: https://docs.rs/fixed/0.4.3/fixed/sealed/trait.Float.html
[`Int`]: https://docs.rs/fixed/0.4.3/fixed/sealed/trait.Int.html
[`consts`]: https://docs.rs/fixed/0.4.3/fixed/consts/index.html
[`saturating_abs`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.saturating_abs
[`saturating_neg`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.saturating_neg
[`signum`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.signum
[`traits`]: https://docs.rs/fixed/0.4.3/fixed/traits/index.html

### Other releases

Details on other releases can be found in [*RELEASES.md*].

[*RELEASES.md*]: https://gitlab.com/tspiteri/fixed/blob/master/RELEASES.md

## Quick examples

```rust
// 20 integer bits, 12 fractional bits
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
<code>[FixedI32][`FixedI32`]&lt;[U12][`U12`]&gt;</code>.
The unsigned counterpart would be [`U20F12`]. Aliases are provided for
all combinations of integer and fractional bits adding up to a total
of eight, 16, 32, 64 or 128 bits.

```rust
// −8 ≤ I4F4 < 8 with steps of 1/16 (~0.06)
use fixed::types::I4F4;
let a = I4F4::from_num(1);
// multiplication and division by integers are possible
let ans1 = a / 5 * 17;
// 1 / 5 × 17 = 3 2/5 (3.4), but we get 3 3/16 (~3.2)
assert_eq!(ans1, I4F4::from_bits((3 << 4) + 3));
assert_eq!(ans1.to_string(), "3.2");

// −8 ≤ I4F12 < 8 with steps of 1/4096 (~0.0002)
use fixed::types::I4F12;
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
fixed = "0.4.3"
```

The *fixed* crate requires rustc version 1.34.0 or later.

## Optional features

The *fixed* crate has two optional feature:

 1. `f16`, disabled by default. This provides conversion to/from
    [`f16`]. This features requires the [*half* crate].
 2. `serde`, disabled by default. This provides serialization support
    for the fixed-point types. This feature requires the
    [*serde* crate].

To enable features, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.fixed]
version = "0.4.3"
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
[*fixed* crate]: https://crates.io/crates/fixed
[*half* crate]: https://crates.io/crates/half
[*serde* crate]: https://crates.io/crates/serde
[*typenum* crate]: https://crates.io/crates/typenum
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`Binary`]: https://doc.rust-lang.org/nightly/std/fmt/trait.Binary.html
[`Display`]: https://doc.rust-lang.org/nightly/std/fmt/trait.Display.html
[`FixedI128`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedU8.html
[`FromFixed`]: https://docs.rs/fixed/0.4.3/fixed/traits/trait.FromFixed.html
[`FromStr`]: https://doc.rust-lang.org/nightly/std/str/trait.FromStr.html
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`I20F12`]: https://docs.rs/fixed/0.4.3/fixed/types/type.I20F12.html
[`I4F12`]: https://docs.rs/fixed/0.4.3/fixed/types/type.I4F12.html
[`I4F4`]: https://docs.rs/fixed/0.4.3/fixed/types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`LossyFrom`]: https://docs.rs/fixed/0.4.3/fixed/traits/trait.LossyFrom.html
[`LossyInto`]: https://docs.rs/fixed/0.4.3/fixed/traits/trait.LossyInto.html
[`LowerHex`]: https://doc.rust-lang.org/nightly/std/fmt/trait.LowerHex.html
[`Octal`]: https://doc.rust-lang.org/nightly/std/fmt/trait.Octal.html
[`ToFixed`]: https://docs.rs/fixed/0.4.3/fixed/traits/trait.ToFixed.html
[`U12`]: https://docs.rs/fixed/0.4.3/fixed/types/extra/type.U12.html
[`U20F12`]: https://docs.rs/fixed/0.4.3/fixed/types/type.U20F12.html
[`UpperHex`]: https://doc.rust-lang.org/nightly/std/fmt/trait.UpperHex.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`from_num`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.from_num
[`from_str_binary`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.from_str_binary
[`from_str_hex`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.from_str_hex
[`from_str_octal`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.from_str_octal
[`to_num`]: https://docs.rs/fixed/0.4.3/fixed/struct.FixedI32.html#method.to_num
[const generics]: https://github.com/rust-lang/rust/issues/44580
