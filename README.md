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

All lossless infallible conversions between fixed-point numbers and
numeric primitives are implemented. That is, you can use [`From`] or
[`Into`] for the conversions that always work without losing any bits.

## What’s new

### Version 0.4.0 news (unreleased)

  * The [*fixed* crate] now requires rustc version 1.31.1 or later.
  * The [`traits`] module was added, with its traits [`Fixed`],
    [`FromFixed`], [`ToFixed`], [`LossyFrom`] and [`LossyInto`],.
  * The [`saturating_neg`] method was added to all fixed-point
    numbers, and the [`saturating_abs`] method was added to signed
    fixed-point numbers.

#### Incompatible changes

  * The sealed traits [`Int`] and [`Float`] now have no provided
    methods; the methods in the old implementation are new provided by
    [`FromFixed`] and [`ToFixed`].

[`Fixed`]: https://docs.rs/fixed/0.3.4/fixed/traits/trait.Fixed.html
[`Float`]: https://docs.rs/fixed/0.3.4/fixed/sealed/trait.Float.html
[`FromFixed`]: https://docs.rs/fixed/0.3.4/fixed/traits/trait.FromFixed.html
[`Int`]: https://docs.rs/fixed/0.3.4/fixed/sealed/trait.Int.html
[`LossyFrom`]: https://docs.rs/fixed/0.3.4/fixed/traits/trait.LossyFrom.html
[`LossyInto`]: https://docs.rs/fixed/0.3.4/fixed/traits/trait.LossyInto.html
[`ToFixed`]: https://docs.rs/fixed/0.3.4/fixed/traits/trait.ToFixed.html
[`saturating_abs`]: https://docs.rs/fixed/0.3.4/fixed/struct.FixedI32.html#method.saturating_abs
[`saturating_neg`]: https://docs.rs/fixed/0.3.4/fixed/struct.FixedI32.html#method.saturating_neg
[`traits`]: https://docs.rs/fixed/0.3.4/fixed/traits/index.html

### Version 0.3.3 news (2019-06-27)

  * Conversions to/from [`isize`] and [`usize`] were added.

[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html

### Version 0.3.2 news (2019-02-27)

  * The [`Wrapping`] wrapper was added.

[`Wrapping`]: https://docs.rs/fixed/0.3.3/fixed/struct.Wrapping.html

### Version 0.3.1 news (2019-02-07)

  * Reimplement [`From<bool>`][`From`] for all fixed-point types which
    can represent the integer 1. This was inadvertently removed in
    0.3.0.

### Version 0.3.0 news (2019-02-03)

#### Highlights

  * Every fixed-point type now supports conversion to/from all
    primitive number types, including checked versions of the
    conversions.
  * Every fixed-point type now supports comparisons with all primitive
    number types.

#### Incompatible changes

  * The method [`to_int`] was changed; now its return type is generic.
  * The [`Int`] trait implementation for [`bool`] was removed.

#### Other changes

  * The new method [`to_fixed`] was added.
  * Checked versions of [`to_fixed`] and [`to_int`] were added.
  * The methods [`from_fixed`][`Int::from_fixed`] and
    [`to_fixed`][`Int::to_fixed`], and their checked versions, were
    added to the [`Int`] trait.
  * The method [`from_fixed`][`Float::from_fixed`], and the method
    [`to_fixed`][`Float::to_fixed`] and its checked versions, were
    added to the [`Float`] trait.
  * The methods [`int_bits`] and [`frac_bits`] were deprecated and
    replaced by the methods [`int_nbits`] and [`frac_nbits`].

[`Float::from_fixed`]: https://docs.rs/fixed/0.3.3/fixed/sealed/trait.Float.html#method.from_fixed
[`Float::to_fixed`]: https://docs.rs/fixed/0.3.3/fixed/sealed/trait.Float.html#method.to_fixed
[`Float`]: https://docs.rs/fixed/0.3.3/fixed/sealed/trait.Float.html
[`Int::from_fixed`]: https://docs.rs/fixed/0.3.3/fixed/sealed/trait.Int.html#method.from_fixed
[`Int::to_fixed`]: https://docs.rs/fixed/0.3.3/fixed/sealed/trait.Int.html#method.to_fixed
[`Int`]: https://docs.rs/fixed/0.3.3/fixed/sealed/trait.Int.html
[`bool`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`frac_bits`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI32.html#method.frac_bits
[`frac_nbits`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI32.html#method.frac_nbits
[`int_bits`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI32.html#method.int_bits
[`int_nbits`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI32.html#method.int_nbits
[`to_fixed`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI32.html#method.to_fixed
[`to_int`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI32.html#method.to_int

### Other releases

Details on other releases can be found in [*RELEASES.md*].

[*RELEASES.md*]: https://gitlab.com/tspiteri/fixed/blob/master/RELEASES.md

## Quick examples

```rust
// 20 integer bits, 12 fractional bits
use fixed::types::I20F12;

// 19/3 = 6 1/3
let six_and_third = I20F12::from_int(19) / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// find the ceil and convert to i32
assert_eq!(six_and_third.ceil().to_int::<i32>(), 7);
// we can also compare directly to integers
assert_eq!(six_and_third.ceil(), 7);
```

The type [`I20F12`] is a 32-bit fixed-point signed number with 20
integer bits and 12 fractional bits. It is an alias to
[`FixedI32<frac::U12>`][`FixedI32`]. The unsigned counterpart would be
[`U20F12`]. Aliases are provided for all combinations of integer and
fractional bits adding up to a total of eight, 16, 32, 64 or 128 bits.

```rust
// −8 ≤ I4F4 < 8 with steps of 1/16 (about 0.06)
use fixed::types::I4F4;
let a = I4F4::from_int(1);
// multiplication and division by integers is possible
let ans1 = a / 5 * 17;
// 1 / 5 × 17 = 3 2/5 (3.4), but we get 3 3/16 (3.19)
assert_eq!(ans1, I4F4::from_bits((3 << 4) + 3));
assert_eq!(ans1.to_string(), "3.19");

// −8 ≤ I4F12 < 8 with steps of 1/4096 (about 0.0002)
use fixed::types::I4F12;
let wider_a = I4F12::from(a);
let wider_ans = wider_a / 5 * 17;
let ans2 = I4F4::from_fixed(wider_ans);
// now the answer is the much closer 3 6/16 (3.38)
assert_eq!(ans2, I4F4::from_bits((3 << 4) + 6));
assert_eq!(ans2.to_string(), "3.38");
```

The second example shows some precision and conversion issues. The low
precision of `a` means that `a / 5` is 3⁄16 instead of 1⁄5, leading to
an inaccurate result `ans1` = 3 3⁄16 (3.19). With a higher precision,
we get `wider_a / 5` equal to 819⁄4096, leading to a more accurate
intermediate result `wider_ans` = 3 1635⁄4096. When we convert back to
four fractional bits, we get `ans2` = 3 6⁄16 (3.38).

Note that we can convert from [`I4F4`] to [`I4F12`] using [`From`], as
the target type has the same number of integer bits and a larger
number of fractional bits. Converting from [`I4F12`] to [`I4F4`]
cannot use [`From`] as we have less fractional bits, so we use
[`from_fixed`] instead.

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.3.3"
```

If you are using the 2015 Rust edition, you also need to declare it by
adding this to your crate root (usually *lib.rs* or *main.rs*):

```rust
extern crate fixed;
```

The *fixed* crate requires rustc version 1.31.1 or later.

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
version = "0.3.3"
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
[`FixedI128`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedU8.html
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`I20F12`]: https://docs.rs/fixed/0.3.3/fixed/types/type.I20F12.html
[`I4F12`]: https://docs.rs/fixed/0.3.3/fixed/types/type.I4F12.html
[`I4F4`]: https://docs.rs/fixed/0.3.3/fixed/types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`U20F12`]: https://docs.rs/fixed/0.3.3/fixed/types/type.U20F12.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`from_fixed`]: https://docs.rs/fixed/0.3.3/fixed/struct.FixedI8.html#method.from_fixed
[const generics]: https://github.com/rust-lang/rust/issues/44580
