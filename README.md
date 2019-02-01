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

### Version 0.3.0 news (unreleased)

  * The return type of [`to_int`] is now generic.
  * The new methods [`to_fixed`], [`to_float`], [`checked_to_fixed`],
    [`checked_to_int`] and [`checked_to_float`] were added.

[`checked_to_int`]: https://docs.rs/fixed/0.3.0/fixed/struct.FixedI32.html#method.checked_to_int
[`checked_to_float`]: https://docs.rs/fixed/0.3.0/fixed/struct.FixedI32.html#method.checked_to_float
[`checked_to_fixed`]: https://docs.rs/fixed/0.3.0/fixed/struct.FixedI32.html#method.checked_to_fixed
[`checked_to_int`]: https://docs.rs/fixed/0.3.0/fixed/struct.FixedI32.html#method.checked_to_int
[`checked_to_float`]: https://docs.rs/fixed/0.3.0/fixed/struct.FixedI32.html#method.checked_to_float
[`checked_to_fixed`]: https://docs.rs/fixed/0.3.0/fixed/struct.FixedI32.html#method.checked_to_fixed

### Version 0.2.1 news (2019-01-29)

  * Bug fix: the [`from_fixed`] and [`from_int`] methods (and their
    checked counterparts) could return wrong values for negative
    values.
  * Bug fix: display was using one fractional digit less than
    required, thus yielding the same output for diffent fixed-point
    numbers.

### Version 0.2.0 news (2019-01-29)

  * The new methods [`from_fixed`], [`checked_from_fixed`],
    [`saturating_from_fixed`], [`wrapping_from_fixed`] and
    [`overflowing_from_fixed`] were added.
  * The old method [`from_int`] was removed to be replaced.
  * The new methods [`from_int`], [`checked_from_int`],
    [`saturating_from_int`], [`wrapping_from_int`] and
    [`overflowing_from_int`] were added.
  * The new methods [`from_float`], [`checked_from_float`],
    [`saturating_from_float`], [`wrapping_from_float`] and
    [`overflowing_from_float`] were added.
  * The new method [`to_float`] was added.
  * The methods [`from_f16`], [`from_f32`], [`from_f64`], [`to_f16`],
    [`to_f32`] and [`to_f64`] were deprecated.
  * The [`to_int`] method was fixed to truncate fractional bits as
    documented for negative values.
  * The new methods [`ceil`], [`floor`], [`round`], [`checked_ceil`],
    [`checked_floor`], [`checked_round`], [`saturating_ceil`],
    [`saturating_floor`], [`saturating_round`], [`wrapping_ceil`],
    [`wrapping_floor`], [`wrapping_round`], [`overflowing_ceil`],
    [`overflowing_floor`] and [`overflowing_round`] were added.
  * The methods [`to_int_ceil`], [`to_int_floor`] and [`to_int_round`]
    were deprecated.

[`ceil`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.ceil
[`checked_ceil`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.checked_ceil
[`checked_floor`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.checked_floor
[`checked_from_fixed`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.checked_from_fixed
[`checked_from_float`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.checked_from_float
[`checked_from_int`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.checked_from_int
[`checked_round`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.checked_round
[`floor`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.floor
[`from_f16`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.from_f16
[`from_f32`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.from_f32
[`from_f64`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.from_f64
[`from_fixed`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.from_fixed
[`from_float`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.from_float
[`from_int`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.from_int
[`from_int`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.from_int
[`overflowing_ceil`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.overflowing_ceil
[`overflowing_floor`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.overflowing_floor
[`overflowing_from_fixed`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.overflowing_from_fixed
[`overflowing_from_float`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.overflowing_from_float
[`overflowing_from_int`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.overflowing_from_int
[`overflowing_round`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.overflowing_round
[`round`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.round
[`saturating_ceil`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.saturating_ceil
[`saturating_floor`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.saturating_floor
[`saturating_from_fixed`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.saturating_from_fixed
[`saturating_from_float`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.saturating_from_float
[`saturating_from_int`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.saturating_from_int
[`saturating_round`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.saturating_round
[`to_f16`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.to_f16
[`to_f32`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.to_f32
[`to_f64`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.to_f64
[`to_float`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.to_float
[`to_int_ceil`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.to_int_ceil
[`to_int_floor`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.to_int_floor
[`to_int_round`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.to_int_round
[`to_int`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.to_int
[`wrapping_ceil`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.wrapping_ceil
[`wrapping_floor`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.wrapping_floor
[`wrapping_from_fixed`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.wrapping_from_fixed
[`wrapping_from_float`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.wrapping_from_float
[`wrapping_from_int`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.wrapping_from_int
[`wrapping_round`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html#method.wrapping_round

### Version 0.1.6 news (2019-01-27)

  * Optional [serde][*serde* crate] support was added.

### Version 0.1.5 news (2019-01-26)

  * A new module [`types`] is available with aliases for all supported
    fixed-point numbers.
  * Lossless infallible conversions between fixed-point numbers and
    numeric primitives are now supported using [`From`] and [`Into`].

[`types`]: https://docs.rs/fixed/0.2.1/fixed/types/index.html

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
fixed = "0.2.1"
```

If you are using the 2015 Rust edition, you also need to declare it by
adding this to your crate root (usually *lib.rs* or *main.rs*):

```rust
extern crate fixed;
```

The *fixed* crate requires rustc version 1.28.0 or later.

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
version = "0.2.1"
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
[`FixedI128`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/0.2.1/fixed/struct.FixedU8.html
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`I20F12`]: https://docs.rs/fixed/0.2.1/fixed/types/type.I20F12.html
[`I4F12`]: https://docs.rs/fixed/0.2.1/fixed/types/type.I4F12.html
[`I4F4`]: https://docs.rs/fixed/0.2.1/fixed/types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`U20F12`]: https://docs.rs/fixed/0.2.1/fixed/types/type.U20F12.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`from_fixed`]: struct.FixedI8.html#method.from_fixed
[const generics]: https://github.com/rust-lang/rust/issues/44580
