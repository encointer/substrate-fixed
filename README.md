<!-- Copyright © 2018 Trevor Spiteri -->

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
integer primitives are implemented. That is, you can use [`From`] or
[`Into`] for the conversions that always work without losing any bits.

## What’s new

### Version 0.1.5 (unreleased)

  * Lossless infallible conversions between fixed-point numbers and
    integer primitives are now supported using [`From`] and [`Into`].

### Version 0.1.4 news (2018-11-29)

  * Division is now implemented for [`FixedI128`] and [`FixedU128`].

### Other releases

Details on other releases can be found in [*RELEASES.md*].

[*RELEASES.md*]: https://gitlab.com/tspiteri/fixed/blob/master/RELEASES.md

## Quick example

```rust
use fixed::frac;
use fixed::FixedI32;

// 20 integer bits, 12 fractional bits
type I20F12 = FixedI32<frac::U12>;
// 19/3 = 6 1/3
let six_and_third = I20F12::from_int(19).unwrap() / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// convert to i32, taking the ceil
assert_eq!(six_and_third.to_int_ceil(), 7);
```

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.1.4"
```

You also need to declare it by adding this to your crate root (usually
*lib.rs* or *main.rs*):

```rust
extern crate fixed;
```

The *fixed* crate requires rustc version 1.28.0 or later.

## Optional features

The *fixed* crate has one optional feature:

 1. `f16`, disabled by default. This provides conversion to/from
    [`f16`]. This features requires the [*half* crate].

To enable the feature, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.fixed]
version = "0.1.4"
features = ["f16"]
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
[*typenum* crate]: https://crates.io/crates/typenum
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`FixedI128`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/0.1.4/fixed/struct.FixedU8.html
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
