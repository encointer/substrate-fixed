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

## What’s new

### Version 0.1.1 news (unreleased)

  * New static methods [`int_bits`] and [`frac_bits`] were added.
  * New methods [`from_int`], [`to_int`], [`to_int_ceil`],
    [`to_int_floor`] and [`to_int_round`] were added.
  * New methods [`int`] and [`frac`] were added.
  * Support for multiplication and division by integers was added.
  
[`frac_bits`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.frac_bits
[`frac`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.frac
[`from_int`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.from_int
[`to_int_bits`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.to_int_bits
[`to_int_ceil`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.to_int_ceil
[`to_int_floor`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.to_int_floor
[`to_int_round`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.to_int_round
[`to_int`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.to_int
[`int`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html#method.int

### Version 0.1.0 news (2018-08-10)

  * [`Unsigned`] constants provided by the [*typenum* crate] are now
    used for the number of fractional bits.
  * Many methods and trait implementations available for primitive
    integers are now also supported by the fixed-point numbers.

[`Unsigned`]: https://docs.rs/typenum/^1.3/typenum/marker_traits/trait.Unsigned.html

### Other releases

Details on other releases can be found in [*RELEASES.md*].

[*RELEASES.md*]: https://gitlab.com/tspiteri/fixed/blob/master/RELEASES.md

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.1.0"
```

You also need to declare it by adding this to your crate root (usually
*lib.rs* or *main.rs*):

```rust
extern crate fixed;
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
[*typenum* crate]: https://crates.io/crates/typenum
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`FixedI128`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/0.1.0/fixed/struct.FixedU8.html
[channels]: https://doc.rust-lang.org/book/second-edition/appendix-07-nightly-rust.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
