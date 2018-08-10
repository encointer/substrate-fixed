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

The crate provides unsigned fixed-point numbers [`FixedU8`],
[`FixedU16`], [`FixedU32`], [`FixedU64`] and [`FixedU128`], and signed
fixed-point numbers [`FixedI8`], [`FixedI16`], [`FixedI32`],
[`FixedI64`] and [`FixedI128`].

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.0.1"
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
[`FixedI128`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/0.0.1/fixed/struct.FixedU8.html
[channels]: https://doc.rust-lang.org/book/second-edition/appendix-07-nightly-rust.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
