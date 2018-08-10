<!-- Copyright © 2018 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

# Fixed-point numbers

Fixed provides fixed-point numbers. **It is not yet useful**, as it is
designed to depend on the as-yet unimplemented [const generics]
compiler feature. (In the current code, the number of fractional bits
is hard-coded to the arbitrary value 7, so if you need a fixed-point
number with seven fractional bits, you’re in luck!)

## Using Fixed

Fixed is available on [crates.io][fixed crate]. To use Fixed in your
crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.0.1"
```

You also need to declare it by adding this to your crate root (usually
*lib.rs* or *main.rs*):

```rust
extern crate fixed;
```

Fixed requires [const generics], which are not yet implemented in the
compiler. When they are implemented, Fixed will require the
[nightly][channels] compiler until the feature makes it way to the
[stable][channels] release.

## License

This crate is licensed under either the

 * [Apache License, Version 2.0][LICENSE-APACHE] or
 * [MIT License][LICENSE-MIT]

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the
Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[channels]: https://doc.rust-lang.org/book/second-edition/appendix-07-nightly-rust.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
[fixed crate]: https://crates.io/crates/fixed
