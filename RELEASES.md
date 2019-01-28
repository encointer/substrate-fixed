<!-- Copyright © 2018–2019 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

Version 0.2.0 (unreleased)
==========================

  * The new methods `from_fixed`, `checked_from_fixed`,
    `saturating_from_fixed`, `wrapping_from_fixed` and
    `overflowing_from_fixed` were added.
  * The old method `from_int` was removed to be replaced.
  * The new methods `from_int`, `checked_from_int`,
    `saturating_from_int`, `wrapping_from_int` and
    `overflowing_from_int` were added.
  * The new methods `from_float`, `checked_from_float`,
    `saturating_from_float`, `wrapping_from_float` and
    `overflowing_from_float` were added.
  * The methods `from_f16`, `from_f32`, `from_f64`, `to_f16`, `to_f32`
    and `to_f64` were deprecated.
  * The new method `to_float` was added.

Version 0.1.6 (2019-01-27)
==========================

  * Optional serde support was added.

Version 0.1.5 (2019-01-26)
==========================

  * Lossless infallible conversions between fixed-point numbers and
    numeric primitives are now supported using `From` and `Into`.
  * A new module `types` is available with aliases for all supported
    fixed-point numbers.

Version 0.1.4 (2018-11-29)
==========================

  * Division is now implemented for `FixedI128` and `FixedU128`.

Version 0.1.3 (2018-08-23)
==========================

  * The `f16` feature was added, and new methods `from_f16` and
    `to_f16` were added.

Version 0.1.2 (2018-08-15)
==========================

  * The crate can now be used without the standard library `std`.
  * New methods `from_f32` and `from_f64` were added.
  * New methods `is_positive` and `is_negative` were added to signed
    fixed-point numbers.

Version 0.1.1 (2018-08-11)
==========================

  * Comparisons are now supported between all fixed-point numbers with
    the same underlying integer type.
  * New static methods `int_bits` and `frac_bits` were added.
  * New methods `from_int`, `to_int`, `to_int_ceil`, `to_int_floor`
    and `to_int_round` were added.
  * New methods `int` and `frac` were added.
  * Support for multiplication and division by integers was added.

Version 0.1.0 (2018-08-10)
==========================

  * `Unsigned` constants provided by the *typenum* crate are now used
    for the number of fractional bits.
  * Many methods and trait implementations available for primitive
    integers are now also supported by the fixed-point numbers.
