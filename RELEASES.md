<!-- Copyright © 2018 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

Version 0.1.4 (unreleased)
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
