module

public import IntegerMultBounds.MathlibTM2.Main
public import IntegerMultBounds.MathlibTM2.FastPath

/-!
# Integer multiplication on Mathlib's `Turing.FinTM2`

`IntegerMultBounds.MathlibTM2.Statement` states multiplication below `n log n` using only Mathlib
vocabulary. `IntegerMultBounds.MathlibTM2.statement` proves it unconditionally via the complete
fast host multiplier. The separate `statement_of_endToEnd` bridge also derives it from the
stronger compact-control target `IntegerMultBounds.Machine.EndToEnd`.
-/
