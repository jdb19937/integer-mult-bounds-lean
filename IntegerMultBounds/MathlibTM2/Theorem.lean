module

public import IntegerMultBounds.MathlibTM2.Fast.CompactFinalR

/-!
# Integer multiplication below `n log n` on Mathlib's Turing machines

`mulInTime` exposes the explicit improved saving; `statement` retains the existential
interface in `Statement.lean`. Both follow from the rounded compact host multiplier
`compactR_mulInTime_final` and its checked runtime bound at `ε = 9/32`.

The exact-arithmetic chains (`mulInTime_exact`, `compact_mulInTime` and the `d^6 ≤ b` width
lemmas behind them) no longer hold at `ε = 9/32` and were removed; restore them from the parent
of the commit that introduced this note.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2

/-- The complete compact multiplier has the explicit power-of-two saving `2^-33`. -/
theorem mulInTime : MulInTime (2 ^ 33 : ℝ)⁻¹ :=
  Fast.Main.compactR_mulInTime_final

theorem statement : Statement :=
  ⟨_, by positivity, mulInTime⟩

end IntegerMultBounds.MathlibTM2
