module

public import IntegerMultBounds.MathlibTM2.Fast.CompactFinal
public import IntegerMultBounds.MathlibTM2.Fast.Final
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynLoop

/-!
# Integer multiplication below `n log n` on Mathlib's Turing machines

`mulInTime` exposes the explicit improved saving; `statement` retains the existential
interface in `Statement.lean`. Both follow from the complete compact host multiplier and its checked runtime bound.
The historical exact margin remains available through `mulInTime_exact`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2

/-- Historical M2 exact saving, retained for compatibility. -/
theorem mulInTime_exact : MulInTime (296 / (10 ^ 11 * 2 ^ 37)) := by
  rw [← Cost.tot_kappa_eq]
  let L := Fast.Main.blLayDs Fast.Main.dsyV₀ Fast.Main.dsyV₀_wires
    (Fast.Main.finCost Cost.mr_loop_cost_le)
  let D := Fast.Main.bdDist Fast.Main.dsyWires Fast.Main.mn_postParam_bd
  have hw : ∀ᶠ n in Filter.atTop, Mult.Sizes.p n + 2 ≤ Fast.Main.bdW n := by
    filter_upwards [D.widths] with n hn
    have := hn.1
    omega
  exact Fast.Main.mulInTime_of_bundles
    ⟨Fast.Main.mnKa, Fast.Main.mnLb, Fast.Main.bdW, Fast.Main.mnσL L,
      ⟨Fast.Main.mnSynOfLay L hw⟩, ⟨D⟩⟩

/-- The complete compact multiplier has the explicit power-of-two saving `2^-37`. -/
theorem mulInTime : MulInTime (2 ^ 37 : ℝ)⁻¹ :=
  Fast.Main.compact_mulInTime

theorem statement : Statement :=
  ⟨_, by positivity, mulInTime⟩

end IntegerMultBounds.MathlibTM2
