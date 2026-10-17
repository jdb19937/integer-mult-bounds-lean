module

public import IntegerMultBounds.MathlibTM2.Fast.DistSynMain
import IntegerMultBounds.MathlibTM2.Fast.DistSynCost
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The wires program as a `BdWires` bundle

`dsyWires : BdWires (fun n => mnσ (blP₀ dsW n) (dsyV₀ n))`: the verified wires program `dsyProg`
(`Fast/DistSynMain`) with its contract `dsyWires_spec` and the cost bound `dsyWiresCost_le`
(`Fast/DistSynCost`), `dsyWiresCost n ≤ 2·10^7 (b n + 1)^7 + 30 · r n · dsW n`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast.TableVM Filter

noncomputable section

/-- **The wires program as a bundle.** -/
def dsyWires : BdWires (fun n => mnσ (blP₀ dsW n) (dsyV₀ n)) where
  prog := dsyProg
  cost := dsyWiresCost
  spec := dsyWires_spec
  costBound := ⟨2 * 10 ^ 7 + 30, 7, by
    filter_upwards [dsyWiresCost_le] with n h
    have h1 : 2 * 10 ^ 7 * (b n + 1) ^ 7 ≤ (2 * 10 ^ 7 + 30) * (b n + 1) ^ 7 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : 30 * (r n * dsW n) ≤ (2 * 10 ^ 7 + 30) * (r n * dsW n) :=
      Nat.mul_le_mul_right _ (by omega)
    omega⟩

end

end IntegerMultBounds.MathlibTM2.Fast.Main
