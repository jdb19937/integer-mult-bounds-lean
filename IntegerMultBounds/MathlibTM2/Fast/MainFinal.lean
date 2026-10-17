module

public import IntegerMultBounds.MathlibTM2.Fast.BundleDist
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The statement from the layout bundle and the wires program

`mn_postParam_bd`: the store the parameter machine leaves (`MnPostParam`, `Fast/MainProg`) has
the seven registers of the rounding and output parameters empty (`MnPostParam.rndEmpty`), so it
meets `BdPostParam` (`Fast/BundleDist`).

`statement_of_wires`: `IntegerMultBounds.MathlibTM2.Statement` from a layout bundle `L : MnLay bdW` (`Fast/MainEmbed`)
and a wires program `BdWires (mnσL L)` (`Fast/BundleDist`), through `bd_statement`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds.MathlibTM2.Node

/-- The parameter machine leaves the registers of `bdRndRegs` empty: `MnPostParam` implies
`BdPostParam`. -/
theorem mn_postParam_bd (R : Regs mnT bdA) (n : ℕ) (h : MnPostParam R n) : BdPostParam R n :=
  { h with rnd := fun r hr => h.rndEmpty r (by simpa [bdRndRegs, mnRndRegs] using hr) }

/-- **The statement** from a layout bundle and a wires program. -/
theorem statement_of_wires (h : ∃ L : MnLay bdW, Nonempty (BdWires (mnσL L))) :
    IntegerMultBounds.MathlibTM2.Statement :=
  bd_statement mn_postParam_bd h

end IntegerMultBounds.MathlibTM2.Fast.Main
