module
public import IntegerMultBounds.MathlibTM2.Fast.TableProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.ENatToNat
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith


/-!
# Thirty-first power for the compact dimension parameter

The program preserves its input in variable `0` and computes its thirty-first power in
variable `1`: one copy, then four square-and-multiply steps give `31 = (((1·2+1)·2+1)·2+1)·2+1`,
for nine table atoms. The explicit word-fit premise keeps this helper independent of the
eventual parameter-word allocation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {A W w : ℕ}

/-- Preserve `x` in `0` and place `x^31` in `1`. -/
def compactDimensionPowerC : TblCode 2 :=
  tblBlock 2 [.copy 0 1, .mul 1 1 1, .mul 1 0 1, .mul 1 1 1, .mul 1 0 1,
    .mul 1 1 1, .mul 1 0 1, .mul 1 1 1] (.mul 1 0 1)

/-- The complete input/output frame and charged execution of the power helper. -/
theorem compactDimensionPowerC_do (st : TblSt 2 A) {x : ℕ}
    (hx : st.val 0 = x) (hW : x ^ 31 < 2 ^ W) :
    TblDo A W w compactDimensionPowerC st
      (fun s => s.val 0 = x ∧ s.val 1 = x ^ 31 ∧ s.acc = st.acc) 9 := by
  have hp (k : ℕ) (hk : 1 ≤ k) (hk31 : k ≤ 31) : x ^ k < 2 ^ W := by
    by_cases hx0 : x = 0
    · simp [hx0, Nat.ne_of_gt hk]
    · exact (Nat.pow_le_pow_right (by omega : 1 ≤ x) hk31).trans_lt hW
  have h2 := hp 2 (by omega) (by omega)
  have h3 := hp 3 (by omega) (by omega)
  have h6 := hp 6 (by omega) (by omega)
  have h7 := hp 7 (by omega) (by omega)
  have h14 := hp 14 (by omega) (by omega)
  have h15 := hp 15 (by omega) (by omega)
  have h30 := hp 30 (by omega) (by omega)
  have e2 : x * x = x ^ 2 := by ring
  have e3 : x ^ 2 * x = x ^ 3 := by ring
  have e6 : x ^ 3 * x ^ 3 = x ^ 6 := by ring
  have e7 : x ^ 6 * x = x ^ 7 := by ring
  have e14 : x ^ 7 * x ^ 7 = x ^ 14 := by ring
  have e15 : x ^ 14 * x = x ^ 15 := by ring
  have e30 : x ^ 15 * x ^ 15 = x ^ 30 := by ring
  have e31 : x ^ 30 * x = x ^ 31 := by ring
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hx, e2, e3, e6, e7, e14, e15, e30, e31,
      h2, h3, h6, h7, h14, h15, h30, hW]
  · simp [tblExactList, TblIns.exact, hx, e2, e3, e6, e7, e14, e15, e30, e31]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
