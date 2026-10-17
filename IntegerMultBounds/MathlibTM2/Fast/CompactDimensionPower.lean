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
# Seventy-ninth power for the compact dimension parameter

The program preserves its input in variable `0` and computes its seventy-ninth power in
variable `1`: one copy, three squarings and a multiplication give the ninth power, and three
square-and-multiply steps give `79 = ((9·2+1)·2+1)·2+1`, for eleven table atoms. The explicit
word-fit premise keeps this helper independent of the eventual parameter-word allocation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {A W w : ℕ}

/-- Preserve `x` in `0` and place `x^79` in `1`. -/
def compactDimensionPowerC : TblCode 2 :=
  tblBlock 2 [.copy 0 1, .mul 1 1 1, .mul 1 1 1, .mul 1 1 1, .mul 1 0 1,
    .mul 1 1 1, .mul 1 0 1, .mul 1 1 1, .mul 1 0 1, .mul 1 1 1] (.mul 1 0 1)

/-- The complete input/output frame and charged execution of the power helper. -/
theorem compactDimensionPowerC_do (st : TblSt 2 A) {x : ℕ}
    (hx : st.val 0 = x) (hW : x ^ 79 < 2 ^ W) :
    TblDo A W w compactDimensionPowerC st
      (fun s => s.val 0 = x ∧ s.val 1 = x ^ 79 ∧ s.acc = st.acc) 11 := by
  have hp (k : ℕ) (hk : 1 ≤ k) (hk79 : k ≤ 79) : x ^ k < 2 ^ W := by
    by_cases hx0 : x = 0
    · simp [hx0, Nat.ne_of_gt hk]
    · exact (Nat.pow_le_pow_right (by omega : 1 ≤ x) hk79).trans_lt hW
  have h2 := hp 2 (by omega) (by omega)
  have h4 := hp 4 (by omega) (by omega)
  have h8 := hp 8 (by omega) (by omega)
  have h9 := hp 9 (by omega) (by omega)
  have h18 := hp 18 (by omega) (by omega)
  have h19 := hp 19 (by omega) (by omega)
  have h38 := hp 38 (by omega) (by omega)
  have h39 := hp 39 (by omega) (by omega)
  have h78 := hp 78 (by omega) (by omega)
  have e2 : x * x = x ^ 2 := by ring
  have e4 : x ^ 2 * x ^ 2 = x ^ 4 := by ring
  have e8 : x ^ 4 * x ^ 4 = x ^ 8 := by ring
  have e9 : x ^ 8 * x = x ^ 9 := by ring
  have e18 : x ^ 9 * x ^ 9 = x ^ 18 := by ring
  have e19 : x ^ 18 * x = x ^ 19 := by ring
  have e38 : x ^ 19 * x ^ 19 = x ^ 38 := by ring
  have e39 : x ^ 38 * x = x ^ 39 := by ring
  have e78 : x ^ 39 * x ^ 39 = x ^ 78 := by ring
  have e79 : x ^ 78 * x = x ^ 79 := by ring
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hx, e2, e4, e8, e9, e18, e19, e38, e39,
      e78, e79, h2, h4, h8, h9, h18, h19, h38, h39, h78, hW]
  · simp [tblExactList, TblIns.exact, hx, e2, e4, e8, e9, e18, e19, e38, e39, e78, e79]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
