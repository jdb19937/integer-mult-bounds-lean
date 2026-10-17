module

public import IntegerMultBounds.MathlibTM2.Fast.CompactDimensionPower
public import IntegerMultBounds.MathlibTM2.Fast.ParamSub
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
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith
public import IntegerMultBounds.MathlibTM2.Mult.CRT

/-!
# Executable dyadic dimension

Compute the sixteenth integer root of the seventh power, retaining the original input.
This standalone program leaves global sizing and parameter-word allocation unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {A W w : ℕ}

/-- Input `0`, seventh power `1`, dimension `2`, and root-search scratch `3` through `6`. -/
def compactDyadicDimensionC : TblCode 7 :=
  compactDimensionPowerC.rename ![0, 1] ;; (pmIrootC 4).rename ![1, 2, 3, 4, 5, 6]

/-- Five power atoms plus the sixteenth-root search budget. -/
def compactDyadicDimensionAtoms (b : ℕ) : ℕ := 44 + 32 * iroot 16 (b ^ 7)

/-- Charged dimension computation, preserving the input and accumulator. -/
theorem compactDyadicDimensionC_do (st : TblSt 7 A) {b : ℕ}
    (hb : st.val 0 = b) (hW : (b ^ 7 + 1) ^ 2 < 2 ^ W) (hkW : 8 < 2 ^ W) :
    TblDo A W w compactDyadicDimensionC st
      (fun s => s.val 0 = b ∧ s.val 1 = b ^ 7 ∧
        s.val 2 = iroot 16 (b ^ 7) ∧ s.acc = st.acc)
      (compactDyadicDimensionAtoms b) := by
  have hp : b ^ 7 < 2 ^ W := by nlinarith
  have hpower := (compactDimensionPowerC_do (W := W) (w := w)
    (st.restrict ![0, 1]) (by simpa [TblSt.restrict] using hb) hp).rename
      (f := ![0, 1]) (by decide)
  refine (hpower.seq (K₂ := 39 + iroot 16 (b ^ 7) * 32)
    (fun s hs => ?_)).mono (fun _ h => h) ?_
  · have hroot := (pmIrootC_do 4 (W := W) (w := w)
      (s.restrict ![1, 2, 3, 4, 5, 6]) (by simpa [TblSt.restrict] using hs.1.2.1)
      (by simpa [sq] using hW) (by omega)).rename
        (f := ![1, 2, 3, 4, 5, 6]) (by decide)
    exact hroot.mono (fun z hz => ⟨
      (hz.2 0 (by decide)).trans (by simpa [TblSt.restrict] using hs.1.1),
      by simpa [TblSt.restrict] using hz.1.1,
      by simpa [TblSt.restrict] using hz.1.2.1,
      hz.1.2.2.trans hs.1.2.2⟩) le_rfl
  · simp [compactDyadicDimensionAtoms]
    omega

end IntegerMultBounds.MathlibTM2.Fast.TableVM
