module
public import IntegerMultBounds.MathlibTM2.Fast.CRTBase
import IntegerMultBounds.MathlibTM2.Fast.TableVM
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
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


/-! # Runtime word-width setup for CRT controls

Three copies of the total address width and one endpoint bit suffice for all
control products. Both interpreter configuration registers are returned by
an explicit cleanup program.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def crtControlWidthSetup (total width unit tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy total width tmp) <| .seq (ucopy total width tmp) <|
  .seq (ucopy total width tmp) <| .seq (crtPush width tick) (crtPush unit tick)

/-- Construct `3*L+1` and one unary tick while preserving the original width. -/
theorem crtControlWidthSetup_runs {total width unit tmp : Fin T}
    (hreg : [total, width, unit, tmp].Nodup) (R : Regs T A)
    (hw : R width = []) (hu : R unit = []) (ht : R tmp = []) :
    crtRuns body (crtControlWidthSetup total width unit tmp) R
      (Function.update (Function.update R width
        (List.replicate (3 * (R total).length + 1) tick)) unit [tick])
      (12 * (R total).length + 14) := by
  have hreg' := hreg
  regs_ne hreg'
  let L := (R total).length
  let R₁ := Function.update R width (List.replicate L tick)
  let R₂ := Function.update R width (List.replicate (2 * L) tick)
  let R₃ := Function.update R width (List.replicate (3 * L) tick)
  have h₁ := crtUcopy_runs (body := body) ‹total ≠ width› ‹total ≠ tmp› ‹width ≠ tmp› R ht
  simp only [hw, List.append_nil] at h₁
  have h₂ := crtUcopy_runs (body := body) ‹total ≠ width› ‹total ≠ tmp› ‹width ≠ tmp› R₁
    (by simp [R₁, Ne.symm ‹width ≠ tmp›, ht])
  have h₂' : crtRuns body (ucopy total width tmp) R₁ R₂ (4 * L + 4) := by
    simpa [R₁, R₂, ‹total ≠ width›, ← List.replicate_add, two_mul, L] using h₂
  have h₃ := crtUcopy_runs (body := body) ‹total ≠ width› ‹total ≠ tmp› ‹width ≠ tmp› R₂
    (by simp [R₂, Ne.symm ‹width ≠ tmp›, ht])
  have h₃' : crtRuns body (ucopy total width tmp) R₂ R₃ (4 * L + 4) := by
    have he : (R total).length + 2 * (R total).length = 3 * (R total).length := by omega
    simpa [R₂, R₃, ‹total ≠ width›, ← List.replicate_add, he, L] using h₃
  have h₄ := crtPush_runs (body := body) width tick R₃
  have h₅ := crtPush_runs (body := body) unit tick (Function.update R₃ width (tick :: R₃ width))
  refine crtRuns_mono (crtRuns_congr
    (crtRuns_seq h₁ (crtRuns_seq h₂' (crtRuns_seq h₃' (crtRuns_seq h₄ h₅)))) ?_) (by dsimp [L]; omega)
  simp [R₃, Ne.symm ‹width ≠ unit›, hu, L, List.replicate_succ]

/-- Return both configuration registers after the arithmetic bank is cleared. -/
def crtControlWidthClear (width unit : Fin T) : Pr P T Q A U :=
  .seq (uclear width) (uclear unit)

theorem crtControlWidthClear_runs {width unit : Fin T} (hne : width ≠ unit)
    (R : Regs T A) (L : ℕ) (hw : (R width).length = 3 * L + 1)
    (hu : (R unit).length = 1) :
    crtRuns body (crtControlWidthClear width unit) R
      (Function.update (Function.update R width []) unit []) (6 * L + 8) := by
  have h₁ := crtClear_runs (body := body) width R
  have h₂ := crtClear_runs (body := body) unit (Function.update R width [])
  exact crtRuns_mono (crtRuns_seq h₁ h₂) (by simp [Ne.symm hne, hw, hu]; omega)

end IntegerMultBounds.MathlibTM2.Fast
