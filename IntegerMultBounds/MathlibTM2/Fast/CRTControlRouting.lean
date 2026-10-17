module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlParameters
public import IntegerMultBounds.MathlibTM2.Fast.CRTSchedule
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Routing headers from the existing CRT target counters

The reversed-layout outer width is the old driver's upper-axis width. The
intervening gap is its lower-axis width minus the cached zero-axis width.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

/-- Axes above the target in the fixed reversed layout. -/
def crtControlRoutingPre {d : ℕ} (i : Fin (d + 1)) : List (Fin (d + 1)) :=
  ((List.finRange (d + 1)).drop (i.val + 1)).reverse

/-- Axes strictly between the target and axis zero. -/
def crtControlRoutingGap {d : ℕ} (i : Fin (d + 1)) : List (Fin (d + 1)) :=
  (crtRevAx i.val).take (i.val - 1)

theorem crtControlRouting_split {d : ℕ} (i : Fin (d + 1)) (hi : i ≠ 0) :
    crtOuterAxes d = crtControlRoutingPre i ++ i :: crtControlRoutingGap i := by
  have hip : 0 < i.val := by
    have h : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  have hfull : crtRevAx (d := d + 1) (d + 1) =
      crtControlRoutingPre i ++ i :: crtRevAx i.val := by
    have h := congrArg List.reverse (List.take_append_drop (i.val + 1) (List.finRange (d + 1)))
    simp only [List.reverse_append] at h
    have h' : crtControlRoutingPre i ++ crtRevAx (i.val + 1) =
        crtRevAx (d := d + 1) (d + 1) := by
      simpa [crtControlRoutingPre, crtRevAx, List.take_of_length_le (by simp : (List.finRange (d + 1)).length ≤ d + 1)] using h
    rw [crtRevAx_succ i.isLt] at h'
    simpa using h'.symm
  have hgap : crtRevAx i.val = crtControlRoutingGap i ++ [0] := by
    have h := List.take_append_drop (i.val - 1) (crtRevAx (d := d + 1) i.val)
    rw [crtRevAx_drop hip i.isLt.le] at h
    have hz : crtRevAx (d := d + 1) 1 = [0] := by
      rw [crtRevAx_succ (by omega : 0 < d + 1)]
      simp [crtRevAx]
    rw [hz] at h
    exact h.symm
  rw [crtRevAx_eq_outer, hgap] at hfull
  exact List.append_cancel_right (show crtOuterAxes d ++ [0] =
    (crtControlRoutingPre i ++ i :: crtControlRoutingGap i) ++ [0] from by
      simpa only [List.append_assoc, List.cons_append] using hfull)

theorem crtControlRoutingPre_width {d : ℕ} (a : Fin (d + 1) → ℕ) (i : Fin (d + 1)) :
    crtW a (crtControlRoutingPre i) = crtW a ((List.finRange (d + 1)).drop (i.val + 1)) := by
  simp [crtW, crtControlRoutingPre]

theorem crtControlRoutingGap_width {d : ℕ} (a : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (hi : i ≠ 0) :
    crtW a (crtControlRoutingGap i) = crtPre a i.val - a 0 := by
  have hip : 1 ≤ i.val := by
    have h : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  have h := crtW_revAx_take a hip i.isLt.le
  have hzero : crtPre a 1 = a 0 := by
    rw [crtPre_succ a (by omega : 0 < d + 1)]
    simp [crtPre]
  rw [hzero] at h
  change crtW a (crtControlRoutingGap i) + a 0 = crtPre a i.val at h
  omega

/-- Reuse the old driver's lower-width and cached zero-width tapes to prepare
exactly the gap header required by distant exposure. -/
theorem crtControlRoutingGap_runs {T Q A : ℕ} {U P : Type}
    {body : P → Pr P T Q A U} {lower zeroWidth gap tmp : Fin T}
    (hreg : [lower, zeroWidth, gap, tmp].Nodup) {d : ℕ}
    (a : Fin (d + 1) → ℕ) (i : Fin (d + 1)) (hi : i ≠ 0)
    (R : Regs T A) (hlower : (R lower).length = crtPre a i.val)
    (hzero : (R zeroWidth).length = a 0) (hgap : R gap = []) (htmp : R tmp = []) :
    crtRuns body (crtControlPrefixWidth lower zeroWidth gap tmp) R
      (Function.update R gap (List.replicate (crtW a (crtControlRoutingGap i)) tick))
      (4 * crtPre a i.val + 4 * a 0 + 8) := by
  simpa only [hlower, hzero, crtControlRoutingGap_width a i hi] using
    crtControlPrefixWidth_runs (body := body) hreg R hgap htmp

end IntegerMultBounds.MathlibTM2.Fast
