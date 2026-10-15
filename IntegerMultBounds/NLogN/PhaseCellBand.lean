module

public import IntegerMultBounds.NLogN.PhaseCellSelectedTail
public import Mathlib.Data.Nat.Sqrt

/-! An executable square-root band for the entire-lattice Gaussian tail.
The width is within one of the real square-root scale, with no dimension
factor. This selects a parameter; it does not assert tape execution costs. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellBand

/-- A positive, executable band width with strict slack at square boundaries. -/
def width (p u : ℕ) : ℕ := Nat.sqrt (16*p/u)+1

theorem width_pos (p u : ℕ) : 0<width p u := by
  simp [width]

theorem width_spec (p u : ℕ) (hu : 0<u) : 16*p<u*(width p u)^2 := by
  have h := Nat.lt_succ_sqrt' (16*p/u)
  have hdiv : 16*p/u<(width p u)^2 := by simpa [width] using h
  have := (Nat.div_lt_iff_lt_mul hu).mp hdiv
  simpa [Nat.mul_comm] using this

/-- The lower square stays within the exact rational target scale. -/
theorem width_pred_sq (p u : ℕ) : u*(width p u-1)^2≤16*p := by
  have h := Nat.sqrt_le' (16*p/u)
  have hmul := Nat.mul_le_mul_left u h
  calc u*(width p u-1)^2 = u*(Nat.sqrt (16*p/u))^2 := by simp [width]
    _≤u*(16*p/u) := hmul
    _≤16*p := by simpa [Nat.mul_comm] using Nat.div_mul_le_self (16*p) u

/-- The selected executable band discharges the full signed-tail allowance. -/
theorem tail_bound (s t p u : ℕ) (hs : 0<s) (hst : s≤t) (hp : 0<p)
    (hu : 1≤u) (α : ℝ) (hα : 0<α) (hαu : α^2=(u : ℝ)) (j : ℤ) :
    (∑' n : ℕ, Real.exp (normExp s t α j
      (PhaseCellTailBounds.tailIndex false (width p u) n)))+
    (∑' n : ℕ, Real.exp (normExp s t α j
      (PhaseCellTailBounds.tailIndex true (width p u) n)))≤
        1/(2 : ℝ)^(46*p) := by
  exact PhaseCellTailBounds.selected_tail s t p u (width p u) hs hst hp hu
    (width_spec p u (by omega)).le α hα hαu j

end IntegerMultBounds.NLogN.PhaseCellBand
