module
public import IntegerMultBounds.MathlibTM2.Fast.ResampBMath
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Fast.CMul
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


/-!
# Lines of a padded box

* `rsbVec`: a line as an array on `ZMod t`; `rsbArr_rsbVec`.
* `rsbLineG p K m E D L`: the `t` outputs of the Neumann line map on a line of `t` records.
* `rsb_fits_of_norm_le`: the numerator of a grid value of norm at most one fits `w ≥ p + 2`
  bits.

The Neumann axis machine (`rsbAxisP`, `rsb_axis_runs`) was removed with the Neumann `B̃₀`;
restore from `1cb2723b`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.NLogN (rowIndex)


noncomputable section

section Axis

variable {s t : ℕ} [NeZero s] [NeZero t]

/-- The line `L` as an array on `ZMod t` (entries past the end are zero). -/
def rsbVec (L : List GaussianInt) : ZMod t → GaussianInt := fun j => L.getD j.val 0

omit [NeZero t] in
lemma rsbArr_rsbVec (L : List GaussianInt) (hL : L.length = t) :
    rsbArr (rsbVec (t := t) L) = L := by
  apply List.ext_getElem (by simp [length_rsbArr, hL])
  intro i h₁ h₂
  have hi : i < t := by simpa [length_rsbArr] using h₁
  simp [rsbArr, rsbVec, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h₂, Nat.mod_eq_of_lt hi]

variable (s t) in
/-- The `t` outputs of `B̃₀` on one line of `t` records: `s` numerators and `t - s` zeros. -/
def rsbLineG (p K m : ℕ) (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ) (L : List GaussianInt) :
    List GaussianInt :=
  rsbArr (rsbLineNum p K m E D (rsbVec (t := t) L)) ++ List.replicate (t - s) 0

variable {T Q A : ℕ} {U : Type} {P : Type}

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

variable {body : P → Pr P T Q A U} {rg}

end Axis

/-! ### Admissible lines from the unit disk -/

section Ball

open IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.OffDiagSum (offTermW)

/-- The numerator of a grid value of norm at most one fits `w ≥ p + 2` bits. -/
lemma rsb_fits_of_norm_le {w p : ℕ} (hw : p + 2 ≤ w) (N : GaussianInt)
    (h : ‖rsbGrid p N‖ ≤ 1) : Fits w N := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hlt : (2 : ℝ) ^ p < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hre : |(N.re : ℝ)| ≤ 2 ^ p := by
    have h1 := (Complex.abs_re_le_norm (rsbGrid p N)).trans h
    rw [rsbGrid, two_pow_complex, toComplex_div_re, abs_div, abs_of_pos hp, div_le_one hp] at h1
    exact h1
  have him : |(N.im : ℝ)| ≤ 2 ^ p := by
    have h1 := (Complex.abs_im_le_norm (rsbGrid p N)).trans h
    rw [rsbGrid, two_pow_complex, toComplex_div_im, abs_div, abs_of_pos hp, div_le_one hp] at h1
    exact h1
  constructor
  · have : (|N.re| : ℝ) < 2 ^ (w - 1) := by linarith
    exact_mod_cast this
  · have : (|N.im| : ℝ) < 2 ^ (w - 1) := by linarith
    exact_mod_cast this

variable {s t : ℕ} [NeZero s] [NeZero t]

end Ball

end

end IntegerMultBounds.MathlibTM2.Fast
