module
public import IntegerMultBounds.NLogN.PhaseCellRow
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.ReduceModChar
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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords


/-! The executable rational periodic matrix underlying the rounded Gaussian
operator, accumulating every retained lattice alias into its actual column. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open PhaseCellRow
variable (s t : ℕ) [NeZero s]

/-- Literal rational matrix; colliding wrapped offsets are added. -/
def matrix (p u : ℕ) : Matrix (ZMod s) (ZMod s) ℚ := fun j l =>
  window (fun k => if j+(k : ZMod s)=l then
    PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u)
      (j.val : ℤ) (j.val+k) else 0) (PhaseCellBand.width p u)

noncomputable def realMatrix (p u : ℕ) : Matrix (ZMod s) (ZMod s) ℝ :=
  fun j l => (matrix s t p u j l : ℝ)

private theorem value_nonneg (P : ℕ) (arg : PhaseCellExecutableCoefficients.ExpArg) :
    0≤arg.value P := PhaseCellExpSample.sample_nonneg P arg.aa arg.b

private theorem kernel_nonneg (P w : ℕ) (arg : ℤ → PhaseCellExecutableCoefficients.ExpArg) (k : ℤ) :
    0≤PhaseCellExecutableCoefficients.kernel P w arg k := by
  unfold PhaseCellExecutableCoefficients.kernel
  split
  · norm_num
  · split
    · exact value_nonneg _ _
    · exact le_refl _

/-- Every retained sample is nonnegative, even outside the selected regime. -/
theorem entry_nonneg (P s t u w : ℕ) (j l : ℤ) :
    0≤PhaseCellCrossCell.entry P s t u w j l := by
  unfold PhaseCellCrossCell.entry
  split
  · unfold PhaseCellConcreteCoefficients.entry PhaseCellExecutableCoefficients.entry
    split
    · norm_num
    · exact div_nonneg (mul_nonneg (value_nonneg _ _) (kernel_nonneg _ _ _ _)) (value_nonneg _ _)
  · split
    · exact value_nonneg _ _
    · exact le_refl _

omit [NeZero s] in
theorem matrix_nonneg (p u : ℕ) (j l : ZMod s) : 0≤matrix s t p u j l := by
  unfold matrix window
  have h (k : ℤ) : (0 : ℚ) ≤ if j+(k : ZMod s)=l then
      PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u)
        (j.val : ℤ) (j.val+k) else 0 := by
    split
    · exact entry_nonneg _ _ _ _ _ _ _
    · exact le_refl _
  exact add_nonneg (add_nonneg (h 0) (Finset.sum_nonneg (fun n _ => h _)))
    (Finset.sum_nonneg (fun n _ => h _))

omit [NeZero s] in
theorem matrix_diag (p u : ℕ) (j : ZMod s) : 1≤matrix s t p u j j := by
  unfold matrix window
  have h (k : ℤ) : (0 : ℚ) ≤ if j+(k : ZMod s)=j then
      PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u)
        (j.val : ℤ) (j.val+k) else 0 := by
    split
    · exact entry_nonneg _ _ _ _ _ _ _
    · exact le_refl _
  have hp := Finset.sum_nonneg (s := Finset.range (PhaseCellBand.width p u)) (fun n _ => h ((n : ℤ)+1))
  have hn := Finset.sum_nonneg (s := Finset.range (PhaseCellBand.width p u)) (fun n _ => h (-((n : ℤ)+1)))
  simp only [Int.cast_zero, add_zero, ite_true, PhaseCellCrossCell.entry_diag]
  linarith

/-- Matrix-vector action agrees with the already checked periodic row. -/
theorem matrix_mulVec (p u : ℕ) (v : ZMod s → ℂ) :
    Matrix.mulVec (fun j l => (matrix s t p u j l : ℂ)) v=
      PhaseCellRow.rounded s t p u (PhaseCellBand.width p u) v := by
  funext j
  simp only [Matrix.mulVec, dotProduct, matrix, PhaseCellRow.rounded, window,
    Rat.cast_add, Rat.cast_sum, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range _),
    Finset.sum_comm (s := Finset.univ) (t := Finset.range _)]
  congr 2
  all_goals simp only [apply_ite, Rat.cast_zero, ite_mul, zero_mul,
    Fintype.sum_ite_eq]

end IntegerMultBounds.NLogN.PhaseCellMatrix
