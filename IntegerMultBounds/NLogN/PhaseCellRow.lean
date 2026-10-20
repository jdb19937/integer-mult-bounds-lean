module

public import IntegerMultBounds.NLogN.PhaseCellBand
public import IntegerMultBounds.NLogN.PhaseCellCrossCell
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! Finite periodic Gaussian rows, formed by wrapping every retained lattice
index into ZMod s. Repeated residue classes are accumulated, never discarded.
The exact infinite row is split into a symmetric window and both signed tails. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRow

open scoped BigOperators
open PhaseCellTailBounds

/-- Symmetric finite lattice sum, with its central term counted once. -/
def window {E : Type*} [AddCommMonoid E] (f : ℤ → E) (w : ℕ) : E :=
  f 0 + (∑ n ∈ Finset.range w, f ((n : ℤ)+1)) +
    ∑ n ∈ Finset.range w, f (-((n : ℤ)+1))

/-- Exact decomposition retaining all positive and negative omitted indices. -/
theorem split_lattice {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℤ → E) (hf : Summable f) (w : ℕ) :
    (∑' k : ℤ, f k) = window f w +
      (∑' n : ℕ, f (tailIndex false w n))+
      (∑' n : ℕ, f (tailIndex true w n)) := by
  have hp : Summable (fun n : ℕ => f (n : ℤ)) := hf.comp_injective Nat.cast_injective
  have hn : Summable (fun n : ℕ => f (-((n : ℤ)+1))) :=
    hf.comp_injective (fun a b h => by omega)
  have hp1 : Summable (fun n : ℕ => f ((n : ℤ)+1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => f (n : ℤ)) 1).mpr hp
  have hpt : Summable (fun n : ℕ => f (((n+w : ℕ) : ℤ)+1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => f ((n : ℤ)+1)) w).mpr hp1
  have hnt : Summable (fun n : ℕ => f (-(((n+w : ℕ) : ℤ)+1))) :=
    (summable_nat_add_iff (f := fun n : ℕ => f (-((n : ℤ)+1))) w).mpr hn
  have hpos : (fun n : ℕ => f (((n+w : ℕ) : ℤ)+1)) =
      fun n : ℕ => f (tailIndex false w n) := by
    funext n
    congr 1
    simp only [tailIndex, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    omega
  have hneg : (fun n : ℕ => f (-(((n+w : ℕ) : ℤ)+1))) =
      fun n : ℕ => f (tailIndex true w n) := by
    funext n
    congr 1
    simp only [tailIndex, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    omega
  have h0 : (∑' n : ℕ, f (n : ℤ)) = f 0 + ∑' n : ℕ, f ((n : ℤ)+1) := by
    simpa using tsum_eq_zero_add' (f := fun n : ℕ => f (n : ℤ))
      (by simpa using hp1)
  have h1 : (∑' n : ℕ, f ((n : ℤ)+1)) =
      (∑ n ∈ Finset.range w, f ((n : ℤ)+1)) +
        ∑' n : ℕ, f (tailIndex false w n) := by
    have h := Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => f ((n : ℤ)+1)) (k := w) hpt
    rw [hpos] at h
    exact h.symm
  have h2 : (∑' n : ℕ, f (-((n : ℤ)+1))) =
      (∑ n ∈ Finset.range w, f (-((n : ℤ)+1))) +
        ∑' n : ℕ, f (tailIndex true w n) := by
    have h := Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => f (-((n : ℤ)+1))) (k := w) hnt
    rw [hneg] at h
    exact h.symm
  rw [tsum_of_nat_of_neg_add_one hp hn, h0, h1, h2]
  simp only [window]
  abel

theorem window_sub {E : Type*} [AddCommGroup E] (f g : ℤ → E) (w : ℕ) :
    window (fun k => f k-g k) w=window f w-window g w := by
  simp only [window, Finset.sum_sub_distrib]
  abel

/-- The approximation budget depends on retained offsets, not axis length. -/
theorem window_norm {E : Type*} [NormedAddCommGroup E] (f : ℤ → E) (w : ℕ)
    (ε : ℝ) (hf : ∀ k : ℤ, k.natAbs≤w → ‖f k‖≤ε) :
    ‖window f w‖≤(2*(w : ℝ)+1)*ε := by
  have hp : ‖∑ n ∈ Finset.range w, f ((n : ℤ)+1)‖≤(w : ℝ)*ε := by
    calc _≤∑ n ∈ Finset.range w, ‖f ((n : ℤ)+1)‖ := norm_sum_le _ _
      _≤∑ n ∈ Finset.range w, ε := by
        apply Finset.sum_le_sum
        intro n hn
        apply hf
        have hn := Finset.mem_range.mp hn
        have hc : ((n : ℤ)+1).natAbs=n+1 := by
          rw [show (n : ℤ)+1=((n+1 : ℕ) : ℤ) by omega, Int.natAbs_natCast]
        omega
      _=(w : ℝ)*ε := by simp
  have hn : ‖∑ n ∈ Finset.range w, f (-((n : ℤ)+1))‖≤(w : ℝ)*ε := by
    calc _≤∑ n ∈ Finset.range w, ‖f (-((n : ℤ)+1))‖ := norm_sum_le _ _
      _≤∑ n ∈ Finset.range w, ε := by
        apply Finset.sum_le_sum
        intro n hn
        apply hf
        have hn := Finset.mem_range.mp hn
        have hc : (-((n : ℤ)+1)).natAbs=n+1 := by
          rw [Int.natAbs_neg, show (n : ℤ)+1=((n+1 : ℕ) : ℤ) by omega,
            Int.natAbs_natCast]
        omega
      _=(w : ℝ)*ε := by simp
  have hz := hf 0 (by simp)
  have htri := norm_add_le (f 0+∑ n ∈ Finset.range w, f ((n : ℤ)+1))
    (∑ n ∈ Finset.range w, f (-((n : ℤ)+1)))
  have htri0 := norm_add_le (f 0) (∑ n ∈ Finset.range w, f ((n : ℤ)+1))
  dsimp [window]
  linarith

variable (s t : ℕ) [NeZero s] [NeZero t]

/-- All retained offsets are wrapped, including when the band crosses the seam
or covers a residue more than once. -/
noncomputable def rounded (p u w : ℕ) (v : ZMod s → ℂ) (j : ZMod s) : ℂ :=
  window (fun k => (PhaseCellCrossCell.entry (2^15*p) s t u w
    (j.val : ℤ) (j.val+k) : ℂ)*v (j+k)) w

noncomputable def exactWindow (α : ℝ) (w : ℕ) (v : ZMod s → ℂ) (j : ZMod s) : ℂ :=
  window (fun k => (Real.exp (normExp s t α j.val k) : ℂ)*v (j+k)) w

/-- Identify the pre-existing normalized periodic operator with its complete
integer lattice series, so alias handling is inherited from that operator. -/
theorem normN_lattice (hst : s<t) (α : ℝ) (v : ZMod s → ℂ) (j : ZMod s) :
    normN s t α v j = ∑' k : ℤ,
      (Real.exp (normExp s t α j.val k) : ℂ)*v (j+k) := by
  unfold normN
  rw [squareT_apply s t hst]
  apply tsum_congr
  intro k
  unfold diagD dCoef normExp
  rw [beta_val_add, Real.exp_add]
  push_cast
  ring

/-- The finite exact periodic row loses only the two entire-lattice tails. -/
theorem exactWindow_error (hst : s<t) {α : ℝ} (hα : 0<α)
    (v : ZMod s → ℂ) (hv : ∀ k, ‖v k‖≤1) (j : ZMod s) (w : ℕ) :
    ‖normN s t α v j-exactWindow s t α w v j‖≤
      (∑' n : ℕ, Real.exp (normExp s t α j.val (tailIndex false w n)))+
      (∑' n : ℕ, Real.exp (normExp s t α j.val (tailIndex true w n))) := by
  let f : ℤ → ℂ := fun k => (Real.exp (normExp s t α j.val k) : ℂ)*v (j+k)
  have hf : Summable f := summable_normN_term s t hα v j
  have hscalar : Summable (fun k : ℤ => Real.exp (normExp s t α j.val k)) := by
    simpa only [mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using
      (summable_normN_term s t hα (fun _ => 1) j).norm
  have ht (b : Bool) : ‖∑' n : ℕ, f (tailIndex b w n)‖≤
      ∑' n : ℕ, Real.exp (normExp s t α j.val (tailIndex b w n)) := by
    have hi : Function.Injective (tailIndex b w) := by
      intro a c h
      cases b <;> simp only [tailIndex, ↓reduceIte] at h <;> omega
    have hfn := hf.norm.comp_injective hi
    calc _≤∑' n : ℕ, ‖f (tailIndex b w n)‖ := norm_tsum_le_tsum_norm hfn
      _≤_ := hfn.tsum_le_tsum (fun n => by
        dsimp [f]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (hv _))
        (hscalar.comp_injective hi)
  have heq : normN s t α v j-exactWindow s t α w v j =
      (∑' n : ℕ, f (tailIndex false w n))+
      (∑' n : ℕ, f (tailIndex true w n)) := by
    rw [normN_lattice s t hst α v j, split_lattice f hf w]
    change window f w + _ + _ - window f w = _
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (ht false) (ht true))

/-- Periodic truncation at the actual executable square-root band. -/
theorem selected_truncation (hst : s<t) {α : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 0<p) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (v : ZMod s → ℂ) (hv : ∀ k, ‖v k‖≤1) (j : ZMod s) :
    ‖normN s t α v j-exactWindow s t α (PhaseCellBand.width p u) v j‖≤
      1/(2 : ℝ)^(46*p) := by
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  exact (exactWindow_error s t hst hα v hv j _).trans
    (PhaseCellBand.tail_bound s t p u hs hst.le hp hu α hα hαu j.val)

/-- A uniform error budget for the actual corrected retained coefficients. -/
noncomputable def entryError (p : ℕ) : ℝ :=
  12*PhaseCellRounded.error (2^15*p)/((1/(2 : ℝ)^(8*p))/2)^2+
    4/(2 : ℝ)^(2^15*p)

omit [NeZero t] in
/-- Wrapping the retained rational entries accumulates aliases while keeping
rounding error proportional to the band cardinality. -/
theorem rounded_error (hst : s<t) {α d : ℝ} (p u w : ℕ) (hp : 0<p)
    (hu : α^2=(u : ℝ)) (htheta : 0<(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (v : ZMod s → ℂ) (hv : ∀ k, ‖v k‖≤1) (j : ZMod s) :
    ‖rounded s t p u w v j-exactWindow s t α w v j‖≤
      (2*(w : ℝ)+1)*entryError p := by
  unfold rounded exactWindow
  rw [←window_sub]
  apply window_norm
  intro k hk
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  have h := PhaseCellCrossCell.selected_entry_error (j := (j.val : ℤ))
    (k := j.val+k) hp hs hst hu htheta hgap hbudget
    (by simpa only [add_sub_cancel_left, entryError] using hk)
  have hc : ‖(PhaseCellCrossCell.entry (2^15*p) s t u w (j.val : ℤ) (j.val+k) : ℂ)-
      (Real.exp (normExp s t α j.val k) : ℂ)‖≤entryError p := by
    rw [show (PhaseCellCrossCell.entry (2^15*p) s t u w (j.val : ℤ) (j.val+k) : ℂ)-
        (Real.exp (normExp s t α j.val k) : ℂ) =
        (((PhaseCellCrossCell.entry (2^15*p) s t u w (j.val : ℤ) (j.val+k) : ℝ)-
          Real.exp (normExp s t α j.val k) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    simpa only [add_sub_cancel_left, entryError] using h
  rw [←sub_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans
    (mul_le_of_le_one_right (by unfold entryError PhaseCellRounded.error; positivity) (hv _))

/-- Complete selected row error against the existing periodic operator. -/
theorem selected_row_error (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 0<p) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (htheta : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1))
    (hbudget : α^2*d≤p) (v : ZMod s → ℂ) (hv : ∀ k, ‖v k‖≤1) (j : ZMod s) :
    ‖normN s t α v j-rounded s t p u (PhaseCellBand.width p u) v j‖≤
      1/(2 : ℝ)^(46*p)+(2*(PhaseCellBand.width p u : ℝ)+1)*entryError p := by
  have htrunc := selected_truncation s t hst hα p u hp hu hαu v hv j
  have hround := rounded_error s t hst p u (PhaseCellBand.width p u) hp hαu
    htheta hgap hbudget v hv j
  calc _≤‖normN s t α v j-exactWindow s t α (PhaseCellBand.width p u) v j‖+
      ‖exactWindow s t α (PhaseCellBand.width p u) v j-
        rounded s t p u (PhaseCellBand.width p u) v j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤_ := by rw [norm_sub_rev (exactWindow _ _ _ _ _ _)]; exact add_le_add htrunc hround

end IntegerMultBounds.NLogN.PhaseCellRow
