module

import IntegerMultBounds.NLogN.PhaseCellRowBudget
import IntegerMultBounds.NLogN.InversePerturbation
public import IntegerMultBounds.NLogN.PhaseCellRow
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! The actual corrected periodic row as a continuous linear map, with its
operator error and quantitative inverse transfer. Sharp exact inverse bounds
and structured execution remain separate obligations. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellOperator

open ContinuousLinearMap
variable (s t : ℕ) [NeZero s] [NeZero t]

/-- The pre-existing exact normalized resampling operator. -/
noncomputable def exact (α : ℝ) : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  rowSelectCLM s t ∘L resampTCLM s t α ∘L diagDCLM s t α

/-- Each retained lattice incidence contributes its own wrapped projection. -/
noncomputable def rounded (p u : ℕ) : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  pi fun j => PhaseCellRow.window (fun k =>
    (PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u)
      (j.val : ℤ) (j.val+k) : ℂ) • proj (j+k)) (PhaseCellBand.width p u)

theorem exact_apply {α : ℝ} (hα : 0<α) (v : ZMod s → ℂ) :
    exact s t α v=normN s t α v := by
  simp only [exact, comp_apply, rowSelectCLM_apply, resampTCLM_apply hα, diagDCLM_apply]
  rfl

omit [NeZero t] in
theorem rounded_apply (p u : ℕ) (v : ZMod s → ℂ) :
    rounded s t p u v=PhaseCellRow.rounded s t p u (PhaseCellBand.width p u) v := by
  funext j
  simp [rounded, PhaseCellRow.rounded, PhaseCellRow.window]

/-- The dimension-independent row estimate gives the actual operator norm. -/
theorem norm_error (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 0<p) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (htheta : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1))
    (hbudget : α^2*d≤p) :
    ‖rounded s t p u-exact s t α‖≤1/(2 : ℝ)^(45*p) := by
  apply opNorm_le_of_unit_norm (by positivity)
  intro v hv
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  simp only [sub_apply, Pi.sub_apply, rounded_apply, exact_apply s t hα]
  rw [norm_sub_rev]
  exact PhaseCellRow.selected_row_dyadic s t hst hα p u hp hu hαu htheta hgap hbudget
    v (fun k => (norm_le_pi_norm v k).trans hv.le) j

/-- Inverse stability now consumes the actual rounded operator and its proved
error, rather than an assumed matrix-approximation premise. -/
theorem inverse_transfer (hst : s<t) {α d M : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 0<p) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (htheta : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1))
    (hbudget : α^2*d≤p)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJN : J ∘L exact s t α=1) (hNJ : exact s t α ∘L J=1)
    (hJ : ‖J‖≤M) (hsmall : M/(2 : ℝ)^(45*p)≤1/2) :
    ∃ L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      L ∘L rounded s t p u=1 ∧ rounded s t p u ∘L L=1 ∧
      ‖L‖≤2*M ∧ ‖L-J‖≤2*M^2/(2 : ℝ)^(45*p) := by
  have herr := norm_error s t hst hα p u hp hu hαu htheta hgap hbudget
  simpa only [mul_one_div] using InversePerturbation.exists_inverse_of_half_gap
    (exact s t α) J (rounded s t p u) hJN hNJ hJ herr
      (by simpa only [mul_one_div] using hsmall)

/-- The selected dyadic precision absorbs even an exponential exact-inverse
bound; constructing that exact inverse remains an explicit obligation. -/
theorem selected_inverse (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 0<p) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (htheta : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1))
    (hbudget : α^2*d≤p)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJN : J ∘L exact s t α=1) (hNJ : exact s t α ∘L J=1)
    (hJ : ‖J‖≤(2 : ℝ)^(16*p)) :
    ∃ L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      L ∘L rounded s t p u=1 ∧ rounded s t p u ∘L L=1 ∧
      ‖L‖≤(2 : ℝ)^(16*p+1) ∧ ‖L-J‖≤1/(2 : ℝ)^(12*p) := by
  have hsmall : (2 : ℝ)^(16*p)/(2 : ℝ)^(45*p)≤1/2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    simp only [one_mul]
    calc (2 : ℝ)^(16*p)*2=(2 : ℝ)^(16*p+1) := (pow_succ _ _).symm
      _≤(2 : ℝ)^(45*p) := pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨L, hLH, hHL, hL, hdiff⟩ := inverse_transfer s t hst hα p u hp hu hαu
    htheta hgap hbudget J hJN hNJ hJ hsmall
  refine ⟨L, hLH, hHL, hL.trans ?_, hdiff.trans ?_⟩
  · rw [pow_succ]
    exact le_of_eq (mul_comm _ _)
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simp only [one_mul]
    calc 2*((2 : ℝ)^(16*p))^2*(2 : ℝ)^(12*p)=(2 : ℝ)^(44*p+1) := by
          rw [←pow_mul]
          rw [show 2*(2 : ℝ)^(16*p*2)=(2 : ℝ)^(16*p*2+1) by rw [pow_succ]; ring,
            ←pow_add]
          congr 1
          omega
      _≤(2 : ℝ)^(45*p) := pow_le_pow_right₀ (by norm_num) (by omega)

end IntegerMultBounds.NLogN.PhaseCellOperator
