module

public import IntegerMultBounds.NLogN.ResamplingPermuted
public import IntegerMultBounds.NLogN.PhaseCellSharpInverse

/-! The permutation-left factorization in the small-gap regime. Without the
old condition `α²θ ≥ 1`, the exact inverse of `N` can have norm up to `4p`;
the source therefore normalizes `B₀` by an extra `2^j` with `2p ≤ 2^j`. This
gives `P_s F_s = 2^(2⌈α²⌉+2+j) B₀' P_t F_t A` with contractions `A` and
`B₀' = B₀ / 2^j`, the form consumed by the pipeline's source-error theorem
with `γ = d (2⌈α²⌉+2+j)`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN

open ContinuousLinearMap

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

theorem smallgap_factorization (hst : s<t) (hcop : Nat.Coprime s t) (hα : 1≤α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1) (j : ℕ) (hj : 2*(p : ℝ)≤2^j) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ), J ∘L (1+offDiagCLM s t α)=1 ∧
      permSCLM t ∘L dftCLM s = ((2 : ℂ)^(2*⌈α^2⌉₊+2+j)) •
        ((((2 : ℂ)^j)⁻¹ • resampB₀ s t α J) ∘L permTCLM s ∘L dftCLM t ∘L resampA s t α) ∧
      ‖resampA s t α‖≤1 ∧ ‖((2 : ℂ)^j)⁻¹ • resampB₀ s t α J‖≤1 := by
  have hα0 : 0<α := by linarith
  obtain ⟨J, hJN, -, hJn⟩ :=
    PhaseCellDominance.selected_exact_inverse s t hst hα0 p u hp hwidth hαu hθ
  have hJ : J ∘L (1+offDiagCLM s t α)=1 := by
    rw [←normN_clm s t α]
    exact hJN
  -- Exact identity from the abstract assembly, without any norm hypothesis on `E`.
  have hres := resampling_identity_clm (s := s) (t := t) hα0
  rw [←permSEquiv_coe hcop] at hres
  have hFs := assemble_explicit (dftCLM s) (dftCLM t) (resampSCLM s t α) (resampTCLM s t α)
    (permSEquiv hcop) (permTCLM s) (rowSelectCLM s t) (diagDCLM s t α) (diagDInvCLM s t α)
    (offDiagCLM s t α) J hres (normN_clm s t α) hJ (diagDCLM_comp_inv s t α)
  have heq : dftCLM s=((2 : ℂ)^(2*⌈α^2⌉₊+2)) •
      (resampB s t α hcop J ∘L dftCLM t ∘L resampA s t α) := by
    have hc : (2 : ℂ)^(2*⌈α^2⌉₊+2)*(2⁻¹*((2 : ℂ)^(2*⌈α^2⌉₊+1))⁻¹)=1 := by
      rw [pow_succ, pow_succ]
      field_simp
    rw [hFs]
    ext x i
    simp only [resampB, resampA, smul_apply, comp_apply, map_smul, smul_smul, hc, one_smul]
  refine ⟨J, hJ, ?_, ?_, ?_⟩
  · rw [resampB_eq hcop J] at heq
    rw [←permSEquiv_coe hcop, heq]
    ext x i
    simp only [comp_apply, smul_apply, map_smul, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, smul_smul]
    rw [pow_add (2 : ℂ) (2*⌈α^2⌉₊+2) j, pow_add (2 : ℂ) (2*⌈α^2⌉₊) 2]
    field_simp
  · unfold resampA
    rw [norm_smul, norm_inv, RCLike.norm_two]
    calc 2⁻¹*‖resampSCLM s t α‖≤2⁻¹*2 := by
          gcongr
          exact opNorm_resampSCLM_le_two s t hα
      _=1 := by norm_num
  · unfold resampB₀
    have hD := opNorm_diagDCLM_le_pow s t α
    have hC := opNorm_rowSelectCLM_le s t
    have hcomp : ‖diagDCLM s t α ∘L J ∘L rowSelectCLM s t‖≤(2 : ℝ)^(2*⌈α^2⌉₊)*(4*p) := by
      calc ‖diagDCLM s t α ∘L J ∘L rowSelectCLM s t‖
          ≤‖diagDCLM s t α‖*(‖J‖*‖rowSelectCLM s t‖) :=
            (opNorm_comp_le _ _).trans (by gcongr; exact opNorm_comp_le _ _)
        _≤(2 : ℝ)^(2*⌈α^2⌉₊)*(4*p*1) := by gcongr
        _=_ := by ring
    rw [smul_smul, norm_smul, ←mul_inv, norm_inv, norm_mul, norm_pow, norm_pow,
      RCLike.norm_two]
    calc ((2 : ℝ)^j*2^(2*⌈α^2⌉₊+1))⁻¹*‖diagDCLM s t α ∘L J ∘L rowSelectCLM s t‖
        ≤((2 : ℝ)^j*2^(2*⌈α^2⌉₊+1))⁻¹*((2 : ℝ)^(2*⌈α^2⌉₊)*(4*p)) := by gcongr
      _=(2*p)/2^j := by
          rw [pow_succ]
          field_simp
          ring
      _≤1 := by
          rw [div_le_one (by positivity)]
          exact hj

end IntegerMultBounds.NLogN
