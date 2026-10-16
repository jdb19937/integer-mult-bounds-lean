module

public import IntegerMultBounds.MathlibTM2.Fast.BandMath
public import IntegerMultBounds.MathlibTM2.Mult.SourceErrScaled
public import IntegerMultBounds.MathlibTM2.Mult.FastB0Sizes

/-!
# The numeric pipeline with the banded `B̃₀`

The pipeline of `Mult/Pipeline.lean` with the line map `bandA n` in place of `lineB n`. The band
line approximates `2^-j ℬ₀` (`j = α²`), so the per-line exponent of the source factorization is
`cB n = 2⌈α²⌉ + 2 + α²` and `γ = d · cB n` (`band_factorization`). Under the small-gap conditions
`8p ≤ 2^(α²)`, `α² d ≤ p` and the margins at `γ = d · cB n`, the pipeline multiplies
(`pipelineB_correct`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.NLogN ContinuousLinearMap
open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.SourceErr
open IntegerMultBounds.Resampling.WindowSum (termW)
open IntegerMultBounds.Resampling.TabledMaps (tol_of_int approxMap_resampANumW)

noncomputable section

section Generic

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- **The factorization with a scaled `ℬ₀`.** With a left inverse `J` of `1 + E`, the line
operators `resampA` and `2^-j ℬ₀ J` factor `P_s F_s` with exponent `2⌈α²⌉ + 2 + j`; the tabled
`Ã` approximates `resampA` within `p²` and keeps the unit ball. -/
theorem band_factorization (hst : s < t) (hcop : Nat.Coprime s t) (hα : 2 ≤ α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (j : ℕ) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p)
    (WA : ZMod t → ℤ → ℤ) (hWA : ∀ k j, |(WA k j : ℝ) - 2 ^ p * resampWeight s t α k j| ≤ 2) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ), J ∘L (1 + offDiagCLM s t α) = 1 ∧
      permSCLM t ∘L dftCLM s = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2 + j)) •
        ((((2 : ℂ) ^ j)⁻¹ • resampB₀ s t α J) ∘L permTCLM s ∘L dftCLM t ∘L resampA s t α) ∧
      ‖resampA s t α‖ ≤ 1 ∧ ‖((2 : ℂ) ^ j)⁻¹ • resampB₀ s t α J‖ ≤ 1 ∧
      ApproxMap p (resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p)) (resampA s t α)
        ((p : ℝ) ^ 2) ∧
      ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 →
        ‖resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u‖ ≤ 1 := by
  have hα0 : (0 : ℝ) < α := by linarith
  obtain ⟨J, hJ, -, hJn⟩ := exists_left_inverse hst hα0 hθ
  obtain ⟨heq, hA, -⟩ := resampling_factorization_explicit hst hcop (by linarith) hθ J hJ
  have hAx := approxMap_resampANumW (s := s) (t := t) (by linarith) hαp hm hm1 _
    (fun k j => tol_of_int p _ _ (hWA k j))
  have hεA : errA m < (p : ℝ) ^ 2 := errA_lt_sq' hmp (by omega)
  have hpow : (4 : ℝ) * (p : ℝ) ^ 2 ≤ 2 ^ p := by exact_mod_cast four_sq_le_pow p hp
  have h4 : 4 * errA m ≤ 2 ^ p := by linarith
  have hA34 := opNorm_resampA_le_three_quarters (s := s) (t := t) hα
  have hBn := opNorm_resampB₀_le (s := s) (t := t) (α := α) J hJn
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  refine ⟨J, hJ, ?_, hA, ?_, fun v hv => (hAx v hv).trans hεA.le,
    fun u hu => ball_of_approx hA34 hAx h4 u hu⟩
  · rw [resampB_eq hcop J] at heq
    rw [← permSEquiv_coe hcop, heq]
    have e : ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2 + j)) * ((2 : ℂ) ^ j)⁻¹ = (2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2) := by
      rw [pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), mul_one]
    rw [smul_comp, smul_smul, e]
    ext u i
    simp only [comp_apply, smul_apply, map_smul, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  · rw [norm_smul, norm_inv, norm_pow, RCLike.norm_two]
    calc ((2 : ℝ) ^ j)⁻¹ * ‖resampB₀ s t α J‖ ≤ 1 * 1 :=
          mul_le_mul (inv_le_one_of_one_le₀ h2j) hBn (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

end Generic

/-! ### The pipeline -/

/-- The per-line exponent with the banded `B̃₀`. -/
def cB (n : ℕ) : ℕ := 2 * ⌈((alpha n : ℝ)) ^ 2⌉₊ + 2 + alpha n * alpha n

/-- The computed source transform with the banded `B̃₀`. -/
def srcMapB (n : ℕ) : (ZMod (∏ i, s n i) → ℂ) → (((i : Fin (d n)) → ZMod (s n i)) → ℂ) :=
  crtSourceApprox (s_pairwise n) (p n) (d n * cB n) (lineA n) (bandA n) (chirpKernel n) (convBox n)

/-- The computed opposite transform with the banded `B̃₀`. -/
def oppMapB (n : ℕ) : (((i : Fin (d n)) → ZMod (s n i)) → ℂ) → (ZMod (∏ i, s n i) → ℂ) :=
  crtOppApprox (s_pairwise n) (p n) (d n * cB n) (lineA n) (bandA n) (chirpKernel n) (convBox n)

/-- The coefficients of `x y` computed with the banded `B̃₀`. -/
def pipelineCoeffsB (n x y : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (∏ i, s n i) =>
    (round (((2 : ℂ) ^ (2 * b n) * ((∏ i, s n i : ℕ) : ℂ)) *
      ExactRecovery.computedConv (p := p n) (k := b n) (srcMapB n) (oppMapB n) (bitsMSB n x)
        (bitsMSB n y) (i.val : ZMod (∏ i, s n i))).re).toNat

variable {n : ℕ}

/-- **Correctness of the pipeline with the banded `B̃₀`.** -/
theorem pipelineB_correct (h : Big n) (hwidth : 8 * p n ≤ 2 ^ (alpha n ^ 2))
    (hbudget : ((alpha n : ℝ)) ^ 2 * (d n : ℝ) ≤ p n)
    (hsmall : 2 * d n * p n ^ 2 ≤ T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ (d n * cB n) * T n * logT n ≤ 2 ^ p n / 100)
    (hfinal : (2 : ℝ) ^ (2 * b n + 4) * S n ^ 2 * (3 * (9 * (2 : ℝ) ^ (d n * cB n) * T n * logT n) + 2)
      < 2 ^ p n / 2)
    (x y : ℕ) (hx : Nat.size x ≤ n) (hy : Nat.size y ≤ n) :
    evalBase (2 ^ b n) (pipelineCoeffsB n x y) = x * y := by
  have hg := h.good
  have hd1 := h.one_le_d
  have hpT : ∏ i, t n i = T n := prod_t hd1
  have hα2 : 2 ≤ alpha n := two_le_alpha h.1
  have hαR : (2 : ℝ) ≤ alpha n := by exact_mod_cast hα2
  have hαp : alpha n ^ 2 ≤ p n := h.alpha_sq_le_p
  have hαpR : ((alpha n : ℝ)) ^ 2 ≤ p n := by exact_mod_cast hαp
  have hp13 := h.thirteen_le_p
  obtain ⟨hm, hm1, hmp⟩ := windowA_spec (alpha_sq_lt_p h)
  have hi0 : 0 < d n := by omega
  choose J hJ hfac hAn hBn hA' hA'1 using fun i =>
    band_factorization (hg.lt i) (hg.coprime i) hαR (h.one_le_alpha_sq_theta i)
      (alpha n * alpha n) hαpR hm hm1 hmp hp13
      (IntegerMultBounds.Resampling.WeightTable.tableA (s n i) (t n i) (alpha n) (p n))
      (IntegerMultBounds.Resampling.WeightTable.tables_ok (s n i) (t n i) (alpha n) (p n)
        (hg.lt i) hp13 hα2 hαp).1
  have hexact : ∀ i, PhaseCellOperator.exact (s n i) (t n i) (alpha n : ℝ) =
      1 + offDiagCLM (s n i) (t n i) (alpha n : ℝ) := fun i => normN_clm _ _ _
  have hB' := fun i => (band_axis_full h hwidth hbudget i).2 (J i) (by rw [hexact]; exact hJ i)
  have hB'1 := fun i => (band_axis_math h hwidth hbudget i).ball
  have hsm : 2 * d n * p n ^ 2 ≤ (∏ i, t n i) * logT n := by rw [hpT]; exact hsmall
  have hEs' : 9 * (2 : ℝ) ^ (d n * cB n) * ((∏ i, t n i : ℕ) : ℝ) * logT n ≤ 2 ^ p n / 100 := by
    rw [hpT]; exact hEs
  have hEsγ : 9 * (2 : ℝ) ^ gamma n * T n * logT n ≤ 2 ^ p n / 100 := by
    refine le_trans ?_ hEs
    have hle : gamma n ≤ d n * cB n := by
      rw [gamma_eq_ceil]; unfold cB; exact Nat.mul_le_mul_left _ (by omega)
    have : (2 : ℝ) ^ gamma n ≤ 2 ^ (d n * cB n) := pow_le_pow_right₀ (by norm_num) hle
    have h0 : (0 : ℝ) ≤ T n * logT n := by positivity
    nlinarith
  have hres := sourceErr_of_componentsC (s := s n) (t := t n) h.two_dvd_t
    (fun i => resampA (s n i) (t n i) (alpha n : ℝ))
    (fun i => ((2 : ℂ) ^ (alpha n * alpha n))⁻¹ • resampB₀ (s n i) (t n i) (alpha n : ℝ) (J i))
    hfac hAn hBn hA' hA'1 hB' hB'1 (Chirp.chirpProd_ha'_explicit (t n) (s n) (p n))
    (convBox_spec h hsmall hEsγ) hi0 (by omega) hsm hEs'
  rw [hpT] at hres
  obtain ⟨hF, hG⟩ := hres
  have hk : 0 < b n := one_le_b h.1
  have hS := h.digits_length_le (length_bitsMSB n x) (length_bitsMSB n y)
  have key := exact_product_crt (s n) (t n) (s_pairwise n) hg.coprime (srcMapB n) (oppMapB n) hk
    hS (crtSource_err (s_pairwise n) hF) (crtOpp_err (s_pairwise n) hG) hEs hfinal
  rw [binaryValue_bitsMSB_of_size hx, binaryValue_bitsMSB_of_size hy] at key
  exact key

end

end IntegerMultBounds.MathlibTM2.Fast
