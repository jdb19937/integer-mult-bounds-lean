module

public import IntegerMultBounds.Vendor.StrongPNT.PNT4_ZeroFreeRegion
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Algebra.Group.Basic
public import IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.ResidueCalcOnRectangles
public import IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.MellinCalculus
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Bound
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Tactic.FunProp
public import IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.Fourier
public import IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.ZetaBounds

@[expose] public section

namespace Erdos970

open _root_.Complex Topology _root_.Filter Interval _root_.Set Asymptotics
local notation (name := riemannzeta') "ζ" => riemannZeta
local notation (name := derivriemannzeta') "ζ'" => deriv riemannZeta

local notation "I" => Complex.I

lemma ZetaNoZerosOn1Line' (t : ℝ) : ζ (1 + t * I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp

lemma ZetaCont' : ContinuousOn ζ (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert differentiableAt_riemannZeta ?_
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx

lemma ZetaNoZerosInBox' (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra h
  push Not at h

  have hn (n : ℕ) := h (σ := 1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra hσn
    push Not at hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n + 1)) atTop (𝓝 1) := by
      simpa using! (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hσ'_ge hσ'_le

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by valid, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert hζ (subseq n) using 3
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      have hprod : Tendsto (fun s : ℂ => ‖(s - 1) * ζ s‖) (𝓝[≠] 1) (𝓝 1) := by
        simpa only [norm_one] using! riemannZeta_residue_one.norm
      have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] 1) (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hdist : Tendsto (fun s : ℂ => ‖s - 1‖) (𝓝[≠] 1) (𝓝 0) := by
        simpa only [sub_self, norm_zero] using! (hid.sub_const 1).norm
      filter_upwards [hprod.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
        hdist.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with s hp hs
      by_contra h
      have hlt : ‖ζ s‖ < 1 := lt_of_not_ge h
      have hm := mul_le_mul_of_nonneg_left hlt.le (norm_nonneg (s - 1))
      rw [norm_mul] at hp
      rw [mul_one] at hm
      linarith

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have hpoint : (1 + Complex.I * t₀ : ℂ) ≠ 1 := by
        intro heq
        have him := congrArg Complex.im heq
        have htzero : t₀ = 0 := by simpa using him
        exact ht₀ htzero
      have hcont := (differentiableAt_riemannZeta hpoint).continuousAt
      have hlim : Tendsto (fun n : ℕ => ζ (σ' (subseq n) + I * t (subseq n))) atTop
          (𝓝 (ζ (1 + I * t₀))) := by
        simpa only [Function.comp_def] using!
          hcont.tendsto.comp (ToOneT0.mono_right nhdsWithin_le_nhds)
      have hfun : (fun n : ℕ => ζ (σ' (subseq n) + I * t (subseq n))) = (fun _ => 0) :=
        funext this
      rw [hfun] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero

lemma LogDerivZetaHoloOn' {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, ζ s ≠ 0) :
    HolomorphicOn (fun s ↦ ζ' s / ζ s) S := by
  apply DifferentiableOn.div _ _ nonzero <;> intro s hs <;> apply DifferentiableAt.differentiableWithinAt
  · apply differentiableAt_deriv_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
  · apply differentiableAt_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one

theorem LogDerivZetaHolcSmallT' :
    ∃ (σ₂ : ℝ) (_ : σ₂ < 1), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂, hσ₂_lt_one, hζ_ne_zero⟩ := ZetaNoZerosInBox 3
  refine ⟨σ₂, hσ₂_lt_one, ?_⟩
  let U := ([[σ₂, 2]] ×ℂ [[-3, 3]]) \ {1}
  have s_in_U_im_le3 : ∀ s ∈ U, |s.im| ≤ 3 := by
    intro s hs
    rw [mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, him⟩
    simp only [Set.mem_preimage] at him
    obtain ⟨him_lower, him_upper⟩ := him
    apply abs_le.2
    simp at him_lower
    simp at him_upper
    constructor
    · exact him_lower
    · exact him_upper

  have s_in_U_re_ges2 : ∀ s ∈ U, σ₂ ≤ s.re := by
    intro s hs
    rw [mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, _him⟩
    simp only [Set.mem_preimage] at hre
    obtain ⟨hre_lower, hre_upper⟩ := hre
    have : min σ₂ 2 = σ₂ := by
      apply min_eq_left
      linarith [hσ₂_lt_one]
    rw[this] at hre_lower
    exact hre_lower

  apply LogDerivZetaHoloOn
  · exact notMem_sdiff_of_mem rfl
  · intro s hs
    rw[← re_add_im s]
    apply hζ_ne_zero
    apply s_in_U_im_le3 _ hs
    apply s_in_U_re_ges2 _ hs

theorem LogDerivZetaHolcLargeT' :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree_p
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox' 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ 1)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact notMem_sdiff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ 1 := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1

  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ 1 := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ 1 := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ 1)) / Real.log 3 ^ 1:= by
        gcongr
        apply min_le_right
      _ = _ := by field_simp; ring

end Erdos970
