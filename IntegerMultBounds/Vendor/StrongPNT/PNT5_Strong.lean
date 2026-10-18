module

public import IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.ZetaBounds
public import IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.ZetaConj
public import IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.SmoothExistence
public import Mathlib.Algebra.Group.Support
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import IntegerMultBounds.Vendor.StrongPNT.ZetaZeroFree

@[expose] public section

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

noncomputable abbrev MellinTransform : (ℝ → ℂ) → ℂ → ℂ := mellin

lemma MellinTransform_integral (f : ℝ → ℂ) (s : ℂ) :
    MellinTransform f s = ∫ x in Set.Ioi (0 : ℝ), f x * (x : ℂ) ^ (s - 1) := by
  simp only [MellinTransform, mellin, smul_eq_mul, mul_comm]

lemma MellinTransform_eq : MellinTransform = (mellin : (ℝ → ℂ) → ℂ → ℂ) := by
  rfl

noncomputable def MellinInverseTransform (F : ℂ → ℂ) (σ : ℝ) (x : ℝ) : ℂ :=
  VerticalIntegral' (fun s ↦ x ^ (-s) * F s) σ

lemma MellinInverseTransform_eq (σ : ℝ) (f : ℂ → ℂ) :
    MellinInverseTransform f σ = mellinInv σ f := by
  unfold mellinInv MellinInverseTransform VerticalIntegral' VerticalIntegral
  beta_reduce; ext x
  rw [← smul_assoc, smul_eq_mul (b := Complex.I), div_mul]; simp

theorem MellinInversion (σ : ℝ) {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) (hfx : ContinuousAt f x) :
    MellinInverseTransform (MellinTransform f) σ x = f x := by
  rw [MellinInverseTransform_eq, mellinInv_mellin_eq σ f hx hf hFf hfx]

local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

noncomputable def ChebyshevPsi (x : ℝ) : ℝ :=
  (Finset.range ⌊x + 1⌋₊).sum Λ

local notation "ψ" => ChebyshevPsi

theorem LogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = ∑' n, Λ n / (n : ℂ) ^ s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp
  · have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    dsimp [LSeriesSummable] at this
    convert! this using 1
    funext n
    by_cases h : n = 0 <;> simp [LSeries.term, h]

noncomputable abbrev SmoothedChebyshevIntegrand (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 ((Smooth1 SmoothingF ε) ·) s * (X : ℂ) ^ s

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate

lemma smoothedChebyshevIntegrand_conj {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    SmoothedChebyshevIntegrand SmoothingF ε X (conj s) = conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
  unfold SmoothedChebyshevIntegrand
  simp only [map_mul, map_div₀, map_neg]
  congr
  · exact deriv_riemannZeta_conj s
  · exact riemannZeta_conj s
  · simp_rw [MellinTransform_integral]

    rw[← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x xpos
    simp only [map_mul, Complex.conj_ofReal]
    congr
    nth_rw 1 [← map_one conj]
    rw[← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg xpos.le]
    exact Real.pi_ne_zero.symm
  · rw[Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm

open _root_.MeasureTheory

lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
  obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  apply Integrable.mono' (g := (fun t ↦ c / ε * 1 / (1 + t ^ 2)))
  · apply Integrable.const_mul integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
      SmoothingFpos mass_one (s := σ + x * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith) |>.continuousAt
    fun_prop
  · filter_upwards [] with t
    calc
      _≤ c / ε * 1 / (σ^2 + t^2) := by
        convert hc (σ / 2) (by linarith) (σ + t * I) (by simp only [add_re, ofReal_re, mul_re,
          I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, half_le_self_iff]; linarith)
          (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero]; linarith) ε εpos  ε_lt_one using 1
        simp only [mul_one, Complex.sq_norm, normSq_apply, add_re, ofReal_re, mul_re, I_re,
          mul_zero, ofReal_im, I_im, sub_self, add_zero, add_im, mul_im, zero_add, mul_inv_rev]
        ring_nf
      _ ≤ _ := by
        gcongr; nlinarith

attribute [fun_prop] Continuous.const_cpow

lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by

  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑a * I) := by
    apply continuousOn_univ.mp
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    . refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one hz).continuousAt
    . fun_prop
    . simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith

  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
                
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y:= σ) (x:= i) (by linarith)]
    norm_cast

  rw [MeasureTheory.integral_tsum]
  have x_neq_zero : X ≠ 0 := by linarith
  . intro i
    by_cases i_eq_zero : i = 0
    . simpa [i_eq_zero] using aestronglyMeasurable_const
    . apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  . rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal, Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnnorm_real, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp), ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top ?_ ENNReal.coe_lt_top

    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

    rw [ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top
    . rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
        (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp[h]
    . simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one: ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos: 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
  dsimp [SmoothedChebyshev, SmoothedChebyshevIntegrand, VerticalIntegral', VerticalIntegral]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt (by linarith : 0 < X)]
    linarith [Real.exp_one_lt_d9]
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by
      simp only [inv_pos]
      linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LogDerivativeDirichlet]
    · rw [← tsum_mul_right, ← tsum_mul_right]
    · simp [σ_gt]
  · congr
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0; simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + t * I) ?_ ?_
    push_cast at this ⊢
    rw [mul_comm I (↑t : ℂ)]
    rw [← this, div_mul_cancel₀]
    · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
    · apply div_nonneg (by linarith : 0 ≤ X); simp
    · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, not_and, not_not]
      intro hn; exfalso; exact n_ne_zero hn
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    congr 1
    funext n

    simp_rw [ht, h, hn]
  · push_cast
    congr
    ext n
    by_cases n_zero : n = 0; simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    rw [(by rw [div_mul]; simp : 1 / (2 * π) = 1 / (2 * π * I) * I), mul_assoc]
    conv => lhs; rhs; rhs; rhs; intro t; rw [mul_comm]; norm_cast
    have := MellinInversion σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [MellinInverseTransform, VerticalIntegral] at this
      rw [this]
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
        εpos (by positivity)

theorem SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2) (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X) (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) → Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
  ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
        ↑((Finset.range ⌊X + 1⌋₊).sum ⇑ArithmeticFunction.vonMangoldt)‖ ≤
    C * ε * X * Real.log X := by
  norm_cast

  let F := Smooth1 SmoothingF ε

  let n₀ := ⌈X * (1 - c₁ * ε)⌉₊

  have n₀_pos : 0 < n₀ := by
    simp only [Nat.ceil_pos, n₀]
    subst C_eq
    simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos]
    exact (mul_le_of_le_one_right c₁_pos.le ε_lt_one.le).trans_lt c₁_lt

  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    apply sub_le_self
    positivity

  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    apply le_of_lt
    exact Nat.ceil_lt_add_one (by bound)

  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))

  have sumΛ : Summable (fun (n : ℕ) ↦ Λ n * F (n / X)) := by
    exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    (hc₂ _ _ (by trivial) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
    (s ∘ Finset.mem_range.2))))))

  have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ Λ (n + n₀) * F ((n + n₀) / X)) := by exact_mod_cast sumΛ.comp_injective fun Q=>by valid

  rw[← Summable.sum_add_tsum_nat_add' (k := n₀) (mod_cast sumΛn₀ n₀)]

  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊

  have n₁_pos : 0 < n₁ := by
      dsimp only [n₁]
      apply Nat.le_floor
      rw[Nat.succ_eq_add_one, zero_add]
      norm_cast
      apply one_le_mul_of_one_le_of_one_le (by linarith)
      apply le_add_of_nonneg_right
      positivity

  have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))

  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)

  have n₁_ge_n₀ : n₀ ≤ n₁ := by
    have hn : (n₀ : ℝ) ≤ (n₁ : ℝ) := by linarith
    exact_mod_cast hn

  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
    calc
      (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                        exact sub_le_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
       _            = X * ε * (c₂ + c₁) := by ring

  have : (∑' (n : ℕ), Λ (n + n₀ : ) * F ((n + n₀ : ) / X)) =
    (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((n + n₀) / X)) +
    (∑' (n : ℕ), Λ (n + n₁ : ) * F ((n + n₁ : ) / X)) := by
    rw[← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)]
    congr! 5
    · simp only [Nat.cast_add]
    · omega
    · congr! 1
      norm_cast
      omega
    · convert sumΛn₀ ((n₁ - n₀) + n₀) using 4
      · omega
      · congr! 1
        norm_cast
        omega

  rw [this]
  clear this

  have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) := by
    have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) + (∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X)) := by
      let fTemp := fun n ↦ Λ (n + n₁) * F ((↑n + ↑n₁) / X)
      have sum_fTemp : Summable fTemp := by exact sumΛn₀ n₁
      have hTemp (n : ℕ): fTemp n = Λ (n + n₁) * F (↑(n + n₁) / X) := by rw[Nat.cast_add]
      have : ∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X) = ∑' (n : ℕ), fTemp n := by exact Eq.symm (tsum_congr hTemp)
      rw[this]
      have (n : ℕ): fTemp (n + 1) = Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X) := by exact hTemp (n + 1)
      have : ∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X) = ∑' (n : ℕ), fTemp (n + 1) := by exact Eq.symm (tsum_congr this)
      rw[this]
      have : Λ n₁ * F (↑n₁ / X) = fTemp 0 := by
        dsimp only [fTemp]
        rw[← Nat.cast_add, zero_add]
      rw[this]
      exact Summable.tsum_eq_zero_add (sumΛn₀ n₁)
    rw[this]
    apply add_eq_left.mpr
    convert tsum_zero with n
    have : n₁ ≤ n + (n₁) := by exact Nat.le_add_left (n₁) n
    convert mul_zero _
    convert smoothIs0 (n + 1 + n₁) ?_
    rw[← mul_le_mul_iff_left₀ X_pos]
    have : ↑(n + 1 + n₁) / X * X = ↑(n + 1 + n₁) := by field_simp
    rw[this]
    have : (1 + c₂ * ε) * X = 1 + (X * (1 + c₂ * ε) - 1) := by ring
    rw[this, Nat.cast_add, Nat.cast_add]
    exact add_le_add (by bound) n₁_ge

  rw [this]
  clear this

  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one, Nat.cast_add, Nat.cast_one]
    have temp : X ≤ ↑⌈X⌉₊ := by exact Nat.le_ceil X
    have : (⌈X⌉₊ : ℝ) ≤ ↑⌊X⌋₊ + 1 := by exact_mod_cast Nat.ceil_le_floor_add_one X
    exact Preorder.le_trans X (↑⌈X⌉₊) (↑⌊X⌋₊ + 1) temp this
    positivity

  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := by exact Nat.floor_le (by positivity)

  have : ∑ x ∈ Finset.range ⌊X + 1⌋₊, Λ x =
      (∑ x ∈ Finset.range n₀, Λ x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + ↑n₀) := by
    simp only [add_comm _ n₀]
    rw [← Finset.sum_range_add, Nat.add_sub_of_le]
    dsimp only [n₀]
    refine Nat.ceil_le.mpr ?_
    exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X X_le_floor_add_one
  rw [this]
  clear this

  have : ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, Λ n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases n_zero : n = 0
    · rw [n_zero]
      simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert mul_one _
      convert smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      have : (n < ⌈X * (1 - c₁ * ε)⌉₊) → (n ≤ ⌊X * (1 - c₁ * ε)⌋₊) := by
        intro n_lt
        by_contra hcontra

        rw[not_le] at hcontra

        have temp1: (⌊X * (1 - c₁ * ε)⌋₊).succ.succ ≤ n.succ := by
          apply Nat.succ_le_succ
          exact Nat.succ_le_of_lt hcontra
        have : n.succ ≤ ⌈X * (1 - c₁ * ε)⌉₊ := by exact Nat.succ_le_of_lt hn
        have temp2: ⌊X * (1 - c₁ * ε)⌋₊ + 2 = (⌊X * (1 - c₁ * ε)⌋₊ + 1) + 1 := by ring
        have : ⌊X * (1 - c₁ * ε)⌋₊ + 2 ≤ ⌈X * (1 - c₁ * ε)⌉₊ := by
          rw[temp2, ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one]
          exact Nat.le_trans temp1 hn
        rw[← and_not_self_iff (⌊X * (1 - c₁ * ε)⌋₊ + 2 ≤ ⌈X * (1 - c₁ * ε)⌉₊), not_le]
        apply And.intro
        exact this
        rw[temp2, ← Nat.succ_eq_add_one, Nat.lt_succ_iff]
        exact Nat.ceil_le_floor_add_one (X * (1 - c₁ * ε))
      exact (Nat.le_floor_iff' n_zero).mp (this hn)

  rw [this, sub_eq_add_neg, add_assoc, add_assoc]
  nth_rewrite 3 [add_comm]
  nth_rewrite 2 [← add_assoc]
  rw [← add_assoc, ← add_assoc, ← sub_eq_add_neg]
  clear this

  have :
    ∑ n ∈ Finset.range n₀, Λ n + (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X)) -
      (∑ x ∈ Finset.range n₀, Λ x + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀))
      =
      (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X)) -
      (∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀)) := by
    ring
  rw [this]
  clear this

  have :
    ‖∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X) - ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀) + Λ n₁ * F (↑n₁ / X)‖
    ≤
    (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
      ‖Λ n₁‖ * ‖F (↑n₁ / X)‖:= by
    apply norm_add_le_of_le
    apply norm_sub_le_of_le
    apply norm_sum_le_of_le
    intro b hb
    exact norm_mul_le_of_le (by rfl) (by rfl)
    apply norm_sum_le_of_le
    intro b hb
    rfl
    exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)

  refine this.trans ?_

  clear this

  have vonBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    intro n hn
    have n_add_n0_le_n1: (n : ℝ) + n₀ ≤ n₁ := by
      apply le_of_lt
      rw[Finset.mem_range] at hn
      rw[← add_lt_add_iff_right (-↑n₀), add_neg_cancel_right, add_comm, ← sub_eq_neg_add]
      exact_mod_cast hn
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
      apply ArithmeticFunction.vonMangoldt_nonneg
    have inter2: Real.log (↑n + ↑n₀) ≤ Real.log (↑n₁) := by exact_mod_cast Real.log_le_log (by positivity) n_add_n0_le_n1
    have inter3: Real.log (↑n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by exact Real.log_le_log (by bound) (by linarith)
    exact inter1.trans (inter2.trans inter3)

  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖
    ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by
    have : (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) = (∑ n ∈ Finset.range (n₁ - n₀), Real.log (X * (1 + c₂ * ε))) := by
      rw[← Nat.cast_sub]
      nth_rewrite 1 [← Finset.card_range (n₁ - n₀)]
      rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
      exact Eq.symm (Finset.sum_const (Real.log (X * (1 + c₂ * ε))))
      exact n₁_ge_n₀
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul (vonBnd1 _ hn) _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddAbove
    bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound

  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤ (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by
    have : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) = (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), Real.log (X + 1)) := by
      rw[← Nat.cast_sub]
      nth_rewrite 1 [← Finset.card_range (⌊X + 1⌋₊ - n₀)]
      rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
      exact Eq.symm (Finset.sum_const (Real.log (X + 1)))
      simp only [Nat.ceil_le, n₀]
      exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X X_le_floor_add_one
    rw[this]
    apply Finset.sum_le_sum
    intro n hn
    have n_add_n0_le_X_add_one: (n : ℝ) + n₀ ≤ X + 1 := by
      rw[Finset.mem_range] at hn
      rw[← add_le_add_iff_right (-↑n₀), add_assoc, ← sub_eq_add_neg, sub_self, add_zero, ← sub_eq_add_neg]
      have temp: (n : ℝ) < ⌊X + 1⌋₊ - n₀ := by
        rw[← Nat.cast_sub, Nat.cast_lt]
        exact hn
        simp only [Nat.ceil_le, n₀]
        exact le_trans n₀_inside_le_X X_le_floor_add_one
      have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
        apply sub_le_sub_right floor_X_add_one_le_self
      exact le_of_lt (lt_of_le_of_lt' this temp)
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
      apply ArithmeticFunction.vonMangoldt_nonneg
    apply le_trans inter1
    exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)

  have largeSumBound := add_le_add bnd1 bnd2

  clear vonBnd1 bnd1 bnd2

  have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
    apply Real.log_le_log (by positivity)
    have const_le_2: 1 + c₂ * ε ≤ 3 := by
      have : (3 : ℝ) = 1 + 2 := by ring
      rw[this]
      apply add_le_add_right
      rw[← mul_one 2]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw[mul_comm]
    exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)

  have inter2 : (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
    apply mul_le_mul n₁_sub_n₀ _ (log_nonneg (by linarith)) (by positivity)
    rw[← Real.log_mul (by positivity) (by positivity)]
    nth_rewrite 3 [mul_comm]
    exact inter1

  have inter3 : (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) ≤ 2 * (X * ε * (c₂ + c₁)) * (Real.log (X)) := by
    nth_rewrite 3 [mul_assoc]
    rw[two_mul, mul_add]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by linarith)

  have inter4 : (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) ≤ 2 * (X * ε * (c₁ + c₂)) * (Real.log (X)) := by
    nth_rewrite 2 [add_comm]
    exact le_trans inter2 inter3

  clear inter2 inter3

  have inter6 : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
    apply mul_le_mul _ _ (log_nonneg (by linarith)) (by positivity)
    have : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)) := by ring
    rw[this]
    apply sub_le_sub
    have : X + 1 ≤ X * (1 + ε * c₁) := by
      ring_nf
      rw[add_comm, add_le_add_iff_left]
      exact X_bound_1
    exact le_trans floor_X_add_one_le_self this
    nth_rewrite 2 [mul_comm]
    exact n₀_gt
    rw[← Real.log_mul (by positivity) (by norm_num), mul_comm]
    exact Real.log_le_log (by positivity) (by linarith)

  have inter7: 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) ≤ 4 * (X * ε * c₁) * Real.log (X) := by
    have : (4 : ℝ) = 2 + 2 := by ring
    rw[this, mul_add]
    nth_rewrite 5 [mul_assoc]
    rw[add_mul]
    apply add_le_add
    nth_rewrite 1 [mul_assoc]
    rfl
    nth_rewrite 1 [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left <| Real.log_le_log (by positivity) (by linarith)
    positivity

  have inter9: (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) + (↑⌊X + 1⌋₊ - ↑n₀) * Real.log (X + 1) ≤
    2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by
    have : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁) := by ring
    rw[this, add_mul]
    exact add_le_add inter4 <| le_trans inter6 inter7

  have largeSumBound2 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤
    2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by
    exact le_trans largeSumBound inter9

  clear largeSumBound inter4 inter9

  have inter2 : ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    rw[← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul _ _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact le_trans ArithmeticFunction.vonMangoldt_le_log <| Real.log_le_log (mod_cast n₁_pos) n₁_le
    rw[Real.norm_of_nonneg]
    apply smooth1BddAbove _ n₁_pos
    apply smooth1BddBelow _ n₁_pos

  have largeSumBound3 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by exact add_le_add largeSumBound2 (le_trans inter2 inter1)
  clear inter1 inter2 largeSumBound2

  have largeSumBound4 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (2 * Real.log X + Real.log (3)) := by
    nth_rewrite 2 [two_mul, add_assoc]
    rw [← Real.log_mul (by positivity) (by positivity), mul_comm X 3]
    apply le_trans largeSumBound3
    nth_rewrite 2 [mul_add]
    apply add_le_add_right
    nth_rewrite 1 [← one_mul (Real.log (3 * X))]
    apply mul_le_mul_of_nonneg_right _ (log_nonneg (by linarith))
    linarith

  clear largeSumBound3

  have largeSumBoundFinal : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ (6 * (X * ε * (3 * c₁ + c₂))) * Real.log (X) := by
    apply le_trans largeSumBound4
    rw[mul_add]
    have : (6 : ℝ) = 4 + 2 := by ring
    rw[this, add_mul, add_mul]
    apply add_le_add
    ring_nf
    rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by linarith)

  clear largeSumBound4

  rw[C_eq]
  linear_combination largeSumBoundFinal

theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ChebyshevPsi X‖ ≤ C * ε * X * Real.log X := by
  have vonManBnd (n : ℕ) : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log

  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one

  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF

  have c₁_lt : c₁ < 1 := by
    rw[c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)

  have c₂_lt : c₂ < 2 := by
    rw[c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    rfl
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    exact Real.log_nonneg (by norm_num)
    positivity

  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl

  clear_value C

  have Cpos : 0 < C := by
    rw [C_eq]
    positivity

  refine ⟨C, Cpos, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩
  unfold ChebyshevPsi

  have X_gt_zero : (0 : ℝ) < X := by linarith

  have X_ne_zero : X ≠ 0 := by linarith

  have n_on_X_pos {n : ℕ} (npos : 0 < n) :
      0 < n / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity

  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)

  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos

  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : n ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le

  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ n / X) :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le

  have ε_pos: ε > 0 := by linarith
  have X_pos: X > 0 := by linarith
  have X_gt_three : 3 < X := by linarith

  intro X_bound

  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw[c₁_eq, ← div_le_iff₀]
    have : 1 / Real.log 2 < 2 := by
      nth_rewrite 2 [← one_div_one_div 2]
      rw[one_div_lt_one_div]
      exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
      exact Real.log_pos (by norm_num)
      norm_num
    apply le_of_lt
    exact gt_trans X_bound this
    exact Real.log_pos (by norm_num)

  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw[c₂_eq, ← div_le_iff₀]
    have : 1 / (2 * Real.log 2) < 2 := by
      nth_rewrite 3 [← one_div_one_div 2]
      rw[one_div_lt_one_div, ← one_mul (1 / 2)]
      apply mul_lt_mul
      norm_num
      apply le_of_lt
      exact lt_trans (by norm_num) (Real.log_two_gt_d9)
      all_goals norm_num
      exact Real.log_pos (by norm_num)

    apply le_of_lt
    exact gt_trans X_bound this
    norm_num
    exact Real.log_pos (by norm_num)

  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF
    mass_one (by linarith) εpos ε_lt_one]

  convert SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε ε_pos ε_lt_one
    X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow smoothIs1 smoothIs0

@[inline] noncomputable def sigma1Of (A T : ℝ) : ℝ := 1 - A / Real.log T

noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-3)..3,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

theorem realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  apply ContinuousAt.comp _ (by fun_prop)
  convert hf.continuousAt
  simp

theorem riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (t : ℝ) :
  ∃ c > 0, ‖ζ (σ₀ + t * I)‖ ≤ c :=
  by
    let s := σ₀ + t * I
    let s_re : ℂ  := σ₀

    have H : s.re = σ₀ := by
          rw [add_re, ofReal_re, mul_re, ofReal_re, I_re, I_im]
          simp

    have non_neg : σ₀ ≠ 0 := by
      by_contra h
      rw [h] at σ₀_gt
      norm_cast at σ₀_gt

    have pos : s.re > 1 := by exact lt_of_lt_of_eq σ₀_gt (id (Eq.symm H))
    have pos_triv : s_re.re > 1 := by exact σ₀_gt

    have series := LSeries_one_eq_riemannZeta pos
    rw [← series]

    have identity : ∀(n : ℕ), ‖LSeries.term 1 s n‖ = 1 / n^σ₀ := by
      unfold LSeries.term
      intro n
      by_cases h0 : n = 0
      · simp [*]
      · simp [*]
        push Not at h0
        have C : n > 0 := by exact Nat.zero_lt_of_ne_zero h0
        have T :=  Complex.norm_natCast_cpow_of_pos C s
        rw [H] at T
        exact T

    have summable : Summable (fun (n : ℕ) ↦  ‖LSeries.term 1 s n‖) := by
      simp [identity]
      exact σ₀_gt

    have B := calc
      ‖∑' (n : ℕ), LSeries.term 1 s n‖ ≤ ∑' (n : ℕ), ‖LSeries.term 1 s n‖ := norm_tsum_le_tsum_norm summable
      _                                ≤ ∑' (n : ℕ), (1 / ↑n^σ₀) := by simp [← identity]
      _                                ≤ norm (∑' (n : ℕ), (1 / ↑n^σ₀) : ℝ ) := by exact le_norm_self (∑' (n : ℕ), 1 / ↑n ^ σ₀)
      _                                ≤ 1 + norm (∑' (n : ℕ), (1 / ↑n^σ₀) : ℝ ) := by linarith

    let c : ℝ := 1 + norm (∑' (n : ℕ), (1 / ↑n^σ₀) : ℝ )

    have c_is_pos : c > 0 := by positivity
    use (1 + norm (∑' (n : ℕ), (1 / ↑n^σ₀) : ℝ ))
    exact ⟨c_is_pos, B⟩

theorem summable_real_iff_summable_coe_complex (f : ℕ → ℝ) :
    Summable f ↔ Summable (fun n => (f n : ℂ)) := by
  constructor

  · intro ⟨s, hs⟩
    use (s : ℂ)
    exact hasSum_ofReal.mpr hs

  · intro ⟨s, hs⟩
    use s.re
    have h_re : HasSum (fun n => ((f n : ℂ)).re) s.re :=
      by exact hasSum_re hs
    simpa using! h_re

theorem cast_pow_eq (n : ℕ) (σ₀ : ℝ):
  (↑((↑n : ℝ) ^ σ₀) : ℂ )  = (↑n : ℂ) ^ (↑σ₀ : ℂ) := by
    have U : (↑n : ℝ) ≥ 0 := by exact Nat.cast_nonneg' n
    have endit := Complex.ofReal_cpow U σ₀
    exact endit

theorem strongPnt_summable_complex_then_summable_real_part (f : ℕ → ℂ) :
  Summable f → Summable (fun n ↦ (f n).re) := by
    intro ⟨s, hs⟩
    use s.re
    have h_re : HasSum (fun n => ((f n : ℂ)).re) s.re :=
      by exact hasSum_re hs
    convert h_re using 1

theorem strongPnt_dlog_riemannZeta_bdd_on_vertical_lines_generalized :
  ∀(σ₀ σ₁ : ℝ), ∀(t : ℝ), 1 < σ₀ → σ₀ ≤ σ₁ →
    ‖(- ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
  intro σ₀ σ₁ t σ₀_gt_one σ₀_lt_σ₁

  let s₁ := σ₁ + t * I
  have s₁_re_eq_sigma : s₁.re = σ₁ := by
    rw [Complex.add_re (σ₁) (t * I)]
    rw [Complex.ofReal_re σ₁]
    rw [Complex.mul_I_re]
    simp [*]

  have s₀_re_eq_sigma : (↑σ₀ : ℂ).re = σ₀ := by
    rw [Complex.ofReal_re σ₀]

  let s₀ := σ₀

  have σ₁_gt_one : 1 < σ₁ := by exact lt_of_le_of_lt' σ₀_lt_σ₁ σ₀_gt_one
  have s₀_gt_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt_one

  have s₁_re_geq_one : 1 < s₁.re := by exact lt_of_lt_of_eq σ₁_gt_one (id (Eq.symm s₁_re_eq_sigma))
  have s₁_re_coerce_geq_one : 1 < (↑s₁.re : ℂ).re := by exact s₁_re_geq_one
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₁_re_geq_one)]
  unfold LSeries

  have summable_von_mangoldt : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) s₁.re i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₁_re_geq_one

  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt σ₀_gt_one

  have summable_re_von_mangoldt : Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) s₁.re i).re) := by
    exact strongPnt_summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) s₁.re) summable_von_mangoldt

  have summable_re_von_mangoldt_at_σ₀ : Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i).re) := by
    exact strongPnt_summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) σ₀) summable_von_mangoldt_at_σ₀

  have positivity : ∀(n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ = (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by
    intro n
    calc
      ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ = Λ n / ‖(↑n : ℂ)^(s₁ : ℂ)‖ := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · push Not at h
          simp [*]

      _ = Λ n / (↑n)^s₁.re := by
        by_cases h : n = 0
        · simp [*]
        · rw [Complex.norm_natCast_cpow_of_pos]
          push Not at h
          exact Nat.zero_lt_of_ne_zero h

      _ = (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · simp [*]
          push Not at h
          ring_nf
          rw [Complex.re_ofReal_mul (Λ n)]
          ring_nf
          rw [Complex.inv_re]
          rw [Complex.cpow_ofReal_re]
          simp [*]
          left
          have N : (0 : ℝ) ≤ ↑n := by exact Nat.cast_nonneg' n
          have T2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).re = (↑n : ℝ)^σ₁ := by exact rfl
          have T1 : ((↑n : ℂ ) ^ (↑σ₁ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [T2]
            simp [*]
            exact Real.rpow_nonneg N σ₁

          simp [Complex.normSq_apply]
          simp [T1, T2]

  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ i‖) := by
    rw [summable_congr positivity]
    exact summable_re_von_mangoldt

  have triangle_ineq : ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), ↑‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ :=
    norm_tsum_le_tsum_norm summable_abs_value

  have bounded_by_sum_of_re : ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n).re :=
    by
      simp [positivity] at triangle_ineq
      exact triangle_ineq

  have sum_of_re_commutes : ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n).re = (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)).re :=
    (Complex.re_tsum (summable_von_mangoldt)).symm

  have re_of_sum_bdd_by_norm : (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)).re  ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)‖ :=
    Complex.re_le_norm (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n))

  have ineq_s₁_s₀ : ∀(n : ℕ),
    (LSeries.term (fun n ↦ Λ n) s₁.re n).re ≤ (LSeries.term (fun n ↦ Λ n) σ₀ n).re :=
  by
    intro n
    unfold LSeries.term
    by_cases h : n = 0
    · simp [*]
    · push Not at h
      simp [*]
      have H : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      ring_nf
      rw [Complex.re_ofReal_mul (Λ n) ((↑n : ℂ) ^ (↑σ₁ : ℂ))⁻¹]
      rw [Complex.re_ofReal_mul (Λ n) ((↑n : ℂ) ^ (↑σ₀ : ℂ))⁻¹]
      refine mul_le_mul_of_nonneg_left ?_ H
      · simp [Complex.inv_re]
        have R1 : ((↑n : ℂ) ^ (↑σ₀ : ℂ)).re = (↑n : ℝ) ^ σ₀ := rfl
        have R2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).re = (↑n : ℝ) ^ σ₁ := rfl
        have geq : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
        have geq_zero : 0 ≤ n := Nat.zero_le n
        have n_geq_one : (1 : ℝ) ≤ ↑n := by
          norm_cast
        have n_geq_pos : (0 : ℝ) ≤ ↑n := by
          norm_cast
        have n_gt_pos : (0 : ℝ) < (↑n) := by
          norm_cast

        have I1 : ((↑n : ℂ) ^ (↑σ₀ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [R1]
            simp [*]
            exact Real.rpow_nonneg n_geq_pos σ₀

        have I2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [R2]
            simp [*]
            exact Real.rpow_nonneg n_geq_pos σ₁

        simp [Complex.normSq_apply, R1, R2, I1, I2]
        have P1 : 0 < (↑n : ℝ)^σ₁ := Real.rpow_pos_of_pos n_gt_pos σ₁
        have P2 : 0 < (↑n : ℝ)^σ₀ := Real.rpow_pos_of_pos n_gt_pos σ₀

        have N : (↑n : ℝ)^σ₀ ≤ (↑n : ℝ)^σ₁ :=
          Real.rpow_le_rpow_of_exponent_le n_geq_one σ₀_lt_σ₁
        apply inv_anti₀
        · exact P2
        · exact N

  have Z :=
    by
      calc
        ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖
            := norm_tsum_le_tsum_norm summable_abs_value
      _ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by simp [←positivity]
      _ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n).re := by
          refine Summable.tsum_mono ?_ ?_ ineq_s₁_s₀
          · exact summable_re_von_mangoldt
          · exact summable_re_von_mangoldt_at_σ₀
      _ = (∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n)).re := (Complex.re_tsum (summable_von_mangoldt_at_σ₀)).symm
      _ ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n)‖ := re_le_norm (∑' (n : ℕ), LSeries.term (fun n ↦ ↑(Λ n)) σ₀ n)
      _ = ‖- ζ' (σ₀) / ζ (σ₀)‖ := by
          simp only [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₀_gt_one)]
          unfold LSeries
          rfl
      _ = ‖ζ' σ₀ / ζ σ₀‖ := by
        rw [← s₀_re_eq_sigma]
        simp [*]

  exact Z

theorem strongPnt_triv_bound_zeta :
  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ → ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C
  := by

      let ⟨U, ⟨U_in_nhds, zeta_residue_on_U⟩⟩ := riemannZetaLogDerivResidue

      let ⟨open_in_U, ⟨open_in_U_subs_U, open_in_U_is_open, one_in_open_U⟩⟩ := mem_nhds_iff.mp U_in_nhds

      let ⟨ε₀, ⟨ε_pos, metric_ball_around_1_is_in_U'⟩⟩ := EMetric.isOpen_iff.mp open_in_U_is_open (1 : ℂ) one_in_open_U

      let ε := if ε₀ = ⊤ then ENNReal.ofReal 1 else ε₀
      have O1 : ε ≠ ⊤ := by
        by_cases h : ε₀ = ⊤
        · unfold ε
          simp [*]
        · unfold ε
          simp [*]

      have metric_ball_around_1_is_in_U :
        Metric.eball (1 : ℂ) ε ⊆ U := by
          by_cases h : ε₀ = ⊤
          · unfold ε
            simp [*]
            have T : Metric.eball (1 : ℂ) 1 ⊆ Metric.eball 1 ε₀ := by
              rw [h]
              exact Metric.eball_subset_eball (by simp)
            exact subset_trans (subset_trans T metric_ball_around_1_is_in_U') open_in_U_subs_U

          · unfold ε

            simp [h]
            exact subset_trans metric_ball_around_1_is_in_U' open_in_U_subs_U

      have O2 : ε ≠ 0 := by
        by_cases h : ε₀ = ⊤
        · unfold ε
          simp [*]
        · unfold ε
          simp [*]
          exact pos_iff_ne_zero.mp ε_pos

      let metric_ball_around_1 := Metric.eball (1 : ℂ) ε
      let ε_div_two := ε / 2
      let boundary := ENNReal.toReal (1 + ε_div_two)

      let ⟨bound, ⟨bound_pos, bound_prop⟩⟩ :=
          BddAbove.exists_ge zeta_residue_on_U 0

      have boundary_geq_one : 1 < boundary := by
          unfold boundary
          have Z : (1 : ENNReal).toReal = 1 := by rfl
          rw [←Z]
          have U : ε_div_two ≠ ⊤ := by
            refine ENNReal.div_ne_top O1 ?_
            simp
          simp
          simp [ENNReal.toReal_add _ U]
          refine ENNReal.toReal_pos ?_ ?_
          · unfold ε_div_two
            simp [*]
          · exact U

      let const : ℝ := bound
      let final_const : ℝ := (boundary - 1)⁻¹ + const
      have boundary_inv_pos : 0 < (boundary - 1)⁻¹ := by
        ring_nf
        apply inv_pos_of_pos
        simp [*]

      have final_const_pos : final_const ≥ 0 := by
        unfold final_const
        simp [*]
        have Z :=
          by
            calc
              0 ≤ (boundary - 1)⁻¹ := by simp; linarith
              _ ≤ (boundary - 1)⁻¹ + const := by unfold const; simp [bound_pos]

        exact Z

      have const_le_final_const : const ≤ final_const := by
        calc
          const ≤ (boundary - 1)⁻¹ + const := by simp; linarith
          _ = final_const := by rfl

      have const_pos : const ≥ 0 := by
        linarith

      use final_const
      use final_const_pos
      intro σ₀ t σ₀_gt

      by_cases h : σ₀ ≤ boundary
      · have σ₀_in_ball : (↑σ₀ : ℂ) ∈ metric_ball_around_1 := by
          unfold metric_ball_around_1
          unfold Metric.eball
          simp [*]
          have Z := edist_dist (↑σ₀) (↑1 : ℂ)
          rw [Z]
          have U := dist_eq_norm (↑σ₀) (↑1 : ℂ)
          rw [U]
          norm_cast
          have U : 0 ≤ σ₀ - 1 := by linarith
          have U1 : ‖σ₀ - 1‖ = σ₀ - 1 := by exact norm_of_nonneg U
          have U2 : ε ≠ ⊤ := by exact O1
          have U3 : 0 ≤ ε := by exact zero_le
          simp [Real.norm_of_nonneg U]
          simp [ENNReal.ofReal_lt_iff_lt_toReal U U2]
          have U4 : ENNReal.ofReal 1 ≠ ⊤ := by exact ENNReal.ofReal_ne_top
          have Z0 : ε_div_two.toReal < ε.toReal := by
            have T1 : ε ≠ ⊤ := by exact U2
            have T2 : ε ≠ 0 := by exact O2
            have T3 : ε_div_two < ε := by
              refine ENNReal.half_lt_self ?_ U2
              exact T2

            exact ENNReal.toReal_strict_mono T1 T3

          have Z := by
            calc
              σ₀ - 1 ≤ boundary - 1 := by linarith
              _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
              _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp
              _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
              _ = ENNReal.toReal (ε_div_two) := by simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
              _ < ε.toReal := Z0

          exact Z

        have σ₀_in_U : (↑σ₀ : ℂ) ∈ (U \ {1}) := by
          refine mem_sdiff_singleton.mpr ?_
          constructor
          · unfold metric_ball_around_1 at σ₀_in_ball
            exact metric_ball_around_1_is_in_U σ₀_in_ball
          · by_contra a
            have U : σ₀ = 1 := by exact ofReal_eq_one.mp a
            rw [U] at σ₀_gt
            linarith

        have bdd := Set.forall_mem_image.mp bound_prop (σ₀_in_U)
        simp [*] at bdd
        have Z :=
          calc
            ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
               have U := strongPnt_dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ₀ t (σ₀_gt) (by simp)
               exact U
            _ = ‖- ζ' σ₀ / ζ σ₀‖ := by simp only [Complex.norm_div, norm_neg]
            _ = ‖(- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹) + (σ₀ - 1)⁻¹‖ := by simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
            _ ≤ ‖(- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹)‖ + ‖(σ₀ - 1)⁻¹‖ := by
              have Z := norm_add_le (- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹) ((σ₀ - 1)⁻¹)
              norm_cast at Z
            _ ≤ const + ‖(σ₀ - 1)⁻¹‖ := by
              have U := add_le_add_left bdd ‖(σ₀ - 1)⁻¹‖
              ring_nf at U
              ring_nf
              norm_cast at U
              norm_cast
            _ ≤ const + (σ₀ - 1)⁻¹ := by
              simp [norm_inv]
              have pos : 0 ≤ σ₀ - 1 := by
                linarith
              simp [abs_of_nonneg pos]
            _ = (σ₀ - 1)⁻¹ + const := by
              rw [add_comm]
            _ ≤ (σ₀ - 1)⁻¹ + final_const := by
              simp [const_le_final_const]

        exact Z

      · push Not at h

        have boundary_geq_one : 1 < boundary := by
          unfold boundary
          have Z : (1 : ENNReal).toReal = 1 := by rfl
          rw [←Z]
          have U : ε_div_two ≠ ⊤ := by
            refine ENNReal.div_ne_top O1 ?_
            simp
          simp
          simp [ENNReal.toReal_add _ U]
          refine ENNReal.toReal_pos ?_ ?_
          · unfold ε_div_two
            simp [*]
          · exact U

        have boundary_in_ball : (↑boundary : ℂ) ∈ metric_ball_around_1 := by
          unfold metric_ball_around_1
          unfold Metric.eball
          simp [*]
          have Z := edist_dist (↑boundary) (↑1 : ℂ)
          rw [Z]
          have U := dist_eq_norm (↑boundary) (↑1 : ℂ)
          rw [U]
          norm_cast
          have U : 0 ≤ boundary - 1 := by linarith
          have U1 : ‖boundary - 1‖ = boundary - 1 := by exact norm_of_nonneg U
          have U2 : ε ≠ ⊤ := by exact O1
          have U3 : 0 ≤ ε := by exact zero_le
          simp [Real.norm_of_nonneg U]
          simp [ENNReal.ofReal_lt_iff_lt_toReal U U2]
          have U4 : ENNReal.ofReal 1 ≠ ⊤ := by exact ENNReal.ofReal_ne_top
          have Z0 : ε_div_two.toReal < ε.toReal := by
            have T1 : ε ≠ ⊤ := by exact U2
            have T2 : ε ≠ 0 := by exact O2
            have T3 : ε_div_two < ε := by
              refine ENNReal.half_lt_self ?_ U2
              exact T2

            exact ENNReal.toReal_strict_mono T1 T3

          have Z := by
            calc
              boundary - 1 ≤ boundary - 1 := by linarith
              _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
              _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp
              _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
              _ = ENNReal.toReal (ε_div_two) := by simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
              _ < ε.toReal := Z0

          exact Z

        have boundary_in_U : (↑boundary : ℂ) ∈ U \ {1} := by
          refine mem_sdiff_singleton.mpr ?_
          constructor
          · unfold metric_ball_around_1 at boundary_in_ball
            exact metric_ball_around_1_is_in_U boundary_in_ball
          · by_contra a
            norm_cast at a
            norm_cast at boundary_geq_one
            simp [←a] at boundary_geq_one

        have bdd := Set.forall_mem_image.mp bound_prop (boundary_in_U)

        have Z :=
          calc
            ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ ‖ζ' boundary / ζ boundary‖ := by
               have U := strongPnt_dlog_riemannZeta_bdd_on_vertical_lines_generalized boundary σ₀ t (boundary_geq_one) (by linarith)
               exact U
            _ = ‖- ζ' boundary / ζ boundary‖ := by simp only [Complex.norm_div, norm_neg]
            _ = ‖(- ζ' boundary / ζ boundary - (boundary - 1)⁻¹) + (boundary - 1)⁻¹‖ := by simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
            _ ≤ ‖(- ζ' boundary / ζ boundary - (boundary - 1)⁻¹)‖ + ‖(boundary - 1)⁻¹‖ := by
              have Z := norm_add_le (- ζ' boundary / ζ boundary - (boundary - 1)⁻¹) ((boundary - 1)⁻¹)
              norm_cast at Z
            _ ≤ const + ‖(boundary - 1)⁻¹‖ := by
              have U9 := add_le_add_left bdd ‖(boundary - 1)⁻¹‖
              ring_nf at U9
              ring_nf
              norm_cast at U9
              norm_cast
              simp [*] at U9
              simp [*]
              exact U9

            _ ≤ const + (boundary - 1)⁻¹ := by
              simp [norm_inv]
              have pos : 0 ≤ boundary - 1 := by
                linarith
              simp [abs_of_nonneg pos]
            _ = (boundary - 1)⁻¹ + const := by
              rw [add_comm]
            _ = final_const := by rfl
            _ ≤ (σ₀ - 1)⁻¹ + final_const := by
              have H : 0 ≤ (σ₀ - 1)⁻¹ := by
                simp
                linarith

              simp [H]

        exact Z

def LogDerivZetaHasBound (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t|)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})

theorem dlog_riemannZeta_bdd_on_vertical_lines_explicit {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∀(t : ℝ), ‖(-ζ' (σ₀ + t * I) / ζ (σ₀ + t * I))‖ ≤ ‖(ζ' σ₀ / ζ σ₀)‖ := by

  intro t
  let s := σ₀ + t * I
  have s_re_eq_sigma : s.re = σ₀ := by
    rw [Complex.add_re (σ₀) (t * I)]
    rw [Complex.ofReal_re σ₀]
    rw [Complex.mul_I_re]
    simp [*]

  have s₀_geq_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt
  have s_re_geq_one : 1 < s.re := by exact lt_of_lt_of_eq σ₀_gt (id (Eq.symm s_re_eq_sigma))
  have s_re_coerce_geq_one : 1 < (↑s.re : ℂ).re := by exact s_re_geq_one
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s_re_geq_one)]
  unfold LSeries

  have summable_von_mangoldt : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) s.re i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s_re_geq_one

  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₀_geq_one

  have summable_re_von_mangoldt : Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) s.re i).re) := by
    exact strongPnt_summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) s.re) summable_von_mangoldt

  have positivity : ∀(n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s n‖ = (LSeries.term (fun n ↦ Λ n) s.re n).re := by
    intro n
    calc
      ‖LSeries.term (fun n ↦ ↑(Λ n)) s n‖ = Λ n / ‖(↑n : ℂ)^(s : ℂ)‖ := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · push Not at h
          simp [*]

      _ = Λ n / (↑n)^s.re := by
        by_cases h : n = 0
        · simp [*]
        · rw [Complex.norm_natCast_cpow_of_pos]
          push Not at h
          exact Nat.zero_lt_of_ne_zero h

      _ = (LSeries.term (fun n ↦ Λ n) s.re n).re := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · simp [*]
          push Not at h
          ring_nf
          rw [Complex.re_ofReal_mul (Λ n)]
          ring_nf
          rw [Complex.inv_re]
          rw [Complex.cpow_ofReal_re]
          simp [*]
          left
          have N : (0 : ℝ) ≤ ↑n := by exact Nat.cast_nonneg' n
          have T2 : ((↑n : ℂ) ^ (↑σ₀ : ℂ)).re = (↑n : ℝ)^σ₀ := by exact rfl
          have T1 : ((↑n : ℂ ) ^ (↑σ₀ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [T2]
            simp [*]
            exact Real.rpow_nonneg N σ₀

          simp [Complex.normSq_apply]
          simp [T1, T2]

  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(Λ n)) s i‖) := by
    rw [summable_congr positivity]
    exact summable_re_von_mangoldt

  have triangle_ineq : ‖LSeries (fun n ↦ ↑(Λ n)) s‖ ≤ ∑' (n : ℕ), ↑‖LSeries.term (fun n ↦ ↑(Λ n)) s n‖ :=
    norm_tsum_le_tsum_norm summable_abs_value

  have bounded_by_sum_of_re : ‖LSeries (fun n ↦ ↑(Λ n)) s‖ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n).re :=
    by
      simp [positivity] at triangle_ineq
      exact triangle_ineq

  have sum_of_re_commutes : ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n).re = (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n)).re :=
    (Complex.re_tsum (summable_von_mangoldt)).symm

  have re_of_sum_bdd_by_norm : (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n)).re  ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n)‖ :=
    Complex.re_le_norm (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n))

  have Z :=
    by
      calc
        ‖LSeries (fun n ↦ ↑(Λ n)) s‖ ≤ ∑' (n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s n‖
            := norm_tsum_le_tsum_norm summable_abs_value
      _ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s.re n).re := by simp [←positivity]
      _ = (∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s.re n)).re := (Complex.re_tsum (summable_von_mangoldt)).symm
      _ ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s.re n)‖ := re_le_norm (∑' (n : ℕ), LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n)
      _ = ‖- ζ' (↑s.re) / ζ (↑s.re)‖ := by
          simp only [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s_re_coerce_geq_one)]
          unfold LSeries
          rfl
      _ = ‖ζ' σ₀ / ζ σ₀‖ := by
        rw [← s_re_eq_sigma]
        simp [*]

  exact Z

theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀)  :
  ∃ c > 0, ∀(t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ c := by

    let s_re : ℂ  := σ₀

    let new_const : ℝ := 1 + (↑(Norm.norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) (↑ s_re : ℂ ) n‖)) : ℝ )
    have new_const_is_pos : new_const > 0 := by positivity

    use new_const
    use new_const_is_pos
    intro t

    let s := σ₀ + t * I

    have DD : (↑ s.re : ℂ)  = s_re := by
      refine ofReal_inj.mpr ?_
      rw [add_re, ofReal_re, mul_re, ofReal_re, I_re, I_im]
      simp

    have L : s_re = σ₀ := by rfl

    have H : s.re = σ₀ := by
          rw [add_re, ofReal_re, mul_re, ofReal_re, I_re, I_im]
          simp

    have non_neg : σ₀ ≠ 0 := by
      by_contra h
      rw [h] at σ₀_gt
      norm_cast at σ₀_gt

    have pos : s.re > 1 := by exact lt_of_lt_of_eq σ₀_gt (id (Eq.symm H))
    have pos_triv : s_re.re > 1 := by exact σ₀_gt

    rw [← norm_neg, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div pos]

    have identity0 : ∀(n : ℕ), ‖LSeries.term 1 s n‖ = 1 / n^σ₀ := by
      unfold LSeries.term
      intro n
      by_cases h0 : n = 0
      · simp [*]
      · simp [*]
        push Not at h0
        have C : n > 0 := by exact Nat.zero_lt_of_ne_zero h0
        have T :=  Complex.norm_natCast_cpow_of_pos C s
        rw [H] at T
        exact T

    have O : ∀(s : ℂ), ∀(n : ℕ), s.re = σ₀ → (↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ) : ℂ) = LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ ) n := by
      intro s n cond
                                    
      by_cases h1 : (n = 0)
      · simp [h1]
      · push Not at h1
        unfold LSeries.term
        simp [*]
        have U : |Λ n| = Λ n := abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
        have R : n > 0 := by exact Nat.zero_lt_of_ne_zero h1
        rw [U]
        have Z := Complex.norm_natCast_cpow_of_pos R s
        rw [Z]
        rw [← L]
                   
        by_cases h : (Λ n = 0)
        · simp [h]
        · norm_cast
          apply_fun (fun (w : ℂ) ↦ w * (↑ n : ℂ)^s_re  / (Λ n))
          · simp [*]
            ring_nf
            rw [mul_comm]
            nth_rewrite 1 [mul_assoc]
            simp [*]
            have := cast_pow_eq n σ₀
            rw [this]
            simp [*]

          · have G : (↑ n : ℂ)^s_re  / (Λ n) ≠ 0 := by
              have T : (↑ n : ℂ)^s_re ≠ 0 := by
                have T : n > 0 := by exact R
                have M : ∃(m : ℕ), n = m + 1 := by exact Nat.exists_eq_succ_of_ne_zero h1
                let ⟨m, pf⟩ := M
                have U := Complex.natCast_add_one_cpow_ne_zero m s_re
                rw [pf]
                push_cast
                exact U
              refine div_ne_zero T ?_
              push Not at h
              norm_cast
            have U := by exact mul_left_injective₀ G
            have T : (fun (x : ℂ) ↦ x * (↑ n : ℂ)^s_re  / (Λ n)) = (fun (x : ℂ) ↦ x * ((↑ n : ℂ)^s_re  / (Λ n))) := by funext x; exact mul_div_assoc x (↑n ^ s_re) ↑(Λ n)
            simp [←T] at U
            exact U

    have K : (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ)) = (fun (n : ℕ) ↦ (LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ )  n )) := by
      funext n
      rw [O s n H]

    have K1 : (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) (↑ s.re : ℂ) n‖ : ℝ)) = (fun (n : ℕ) ↦ (LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ )  n )) := by
      funext n
      rw [O (↑ s.re : ℂ) n H]
      simp [*]

    have D2 :  (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ)) = (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) (↑ s.re : ℂ)  n‖ : ℝ)) := by
      simp [← K]

    have S : Summable (fun n ↦ (↑(‖LSeries.term (fun x ↦ Λ x) s n‖ : ℝ) : ℝ  )) := by
      apply (summable_real_iff_summable_coe_complex (fun n ↦ (↑(‖LSeries.term (fun x ↦ Λ x) s n‖ : ℝ) : ℝ  ))).mpr
      rw [K]
      have T := ArithmeticFunction.LSeriesSummable_vonMangoldt (pos_triv)
      have U : s_re = s.re := by exact congrFun (congrArg Complex.mk (id (Eq.symm H))) 0
      simp [← U]
      exact T

    have C := calc
      ‖∑' (n : ℕ), (LSeries.term (fun x ↦ Λ x) s n)‖ ≤ ∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) s n‖ := norm_tsum_le_tsum_norm S
                                                                                                                                
      _                                              ≤ norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) s n‖) := by exact le_norm_self (∑' (n : ℕ), ‖LSeries.term (fun x ↦ ↑(Λ x)) s n‖)
      _                                              = norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ) n‖) := by simp [D2]
      _                                              ≤ 1 + norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) ( ↑ s.re : ℂ) n‖ ) := by linarith
      _                                              = new_const := by rw [DD]

    exact C

theorem dlog_riemannZeta_bdd_on_vertical_lines' {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∃ C > 0, ∀ (t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ C :=
  dlog_riemannZeta_bdd_on_vertical_lines σ₀_gt

theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines' σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
    intro t
    simp only [Complex.norm_mul, c]
    gcongr
    · simpa only [neg_div, norm_neg] using hC t

    · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
      · simp
      · linarith
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, ne_eq]
        linarith
  convert! (SmoothedChebyshevDirichlet_aux_integrable ContDiffSmoothingF SmoothingFnonneg
    suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul (c := c) ?_ (Filter.Eventually.of_forall this) using 2
  · unfold SmoothedChebyshevIntegrand
    ring
  · apply Continuous.aestronglyMeasurable
    apply continuousOn_univ.mp
    intro t _
    let s := σ₀ + (t : ℂ) * I
    have s_ne_one : s ≠ 1 := by
      intro h
                                                               
      have : σ₀ = 1 := by
        have := congr_arg Complex.re h
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, one_re, s] at this
        exact this
                                    
      linarith [σ₀_gt]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have diffζ := differentiableAt_riemannZeta s_ne_one
      apply ContinuousAt.div
      · apply ContinuousAt.neg
        have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
          differentiableAt_deriv_riemannZeta s_ne_one
        convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) this <;> simp
      · convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp [σ₀_gt]
    · apply ContinuousAt.comp _ (by fun_prop)
      apply continuousAt_const_cpow
      norm_cast
      linarith

lemma BddAboveOnRect {g : ℂ → ℂ} {z w : ℂ} (holoOn : HolomorphicOn g (z.Rectangle w)) :
    BddAbove (norm ∘ g '' (z.Rectangle w)) := by
  have compact_rect : IsCompact (z.Rectangle w) := by
    apply IsCompact.reProdIm <;> apply isCompact_uIcc
  refine IsCompact.bddAbove_image compact_rect ?_
  apply holoOn.continuousOn.norm

theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X := by
  unfold SmoothedChebyshev
  unfold VerticalIntegral'
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    refine add_lt_add_of_le_of_lt ?_ ?_
    rfl
    rw[inv_pos, ← Real.log_one]
    apply Real.log_lt_log
    norm_num
    linarith
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw[← one_add_one_eq_two]
    refine (add_lt_add_iff_left 1).mpr ?_
    refine inv_lt_one_of_one_lt₀ ?_
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    positivity
    have : rexp 1 < 3 := by exact lt_trans (Real.exp_one_lt_d9) (by norm_num)
    linarith
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  ·
    exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
      X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
  ·
    have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by push_cast; rfl
    repeat rw[smul_eq_mul]
    unfold I₁
    rw[temp, mul_add, mul_add, add_assoc, sub_eq_add_neg]
    nth_rewrite 4 [add_assoc]
    nth_rewrite 3 [add_assoc]
    nth_rewrite 2 [add_assoc]
    rw[add_assoc, add_left_cancel_iff, add_assoc]
    nth_rewrite 7 [add_comm]
    rw[← add_assoc]
    unfold I₉
    rw[add_right_cancel_iff, ← add_right_inj (1 / (2 * ↑π * I) *
      -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
      ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
    unfold VIntegral I₂ I₃₇ I₈
    rw[smul_eq_mul, temp, ← add_assoc, ← add_assoc]
    nth_rewrite 2 [div_mul_comm]
    rw[mul_one, ← neg_div, ← mul_neg]
    nth_rewrite 2 [← one_div_mul_eq_div]
    repeat rw[← mul_add]
    let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
      SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
    let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
    have : ∫ (y : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
      ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
      unfold fTempRR
      rw[temp]
    rw[this]
    have : ∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I) =
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
      unfold fTempRR
      rw[Complex.ofReal_neg, neg_mul]
      rfl
    rw[this]
    have : ∫ (t : ℝ) in -T..T, SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
      ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := by rfl
    rw[this]
    have : ∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ + ↑T * I) =
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := by rfl
    rw[this]
    repeat rw[← add_assoc]
    have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
      -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
      I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
        -1 * RectangleIntegral fTempC ((1 : ℝ) + (Real.log X)⁻¹ + T * I) (σ₁ - T * I) := by
      unfold RectangleIntegral
      rw[HIntegral_symm, VIntegral_symm]
      nth_rewrite 2 [HIntegral_symm, VIntegral_symm]
      unfold HIntegral VIntegral
      repeat rw[smul_eq_mul]
      repeat rw[add_re]
      repeat rw[add_im]
      repeat rw[sub_re]
      repeat rw[sub_im]
      repeat rw[mul_re]
      repeat rw[mul_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      rw[I_re, I_im, mul_zero, zero_mul, mul_one]
      ring_nf
      unfold fTempC
      have : ∫ (y : ℝ) in -T..T, fTempRR (I * ↑y + ↑σ₁).re (I * ↑y + ↑σ₁).im =
        ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := by simp
      rw[this]
      have : ∫ (y : ℝ) in -T..T,
          fTempRR (I * ↑y + ↑(1 + (Real.log X)⁻¹)).re (I * ↑y + ↑(1 + (Real.log X)⁻¹)).im =
        ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by simp
      rw[this]
      have : ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR (I * ↑T + ↑x).re (I * ↑T + ↑x).im =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := by simp
      rw[this]
      have : ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR (I * ↑(-T) + ↑x).re (I * ↑(-T) + ↑x).im =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by simp
      rw[this]
      ring_nf
    rw[this, neg_one_mul, div_mul_comm, mul_one,
        ← add_right_inj
        (RectangleIntegral fTempC (1 + ↑(Real.log X)⁻¹ + ↑T * I) (↑σ₁ - ↑T * I) / (2 * ↑π * I)),
        ← add_assoc]
    simp only [ofReal_one, ofReal_inv, add_zero]
    rw[rectangleIntegral_symm]
    have : RectangleIntegral fTempC (↑σ₁ - ↑T * I) (1 + 1 / ↑(Real.log X) + ↑T * I) / (2 * ↑π * I) =
      RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
      unfold RectangleIntegral'
      rw [smul_eq_mul]
      simp only [one_div, ofReal_inv]
      ring

    simp only [one_div, ofReal_inv] at this
    rw [this]

    let holoMatch : ℂ → ℂ := fun z ↦
      (fTempC z - (𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) 1 * ↑X) / (z - 1))
    have inv_log_X_pos: 0 < (Real.log X)⁻¹ := by
      rw[inv_pos, ← Real.log_one]
      apply Real.log_lt_log (by positivity) (by linarith)
    have pInRectangleInterior :
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
      refine rectangle_mem_nhds_iff.mpr ?_
      refine mem_reProdIm.mpr ?_
      have : re 1 = 1 := by rfl
      rw[this]
      have : im 1 = 0 := by rfl
      rw[this]
      repeat rw[sub_re]
      repeat rw[sub_im]
      repeat rw[add_re]
      repeat rw[add_im]
      rw[mul_re, mul_im, I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have temp : 1 ∈ uIoo σ₁ (re 1 + (Real.log X)⁻¹) := by
        have : re 1 = 1 := by rfl
        rw[this]
        unfold uIoo
        have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
        rw[this]
        have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by exact max_eq_right (by linarith)
        rw[this]
        refine mem_Ioo.mpr ?_
        exact ⟨σ₁_lt_one, (by linarith)⟩
      have : 0 ∈ uIoo (-T) (T + im 1) := by
        have : im 1 = 0 := by rfl
        rw[this, add_zero]
        unfold uIoo
        have : min (-T) T = -T := by exact min_eq_left (by linarith)
        rw[this]
        have : max (-T) T = T := by exact max_eq_right (by linarith)
        rw[this]
        refine mem_Ioo.mpr ?_
        exact ⟨(by linarith), (by linarith)⟩
      exact ⟨temp, this⟩
           
    have holoMatchHoloOn : HolomorphicOn holoMatch
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) \ {1}) := by
      unfold HolomorphicOn holoMatch
      refine DifferentiableOn.sub ?_ ?_
      · unfold fTempC fTempRR
        have : (fun z ↦ SmoothedChebyshevIntegrand SmoothingF ε X (↑z.re + ↑z.im * I)) =
          (fun z ↦ SmoothedChebyshevIntegrand SmoothingF ε X z) := by
          apply funext
          intro z
          have : (↑z.re + ↑z.im * I) = z := by exact re_add_im z
          rw[this]
        rw[this]
        refine DifferentiableOn.mul ?_ ?_
        · refine DifferentiableOn.mul ?_ ?_
          · have : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)) := by
              refine funext ?_
              intro x
              exact neg_div (ζ x) (ζ' x)
            rw[this]
            refine DifferentiableOn.neg ?_
            unfold DifferentiableOn
            intro x x_location
            unfold Rectangle at x_location
            rw[Set.mem_sdiff, Complex.mem_reProdIm, sub_re, add_re, sub_im, add_im, mul_re, mul_im,
              I_re, I_im, add_re, add_im] at x_location
            simp only [ofReal_re, mul_zero, ofReal_im, mul_one, sub_self, sub_zero, one_re,
              ofReal_inv, inv_re, normSq_ofReal, div_self_mul_self', add_zero, zero_sub, one_im,
              inv_im, neg_zero, zero_div, zero_add, mem_singleton_iff] at x_location

            obtain ⟨⟨xReIn, xImIn⟩, xOut⟩ := x_location
            unfold uIcc at xReIn xImIn
            have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
            rw[this] at xReIn
            have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by exact max_eq_right (by linarith)
            rw[this] at xReIn
            have : min (-T) T = (-T) := by exact min_eq_left (by linarith)
            rw[this] at xImIn
            have : max (-T) T = T := by exact max_eq_right (by linarith)
            rw[this] at xImIn
            unfold HolomorphicOn DifferentiableOn at holoOn
            have temp : DifferentiableWithinAt ℂ (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) x := by
              have : x ∈ Icc σ₁ 2 ×ℂ Icc (-T) T \ {1} := by
                rw [Set.mem_sdiff, Complex.mem_reProdIm]
                have xReTemp : x.re ∈ Icc σ₁ 2 := by
                  have xReLb : σ₁ ≤ x.re := by exact xReIn.1
                  have xReUb : x.re ≤ 2 := by exact (lt_of_le_of_lt xReIn.2 X_eq_lt_two).le
                  exact ⟨xReLb, xReUb⟩
                have xImTemp : x.im ∈ Icc (-T) T := by exact ⟨xImIn.1, xImIn.2⟩
                exact ⟨⟨xReTemp, xImTemp⟩, xOut⟩
              exact holoOn x this

            have : ((↑σ₁ - ↑T * I).Rectangle (1 + ↑(Real.log X)⁻¹ + ↑T * I) \ {1}) ⊆
              (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) := by
              intro a a_location
              rw[Set.mem_sdiff, Complex.mem_reProdIm]
              rw[Set.mem_sdiff] at a_location
              obtain ⟨aIn, aOut⟩ := a_location
              unfold Rectangle uIcc at aIn
              rw[sub_re, add_re, add_re, sub_im, add_im, add_im, mul_re, mul_im, ofReal_re, ofReal_re, ofReal_re, ofReal_im, ofReal_im, ofReal_im, I_re, I_im] at aIn
              have : re 1 = 1 := by rfl
              rw[this] at aIn
              have : im 1 = 0 := by rfl
              rw[this] at aIn
              ring_nf at aIn
              have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by linarith
              rw[this] at aIn
              have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by linarith
              rw[this] at aIn
              have : min (-T) T = (-T) := by linarith
              rw[this] at aIn
              have : max (-T) T = T := by linarith
              rw[this] at aIn
              rw[Complex.mem_reProdIm] at aIn
              obtain ⟨aReIn, aImIn⟩ := aIn
              have aReInRedo : a.re ∈ Icc σ₁ 2 := by
                have : a.re ≤ 2 := by exact (lt_of_le_of_lt aReIn.2 X_eq_lt_two).le
                exact ⟨aReIn.1, this⟩
              exact ⟨⟨aReInRedo, aImIn⟩, aOut⟩
            exact DifferentiableWithinAt.mono temp this
          · unfold DifferentiableOn
            intro x x_location
            refine DifferentiableAt.differentiableWithinAt ?_
            have hε : ε ∈ Ioo 0 1 := by exact ⟨ε_pos, ε_lt_one⟩
            have xRePos : 0 < x.re := by
              unfold Rectangle at x_location
              rw[Set.mem_sdiff, Complex.mem_reProdIm] at x_location
              obtain ⟨⟨xReIn, _⟩, _⟩ := x_location
              unfold uIcc at xReIn
              rw[sub_re, add_re, add_re, mul_re, I_re, I_im] at xReIn
              repeat rw[ofReal_re] at xReIn
              repeat rw[ofReal_im] at xReIn
              ring_nf at xReIn
              have : re 1 = 1 := by rfl
              rw[this] at xReIn
              have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
              rw[this] at xReIn
              have : σ₁ ≤ x.re := by exact xReIn.1
              linarith
            exact Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF hε SmoothingFnonneg mass_one xRePos
        · unfold DifferentiableOn
          intro x x_location
          apply DifferentiableAt.differentiableWithinAt
          unfold HPow.hPow instHPow
          simp only
          apply DifferentiableAt.const_cpow
          · exact differentiableAt_fun_id
          · left
            refine ne_zero_of_re_pos ?_
            simp only [ofReal_re]
            linarith
      · refine DifferentiableOn.mul ?_ ?_
        ·
          unfold DifferentiableOn
          intro x x_location
          rw[Set.mem_sdiff] at x_location
          obtain ⟨xInRect, xOut⟩ := x_location
          apply DifferentiableAt.differentiableWithinAt
          apply differentiableAt_const
        · unfold DifferentiableOn
          intro x x_location
          apply DifferentiableAt.differentiableWithinAt
          apply DifferentiableAt.inv
          · fun_prop
          · intro h
            rw [sub_eq_zero] at h
            have := x_location.2
            simp only [mem_singleton_iff] at this
            exact this h

    have holoMatchBddAbove : BddAbove
        (norm ∘ holoMatch '' (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) \ {1})) := by
      let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
      let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
      let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
      have bigO_holoMatch : holoMatch =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
        unfold holoMatch fTempC fTempRR SmoothedChebyshevIntegrand
        simp only [re_add_im]
        have : (fun z ↦
            (-ζ' z / ζ z * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z -
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) 1 * ↑X / (z - 1))) =
            (fun z ↦ (f z * g z - 1 * g 1 / (z - 1))) := by
          apply funext
          intro x
          simp[f, g]
          rw[mul_assoc]
        rw[this]
        have g_holc : HolomorphicOn g U := by
          unfold HolomorphicOn DifferentiableOn
          intro u uInU
          refine DifferentiableAt.differentiableWithinAt ?_
          simp[g]
          refine DifferentiableAt.mul ?_ ?_
          have hε : ε ∈ Set.Ioo 0 1 := by exact ⟨ε_pos, ε_lt_one⟩
          have hu : 0 < u.re := by
            simp[U] at uInU
            unfold Rectangle uIcc at uInU
            rw[Complex.mem_reProdIm] at uInU
            obtain ⟨uReIn, uImIn⟩ := uInU
            have : min (↑σ₁ - ↑T * I).re (1 + (↑(Real.log X))⁻¹ + ↑T * I).re = σ₁ := by
              rw[sub_re, add_re, add_re, mul_re, I_re, I_im]
              repeat rw[ofReal_re]
              repeat rw[ofReal_im]
              simp
              linarith
            rw[this] at uReIn
            have : σ₁ ≤ u.re := by exact uReIn.1
            linarith
          exact Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF hε SmoothingFnonneg mass_one hu
          unfold HPow.hPow instHPow
          simp
          apply DifferentiableAt.const_cpow
          exact differentiableAt_fun_id
          refine Or.inl ?_
          refine ne_zero_of_re_pos ?_
          rw[ofReal_re]
          positivity
        have U_in_nhds : U ∈ nhds 1 := by
          simp only [U]
          exact pInRectangleInterior
        have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
          simp[f]
          have : ((fun z ↦ -ζ' z / ζ z) - fun z ↦ (z - 1)⁻¹) =
            (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
            apply funext
            intro z
            simp
          rw[this]
          exact riemannZetaLogDerivResidueBigO
        exact ResidueMult g_holc U_in_nhds f_near_p
      have : ∃ V ∈ nhds 1, BddAbove (norm ∘ holoMatch '' (V \ {1})) := by exact IsBigO_to_BddAbove bigO_holoMatch
      obtain ⟨V, VInNhds_one, BddAboveV⟩ := this
      have : ∃ W ⊆ V, 1 ∈ W ∧ IsOpen W ∧ BddAbove (norm ∘ holoMatch '' (W \ {1})) := by
        rw[mem_nhds_iff] at VInNhds_one
        obtain ⟨W, WSubset, WOpen, one_in_W⟩ := VInNhds_one
        use W
        have : BddAbove (Norm.norm ∘ holoMatch '' (W \ {1})) := by
          have : Norm.norm ∘ holoMatch '' (W \ {1}) ⊆
            Norm.norm ∘ holoMatch '' (V \ {1}) := by
            exact image_mono (by exact sdiff_subset_sdiff_left WSubset)
          exact BddAbove.mono this BddAboveV
        exact ⟨WSubset, ⟨one_in_W, WOpen, this⟩⟩
      obtain ⟨W, WSubset, one_in_W, OpenW, BddAboveW⟩ := this
      have : (↑σ₁ - ↑T * I).Rectangle (1 + ↑(Real.log X)⁻¹ + ↑T * I) = U := by rfl
      rw[this] at holoMatchHoloOn ⊢
      have one_in_U : 1 ∈ U := by
        have U_in_nhds : U ∈ nhds 1 := by
          simp only [U]
          exact pInRectangleInterior
        exact mem_of_mem_nhds U_in_nhds
      have (h1 : 1 ∈ U) (h2 : 1 ∈ W) : U \ {1} = (U \ W) ∪ ((U ∩ W) \ {1}) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff]
        constructor
        intro ⟨hxU, hx1⟩
        by_cases hw : x ∈ W
        · right
          exact ⟨⟨hxU, hw⟩, hx1⟩
        · left
          exact ⟨hxU, hw⟩
        · intro h
          cases' h with h_left h_right
          have : x ≠ 1 := by
            intro x_eq_1
            rw[x_eq_1] at h_left
            exact h_left.2 h2
          · exact ⟨h_left.1, this⟩
          · exact ⟨h_right.1.1, h_right.2⟩
      rw[this one_in_U one_in_W]
      have : Norm.norm ∘ holoMatch '' (U \ W ∪ (U ∩ W) \ {1}) =
        Norm.norm ∘ holoMatch '' (U \ W) ∪ Norm.norm ∘ holoMatch '' ((U ∩ W) \ {1}) := by
        exact image_union (Norm.norm ∘ holoMatch) (U \ W) ((U ∩ W) \ {1})
      rw[this]
      refine BddAbove.union ?_ ?_
      refine IsCompact.bddAbove_image ?_ ?_
      refine IsCompact.diff ?_ ?_
      unfold U Rectangle
      apply IsCompact.reProdIm
      unfold uIcc
      exact isCompact_Icc
      unfold uIcc
      exact isCompact_Icc
      exact OpenW
      refine Continuous.comp_continuousOn ?_ ?_
      exact continuous_norm
      have : HolomorphicOn holoMatch (U \ W) := by
        have : U \ W ⊆ U \ {1} := by
          intro x x_location
          obtain ⟨xInU, xOutW⟩ := x_location
          rw[Set.mem_sdiff]
          apply And.intro
          exact xInU
          rw[Set.mem_singleton_iff]
          intro x_eq_1
          rw[x_eq_1] at xOutW
          exact xOutW one_in_W
        exact DifferentiableOn.mono holoMatchHoloOn this
      unfold HolomorphicOn at this
      exact DifferentiableOn.continuousOn this
      have : Norm.norm ∘ holoMatch '' ((U ∩ W) \ {1}) ⊆
        Norm.norm ∘ holoMatch '' (W \ {1}) := by
        have : (U ∩ W) \ {1} ⊆ W \ {1} := by
          intro x x_location
          rw[Set.mem_sdiff] at x_location
          obtain ⟨⟨xInU, xInW⟩, xOut⟩ := x_location
          exact ⟨xInW, xOut⟩
        exact image_mono this
      exact BddAbove.mono this BddAboveW

    obtain ⟨g, gHolo_Eq⟩ := existsDifferentiableOn_of_bddAbove
      pInRectangleInterior holoMatchHoloOn holoMatchBddAbove
    obtain ⟨gHolo, gEq⟩ := gHolo_Eq

    have zRe_le_wRe : (σ₁ - ↑T * I).re ≤ (1 + (Real.log X)⁻¹ + T * I).re := by
      repeat rw[sub_re]
      repeat rw[add_re]
      repeat rw[mul_re]
      rw[I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have : re 1 = 1 := by rfl
      rw[this]
      linarith
    have zIm_le_wIm : (σ₁ - ↑T * I).im ≤ (1 + (Real.log X)⁻¹ + T * I).im := by
      repeat rw[sub_im]
      repeat rw[add_im]
      repeat rw[mul_im]
      rw[I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have : im 1 = 0 := by rfl
      rw[this]
      linarith
    have hres := ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm
      pInRectangleInterior gHolo gEq
    simp only [ofReal_inv] at hres
    rw [← hres]
    unfold RectangleIntegral'
    simp only [smul_eq_mul]
    ring

lemma interval_membership (r : ℝ)(a b: ℝ)(h1 : r ∈ Set.Icc (min a b) (max a b)) (h2 : a < b) :
  a ≤ r ∧ r ≤ b := by
                                                       
  have min_eq : min a b = a := min_eq_left (le_of_lt h2)
  have max_eq : max a b = b := max_eq_right (le_of_lt h2)
  rw [min_eq, max_eq] at h1
  rw [← @mem_Icc]
  exact h1

lemma verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    VIntegral f σ s e =
    VIntegral f σ s a +
    VIntegral f σ a b +
    VIntegral f σ b e := by
  dsimp [VIntegral]
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
  rw[← intervalIntegral.integral_add_adjacent_intervals (b := a), ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
  · ring
  all_goals apply IntervalIntegrable.mono_set hf; apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith

lemma verticalIntegral_split_three_finite' {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s e) =
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) := by
  have : (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) = (1 : ℂ) / (2 * π * I) * ((VIntegral f σ s a) +
    (VIntegral f σ a b) +
    (VIntegral f σ b e)) := by ring
  rw [this]
  clear this
  rw [← verticalIntegral_split_three_finite hf hab]

theorem SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
  (holoOn : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
  ContinuousOn (fun (t : ℝ) ↦ -ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)) (Icc (-T) T) := by
  rw [show (fun (t : ℝ) ↦ -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) = -(ζ' / ζ) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
  apply ContinuousOn.neg
  apply holoOn.continuousOn.comp (by fun_prop)
  intro t ht
  simp
  constructor
  · apply mem_reProdIm.mpr
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
    linarith
  · intro h
    replace h := congr_arg re h
    simp at h
    linarith

theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith

  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
                                         
    intro x hx
    constructor
    .                                       
      simp only [Rectangle, uIcc] at hx
      rw [Complex.mem_reProdIm] at hx ⊢
      obtain ⟨hx_re, hx_im⟩ := hx
                                                      
      have hzw_re : z.re < w.re := by
        simp only [z, w, add_re, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
        linarith
      have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
        exact interval_membership x.re z.re w.re hx_re hzw_re
      have x_re_in_Icc : x.re ∈ Icc σ₂ 2 := by
        have ⟨h_left, h_right⟩ := x_re_bounds
        have h_left' : σ₂ ≤ x.re := by
          simp only [z, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, mul_one] at h_left
          linarith
        have h_right' : x.re ≤ 2 := by
          apply le_trans h_right
          simp only [w, add_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
          linarith
        exact ⟨h_left', h_right'⟩
                                                           
      have hzw_im : z.im < w.im := by
        simp only [z, w, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, add_im, sub_im, mul_im, mul_one, zero_sub]
        linarith
      have x_im_bounds : z.im ≤ x.im ∧ x.im ≤ w.im := by
        exact interval_membership x.im z.im w.im hx_im hzw_im
      have x_im_in_Icc : x.im ∈ Icc (-3) 3 := by
        have ⟨h_left, h_right⟩ := x_im_bounds
        have h_left' : -3 ≤ x.im := by
          simp only [z, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, sub_im, mul_im, mul_one, zero_sub] at h_left
          linarith
        have h_right' : x.im ≤ 3 := by
          simp only [w, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, add_im, mul_im, mul_one] at h_right
          linarith
        exact ⟨h_left', h_right'⟩
      exact ⟨x_re_in_Icc, x_im_in_Icc⟩
                                       
    . simp only [mem_singleton_iff]
                                    
      have x_re_upper: x.re ≤ σ₁ := by
        simp only [Rectangle, uIcc] at hx
        rw [Complex.mem_reProdIm] at hx
        obtain ⟨hx_re, _⟩ := hx
                                                
        have hzw_re : z.re < w.re := by
          simp only [z, w, add_re, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
          linarith
        have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
          exact interval_membership x.re z.re w.re hx_re hzw_re
        have x_re_upper' : x.re ≤ w.re := by exact x_re_bounds.2
        simp only [w, add_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one] at x_re_upper'
        linarith
                          
      have h_x_ne_one : x ≠ 1 := by
        intro h_eq
        have h_re : x.re = 1 := by rw [h_eq, Complex.one_re]
        have h1 : 1 ≤ σ₁ := by
          rw [← h_re]
          exact x_re_upper
        linarith
      exact h_x_ne_one
  have zero_over_box := HolomorphicOn.vanishesOnRectangle holoOn2 sub
  have splitting : I₃₇ SmoothingF ε T X σ₁ =
    I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    unfold I₃₇ I₃ I₅ I₇
    apply verticalIntegral_split_three_finite'
    · apply ContinuousOn.integrableOn_Icc
      unfold SmoothedChebyshevIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t t_mem
          have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF  ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
          simpa using! realDiff_of_complexDiff _ this
      · apply continuousOn_of_forall_continuousAt
        intro t t_mem
        apply ContinuousAt.comp
        · refine continuousAt_const_cpow' ?_
          intro h
          have : σ₁ = 0 := by
            have h_real : (↑σ₁ + ↑t * I).re = (0 : ℂ).re := by
              rw [h]
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, zero_re] at h_real
            exact h_real
          linarith
        ·                        
          apply ContinuousAt.add
          · exact continuousAt_const
          · apply ContinuousAt.mul
            · apply continuous_ofReal.continuousAt
            · exact continuousAt_const
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc I₃₇ SmoothingF ε T X σ₁ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
    - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by simp [RectangleIntegral]
    _ = I₃₇ SmoothingF ε T X σ₁ - ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
        w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
                                                                                                                               
    _ = I₃ SmoothingF ε T X σ₁
    + I₅ SmoothingF ε X σ₁
    + I₇ SmoothingF ε T X σ₁
    - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      rw [splitting]
    _ = I₃ SmoothingF ε T X σ₁
    - I₄ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₂
    + I₆ SmoothingF ε X σ₁ σ₂
    + I₇ SmoothingF ε T X σ₁ := by
      ring

theorem ZetaBoxEval {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C, ∀ᶠ ε in (nhdsWithin 0 (Ioi 0)), ∀ X : ℝ, 0 ≤ X →
    ‖𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X - X‖ ≤ C * ε * X := by
  have := MellinOfSmooth1c ContDiffSmoothingF suppSmoothingF mass_one
  clear suppSmoothingF mass_one ContDiffSmoothingF
  rw[Asymptotics.isBigO_iff] at this
  obtain ⟨C, hC⟩ := this
  use C
  have εpos : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), ε > 0 :=
    eventually_mem_of_tendsto_nhdsWithin fun ⦃U⦄ hU ↦ hU
  filter_upwards [hC, εpos] with ε hC εpos
  rw[id_eq, norm_of_nonneg (le_of_lt εpos)] at hC
  intro X Xnne
  nth_rw 2 [← one_mul (X : ℂ)]
  rw[← sub_mul, norm_mul, norm_real, norm_of_nonneg Xnne]
  exact mul_le_mul_of_nonneg_right hC Xnne

theorem norm_reciprocal_inequality_1 (x : ℝ) (x₁ : ℝ) (hx₁ : x₁ ≥ 1) :
  ‖x^2 + x₁^2‖₊⁻¹ ≤ (‖x₁‖₊^2)⁻¹ := by
                                                
  have h1 : x₁^2 ≥ 1 := by
    have h_abs : |x₁| ≥ 1 := by
      rw [abs_of_pos]
      linarith
      positivity
    simp only [ge_iff_le, one_le_sq_iff_one_le_abs, h_abs]

  have h2 : x^2 + x₁^2 ≥ x₁^2 := by
    linarith [sq_nonneg x]

  have h3 : x₁^2 > 0 := by
    apply sq_pos_of_ne_zero
    linarith

  have h33 : 2 * x₁^2 > 0 := by
    simp [*]

  have h4 : x^2 + x₁^2 > 0 := by
    linarith [sq_nonneg x, h3]

  have h5 : x₁^2 ≤ x^2 + x₁^2 := h2

  have h6 : ‖x₁^2‖₊ = ‖x₁‖₊^2 := by
    rw [nnnorm_pow]

  have h7 : ‖x^2 + x₁^2‖₊ = x^2 + x₁^2 := by
    rw [Real.nnnorm_of_nonneg (le_of_lt h4)]
    norm_cast

  rw [← NNReal.coe_le_coe]
  push_cast
  simp [*]
  simp_all
  rw [abs_of_nonneg]
  · have U := inv_le_inv₀ h4 h3
    rw [U]
    simp [*]

  · positivity

theorem norm_reciprocal_inequality (x : ℝ) (x₁ : ℝ) (hx₁ : x₁ ≤ -1) :
  ‖x^2 + x₁^2‖₊⁻¹ ≤ (‖x₁‖₊^2)⁻¹ := by
                                                
  have h1 : x₁^2 ≥ 1 := by
    have h_abs : |x₁| ≥ 1 := by
      rw [abs_of_nonpos (le_of_lt (lt_of_le_of_lt hx₁ (by norm_num : (-1 : ℝ) < 0)))]
      linarith
    simp only [ge_iff_le, one_le_sq_iff_one_le_abs, h_abs]

  have h2 : x^2 + x₁^2 ≥ x₁^2 := by
    linarith [sq_nonneg x]

  have h3 : x₁^2 > 0 := by
    apply sq_pos_of_ne_zero
    linarith

  have h33 : 2 * x₁^2 > 0 := by
    simp [*]

  have h4 : x^2 + x₁^2 > 0 := by
    linarith [sq_nonneg x, h3]

  have h5 : x₁^2 ≤ x^2 + x₁^2 := h2

  have h6 : ‖x₁^2‖₊ = ‖x₁‖₊^2 := by
    rw [nnnorm_pow]

  have h7 : ‖x^2 + x₁^2‖₊ = x^2 + x₁^2 := by
    rw [Real.nnnorm_of_nonneg (le_of_lt h4)]
    norm_cast

  rw [← NNReal.coe_le_coe]
  push_cast
  simp [*]
  simp_all
  rw [abs_of_nonneg]
  · have U := inv_le_inv₀ h4 h3
    rw [U]
    simp [*]

  · positivity

theorem poisson_kernel_integrable (x : ℝ) (hx : x ≠ 0) :
  MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
                                     
  have h1 : ∀ t : ℝ, ‖x + t * I‖^2 = x^2 + t^2 := by
    intro t
    rw [Complex.norm_add_mul_I, Real.sq_sqrt]
    positivity
                                                    
  have h2 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) = (fun (t : ℝ) ↦ (x^2 + t^2)⁻¹) := by
    ext t
    rw [h1]
  rw [h2]
                                                 
  have h3 : ∀ t : ℝ, x^2 + t^2 > 0 := by
    intro t
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_ne_zero hx
    · exact sq_nonneg t
                                          
  have h4 : Continuous (fun t : ℝ ↦ (x^2 + t^2)⁻¹) := by
    apply Continuous.inv₀
    · exact continuous_const.add (continuous_pow 2)
    · intro t
      exact ne_of_gt (h3 t)

  have integrable_on_bounded : ∀ R > 0, MeasureTheory.IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Icc (-R) R) := by
    intro R hR
    refine ContinuousOn.integrableOn_Icc ?_
    · exact Continuous.continuousOn h4

  have decay_bound : ∀ t : ℝ, 0 < |t| → (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro t hyp_t
    rw [←inv_le_inv₀]
    simp_all only [ne_eq, gt_iff_lt, abs_pos, inv_inv, le_add_iff_nonneg_left]
    · positivity
    · simp_all only [ne_eq, gt_iff_lt, abs_pos, inv_pos]
      positivity
    · positivity

  have decay_bound_1 : ∀ x_1 ≤ -1, ‖x ^ 2 + x_1 ^ 2‖₊⁻¹ ≤ (‖x_1‖₊ ^ 2)⁻¹ := by
    exact norm_reciprocal_inequality x

  have decay_bound_2 : ∀ (x_1 : ℝ), 1 ≤ x_1 → ‖x ^ 2 + x_1 ^ 2‖₊⁻¹ ≤ (‖x_1‖₊ ^ 2)⁻¹ := by
    exact norm_reciprocal_inequality_1 x

  have f_int_1 : IntegrableOn (fun (t : ℝ) ↦ (t^2)⁻¹) (Set.Iic (-1)) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff,
      Nat.one_lt_ofNat]
    have D2 : 0 < (1 : ℝ) := by simp only [zero_lt_one]
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat,
            zero_lt_one, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton,
            EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat, zero_lt_one,
      rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow, Int.reduceNegSucc, Int.cast_neg, Int.cast_one]
    exact D4

  have f_int_2 : IntegrableOn (fun (t : ℝ) ↦ (t^2)⁻¹) (Set.Ici 1) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff,
      Nat.one_lt_ofNat]
    have D2 : 0 < (1 : ℝ) := by simp only [zero_lt_one]
    have D3 := integrableOn_Ioi_rpow_of_lt D1 D2
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg] at D3
    have D4 :=
      (integrableOn_Ici_iff_integrableOn_Ioi'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat,
            zero_lt_one, measure_singleton, EReal.coe_ennreal_zero, EReal.coe_ennreal_top,
            EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat, zero_lt_one]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4

  have int_neg : IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Iic (-1)) volume := by
    have h_le : ∀ t ∈ Set.Iic (-1), (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
      intro t ht
      simp only [Set.mem_Iic] at ht
                                                    
      have t_neg : t < 0 := lt_of_le_of_lt ht (by norm_num : (-1 : ℝ) < 0)
      exact decay_bound t (abs_pos.mpr (ne_of_lt t_neg))
    have h_meas : AEStronglyMeasurable (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Set.Iic (-1))) := by
      exact Continuous.aestronglyMeasurable h4

    unfold IntegrableOn
    unfold Integrable
    constructor
    · exact h_meas
    · have Z : HasFiniteIntegral (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Iic (-1))) := by
        refine MeasureTheory.HasFiniteIntegral.mono'_enorm f_int_1.2 ?_
        · unfold Filter.Eventually
          simp only [measurableSet_Iic, ae_restrict_eq, nnnorm_inv, nnnorm_pow, enorm_le_coe]
          refine mem_inf_of_right ?_
          · refine mem_principal.mpr ?_
            · rw [Set.subset_def]
              simp only [mem_Iic, mem_ofPred_eq]
              exact decay_bound_1

      exact Z

  have int_pos : IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Ici 1) volume := by
    have h_le : ∀ t ∈ Set.Ici 1, (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
      intro t ht
      simp only [Set.mem_Ici] at ht
                                                   
      have t_pos : t > 0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht
      exact decay_bound t (abs_pos.mpr (ne_of_gt t_pos))
    have h_meas : AEStronglyMeasurable (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Set.Ici 1)) := by
      exact Continuous.aestronglyMeasurable h4

    unfold IntegrableOn
    unfold Integrable
    constructor
    · exact h_meas
    · have Z : HasFiniteIntegral (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Ici (1))) := by
        refine MeasureTheory.HasFiniteIntegral.mono'_enorm f_int_2.2 ?_
        · unfold Filter.Eventually
          simp only [measurableSet_Ici, ae_restrict_eq, nnnorm_inv, nnnorm_pow, enorm_le_coe]
          refine mem_inf_of_right ?_
          · refine mem_principal.mpr ?_
            · rw [Set.subset_def]
              simp only [mem_Ici, mem_ofPred_eq]
              exact decay_bound_2

      exact Z

  have split : Set.univ = Set.Iic (-1) ∪ Set.Icc (-1) 1 ∪ Set.Ici 1 := by
    ext t
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici, true_iff]
    by_cases h : t ≤ -1
    · left; left; exact h
    · by_cases h' : t ≥ 1
      · right; exact h'
      · left; right; constructor <;> linarith

  have Z :=
    MeasureTheory.IntegrableOn.union
      (MeasureTheory.IntegrableOn.union
          (int_neg)
          (integrable_on_bounded 1 zero_lt_one))
      (int_pos)

  simp_all only [ne_eq, gt_iff_lt, abs_pos, Int.reduceNeg, neg_le_self_iff, zero_le_one, Iic_union_Icc_eq_Iic,
  Iic_union_Ici, integrableOn_univ]

theorem ae_volume_of_contains_compl_singleton_zero                                                                             
  (s : Set ℝ)
  (h : (univ : Set ℝ) \ {0} ⊆ s) :
  s ∈ (MeasureTheory.ae volume) := by
                                                      
  have h_zero_null : volume ({0} : Set ℝ) = 0 := by
    exact volume_singleton

  have h_compl_subset : sᶜ ⊆ {0} := by
    intro x hx

    by_contra h_not_zero
    have : x ∈ univ \ {0} := ⟨trivial, h_not_zero⟩
    exact hx (h this)

  have h_compl_measure : volume sᶜ ≤ volume ({0} : Set ℝ) :=
    measure_mono h_compl_subset

  have h_compl_zero : volume sᶜ = 0 := by
    rw [h_zero_null] at h_compl_measure
    exact le_antisymm h_compl_measure zero_le

  rwa [mem_ae_iff]

theorem integral_evaluation (x : ℝ) (T : ℝ)
  : (3 < T) → ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by

  intro T_large

  have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
    intro x t
    rw [Complex.norm_add_mul_I x t]
    ring_nf
    rw [Real.sq_sqrt _]
    simp only [le_add_iff_nonneg_right]; positivity
    positivity

  have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro x t hyp
    have U0 : 0 < t^2 := by positivity
    have U1 : 0 < ‖x + t * I‖^2 := by
      rw [Complex.norm_add_mul_I x t]
      rw [Real.sq_sqrt _]
      positivity
      positivity
    rw [inv_le_inv₀ U1 U0]
    exact (T00 x t)

  have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    refine mem_inf_of_left ?_
    · refine Filter.mem_sets.mp ?_
      · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
          rw [Set.ofPred_subset_ofPred]
          intro t hyp_t
          exact T0 x t hyp_t
        have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
          apply Set.ext
          intro x
          simp_all only [ne_eq, ofPred_subset_ofPred, not_false_eq_true, implies_true, mem_ofPred_eq, Set.mem_sdiff, mem_univ,
  mem_singleton_iff, true_and]

        rw [U1] at U
        have Z := ae_volume_of_contains_compl_singleton_zero
          ({x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹} : Set ℝ) U
        exact Z

  have T2 : 0 ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, Pi.zero_apply, inv_nonneg, norm_nonneg, pow_nonneg,
  ofPred_true, univ_mem]

  have T4 : deriv (fun (t : ℝ) ↦ t⁻¹) = (fun t ↦ (- (t^2)⁻¹)) := by
    exact deriv_inv'

  have hcont : ContinuousWithinAt (fun t ↦ t⁻¹) (Set.Iic (-T)) (-T) := by
    refine ContinuousWithinAt.inv₀ ?_ ?_
    · exact ContinuousAt.continuousWithinAt fun ⦃U⦄ a ↦ a
    · intro hyp
      linarith

  have hderiv : ∀ x ∈ Set.Iio (-T), HasDerivAt (fun t ↦ t⁻¹) ((fun t ↦ - (t^2)⁻¹) x) x := by
                                                                                    
    intro x hx
                                            
    have hx_ne_zero : x ≠ 0 := by
      intro h
      rw [h] at hx
      simp [Set.Iio] at hx
      linarith
                                                    
    convert hasDerivAt_inv hx_ne_zero

  have f'int : IntegrableOn (fun t ↦ - (t^2)⁻¹) (Set.Iic (-T)) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp only [neg_lt_neg_iff, Nat.one_lt_ofNat]
    have D2 : 0 < T := by positivity
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
              
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp [*] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, neg_lt_neg_iff,
  Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton, EReal.coe_ennreal_zero,
  EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, neg_lt_neg_iff,
  Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
                       
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]

    simp_all only [even_two, Even.neg_pow]
    have D6 := MeasureTheory.integrable_neg_iff.mpr D4
    have eq_fun : (-fun x ↦ (x^2)⁻¹) = (fun (x : ℝ) ↦ - (x^2)⁻¹) := by
      funext x
      simp only [Pi.neg_apply]
    rw [eq_fun] at D6
    exact D6

  have hf : Filter.Tendsto (fun (t : ℝ) ↦ t⁻¹) Filter.atBot (nhds 0) := by exact
    tendsto_inv_atBot_zero

  have T5 : ∫ (t : ℝ) in Iic (-T), - (t^2)⁻¹ = (-T)⁻¹ - 0 := by
    exact MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto hcont hderiv f'int hf

  have T6 : ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹ = T⁻¹ := by
    simp only [inv_neg, sub_zero] at T5
    have D6 : - ∫ (t : ℝ) in Iic (-T), - (t^2)⁻¹ =  ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹ := by
      simp only [integral_neg fun a ↦ (a ^ 2)⁻¹, neg_neg]

    rw [←D6]
    rw [T5]
    simp only [neg_neg]

  have T3 : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Iic (-T))) := by
              
    have D1 : (-2) < (-1 : ℝ) := by simp only [neg_lt_neg_iff, Nat.one_lt_ofNat]
    have D2 : 0 < T := by positivity
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
              
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, inv_neg, sub_zero,
  neg_lt_neg_iff, Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton, EReal.coe_ennreal_zero,
  EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, inv_neg, sub_zero,
  neg_lt_neg_iff, Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
                       
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow]

  have Z :=
    by
      calc
        ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹  := by
          exact MeasureTheory.integral_mono_of_nonneg T2 T3 T1

        _ = T⁻¹ := by exact T6

  exact Z

theorem integral_evaluation' (x : ℝ) (T : ℝ)
  : (3 < T) → ∫ (t : ℝ) in Ici (T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
  intro T_large

  have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
    intro x t
    rw [Complex.norm_add_mul_I x t]
    ring_nf
    rw [Real.sq_sqrt _]
    simp only [le_add_iff_nonneg_right]; positivity
    positivity

  have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro x t hyp
    have U0 : 0 < t^2 := by positivity
    have U1 : 0 < ‖x + t * I‖^2 := by
      rw [Complex.norm_add_mul_I x t]
      rw [Real.sq_sqrt _]
      positivity
      positivity
    rw [inv_le_inv₀ U1 U0]
    exact (T00 x t)

  have T2 : 0 ≤ᶠ[ae (volume.restrict (Ioi T))] (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, Pi.zero_apply, inv_nonneg, norm_nonneg, pow_nonneg,
  ofPred_true, univ_mem]

  have T3 : Integrable (fun (t : ℝ) ↦ - (t^2)⁻¹) (volume.restrict (Ioi T)) := by
    have D1 : (-2) < (-1 : ℝ) := by simp only [neg_lt_neg_iff, Nat.one_lt_ofNat]
    have D2 : 0 < T := by positivity
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg] at D
    exact MeasureTheory.Integrable.fun_neg D

  have T3' : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Ioi T)) := by
    have D := MeasureTheory.Integrable.fun_neg T3
    simp_all only [ne_eq, measurableSet_Ioi, ae_restrict_eq, neg_neg]

  have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Ioi T))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Ioi, ae_restrict_eq]
    refine mem_inf_of_left ?_
    · refine Filter.mem_sets.mp ?_
      · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
          rw [Set.ofPred_subset_ofPred]
          intro t hyp_t
          exact T0 x t hyp_t
        have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
          apply Set.ext
          intro x
          simp_all only [ne_eq, ofPred_subset_ofPred, not_false_eq_true, implies_true, mem_ofPred_eq, Set.mem_sdiff, mem_univ,
  mem_singleton_iff, true_and]

        rw [U1] at U
        have Z := ae_volume_of_contains_compl_singleton_zero
          ({x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹} : Set ℝ) U
        exact Z

  have hcont : ContinuousWithinAt (fun t ↦ t⁻¹) (Set.Ici T) T := by
    refine ContinuousWithinAt.inv₀ ?_ ?_
    · exact ContinuousAt.continuousWithinAt fun ⦃U⦄ a ↦ a
    · intro hyp
      linarith

  have hderiv : ∀ x ∈ Set.Ioi T, HasDerivAt (fun t ↦ t⁻¹) ((fun t ↦ - (t^2)⁻¹) x) x := by
                                                                                    
    intro x hx
                                            
    have hx_ne_zero : x ≠ 0 := by
      intro h
      rw [h] at hx
      simp at hx
      linarith
                                                    
    convert hasDerivAt_inv hx_ne_zero

  have hf : Filter.Tendsto (fun (t : ℝ) ↦ t⁻¹) Filter.atTop (nhds 0) := by exact
    tendsto_inv_atTop_zero

  have T5 : ∫ (t : ℝ) in Ioi T, (t^2)⁻¹ = (T)⁻¹ - 0 := by
    have U := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv T3 hf
    simp [*] at U
    rw [MeasureTheory.integral_neg] at U
    simp_all only [ne_eq, mem_Ioi, neg_inj, sub_zero]

  have T6 : ∫ (t : ℝ) in Ioi T, (t^2)⁻¹ = T⁻¹ := by
    simp only [sub_zero] at T5
    have D6 : - ∫ (t : ℝ) in Ioi T, - (t^2)⁻¹ =  ∫ (t : ℝ) in Ioi T, (t^2)⁻¹ := by
      simp only [integral_neg fun a ↦ (a ^ 2)⁻¹, neg_neg]

    rw [←D6]
    rw [←T5]
    exact D6

  have Z :=
    by
      calc
        ∫ (t : ℝ) in Ioi T, (‖x + t * I‖ ^ 2)⁻¹ ≤ ∫ (t : ℝ) in Ioi T, (t^2)⁻¹  := by
          exact MeasureTheory.integral_mono_of_nonneg T2 T3' T1

        _ = T⁻¹ := by exact T6

  rw [←MeasureTheory.integral_Ici_eq_integral_Ioi] at Z

  exact Z

lemma IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) (k : ℕ) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
                                          
  have ⟨M, hM⟩ := Filter.eventually_atTop.mp (isLittleO_log_rpow_rpow_atTop k zero_lt_one).eventuallyLE
                                                    
  let f := fun X ↦ Real.log X ^ k / X
  let I1 := Icc X₀ M
  have : 0 ∉ I1 := notMem_Icc_of_lt X₀pos
  have f_cont : ContinuousOn f (Icc X₀ M) :=
    ((continuousOn_log.pow k).mono (subset_compl_singleton_iff.mpr this)).div
    continuous_id.continuousOn (fun x hx ↦ ne_of_mem_of_not_mem hx this)
  have ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn f_cont
  use max C₁ 1, le_max_right C₁ 1
  intro X hX
  have Xpos : X > 0 := lt_of_lt_of_le X₀pos hX
  by_cases hXM : X ≤ M
  · rw[← div_le_iff₀ Xpos]
    calc
      f X ≤ ‖f X‖ := le_norm_self _
      _ ≤ C₁ := hC₁ X ⟨hX, hXM⟩
      _ ≤ max C₁ 1 := le_max_left C₁ 1
  · calc
      Real.log X ^ k ≤ ‖Real.log X ^ k‖ := le_norm_self _
      _ ≤ ‖X ^ 1‖ := by exact_mod_cast hM X (by linarith[hXM])
      _ = 1 * X := by
        rw[pow_one, one_mul]
        apply norm_of_nonneg
        exact Xpos.le
      _ ≤ max C₁ 1 * X := by
        rw[mul_le_mul_iff_left₀ Xpos]
        exact le_max_right C₁ 1

theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by

  obtain ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  have G0 : ∃K > 0, ∀(t σ : ℝ), 1 < σ → σ < 2 → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    let ⟨K', ⟨K'_pos, K'_bounds_zeta⟩⟩ := strongPnt_triv_bound_zeta
    use (2 * (K' + 1))
    use (by positivity)
    intro t σ cond cond2

    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
  norm_neg, tsub_le_iff_right, inv_one]

    have T : (K' + 1) * 1 ≤ (K' + 1) * (σ - 1)⁻¹ :=
      by
        exact (mul_le_mul_iff_right₀ T0).mpr T1
    have T2 : (K' + 1) ≤ (K' + 1) * (σ - 1)⁻¹ := by
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
  norm_neg, mul_one, le_mul_iff_one_le_right]

    have U := calc
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by
        rw [← norm_neg _, mul_comm, neg_div' _ _]
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds_zeta σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by linarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by
        ring_nf

    exact U

  obtain ⟨K, ⟨K_is_pos, K_bounds_zeta_at_any_t'⟩⟩ := G0

  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity

  use (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M))
  use C_final_pos

  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)

  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := by
    intro t
    unfold pts
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]

  have pts_re_ge_one : 1 < pts_re := by
    unfold pts_re
    simp only [lt_add_iff_pos_right, inv_pos]
    have U : 1 < X := by linarith
    exact Real.log_pos U

  have pts_re_le_one : pts_re < 2 := by
    unfold pts_re
    have Z0 : 3 ∈ {x : ℝ | 1 ≤ x} := by
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt, Complex.norm_div,
  mem_ofPred_eq, Nat.one_le_ofNat]
    have Z1 : X ∈ {x : ℝ | 1 ≤ x} := by
      simp only [mem_ofPred_eq]
      linarith
    have Z : Real.log 3 < Real.log X :=
      by
        refine log_lt_log ?_ X_large
        simp only [Nat.ofNat_pos]

    have Z01 : 1 < Real.log 3  :=
      by
        have Z001 : 1 = Real.log (rexp 1) := by exact Eq.symm (Real.log_exp 1)
        rw [Z001]
        have Z002 : (0 : ℝ) < rexp 1 := by positivity
        have Z003 : (0 : ℝ) < 3 := by positivity
        have Z004 : rexp 1 < 3 := by
          calc
            rexp 1 < (↑ 2.7182818286 : ℚ) := Real.exp_one_lt_d9
            _ < (↑ 3 : ℚ) := by linarith

        exact (Real.log_lt_log_iff Z002 Z003).mpr Z004

    have Zpos0 : 0 < Real.log 3 := by positivity
    have Zpos1 : 0 < Real.log X := by calc
      0 < Real.log 3 := Zpos0
      _ < Real.log X := Z

    have Z1 : (Real.log X)⁻¹ < (Real.log 3)⁻¹ :=
      by
        exact (inv_lt_inv₀ Zpos1 Zpos0).mpr Z

    have Z02 : (Real.log 3)⁻¹ < 1 := by
      have T01 := (inv_lt_inv₀ ?_ ?_).mpr Z01
      simp only [inv_one] at T01
      exact T01
      exact Zpos0
      simp only [zero_lt_one]

    have Z2 : 1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := by
      exact (add_lt_add_iff_left 1).mpr Z1

    have Z3 : 1 + (Real.log 3)⁻¹ < 2 := by
      calc
        1 + (Real.log 3)⁻¹ < 1 + 1 := by linarith
        _ = 2 := by ring_nf

    calc
      1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := Z2
      _ < 2 := Z3

  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    unfold pts_re
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, add_sub_cancel_left, inv_inv]

  have K_bounds_zeta_at_any_t : ∀(t : ℝ), ‖ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
    intro t
    rw [←inve]
    exact K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by
    unfold pts_re
    positivity

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := by
    intro t
    unfold pts_re
    exact Eq.ge (pts_re_triv t)

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 := by
    intro t
    unfold pts
    refine EReal.coe_le_coe_iff.mp ?_
    · simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, le_refl, implies_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, EReal.coe_le_coe_iff]
      exact le_of_lt pts_re_le_one

  have pts_re_ge_1 : pts_re > 1 := by
    unfold pts_re
    exact pts_re_ge_one

  have X_pos_triv : 0 < X := by positivity

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by

    intro t

    let M_bounds_mellin_easy := fun (t : ℝ) ↦ M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t) (triv_pts_up_bound t) eps eps_pos eps_less_one

    let zeta_part := (fun (t : ℝ) ↦ -ζ' (pts t) / ζ (pts t))
    let mellin_part := (fun (t : ℝ) ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF eps x)) (pts t))
    let X_part := (fun (t : ℝ) ↦ (↑X : ℂ) ^ (pts t))

    let g := fun (t : ℝ) ↦ (zeta_part t) * (mellin_part t) * (X_part t)

    have X_part_eq : ∀(t : ℝ), ‖X_part t‖ = X^pts_re := by
      intro t
      have U := Complex.norm_cpow_eq_rpow_re_of_pos (X_pos_triv) (pts t)
      rw [pts_re_triv t] at U
      exact U

    have X_part_bound : ∀(t : ℝ), ‖X_part t‖ ≤ X^pts_re := by
      intro t
      rw [←X_part_eq]

    have mellin_bound : ∀(t : ℝ), ‖mellin_part t‖ ≤ M * (eps * ‖pts t‖ ^ 2)⁻¹ := by
      intro t
      exact M_bounds_mellin_easy t

    have X_part_and_mellin_bound : ∀(t : ℝ),‖mellin_part t * X_part t‖ ≤ M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
      intro t
      exact norm_mul_le_of_le (mellin_bound t) (X_part_bound t)

    have T2 : ∀(t : ℝ), ‖zeta_part t‖ = ‖ζ' (pts t) / ζ (pts t)‖ := by
      intro t
      unfold zeta_part
      simp only [Complex.norm_div, norm_neg]

    have zeta_bound : ∀(t : ℝ), ‖zeta_part t‖ ≤ K * Real.log X := by
      intro t
      unfold zeta_part
      rw [T2]
      exact K_bounds_zeta_at_any_t t

    have g_bound : ∀(t : ℝ), ‖zeta_part t * (mellin_part t * X_part t)‖ ≤ (K * Real.log X) * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      intro t
      exact norm_mul_le_of_le (zeta_bound t) (X_part_and_mellin_bound t)

    have T1 : f = g := by rfl

    have final_bound_pointwise : ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      rw [T1]
      unfold g
      rw [mul_assoc]
      exact g_bound t

    have trivialize : K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) = (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
            ring_nf

    rw [trivialize] at final_bound_pointwise
    exact final_bound_pointwise

  have σ₀_gt : 1 < pts_re := by exact pts_re_ge_1
  have σ₀_le_2 : pts_re ≤ 2 := by
    unfold pts_re
           
    exact
      Preorder.le_trans (1 + (Real.log X)⁻¹) (pts (SmoothingF (SmoothingF M))).re 2
        (triv_pts_lo_bound (SmoothingF (SmoothingF M))) (triv_pts_up_bound (SmoothingF (SmoothingF M)))

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large σ₀_gt σ₀_le_2 suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    unfold pts_re

    calc
      X ^ (1 + (Real.log X)⁻¹) = X * X ^ ((Real.log X)⁻¹) := by
        refine rpow_one_add' ?_ ?_
        · positivity
        · exact Ne.symm (ne_of_lt pts_re_pos)
      _ = X * rexp 1 := by
        refine (mul_right_inj' ?_).mpr ?_
        · exact Ne.symm (ne_of_lt X_pos_triv)
        · refine rpow_inv_log X_pos_triv ?_
          · by_contra h
            simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
              Complex.norm_div, Nat.not_ofNat_lt_one]
      _ = rexp 1 * X := by ring_nf

  have pts_re_neq_zero : pts_re ≠ 0 := by
    by_contra h
    rw [h] at pts_re_ge_1
    simp only [gt_iff_lt] at pts_re_ge_1
    norm_cast at pts_re_ge_1

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Iic (-T), f t‖ ≤ ∫ (t : ℝ) in Iic (-T), ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Iic (-T), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono ?_ ?_ (fun t ↦ G t)
            · refine Integrable.norm ?_
              · unfold f
                exact MeasureTheory.Integrable.restrict f_integrable
            · have equ : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹ := by
                   intro t; ring_nf
              have fun_equ : (fun (t : ℝ) ↦ ((K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re)) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹)) := by
                   funext t
                   exact equ t

              rw [fun_equ]
              have nonzero := ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              have simple_int : MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
                := by
                   unfold pts
                   exact poisson_kernel_integrable pts_re (pts_re_neq_zero)

              have U := MeasureTheory.Integrable.const_mul simple_int ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              refine MeasureTheory.Integrable.restrict ?_
              exact U
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * ∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹ := by
              have simpli : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹ :=
                by intro t; ring_nf
              have simpli_fun : (fun (t : ℝ) ↦ (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re ) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹)) :=
                by funext t; ring_nf
              rw [simpli_fun]
              exact MeasureTheory.integral_const_mul ((K * M) * Real.log X * X ^ pts_re * eps⁻¹) (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ := by
              have U := integral_evaluation (pts_re) T (T_large)
              unfold pts
              simp only [ge_iff_le]
              have U2 : 0 ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ := by
                simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
                  Complex.norm_div, le_refl, implies_true, inv_pos, mul_nonneg_iff_of_pos_right]
                refine Left.mul_nonneg ?_ ?_
                · refine Left.mul_nonneg ?_ ?_
                  · exact Left.mul_nonneg (by positivity) (by positivity)
                  · refine log_nonneg ?_
                    · linarith
                · refine Left.mul_nonneg ?_ ?_
                  · exact exp_nonneg 1
                  · exact le_of_lt X_pos_triv
              have U1 := mul_le_mul_of_nonneg_left U U2

              exact U1
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf

  unfold I₁
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 :=
    mul_le_mul_of_nonneg_left Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4

lemma I9I1 {SmoothingF : ℝ → ℝ} {ε X T : ℝ} (Xpos : 0 < X) :
    I₉ SmoothingF ε X T = conj (I₁ SmoothingF ε X T) := by
  unfold I₉ I₁
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun <| measurableSet_Ioi
    intro t ht
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp

theorem I9Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
  obtain ⟨C, Cpos, bound⟩ := I1Bound suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]

lemma one_add_inv_log {X : ℝ} (X_ge : 3 ≤ X): (1 + (Real.log X)⁻¹) < 2 := by
  rw[← one_add_one_eq_two]
  refine (add_lt_add_iff_left 1).mpr ?_
  refine inv_lt_one_of_one_lt₀ ?_
  refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> linarith[Real.exp_one_lt_d9]

theorem log_pos (T : ℝ) (T_gt : 3 < T) : (Real.log T > 1) := by
    have elt3 : Real.exp 1 < 3 := by
      linarith[Real.exp_one_lt_d9]
    have logTgt1 : Real.log T > 1 := by
      refine (lt_log_iff_exp_lt ?_).mpr ?_
      · linarith
      · linarith
    exact logTgt1

lemma I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
                                                     
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound: LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ := sigma1Of A T
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) 9)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
                                                    
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  have log_big : 1 < Real.log T := by exact log_pos T (T_gt)
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    have : σ₁ = sigma1Of A T := rfl
    rw [this]
    unfold sigma1Of
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_right
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      exact A_in.1.le
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have : σ₁ = sigma1Of A T := rfl
  have σ₁pos : 0 < σ₁ := by
    have : σ₁ = sigma1Of A T := rfl
    rw [this]
    unfold sigma1Of
    rw[sub_pos]
    calc
      A / Real.log T ≤ 1 / 2 / Real.log T := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply le_of_lt
        linarith
                                                          
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        apply le_of_lt
        refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> linarith[Real.exp_one_lt_d9]
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹), ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro σ hσ
        rw [uIoc_of_le interval_length_nonneg] at hσ
        exact this σ hσ
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
        calc
          1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
          _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
                            
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ 9 := has_bound σ (-T) (by simp; rw [abs_of_pos Tpos]; exact T_gt) (by rw[this] at hσ; unfold sigma1Of at hσ; simp at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ 9 := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero] at hσ ⊢
          linarith[one_add_inv_log X_gt.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero]
          rw[← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
          exact hσ.2
          · refine (Real.log_pos ?_).ne.symm
            linarith
          · apply Real.log_pos
            linarith
          · linarith
          · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          exact this
          exact ε_pos
          positivity
          apply mul_pos ε_pos
          exact lt_of_lt_of_le (pow_pos Tpos 2) this
          positivity
        _ = C' * X / (ε * T) := by
          field_simp

lemma I8I2 {SmoothingF : ℝ → ℝ}
    {X ε T σ₁ : ℝ} (T_gt : 3 < T) :
    I₈ SmoothingF ε X T σ₁ = -conj (I₂ SmoothingF ε X T σ₁) := by
  unfold I₂ I₈
  rw[map_mul, ← neg_mul]
  congr
  · simp[conj_ofNat]
  · rw[← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw[← smoothedChebyshevIntegrand_conj]
    simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    exact lt_trans (by norm_num) T_gt

lemma I8Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
                                                       
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by

  obtain ⟨C, hC, i2Bound⟩ := I2Bound suppSmoothingF ContDiffSmoothingF has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
            
  change ‖I₂ SmoothingF ε T X (sigma1Of A T)‖ ≤ C * X / (ε * T) at i2Bound
  unfold sigma1Of at i2Bound
  have σ₁_eq : σ₁ = 1 - A / (Real.log T) := rfl
  rw[σ₁_eq]
  exact i2Bound

lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ T >3, ∫ x in Ioo 3 T, (Real.log x)^n / x^2 < C := by
  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]
  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3
  intro n
  induction n with
  | zero =>
    use 1
    constructor
    · norm_num
    · intro T hT
      have Tgt3 : (3 : ℝ) < T := hT
      simp only [pow_zero]
      have h1 :(0 ≤ (-2) ∨ (-2) ≠ (-1) ∧ 0 ∉ Set.uIcc 3 T) := by
        right
        constructor
        · linarith
        · refine notMem_uIcc_of_lt ?_ ?_
          · exact three_pos
          · linarith
      have integral := integral_zpow h1
      ring_nf at integral

      have swap_int_kind : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), 1 / x ^ 2 = ∫ (x : ℝ) in Ioo 3 T, 1 / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      rw [← swap_int_kind]
      have change_int_power : ∫ (x : ℝ) in (3 : ℝ)..T, (1 : ℝ) / x ^ (↑ 2)
                            = ∫ (x : ℝ) in (3 : ℝ).. T, x ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp
      rw [change_int_power, integral]
      have : T ^ (-1 : ℤ) > 0 := by
        refine zpow_pos ?_ (-1)
        linarith
      linarith
  | succ d ih =>
    obtain ⟨Cd, Cdpos, IH⟩ := ih
    use ((Real.log 3)^(d+1) / 3) + (d+1) * Cd
    constructor
    · have logpowpos : (Real.log 3) ^ (d + 1) > 0 := by
        refine pow_pos ?_ (d + 1)
        linarith
      have :  0 < (Real.log 3) ^ (d + 1) / 3 := by
        exact div_pos logpowpos (by norm_num)
      have dbound : d + 1 ≥ 1 := by
        exact Nat.le_add_left 1 d
      have : Real.log 3 ^ (d + 1) / 3 + (↑d + 1) * Cd > 0 / 3 + 0 := by
        have term1_pos : 0 < Real.log 3 ^ (d + 1) / 3 := this
        have term2_pos : 0 < (↑d + 1) * Cd := by
          refine (mul_pos_iff_of_pos_right Cdpos).mpr ?_
          exact Nat.cast_add_one_pos d
        refine add_lt_add ?_ term2_pos
        refine div_lt_div₀ logpowpos ?_ ?_ ?_
        linarith
        linarith
        linarith
      ring_nf at this
      ring_nf
      exact this
    · intro T Tgt3
      let u := fun x : ℝ ↦ (Real.log x) ^ (d + 1)
      let v := fun x : ℝ ↦ -1 / x
      let u' := fun x : ℝ ↦ (d + 1 : ℝ) * (Real.log x)^d / x
      let v' := fun x : ℝ ↦ 1 / x^2

      have swap_int_type : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2
                          = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ (d + 1) / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw [← swap_int_type]

      have uIcc_is_Icc : Set.uIcc 3 T = Set.Icc 3 T := by
        exact uIcc_of_lt Tgt3

      have cont_u : ContinuousOn u (Set.uIcc 3 T) := by
        unfold u
        rw[uIcc_is_Icc]
        refine ContinuousOn.pow ?_ (d + 1)
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        refine continuousAt_log ?_
        linarith [hx.1]

      have cont_v : ContinuousOn v (Set.uIcc 3 T) := by
        unfold v
        rw[uIcc_is_Icc]
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        have cont1 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) x := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have cont2 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) (-x) := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have fun1 : (fun (x : ℝ) ↦ -1 / x) = (fun (x : ℝ) ↦ 1 / (-x)) := by
          ext x
          ring_nf
        rw [fun1]
        exact ContinuousAt.comp cont2 (HasDerivAt.neg (hasDerivAt_id x)).continuousAt

      have deriv_u : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt u (u' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        unfold u u'
        have xne0 : x ≠ 0 := by linarith [hx.1]
        have deriv1 := Real.deriv_log x
        have deriv2 := (Real.hasDerivAt_log xne0).pow (d + 1)
        have fun1 : (fun x ↦ (↑d + 1) * Real.log x ^ d / x) = (fun x ↦ (↑d + 1) * Real.log x ^ d * x⁻¹) := by
          exact rfl
        have fun2 : (↑d + 1) * Real.log x ^ d / x =  (↑d + 1) * Real.log x ^ d * x⁻¹:= by
          exact rfl
        rw [fun2]
        simpa [Nat.cast_add, Nat.cast_one] using! deriv2

      have deriv_v : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt v (v' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        have xne0 : x ≠ 0 := by linarith [hx.1]
        unfold v v'
        have deriv1 := hasDerivAt_inv xne0
        have fun1 : (fun (x : ℝ) ↦ x⁻¹) = (fun (x : ℝ) ↦ 1 / x) := by
          ext x
          exact inv_eq_one_div x
        rw [fun1] at deriv1
        have fun2 : -(x ^ 2)⁻¹ = - 1 / x ^ 2 := by
          field_simp
        rw [fun2] at deriv1
        simpa [neg_div, neg_neg] using! HasDerivAt.neg deriv1

      have cont_u' : ContinuousOn u' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold u'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · refine ContinuousOn.mul ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.pow ?_ d
            refine continuousOn_of_forall_continuousAt ?_
            intro x hx
            refine continuousAt_log ?_
            linarith [hx.1]
        · exact continuousOn_id' (Icc 3 T)
        · intro x hx
          linarith [hx.1]

      have cont_v' : ContinuousOn v' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold v'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · exact continuousOn_const
        · exact continuousOn_pow 2
        · intro x hx
          refine pow_ne_zero 2 ?_
          linarith [hx.1]

      have int_u': IntervalIntegrable u' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_u'

      have int_v': IntervalIntegrable v' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_v'

      have IBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt cont_u cont_v deriv_u deriv_v int_u' int_v'

      unfold u u' v v' at IBP

      have int1 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) * (1 / x ^ 2)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2 := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          field_simp

      rw[int1] at IBP
      rw[IBP]

      have int2 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = -(↑d + 1) * ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2 := by
        have : ∀ x, (↑d + 1) * Real.log x ^ d / x * (-1 / x)
         = -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          intro x
          field_simp
        have : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          exact intervalIntegral.integral_congr fun ⦃x⦄ a ↦ this x
        rw [this]
        rw [←intervalIntegral.integral_const_mul]
        ring_nf

      rw[int2]

      have int3 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2
                = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw[int3]

      have IHbound : ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := by
        exact IH T Tgt3

      ring_nf
      have bound2 : (Real.log T * Real.log T ^ d * T⁻¹) ≥ 0 := by
        have logTpos : Real.log T ≥ 0 := by
          refine log_nonneg ?_
          linarith
        apply mul_nonneg
        · apply mul_nonneg
          · exact logTpos
          · exact pow_nonneg logTpos d
        · positivity

      have bound3 : -(Real.log T * Real.log T ^ d * T⁻¹) ≤ 0 := by
        exact Right.neg_nonpos_iff.mpr bound2
      let S := Real.log T * Real.log T ^ d * T⁻¹
      have Spos : S ≥ 0 := by
        unfold S
        exact bound2

      have : (-(Real.log T * Real.log T ^ d * T⁻¹) + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 = (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        unfold S
        rfl
      rw [this]

      have GetRidOfS : (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2
                      ≤ ( Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        linarith [Spos]
      apply lt_of_le_of_lt GetRidOfS
      rw [add_assoc]

      have bound4 : ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := IHbound

      have bound5 : ↑d * ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 ≤ ↑d * Cd := by
        apply (mul_le_mul_of_nonneg_left bound4.le)
        exact Nat.cast_nonneg d

      have bound_sum : ↑d * (∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2)
                       + ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < ↑d * Cd + Cd := by
        linarith [bound4, bound5]
      rw[add_assoc]
      apply add_lt_add_right
      field_simp
      linarith [bound_sum]

theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),

        let σ₁ : ℝ := 1 - A / (Real.log T)
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
                                                      
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded 9
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁                             
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3

  have logXgt1 : Real.log X > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logTgt1 : Real.log T > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logX9gt1 : Real.log X ^ 1 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logXgt1
    linarith
    linarith

  have logT9gt1 : Real.log T ^ 1 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logTgt1
    linarith
    linarith

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      linarith[h2]
    have abs_tgt3 : 3 < |t| := by
      rw[this]
      linarith[h2]
    have abs_tltX : |t| < T := by
      rw[this]
      linarith[h1]
    exact ⟨abs_tgt3, abs_tltX⟩

  have logtgt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| > 1 := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine logt_gt_one ?_
    exact h1.le

  have logt9gt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9  > 1 := by
    intro t ht
    refine one_lt_pow₀ (logtgt1_bounds t ht) ?_
    linarith

  have logtltlogT_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| < Real.log T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have m := log_lt_log (by linarith : 0 < (|t|)) (h2 : |t| < T )
    exact m

  have logt9ltlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 < Real.log T ^ 9 := by
    intro t ht
    obtain h1 := logtltlogT_bounds t ht
    obtain h2 := logtgt1_bounds t ht
    have h3: 0 ≤ Real.log |t| := by linarith
    refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr h1
    linarith
    linarith
    linarith

  have Aoverlogt9gtAoverlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ 9 > A / Real.log T ^ 9 := by
    intro t ht
    have h1 := logt9ltlogT9_bounds t ht
    have h2 :=logt9gt1_bounds t ht
    refine div_lt_div_of_pos_left ?_ ?_ h1
    linarith [hA.1]
    linarith

  have AoverlogT9in0half: A / Real.log T ^ 1 ∈ Ioo 0 (1/2) := by
    constructor
    · refine div_pos ?_ ?_
      refine EReal.coe_pos.mp ?_
      exact EReal.coe_lt_coe hA.1
      linarith
    · refine (div_lt_comm₀ ?_ ?_).mpr ?_
      linarith
      linarith
      refine (div_lt_iff₀' ?_).mpr ?_
      linarith
      have hA_lt : A ≤ 1 / 2 := hA.2
      have hbound : 1 / 2 < (1 / 2) * Real.log T ^ 1 := by
        linarith
      linarith

  have σ₁lt2 : (σ₁ : ℝ) < 2 := by
    unfold σ₁
    calc 1 - A / Real.log T
      < 1 - 0 := by simp only [sub_zero]; exact sub_lt_self 1 (div_pos hA.1 (lt_trans zero_lt_one logTgt1))
      _ = 1 := by norm_num
      _ < 2 := by norm_num

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    calc 1 - A / Real.log T
      < 1 - 0 := by simp only [sub_zero]; exact sub_lt_self 1 (div_pos hA.1 (by linarith [logTgt1]))
      _ = 1 := by norm_num

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    rw [sub_pos]
    calc
      A / Real.log T ≤ (1/2) / Real.log T := by
        apply div_le_div_of_nonneg_right hA.2 (by linarith)
      _ ≤ (1/2) / 1 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ = 1/2 := by norm_num
      _ < 1 := by norm_num

  have quotient_bound : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ 9/ t ^ 2  := by
    intro t ht
    have loght := logt9gt1_bounds t ht
    have logpos : Real.log |t| ^ 9 > 0 := by linarith
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    have denom_pos : 0 < t ^ 2 := by
      have : t ^ 2 = |t| ^ 2 := by
        exact Eq.symm (sq_abs t)
      rw [this]
      have h1 := ht.1
      have abspos : |t| > 0 := by linarith
      exact sq_pos_of_pos abspos
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have boundthing : ∀ t, 3 < |t| ∧ |t| < T → σ₁ ∈ Ici (1 - A / Real.log |t|) := by
    intro t ht
    have h1 := Aoverlogt9gtAoverlogT9_bounds t ht
    unfold σ₁
    apply mem_Ici.mpr
    ring_nf

    apply sub_le_sub_left
    have : Real.log |t| ≤ Real.log T := by
      apply Real.log_le_log (by linarith) (le_of_lt ht.2)
    exact div_le_div_of_nonneg_left (le_of_lt hA.1) (Real.log_pos (by linarith)) this

  have : ∫ (t : ℝ) in -T..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) = ∫ (t : ℝ) in Ioo (-T : ℝ) (-3 : ℝ),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.integral_Ioc_eq_integral_Ioo
  rw[this]

  have MellinBound : ∀ (t : ℝ) , ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    apply CMhyp σ₁
    exact σ₁pos
    · simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact le_rfl
    · simpa only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] using σ₁lt2.le
    exact εgt0
    exact εlt1

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ 9 := by
    intro t tbounds
    obtain ⟨tgt3, tltT⟩ := tbounds
    apply hCζ
    · exact tgt3
    · apply boundthing
      constructor
      · exact tgt3
      · exact tltT

  have Mellin_bd : ∀ t, 3 < |t| ∧ |t| < T →
  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖σ₁ + t * I‖ ^ 2)⁻¹ := by
    intro t ht
    apply MellinBound

  have logzeta_bd : ∀ t, 3 < |t| ∧ |t| < T →
    ‖ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)‖ ≤ Cζ * Real.log |t| ^ 9 := by
    intro t t_bounds
    obtain ⟨abs_tgt3,abs_tltX⟩ := t_bounds
    apply logzetabnd
    constructor
    · exact abs_tgt3
    · exact abs_tltX
  have : ‖1 / (2 * ↑π * I) *
        (I * ∫ (t : ℝ) in -X..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑T ^ (↑σ₁ + ↑t * I))‖
    =
    (1 / (2 * π)) * ‖∫ (t : ℝ) in -X..-3,
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑T ^ (↑σ₁ + ↑t * I)‖ := by
    simp only [norm_mul]
    rw[Complex.norm_I]
    simp only [one_mul]
    have : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by

      ring_nf
      simp only [norm_mul]
      rw[inv_I]
      have : ‖-I‖ = ‖-1 * I‖ := by
        simp
      rw[this]
      have : ‖-1 * I‖ = ‖-1‖ * ‖I‖ := by
        simp
      rw[this, Complex.norm_I]
      ring_nf
      simp
    rw[this]

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have norm_X_sigma1: ∀ (t : ℝ), ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
    intro t
    have Xpos : 0 < X := by linarith
    have : ((↑σ₁ + ↑t * I).re) = σ₁ := by
      simp

    nth_rw 2[← this]
    apply Complex.norm_cpow_eq_rpow_re_of_pos Xpos

  have bound_integral : ∀ (t : ℝ), 3  < |t| ∧ |t| < T → ‖f t‖ ≤ g t := by
    intro t
    rintro ⟨ht_gt3, ht_ltT⟩
    have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := norm_X_sigma1 t
    have logtgt1 : 1 < Real.log |t| := by
        exact logt_gt_one ht_gt3.le
    have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
    have h𝓜 := MellinBound t
    have : ‖f ↑t‖ = ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ := by
      rfl
    rw[this]
    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ 9) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      rw[Xσ_bound]
      gcongr
    have : (Cζ * Real.log |t| ^ 9) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f: ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I))‖ = ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          f t)‖ := by
      unfold f
      simp
  rw[int_with_f]
  apply (norm_mul_le _ _).trans
  have int_mulbyI_is_int : ‖I * ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ = ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    rw [Complex.norm_mul, Complex.norm_I]
    ring
  rw[int_mulbyI_is_int]

  have norm_1over2pii_le1: ‖1 / (2 * ↑π * I)‖ ≤ 1 := by
    simp
    have pi_gt_3 : Real.pi > 3 := by
      exact pi_gt_three
    have pi_pos : 0 < π := by linarith [pi_gt_3]
    have abs_pi_inv_le : |π|⁻¹ ≤ (1 : ℝ) := by
      rw [abs_of_pos pi_pos]
      have h : 1 = π * π⁻¹ := by
        field_simp
      rw[h]
      nth_rw 1 [← one_mul π⁻¹]
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact inv_nonneg.mpr (le_of_lt pi_pos)
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_half_le_one : (2 : ℝ)⁻¹ ≤ 1 := by norm_num
    rw [abs_of_pos pi_pos] at abs_pi_inv_le
    norm_num; linarith

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · exact norm_1over2pii_le1
  apply le_trans this
  have : ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑ t‖ := by
    apply norm_integral_le_integral_norm
  apply le_trans this

  have norm_f_nonneg: ∀ t, ‖f t‖ ≥ 0 := by
    exact fun t ↦ norm_nonneg (f t)

  have g_cont : ContinuousOn g (Icc (-T) (-3)) := by
    unfold g
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_const
    · exact continuousOn_const
    · refine ContinuousOn.pow ?_ 9
      refine ContinuousOn.log ?_ ?_
      · refine Continuous.continuousOn ?_
        exact _root_.continuous_abs
      · intro t ht
        have h1 := ht.1
        have h2 := ht.2
        by_contra!
        have : t = 0 := by
          exact abs_eq_zero.mp this
        rw[this] at h2
        absurd
        h2
        linarith
    · refine ContinuousOn.inv₀ ?_ ?_
      · refine ContinuousOn.mul ?_ ?_
        · exact continuousOn_const
        · refine ContinuousOn.pow ?_ 2
          refine ContinuousOn.norm ?_
          refine ContinuousOn.add ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.mul ?_ ?_
            · refine continuousOn_of_forall_continuousAt ?_
              intro x hx
              exact continuous_ofReal.continuousAt
            · exact continuousOn_const
      · intro x hx
        have norm_sq_pos : ‖(σ₁ : ℂ) + x * Complex.I‖ ^ 2 = σ₁ ^ 2 + x ^ 2 := by
          rw [Complex.sq_norm]
          exact normSq_add_mul_I σ₁ x
        have : 0 < σ₁ ^ 2 + x ^ 2 := by
          apply add_pos_of_pos_of_nonneg
          · exact sq_pos_of_pos σ₁pos
          · exact sq_nonneg x
        apply mul_ne_zero
        · linarith
        · rw [norm_sq_pos]
          exact ne_of_gt this
    · exact continuousOn_const

  have g_integrable_Icc : IntegrableOn g (Icc (-T) (-3)) volume := by
    exact ContinuousOn.integrableOn_Icc g_cont

  have g_integrable_Ioo : IntegrableOn g (Ioo (-T) (-3)) volume := by
    apply MeasureTheory.IntegrableOn.mono_set g_integrable_Icc
    exact Ioo_subset_Icc_self

  have int_normf_le_int_g: ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in Ioo (-T) (-3), g ↑t := by

    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · have f_int : IntegrableOn (fun (t : ℝ) ↦ ‖f t‖) (Ioo (-T : ℝ) (-3 : ℝ)) volume := by
        have hle : -T ≤ -3 := by linarith
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp h_int
      apply MeasureTheory.setIntegral_mono_on
      exact f_int
      exact g_integrable_Ioo
      exact measurableSet_Ioo
      intro t ht
      apply bound_integral
      have : |t| = -t := by
        refine abs_of_neg ?_
        linarith [ht.2]
      have abs_tgt3 : 3 < |t| := by
        rw[this]
        linarith[ht.2]
      have abs_tltX : |t| < T := by
        rw[this]
        linarith[ht.1]
      constructor
      · linarith
      · linarith
    · have : ∫ (t : ℝ) in -T..-3, ‖f ↑ t‖ = ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖  := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      have : ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖ = 0 := by
        rw [← this]
        exact intervalIntegral.integral_undef h_int
      rw [this]
      apply MeasureTheory.setIntegral_nonneg
      · exact measurableSet_Ioo
      · intro t ht
        have abst_negt : |t| = -t := by
          refine abs_of_neg ?_
          linarith [ht.2]
        have tbounds1 : 3 < |t| ∧ |t| < T := by
          rw[abst_negt]
          constructor
          · linarith [ht.2]
          · linarith [ht.1]
        unfold g
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        · linarith
        · linarith
        · have : 0 ≤ Real.log |t| := by
            apply Real.log_nonneg
            linarith [tbounds1.1]
          positivity
        · positivity

        · apply Real.rpow_nonneg
          linarith

  apply le_trans int_normf_le_int_g
  unfold g

  have : X ^ σ₁ = X ^ (1 - A / Real.log T ) := by
    rfl
  rw[this]

  have : X ^ (1 - A / Real.log T) = X * X ^ (- A / Real.log T) := by
    have hX : X > 0 := by linarith
    simp only [Real.rpow_sub hX, Real.rpow_one]
    have h₁ : X ^ (-A / Real.log T) * X ^ (A / Real.log T) = 1 := by
      rw [← Real.rpow_add hX]
      ring_nf
      exact rpow_zero X
    field_simp
    simpa only [neg_div, mul_comm] using h₁.symm

  rw[this]

  have Bound_of_log_int: ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]
    have normsquared : ∀ (t : ℝ), ‖↑σ₁ + ↑t * I‖ ^ 2 = σ₁ ^ 2 + t ^ 2 := by
      intro t
      simp only [Complex.sq_norm]
      exact normSq_add_mul_I σ₁ t

    have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2
          = ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) := by
      simp_rw [normsquared]

    have bound : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      rw [this]
      have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 /  t ^ 2 := by
        refine setIntegral_mono_on ?_ ?_ ?_ ?_
        ·
          have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have h2 : t ≠ 0 := by linarith
              have h3 : 0 < t ^ 2 := pow_two_pos_of_ne_zero h2
              have h4 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              linarith [h3, h4]
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have tne0 : t ≠ 0 := by linarith
              exact pow_ne_zero 2 tne0
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · exact measurableSet_Ioo
        · intro x hx
          have xneg : x < 0 := by linarith[hx.2]
          have absx : |x| = -x := abs_of_neg xneg
          have h1 : 3 < |x| ∧ |x| < T := by
            rw[absx]
            constructor
            · linarith [hx.2]
            · linarith [hx.1]
          exact quotient_bound x (t_bounds x hx)
      apply le_trans this
      have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
            = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
        have eq_integrand : ∀ (t : ℝ), t ∈ Ioo (-T) (-3) → (Real.log |t|) ^ 9 / t ^ 2 = (Real.log (-t)) ^ 9 / (-t) ^ 2 := by
          intro t ht
          have tneg : t < 0 := by linarith[ht.2]
          have : |t| = -t := abs_of_neg tneg
          rw [this, neg_sq]

        have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
              = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo eq_integrand

        rw [this]

        have interval_to_Ioo1 : ∫ (t : ℝ) in -T..-3, Real.log (-t) ^ 9 / (-t) ^ 2
                        = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        have interval_to_Ioo2 : ∫ (t : ℝ) in (3)..(T), Real.log t ^ 9 / t ^ 2
                    = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        rw [← interval_to_Ioo1, ← interval_to_Ioo2]
        rw [intervalIntegral.integral_comp_neg (fun (t : ℝ) ↦ Real.log (t) ^ 9 / (t) ^ 2)]
        simp
      rw [this]
      have : ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 < Cint := by
        exact Cinthyp T Tgt3
      linarith
    rw [ mul_comm]
    rw [← mul_div_assoc, mul_one]
    exact (div_le_div_iff_of_pos_right εgt0).mpr bound

  have factor_out_constants :
  ∫ (t : ℝ) in Ioo (-T) (-3), Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ))
  = Cζ * CM * (X * X ^ (-A / Real.log T)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     rw [← integral_const_mul]
     apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
     intro t ht
     ring_nf

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · have hpos : 0 < X * X ^ (-A / Real.log T) := by
        apply mul_pos
        · linarith
        · apply Real.rpow_pos_of_pos
          linarith
      apply mul_nonneg
      · apply mul_nonneg
        · linarith
        · linarith
      · linarith [hpos]

  apply le_trans this
  ring_nf
  field_simp; norm_num

lemma I7I3 {SmoothingF : ℝ → ℝ} {ε X T σ₁ : ℝ} (Xpos : 0 < X) :
    I₇ SmoothingF ε T X σ₁ = conj (I₃ SmoothingF ε T X σ₁) := by
  unfold I₃ I₇
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj, ← intervalIntegral.integral_comp_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [← smoothedChebyshevIntegrand_conj Xpos]
    simp

lemma I7Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2))
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
  obtain ⟨C, Cpos, bound⟩ := I3Bound suppSmoothingF ContDiffSmoothingF hCζ Cζpos hA
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]

lemma I4Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)

    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ}                                                                
    (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by

  have reOne : re 1 = 1 := by exact rfl
  have imOne : im 1 = 0 := by exact rfl
  have reThree : re 3 = 3 := by exact rfl
  have imThree : im 3 = 0 := by exact rfl

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  unfold I₄ SmoothedChebyshevIntegrand

  let S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1
  let C' : ℝ := sSup S
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -(ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        ((ζ' / ζ) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by exact rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        have : -3 ≠ 0 := by norm_num
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  obtain ⟨D, Dpos, MellinSmooth1bBound⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  let C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)
  use C
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnnorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := by
          apply (NNReal.coe_le_coe).mp
          convert! temp using 1; congr 2; ring
        have hp : (0 : NNReal) < ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ :=
          lt_of_lt_of_le (by norm_num) this
        convert! hp using 1; congr 2; ring
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert sInfPos.le using 5
      norm_cast
  use CNonneg

  let Tlb : ℝ := max 4 (max (rexp A) (rexp (A / (1 - σ₂))))
  use Tlb

  have : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  use this

  intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := by exact le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb := by
      have : rexp (A / (1 - σ₂)) ≤ Tlb := by
        unfold Tlb
        apply le_max_of_le_right
        apply le_max_right
      rw[← Real.le_log_iff_exp_le] at this
      · rw[div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · linarith
        · exact logTlb_pos
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ≤ 1 - A / Real.log T := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · exact logTlb_pos
      · apply log_le_log (by positivity)
        exact le_of_lt (by exact T_gt_Tlb)
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := by exact min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := by exact max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T) / ε = 1 * (C * X * X ^ (-A / Real.log T) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg, Complex.norm_I, mul_one]
    have : 1 / (2 * π) < 1 / 6 := by
      rw[one_div_lt_one_div]
      · refine (div_lt_iff₀' ?_).mp ?_
        norm_num
        ring_nf
        refine gt_iff_lt.mpr ?_
        exact Real.pi_gt_three
      · positivity
      · norm_num
    apply le_of_lt
    exact lt_trans this (by norm_num)
    exact pi_nonneg
  · let f : ℝ → ℂ := fun σ ↦ (-ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul]
        have : C * X * X ^ (-A / Real.log T) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T)) := by ring
        rw[this]
        have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I) =
              𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) s := by exact rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]

                · have one_inv: (1⁻¹ : ℝ) = ( 1 : ℝ) := by norm_num
                  rw[zero_mul, neg_zero, Real.exp_zero, one_inv, mul_one]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    rw [←div_eq_mul_inv]
                    ring_nf at xInIoc ⊢
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  simp only [norm_nonneg]
  norm_num

lemma I6I4 {SmoothingF : ℝ → ℝ} {ε X σ₁ σ₂ : ℝ} (Xpos : 0 < X) :
    I₆ SmoothingF ε X σ₁ σ₂ = -conj (I₄ SmoothingF ε X σ₁ σ₂) := by
  unfold I₆ I₄
  simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_one, conj_ofNat]
  rw [← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp [conj_ofNat]

lemma I6Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)

    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ}                                                                
    (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
  obtain ⟨C, Cpos, Tlb, Tlb_gt, bound⟩ := I4Bound suppSmoothingF ContDiffSmoothingF h_logDeriv_holo hσ₂ hA
  refine ⟨C, Cpos, Tlb, Tlb_gt, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]

lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by

  unfold LogDerivZetaIsHoloSmall HolomorphicOn at h_logDeriv_holo
  let zeta'_zeta_on_line := fun (t : ℝ) ↦ ζ' (σ₂ + t * I) / ζ (σ₂ + t * I)

  have subst : {σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
    simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, neg_le_self_iff,
      Nat.ofNat_nonneg, uIcc_of_le]
    intro z hyp_z
    simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · constructor
      · rw [hyp_z.1]
        apply left_mem_uIcc
      · exact hyp_z.2
    · push Not
      by_contra h
      rw [h] at hyp_z
      simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
      linarith [hσ₂.2]

  have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn

  have is_compact' : IsCompact ({σ₂} ×ℂ uIcc (-3) 3) := by
    refine IsCompact.reProdIm ?_ ?_
    · exact isCompact_singleton
    · exact isCompact_uIcc

  let ⟨zeta_bound, zeta_prop⟩ :=
    IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

  let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

  unfold I₅
  unfold SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith[hσ₂.2]))

  simp only [mul_inv_rev] at mellin_prop

  let Const := 1 + (σ₂^2)⁻¹ * (abs zeta_bound) * M

  let C := |π|⁻¹ * 2⁻¹ * 6 * Const
  use C
  have C_pos : 0 < C := by positivity
  use C_pos

  have U : σ₂ ∈ Ioo 0 1 := by
    refine mem_Ioo.mpr ?_
    · constructor
      · linarith[hσ₂.1]
      · linarith[hσ₂.2]

  clear U    C_pos

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < σ₂^2 := by
    exact sq_pos_of_pos (by linarith[hσ₂.1])

  have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      rw [Complex.sq_norm]; rw [Complex.normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]; ring_nf; simp only [le_add_iff_nonneg_right]; exact zpow_two_nonneg t
      rw [Complex.sq_norm, Complex.normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]; ring_nf; positivity
      positivity

  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
    intro t hyp_t
    have Z := by
      calc
        ‖(-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)) * (𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · trivial
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have T : 0 ≤ abs zeta_bound * M := by positivity
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z

  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε :=
    by
      unfold C
      ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)

lemma LogDerivZetaBoundedAndHolo : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by

  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd2⟩ := LogDerivZetaBndUnif2
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT'
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  ·                                                                                  
    intro σ t ht hσ
    have hσ' : σ ∈ Ici (1 - A₁ / Real.log |t| ^ 1) := by

      have hAle : min A₁ A₂ ≤ A₁ := min_le_left _ _
      have hlogpos : 0 < Real.log |t| := by
                               
        exact Real.log_pos (lt_trans (by norm_num) ht)
      have := sub_le_sub_left
        (div_le_div_of_nonneg_right (show min A₁ A₂ ≤ A₁ from hAle) (le_of_lt hlogpos)) 1
                                     
      have hthr : 1 - A₁ / Real.log |t| ^ 1 ≤ 1 - (min A₁ A₂) / Real.log |t| ^ 1 := by
        simpa [pow_one] using this
                                           
      have : σ ∈ Ici (1 - (min A₁ A₂) / Real.log |t| ^ 1) := by
        simpa [pow_one] using hσ
      exact le_trans hthr (mem_Ici.mp this)
                                                                           
    have hmain := zeta_bnd2 σ t ht (by simpa [pow_one] using hσ')
    have hlog_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                                                              
      have hpos : 0 < |t| := lt_trans (by norm_num) ht
      have hle : Real.exp 1 ≤ |t| := by
        have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
        exact this.trans (le_of_lt ht)
      have := Real.log_le_log (Real.exp_pos 1) hle
      simpa [Real.log_exp] using this
    have hpow : Real.log |t| ^ (2 : ℕ) ≤ Real.log |t| ^ (9 : ℕ) := by
      exact pow_le_pow_right₀ hlog_ge_one (by decide : (2 : ℕ) ≤ 9)
                                   
    have : C * Real.log |t| ^ (2 : ℕ) ≤ C * Real.log |t| ^ (9 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt C_pos)
    exact (le_trans hmain this)
  ·                                                                    
    intro T hT
                                                                           
    have hsubset :
        ((Icc ((1 : ℝ) - min A₁ A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) ⊆
        ((Icc ((1 : ℝ) - A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) := by
      intro s hs
      rcases hs with ⟨hs_box, hs_ne⟩
      rcases hs_box with ⟨hre, him⟩
      rcases hre with ⟨hre_left, hre_right⟩
                                     
      constructor
      ·                                                     
        constructor
        ·                                              
          constructor
          ·                                  
            have hAle : min A₁ A₂ ≤ A₂ := min_le_right _ _
            have hlogpos : 0 < Real.log T := by
              have hT' : 1 < T := by linarith
              exact Real.log_pos hT'
            have := sub_le_sub_left
              (div_le_div_of_nonneg_right hAle (le_of_lt hlogpos)) 1
            have hthr : 1 - A₂ / Real.log T ^ 1 ≤ 1 - (min A₁ A₂) / Real.log T ^ 1 := by
              simpa [pow_one] using this
            exact le_trans hthr hre_left
          · exact hre_right
        · exact him
      · exact hs_ne
    exact (holo T hT).mono hsubset

lemma MellinOfSmooth1cExplicit {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
    ∀ ε ∈ Ioo 0 ε₀, ‖𝓜 ((Smooth1 ν ε) ·) 1 - 1‖ ≤ c * ε := by
  have := MellinOfSmooth1c diffν suppν mass_one
  rw [Asymptotics.isBigO_iff'] at this
  rcases this with ⟨c, cpos, hc⟩
  unfold Filter.Eventually at hc
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hc
  rcases hc with ⟨ε₀, ε₀pos, h⟩
  refine ⟨ε₀, c, ε₀pos, cpos, fun ε hε ↦ ?_⟩
  specialize h hε
  rw [mem_ofPred_eq, id_eq, norm_of_nonneg hε.1.le] at h
  exact h

open _root_.Filter Topology

theorem Strong_PNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := by
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by
    exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by
    rwa [← integral_Ici_eq_integral_Ioi]
  clear ContDiffν ν_nonneg'  ν_massOne'
  obtain ⟨c_close, c_close_pos, h_close⟩ :=
    SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩  := MellinOfSmooth1cExplicit ContDiff1ν ν_supp ν_massOne
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := LogDerivZetaBoundedAndHolo
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  have holo2 : HolomorphicOn (fun s ↦ ζ' s / ζ s) (uIcc σ₂ 2 ×ℂ uIcc (-3) 3 \ {1}) := by
    apply holo2'.mono
    intro s hs
    simp [mem_reProdIm] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    rcases hs.1.1 with ⟨left, right⟩
    constructor
    · apply le_trans _ left
      apply min_le_min_right
      apply le_max_left
    · rw [max_eq_right (by linarith)] at right ⊢
      exact right

  clear holo2' σ₂'_lt_one

  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  ⟨σ₂_pos, σ₂_lt_one⟩
  obtain ⟨c₇, c₇pos, hc₇⟩ := I7Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₈, c₈pos, hc₈⟩ := I8Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne

  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc

  obtain ⟨c₆, c₆pos, Tlb₆, Tlb₆bnd, hc₆⟩ := I6Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc

  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇

  let c : ℝ := A ^ ((1 : ℝ) / 2) / 4
  have cpos : 0 < c := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c]
    obtain ⟨left, right⟩ := A_in_Ioc
    positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩

  let c_εx : ℝ := A ^ ((1 : ℝ) / 2) / 2
  have c_εx_pos : 0 < c_εx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx]
  let c_Tx : ℝ := A ^ ((1 : ℝ) / 2)
  have c_Tx_pos : 0 < c_Tx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx, c_Tx]

  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / 2)))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / 2)))

  have coeff_to_zero {B : ℝ} (B_le : B < 1) :
      Tendsto (fun x ↦ Real.log x ^ (B - 1)) atTop (𝓝 0) := by
    have B_minus_1_neg : B - 1 < 0 := by linarith
    rw [← Real.zero_rpow (ne_of_lt B_minus_1_neg)]
    rw [zero_rpow (ne_of_lt B_minus_1_neg)]
    have one_minus_B_pos : 0 < 1 - B := by linarith
    rw [show B - 1 = -(1 - B) by ring]
    have : ∀ᶠ (x : ℝ) in atTop, Real.log x ^ (-(1 - B)) = (Real.log x ^ ((1 - B)))⁻¹ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      apply Real.rpow_neg
      exact Real.log_nonneg hx
    rw [tendsto_congr' this]
    apply tendsto_inv_atTop_zero.comp
    apply (tendsto_rpow_atTop one_minus_B_pos).comp
    exact tendsto_log_atTop

  have log_sub_log_pow_inf (c : ℝ) {B : ℝ} (B_le : B < 1) :
      Tendsto (fun (x : ℝ) ↦ Real.log x - c * Real.log x ^ B) atTop atTop := by
    have factor_form : ∀ x > 1, Real.log x - c * Real.log x ^ B =
        Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      intro x hx
      ring_nf
      congr! 1
      rw [mul_assoc, mul_comm (Real.log x), mul_assoc]
      congr! 1
      have log_pos : 0 < Real.log x := Real.log_pos hx
      rw [(by simp : Real.log x ^ (-1 + B) * Real.log x =
        Real.log x ^ (-1 + B) * (Real.log x) ^ (1 : ℝ))]
      rw [← Real.rpow_add log_pos]
      ring_nf
    have B_minus_1_neg : B - 1 < 0 := by linarith
    have coeff_to_one : Tendsto (fun x ↦ 1 - c * Real.log x ^ (B - 1)) atTop (𝓝 1) := by
      specialize coeff_to_zero B_le
      apply Tendsto.const_mul c at coeff_to_zero
      convert (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub coeff_to_zero
      ring

    have eventually_pos : ∀ᶠ x in atTop, 0 < 1 - c * Real.log x ^ (B - 1) := by
      apply (tendsto_order.mp coeff_to_one).1
      norm_num

    have eventually_factored : ∀ᶠ x in atTop, Real.log x - c * Real.log x ^ B =
    Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact factor_form x hx

    rw [tendsto_congr' eventually_factored]
    apply Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) tendsto_log_atTop  coeff_to_one

  have x_εx_eq (c B : ℝ) : ∀ᶠ (x : ℝ) in atTop, x * rexp (-c * Real.log x ^ B) =
        rexp (Real.log x - c * Real.log x ^ B) := by
    filter_upwards [eventually_gt_atTop 0] with x hx_pos
    conv =>
      enter [1, 1]
      rw [(Real.exp_log hx_pos).symm]
    rw [← Real.exp_add]
    ring_nf

  have x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
    rw [tendsto_congr' (x_εx_eq c B)]
    exact tendsto_exp_atTop.comp (log_sub_log_pow_inf c B_le)

  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 2)).comp Real.tendsto_log_atTop

  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x : ℝ) : -c_εx * Real.log x ^ ((1 : ℝ) / 2) = -(c_εx * Real.log x ^ ((1 : ℝ) / 2)) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    apply (tendsto_rpow_atTop (by norm_num)).comp
    exact tendsto_log_atTop

  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num

  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx (by norm_num : (1 : ℝ) / 2 < 1)
    exact this.eventually_gt_atTop 2

  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3

  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _

  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) := by
                                      
    apply (tendsto_order.mp ?_).1
    · exact σ₂_lt_one
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp [Function.comp, div_eq_mul_inv]
    · simp

  have eventually_ε_lt_ε_main : ∀ᶠ (x : ℝ) in atTop, εx x < ε_main := by
    apply (tendsto_order.mp ex_to_zero).2
    assumption

  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop

  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 100] with x hx x_gt
        convert hx using 1
        · rw [Real.norm_of_nonneg]
          apply Real.log_nonneg
          have : (1 : ℝ) = Real.log (rexp 1) := by
            exact Eq.symm (Real.log_exp 1)

          rw [this]
          apply Real.log_le_log
          · exact Real.exp_pos _
          · have := Real.exp_one_lt_d9
                       
            linarith
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp

  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this]
      rw [mul_assoc]
      grw [hx]
      simp

  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c εx c_εx
    have : 0 < (A ^ ((1 : ℝ) / 2) / 4) := by
        positivity
    have const1bnd : (A ^ ((1 : ℝ) / 2) / 4) < (A ^ ((1 : ℝ) / 2) / 2) := by
        linarith
    have const2bnd : (0 : ℝ) < 1 / 2 := by norm_num
    have this (x : ℝ) :
      C' * rexp (-(A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]

  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / 2
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have : 0 < A ^ const2 := by
      unfold const2
                                           
      apply Real.rpow_pos_of_pos
      exact A_in_Ioc.1
    have this (x : ℝ) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]

  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / 2)
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (1 : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul]
    rw [Real.log_exp]
    rw [Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (1 : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le]
        rw [div_eq_mul_inv]
        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos]
        rw [(by linarith : 1 + -(const2 * 1) = const2)]
      rw [div_mul_eq_div_div]
      rw [neg_div]
      rw [this (A_in_Ioc.1)]

      rw [mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div]

      rw [this (y := Real.log x) logxpos]

      rw [← Real.exp_add]
      apply Real.exp_monotone

      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]

      gcongr

      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      rw [←Real.sqrt_eq_rpow]
      apply Real.sqrt_nonneg

    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith

  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / 2
    have const2eq : const2 = 1 / 2 := by rfl
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    have const1eq : const1 = (A ^ const2 / 2) := by rfl
    set const1' := (A ^ const2 / 4)
    have const1'eq : const1' = (A ^ const2 / 4) := by rfl
    have A_pow_pos : 0 < A ^ const2 := by
      unfold const2
      apply Real.rpow_pos_of_pos
      exact A_in_Ioc.1

    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]

    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt

    have this (x : ℝ) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)))
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      ring
    rw [this]
    rw [rpow_one] at x_bnd
    grw [x_bnd]

  have event_4_aux4 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      Tendsto (fun x ↦ c' * Real.log x ^ pow2) atTop (𝓝 0) := by
    rw [← mul_zero c']
    apply Tendsto.const_mul
    have := tendsto_rpow_neg_atTop (y := -pow2) (by linarith)
    rw [neg_neg] at this
    apply this.comp
    exact Real.tendsto_log_atTop

  have event_4_aux3 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      ∀ᶠ (x : ℝ) in atTop, c' * (Real.log x) ^ pow2 < c := by
    apply (event_4_aux4 pow2_neg cpos c').eventually_lt_const
    exact cpos

  have event_4_aux2 {c1 : ℝ} (c1pos : 0 < c1) (c2 : ℝ) {pow1 : ℝ} (pow1_lt : pow1 < 1) :
      ∀ᶠ (x : ℝ) in atTop, 0 ≤ Real.log x * (c1 - c2 * (Real.log x) ^ (pow1 - 1)) := by
    filter_upwards [eventually_gt_atTop 3 , event_4_aux3 (by linarith : pow1 - 1 < 0)
      (by linarith : 0 < c1 / 2) c2] with x x_gt hx
    have : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      linarith
    apply mul_nonneg this
    linarith

  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    filter_upwards [event_4_aux2 (by linarith : 0 < 1 - const1) (const2 + const3) pow1_lt,
      eventually_gt_atTop 3] with x hx x_gt
    rw [← sub_nonneg]
    have :
      Real.log x - const3 * Real.log x ^ pow1 - (const1 * Real.log x + const2 * Real.log x ^ pow1)
      = (1 - const1) * Real.log x - (const2 + const3) * Real.log x ^ pow1 := by ring
    rw [this]
    convert hx using 1
    ring_nf
    congr! 1
    have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
        = const2 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]
    have : Real.log x * const3 * Real.log x ^ (-1 + pow1)
        = const3 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]

  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / 2) / 4) * Real.log x ^ ((1 : ℝ) / 2)) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂_lt_one (A ^ ((1 : ℝ) / 2) / 2)
      (A ^ ((1 : ℝ) / 2) / 4) (by norm_num : (1 : ℝ) / 2 < 1)] with x x_gt hx
    rw [mul_le_mul_iff_right₀ c₅pos]
    apply Real.exp_monotone
    convert hx

  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf

    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf

  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4

  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge zeta_bnd

  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X

  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T)
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T) >= 1 - (1/2) / 1 := by
      gcongr
      · exact A_in_Ioc.2
      · apply (Real.le_log_iff_exp_le (by positivity)).mpr
        linarith[Real.exp_one_lt_d9]
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound

  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo1_compat : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) := by
                                          
    simpa [σ₁, pow_one] using! holo1

  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith[mem_reProdIm.mp hs.1 |>.1.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 ((Smooth1 ν ε) ·) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1_compat ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂_pos σ₁_lt_one σ₂_lt_σ₁ holo1_compat holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    exact (norm_sub_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)

  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖𝓜 ((Smooth1 ν ε) ·) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]

  have C'''bnd : c₃ * X * X ^ (-A / Real.log T) / ε
                    + c₄ * X * X ^ (-A / Real.log T) / ε
                    + c₆ * X * X ^ (-A / Real.log T) / ε
                    + c₇ * X * X ^ (-A / Real.log T) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T) / ε := by
    apply le_of_eq
    ring

  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X)
                  + (𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X‖
                  + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖
                  + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T) / ε
                  + c₇ * X * X ^ (-A / Real.log T) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! h_close using 1
      rw [← norm_neg]
      congr
      ring

      change ‖I₂ ν ε (Tx X) X σ₁‖ ≤ c₂ * X / (ε * (Tx X))
      dsimp at hc₂
      dsimp [σ₁]
                                                    
      unfold sigma1Of at hc₂

      exact hc₂

    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε
                  + c₆ * X * X ^ (-A / Real.log T) / ε
                  + c₇ * X * X ^ (-A / Real.log T) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

end Erdos970
