module

public import IntegerMultBounds.NLogN.BluesteinApprox
public import IntegerMultBounds.NLogN.ResamplingPermutedNumeric

/-!
# Approximations on a ball and the weighted chirp transform

Paper §8, "Chirp and source-transform procedures" and "Scales and disk margins"; §7,
`lem:chirp-permutation`. Gaps M4 and M5 of `docs/assembly-map.md`.

Conventions as in `NLogN.Approx`: `Q_p` is `NLogN.rhoC p` (componentwise truncation toward
zero to `2^{-p} ℤ`), arrays carry the sup norm of `Pi`, and errors are scaled by `2^p`.

## Approximation on a ball (gap M5)

* `ApproxOn p A' A r ε`: `2^p ‖A' v − A v‖ ≤ ε` whenever `‖v‖ ≤ r`. At `r = 1` this is
  `NLogN.ApproxMap` (`approxOn_one_iff`, `approxOn_of_approxMap`).
* `ApproxOn.apply` and `ApproxOn.comp` (Lemma 2.7 and Corollary 2.8 of Harvey–van der Hoeven
  on balls): the inner map sends the `r`-ball into the `r'`-ball on which the outer map is
  accurate. `ApproxOn.norm_le`: an approximation of a contraction has output norm at most
  `‖v‖ + ε·2^{-p}`. `ApproxOn.smul`: scaling by `c` scales the error by `‖c‖`.
* `prop52_on`: `NLogN.prop52` on balls `r₁ → r₂ → r₃`, i.e. `2^γ B' F' A'` approximates
  `2^γ B F A` on the `r₁`-ball with error `2^γ (ε_B + ε_F + ε_A)`.

## The weighted chirp (gap M4)

* `permQCLM_apply`: `Q z k = z (permQ s k)`. `norm_chirpS`, `norm_chirpW`: unit phases.
* `permQCLM_dftDCLM` (eq. `permuted-chirp`, normalized): `Q F_N x = w · M(w̄, w · x)` with
  `w = chirpW N s` (the paper's `ā`) and `M = NLogN.convNormD N`, for even `N i`.
* `chirpApprox_err`: the computed chirp transform
  `C̃ x = Q_p(ā' · M'(a', Q_p(ā' · x)))` (`NLogN.bluesteinApproxD p a' M' x`), with
  `2^p |a'_j − w̄_j| ≤ εa`, `|a'_j| ≤ 1`, and `M'` within `εM` of `M` with outputs of norm at
  most `μ ≤ 1` whenever its second operand has norm at most `ρ`, satisfies
  `2^p ‖C̃ x − Q F_N x‖ ≤ εM + 3 εa + 4` and `‖C̃ x‖ ≤ μ` for `‖x‖ ≤ ρ`, `‖x‖ ≤ 1`. The data
  operand `Q_p(ā' · x)` has norm at most `‖x‖`, which supplies the smaller-operand condition.
  `approxOn_chirp` states the same as `ApproxOn` on the `ρ`-ball.
-/

@[expose] public section


open IntegerMultBounds IntegerMultBounds.NLogN

namespace IntegerMultBounds.MathlibTM2.Mult.SourceErr

section Restricted

variable {U V W X : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `A'` approximates `A` on the closed ball of radius `r`, with scaled error at most `ε`. -/
def ApproxOn (p : ℕ) (A' : V → W) (A : V →L[ℂ] W) (r ε : ℝ) : Prop :=
  ∀ v, ‖v‖ ≤ r → 2 ^ p * ‖A' v - A v‖ ≤ ε

theorem approxOn_one_iff {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {ε : ℝ} :
    ApproxOn p A' A 1 ε ↔ ApproxMap p A' A ε :=
  Iff.rfl

theorem ApproxOn.mono {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {r r' ε ε' : ℝ}
    (h : ApproxOn p A' A r ε) (hr : r' ≤ r) (hε : ε ≤ ε') : ApproxOn p A' A r' ε' :=
  fun v hv => (h v (hv.trans hr)).trans hε

theorem approxOn_of_approxMap {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {r ε : ℝ}
    (h : ApproxMap p A' A ε) (hr : r ≤ 1) : ApproxOn p A' A r ε :=
  ApproxOn.mono h hr le_rfl

theorem two_pow_mul_le_iff {p : ℕ} {x ε : ℝ} : 2 ^ p * x ≤ ε ↔ x ≤ ε / 2 ^ p := by
  rw [le_div_iff₀ (by positivity), mul_comm]

/-- Lemma 2.7 on a ball: an approximate contraction applied to an approximate input. -/
theorem ApproxOn.apply {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {r ε η : ℝ} {v' v : V}
    (hA : ‖A‖ ≤ 1) (h : ApproxOn p A' A r ε) (hv' : ‖v'‖ ≤ r)
    (hvv : 2 ^ p * ‖v' - v‖ ≤ η) : 2 ^ p * ‖A' v' - A v‖ ≤ ε + η := by
  have h1 := h v' hv'
  have h2 : ‖A v' - A v‖ ≤ ‖v' - v‖ := by
    rw [← map_sub]
    calc ‖A (v' - v)‖ ≤ ‖A‖ * ‖v' - v‖ := A.le_opNorm _
      _ ≤ 1 * ‖v' - v‖ := by gcongr
      _ = ‖v' - v‖ := one_mul _
  have h3 : ‖A' v' - A v‖ ≤ ‖A' v' - A v'‖ + ‖A v' - A v‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  calc 2 ^ p * ‖A' v' - A v‖ ≤ 2 ^ p * ‖A' v' - A v'‖ + 2 ^ p * ‖A v' - A v‖ := by
        rw [← mul_add]; gcongr
    _ ≤ ε + η := add_le_add h1 ((mul_le_mul_of_nonneg_left h2 hp).trans hvv)

/-- Corollary 2.8 on balls: `A'` maps the `r`-ball into the `r'`-ball, where `B'` is
accurate. -/
theorem ApproxOn.comp {p : ℕ} {A' : U → V} {A : U →L[ℂ] V} {B' : V → W} {B : V →L[ℂ] W}
    {r r' ε₁ ε₂ : ℝ} (hB : ‖B‖ ≤ 1) (hA' : ApproxOn p A' A r ε₁)
    (hB' : ApproxOn p B' B r' ε₂) (hball : ∀ u, ‖u‖ ≤ r → ‖A' u‖ ≤ r') :
    ApproxOn p (B' ∘ A') (B ∘L A) r (ε₂ + ε₁) :=
  fun u hu => by
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply] using
      hB'.apply hB (hball u hu) (hA' u hu)

/-- Disk margin: an approximation of a contraction stays within its scaled error of the
input norm. -/
theorem ApproxOn.norm_le {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {r ε : ℝ} (hA : ‖A‖ ≤ 1)
    (h : ApproxOn p A' A r ε) {v : V} (hv : ‖v‖ ≤ r) : ‖A' v‖ ≤ ‖v‖ + ε / 2 ^ p := by
  have h1 : ‖A' v - A v‖ ≤ ε / 2 ^ p := two_pow_mul_le_iff.1 (h v hv)
  have h2 : ‖A v‖ ≤ ‖v‖ := by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm _
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := one_mul _
  calc ‖A' v‖ = ‖(A' v - A v) + A v‖ := by rw [sub_add_cancel]
    _ ≤ ‖A' v - A v‖ + ‖A v‖ := norm_add_le _ _
    _ ≤ ‖v‖ + ε / 2 ^ p := by linarith

/-- Scaling by a complex number `c` scales the error by `‖c‖`; no rounding is involved. -/
theorem ApproxOn.smul {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {r ε : ℝ} (c : ℂ)
    (h : ApproxOn p A' A r ε) : ApproxOn p (fun v => c • A' v) (c • A) r (‖c‖ * ε) := by
  intro v hv
  simp only [smul_apply]
  rw [← smul_sub, norm_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h v hv) (norm_nonneg c)

/-- Proposition 5.2 on balls: `2^γ B' F' A'` approximates `F_s = 2^γ B F A` on the
`r₁`-ball when `A'` maps it into the `r₂`-ball and `F'` maps that into the `r₃`-ball. -/
theorem prop52_on {p γ : ℕ} {A' : U → V} {A : U →L[ℂ] V} {F' : V → W} {F : V →L[ℂ] W}
    {B' : W → X} {B : W →L[ℂ] X} {Fs : U →L[ℂ] X} {r₁ r₂ r₃ εA εF εB : ℝ}
    (hB : ‖B‖ ≤ 1) (hF : ‖F‖ ≤ 1)
    (hA' : ApproxOn p A' A r₁ εA) (hF' : ApproxOn p F' F r₂ εF) (hB' : ApproxOn p B' B r₃ εB)
    (hA'ball : ∀ u, ‖u‖ ≤ r₁ → ‖A' u‖ ≤ r₂) (hF'ball : ∀ v, ‖v‖ ≤ r₂ → ‖F' v‖ ≤ r₃)
    (hFs : Fs = ((2 : ℂ) ^ γ) • (B ∘L F ∘L A)) :
    ApproxOn p (fun v => ((2 : ℂ) ^ γ) • B' (F' (A' v))) Fs r₁
      (2 ^ γ * (εB + εF + εA)) := by
  subst hFs
  have h1 := hA'.comp hF hF' hA'ball
  have h2 := h1.comp hB hB' fun u hu => hF'ball _ (hA'ball u hu)
  have h3 := h2.smul ((2 : ℂ) ^ γ)
  have hn : ‖(2 : ℂ) ^ γ‖ = 2 ^ γ := by simp
  rw [hn, ← add_assoc] at h3
  exact h3

end Restricted

section Chirp

open Complex Real

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- `Q = ⊗ P_{N_i}` reads its input at `permQ s k = (-(s_i k_i))_i`. -/
theorem permQCLM_apply (s : Fin d → ℕ) (z : ((i : Fin d) → ZMod (N i)) → ℂ)
    (k : (i : Fin d) → ZMod (N i)) : permQCLM s N z k = z (permQ s k) := by
  rw [permQCLM, tensorRCLM_apply]
  have hm : ∀ i (a b : ZMod (N i)), matOf (permTCLM (t := N i) (s i)) a b =
      if -((s i : ZMod (N i)) * a) = b then 1 else 0 := by
    intro i a b
    simp only [matOf, permTCLM_apply, permT, Pi.single_apply]
  rw [Fintype.sum_eq_single (permQ s k)]
  · rw [Finset.prod_eq_one fun i _ => by rw [hm]; simp [permQ], one_mul]
  · intro j hj
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hj
    have hi' : ¬-((s i : ZMod (N i)) * k i) = j i := fun h => hi (by rw [← h]; rfl)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hm, hi']), zero_mul]

omit [∀ i, NeZero (N i)] in
theorem norm_chirpS (n s : ℕ) (j : ZMod n) : ‖chirpS n s j‖ = 1 := by
  unfold chirpS chirpExp
  have : π * I * ((s * (j.val : ℤ) ^ 2 : ℤ) : ℂ) / n =
      ((π * (s * (j.val : ℤ) ^ 2 : ℤ) / n : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

omit [∀ i, NeZero (N i)] in
theorem norm_chirpW (s : Fin d → ℕ) (j : (i : Fin d) → ZMod (N i)) : ‖chirpW N s j‖ = 1 := by
  simp only [chirpW, norm_prod, norm_chirpS, Finset.prod_const_one]

/-- Lemma 7.3 in the normalized convention: `Q F_N x = w · M(w̄, w · x)` with the weighted
chirp `w = chirpW N s` (the paper's `ā`) and `M = convNormD N`. -/
theorem permQCLM_dftDCLM (hN : ∀ i, 2 ∣ N i) (s : Fin d → ℕ)
    (x : ((i : Fin d) → ZMod (N i)) → ℂ) :
    permQCLM s N (dftDCLM N x) = fun j => chirpW N s j *
      convNormD N (fun k => starRingEnd ℂ (chirpW N s k)) (fun k => chirpW N s k * x k) j := by
  funext j
  have h := congrFun (permuted_bluesteinD hN s x) j
  have hroot : (fun i => (Complex.exp (2 * π * I / (N i)))⁻¹) =
      fun i => Complex.exp (-2 * π * I / (N i)) := by
    funext i
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [permQCLM_apply, dftDCLM_apply, hroot]
  simp only at h ⊢
  rw [h, convNormD, convG_comm]
  ring


/-- The weighted chirp transform with the smaller-operand margin.
The computed chirp transform `C̃ x = Q_p(ā' · M'(a', Q_p(ā' · x)))` (`bluesteinApproxD`)
with a kernel `a'` approximating `w̄ = conj (chirpW N s)` (the paper's `a`) approximates
`Q F_N` on inputs of norm at most `ρ`, provided `M'` is accurate when its second operand
has norm at most `ρ`. Its output norm is bounded by the output bound `μ` of `M'`. -/
theorem chirpApprox_err {p : ℕ} {εa εM ρ μ : ℝ} (hN : ∀ i, 2 ∣ N i) (s : Fin d → ℕ)
    {a' : ((i : Fin d) → ZMod (N i)) → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW N s j)‖ ≤ εa) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (N i)) → ℂ) → (((i : Fin d) → ZMod (N i)) → ℂ) →
      (((i : Fin d) → ZMod (N i)) → ℂ)}
    (hM : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ ρ →
      2 ^ p * ‖M' f g - convNormD N f g‖ ≤ εM ∧ ‖M' f g‖ ≤ μ)
    (hμ : μ ≤ 1) {x : ((i : Fin d) → ZMod (N i)) → ℂ} (hx : ‖x‖ ≤ ρ) (hx1 : ‖x‖ ≤ 1) :
    2 ^ p * ‖bluesteinApproxD p a' M' x - permQCLM s N (dftDCLM N x)‖ ≤ εM + 3 * εa + 4 ∧
      ‖bluesteinApproxD p a' M' x‖ ≤ μ := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set w := chirpW N s with hw
  have hw1 : ∀ j, ‖w j‖ = 1 := norm_chirpW s
  have hεa : 0 ≤ εa := le_trans (by positivity) (ha 0)
  have hxj : ∀ j, ‖x j‖ ≤ ‖x‖ := fun j => norm_le_pi_norm x j
  set b : ((i : Fin d) → ZMod (N i)) → ℂ := fun j => w j * x j with hb
  set b' : ((i : Fin d) → ZMod (N i)) → ℂ :=
    fun j => rhoC p (starRingEnd ℂ (a' j) * x j) with hb'
  have hb'x : ∀ j, ‖b' j‖ ≤ ‖x‖ := fun j => by
    refine (norm_rhoC_le _ _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    calc ‖a' j‖ * ‖x j‖ ≤ 1 * ‖x‖ := mul_le_mul (ha1 j) (hxj j) (norm_nonneg _) zero_le_one
      _ = ‖x‖ := one_mul _
  have hb'ρ : ‖b'‖ ≤ ρ :=
    (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hx)).2 fun j => (hb'x j).trans hx
  have hb'1 : ∀ j, ‖b' j‖ ≤ 1 := fun j => (hb'x j).trans hx1
  have hconj : ∀ j, 2 ^ p * ‖starRingEnd ℂ (a' j) - w j‖ ≤ εa := fun j => by
    rw [← Complex.conj_conj (w j), norm_conj_sub]
    exact ha j
  have hbb : ∀ j, 2 ^ p * ‖b' j - b j‖ ≤ 2 + εa + 0 := fun j =>
    approx_mul_round (by rw [Complex.norm_conj]; exact ha1 j) ((hxj j).trans hx1)
      (by rw [hw1]) (hconj j) (by simp)
  set a : ((i : Fin d) → ZMod (N i)) → ℂ := fun k => starRingEnd ℂ (w k) with ha_def
  have ha'1 : ‖a'‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 ha1
  obtain ⟨hMe, hMn⟩ := hM a' b' ha'1 hb'ρ
  set c := convNormD N a b with hc
  set c' := M' a' b' with hc'
  have hc'μ : ∀ j, ‖c' j‖ ≤ μ := fun j => (norm_le_pi_norm _ j).trans hMn
  have hcc : ∀ j, 2 ^ p * ‖c' j - c j‖ ≤ εM + (εa + (2 + εa)) := by
    intro j
    have h1 : 2 ^ p * ‖M' a' b' j - convNormD N a' b' j‖ ≤ εM := by
      refine le_trans ?_ hMe
      gcongr
      exact norm_le_pi_norm (M' a' b' - convNormD N a' b') j
    have h2 : 2 ^ p * ‖convNormD N a' b' j - convNormD N a b j‖ ≤ εa + (2 + εa) := by
      have e : convNormD N a' b' j - convNormD N a b j =
          convNormD N (fun i => a' i - a i) b' j +
            convNormD N a (fun i => b' i - b i) j := by
        rw [convNormD_sub_left, convNormD_sub_right]
        ring
      have hA : ∀ i, ‖a' i - a i‖ ≤ εa / 2 ^ p := fun i => by
        rw [le_div_iff₀ hp, mul_comm]
        exact ha i
      have hB : ∀ i, ‖b' i - b i‖ ≤ (2 + εa + 0) / 2 ^ p := fun i => by
        rw [le_div_iff₀ hp, mul_comm]
        exact hbb i
      have ha1 : ∀ i, ‖a i‖ ≤ 1 := fun i => by
        simp only [ha_def, Complex.norm_conj, hw1, le_refl]
      have hX : 0 ≤ εa / 2 ^ p := by positivity
      have hY : 0 ≤ (2 + εa + 0) / 2 ^ p := by positivity
      rw [e]
      calc 2 ^ p * ‖convNormD N (fun i => a' i - a i) b' j +
              convNormD N a (fun i => b' i - b i) j‖
          ≤ 2 ^ p * (‖convNormD N (fun i => a' i - a i) b' j‖ +
              ‖convNormD N a (fun i => b' i - b i) j‖) := by
            gcongr
            exact norm_add_le _ _
        _ ≤ 2 ^ p * (εa / 2 ^ p * 1 + 1 * ((2 + εa + 0) / 2 ^ p)) := by
            gcongr
            · exact norm_convNormD_le' hA hb'1 hX zero_le_one j
            · exact norm_convNormD_le' ha1 hB zero_le_one hY j
        _ = εa + (2 + εa) := by
            field_simp
            ring
    calc 2 ^ p * ‖c' j - c j‖
        = 2 ^ p * ‖(M' a' b' j - convNormD N a' b' j) +
            (convNormD N a' b' j - convNormD N a b j)‖ := by
          simp only [hc', hc]
          ring_nf
      _ ≤ 2 ^ p * ‖M' a' b' j - convNormD N a' b' j‖ +
            2 ^ p * ‖convNormD N a' b' j - convNormD N a b j‖ := by
          rw [← mul_add]
          gcongr
          exact norm_add_le _ _
      _ ≤ εM + (εa + (2 + εa)) := add_le_add h1 h2
  have hk : ∀ k, 2 ^ p * ‖bluesteinApproxD p a' M' x k - permQCLM s N (dftDCLM N x) k‖ ≤
      εM + 3 * εa + 4 := by
    intro k
    have hfinal := approx_mul_round (p := p) (η₁ := εa) (η₂ := εM + (εa + (2 + εa)))
      (u' := starRingEnd ℂ (a' k)) (v' := c' k) (u := w k) (v := c k)
      (by rw [Complex.norm_conj]; exact ha1 k) ((hc'μ k).trans hμ)
      (by rw [hw1]) (hconj k) (hcc k)
    have hgoal : bluesteinApproxD p a' M' x k - permQCLM s N (dftDCLM N x) k =
        rhoC p (starRingEnd ℂ (a' k) * c' k) - w k * c k := by
      rw [permQCLM_dftDCLM hN]
      rfl
    rw [hgoal]
    linarith
  have hE : 0 ≤ εM + 3 * εa + 4 := le_trans (by positivity) (hk 0)
  refine ⟨?_, ?_⟩
  · rw [two_pow_mul_le_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    rw [← two_pow_mul_le_iff]
    exact hk k
  · refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hc'μ 0))).2 fun k => ?_
    exact (norm_rhoC_le _ _).trans (by
      rw [norm_mul, Complex.norm_conj]
      calc ‖a' k‖ * ‖c' k‖ ≤ 1 * μ :=
            mul_le_mul (ha1 k) (hc'μ k) (norm_nonneg _) zero_le_one
        _ = μ := one_mul _)

/-- The weighted chirp transform on a ball: `C̃` approximates `Q F_N` on the
`ρ`-ball with error `εM + 3 εa + 4` and maps it into the `μ`-ball. -/
theorem approxOn_chirp {p : ℕ} {εa εM ρ μ : ℝ} (hN : ∀ i, 2 ∣ N i) (s : Fin d → ℕ)
    {a' : ((i : Fin d) → ZMod (N i)) → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW N s j)‖ ≤ εa) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (N i)) → ℂ) → (((i : Fin d) → ZMod (N i)) → ℂ) →
      (((i : Fin d) → ZMod (N i)) → ℂ)}
    (hM : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ ρ →
      2 ^ p * ‖M' f g - convNormD N f g‖ ≤ εM ∧ ‖M' f g‖ ≤ μ)
    (hμ : μ ≤ 1) (hρ : ρ ≤ 1) :
    ApproxOn p (bluesteinApproxD p a' M') (permQCLM s N ∘L dftDCLM N) ρ (εM + 3 * εa + 4) ∧
      ∀ x, ‖x‖ ≤ ρ → ‖bluesteinApproxD p a' M' x‖ ≤ μ :=
  ⟨fun _x hx => (chirpApprox_err hN s ha ha1 hM hμ hx (hx.trans hρ)).1,
    fun _x hx => (chirpApprox_err hN s ha ha1 hM hμ hx (hx.trans hρ)).2⟩

end Chirp

end IntegerMultBounds.MathlibTM2.Mult.SourceErr
