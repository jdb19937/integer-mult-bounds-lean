module

public import IntegerMultBounds.MathlibTM2.Mult.SourceErrChirp
public import IntegerMultBounds.MathlibTM2.Mult.CRT
public import IntegerMultBounds.Resampling.TabledMaps
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Error of the computed source transform

Paper §8, "The source transform" and "Precision and exact recovery" (eq. `source-error`).
Gaps M7 and M8 of `docs/assembly-map.md`; the convolution identity `hconv` is
`IntegerMultBounds.MathlibTM2.Mult.crt_hconv`.

## Maps

* `sourceApprox s t p γ A' B' a' M' u = 2^γ · B̃₀(C̃(Ã u))`: `Ã = tensorZR d s t A'` and
  `B̃₀ = tensorZR d t s B'` apply the line maps along every axis, and
  `C̃ = bluesteinApproxD p a' M'` is the computed chirp transform
  `Q_p(ā' · M'(a', Q_p(ā' · x)))` with `Q_p = rhoC p`. The scale by `2^γ` multiplies the
  represented values exactly; on grid values it commutes with `Q_p`
  (`rhoC_two_pow_mul_of_isFixed`). The paper's sign-extension removal changes only the word
  width, and `sourceApprox_norm_le` shows that the scaled values stay in the disk.
* `oppApprox ... z = conj (sourceApprox ... (conj z))`, the paper's `F̃⁺`.
* `crtSourceApprox hs ... u = sourceApprox ... (u ∘ Φ⁻¹)` and
  `crtOppApprox hs ... y = oppApprox ... y ∘ Φ`, with `Φ = crtPhi s hs`.

## Results

* `sourceApprox_err`: if `R F_s = 2^γ ℬ Q F_t 𝒜` with linewise contractions `𝒜 = ⊗ Aℓ i`,
  `ℬ = ⊗ Bℓ i`, the line maps are within `εA`, `εB` and keep the unit ball, the kernel is
  within `εa` of `conj (chirpW t s)`, and `M'` is within `εM` of `convNormD t` with outputs of
  norm at most `μ ≤ 1` whenever its second operand has norm at most `ρ`, where
  `1/2 + d εA 2^{-p} ≤ ρ ≤ 1`, then `F̃` approximates `R F_s = permRCLM s t ∘L dftDCLM s` on
  the `1/2`-ball with error `2^γ (d εB + (εM + 3 εa + 4) + d εA)`.
* `permRCLM_dftDPlusCLM_eq_conj`: `R F_s⁺ z = conj (R F_s (conj z))`. `ApproxOn.conj` and
  `oppApprox_approxOn`: `F̃⁺` approximates `R F_s⁺ = permRCLM s t ∘L dftDPlusCLM s` with the
  error of `F̃`.
* `sourceErr_of_components` (paper constants): line errors `p²`, kernel error `2`,
  convolution error `6TL` with the margins `.7` and `.701`, `0 < d`, `2 ≤ p`, `2dp² ≤ TL`
  and `E_s ≤ 2^p/100` give error `E_s = 9 · 2^γ T L` with `γ = d (2⌈α²⌉ + 2)` for both
  `F̃` and `F̃⁺`. `sourceErr_of_tables`: the same with the table-driven line maps of
  `Resampling.TabledMaps.permuted_numeric_tabled`.
* `sourceApprox_margins`: on the `1/2`-ball, `‖Ã u‖ ≤ .6`, `‖Q_p(ā' · Ã u)‖ ≤ .6`,
  `‖M'(a', Q_p(ā' · Ã u))‖ ≤ .701` and `‖C̃(Ã u)‖ ≤ .701`. `sourceApprox_norm_le`: the
  outputs of `F̃` and `F̃⁺` have norm at most `.51`.
* `crtSource_err`, `crtOpp_err`: the hypotheses `hF'`, `hG'` of
  `IntegerMultBounds.MathlibTM2.Mult.exact_product_crt`. `exact_product_of_components`: the coefficient identity
  of `ExactRecovery.exact_product` for `crtSourceApprox` and `crtOppApprox`.

## Scope

All arrays are functions on the boxes `∏ ZMod (s i)` and `∏ ZMod (t i)`; `tensorZR` passes
through boxes that mix `s`- and `t`-axes (`NLogN.mixFam`). The paper's padded box
`∏ [0, t_i)` with zeros off `∏ [0, s_i)` does not enter this chain. It enters when tape arrays
are read as these functions: a linewise pass over the padded box must either skip the lines
through padding coordinates or use `A' i 0 = 0` and `B' i 0 = 0` to keep them zero, and
`B̃₀` must write zeros at its padding positions. Neither condition is a hypothesis here.
-/

@[expose] public section


open IntegerMultBounds IntegerMultBounds.NLogN
open scoped Function

namespace IntegerMultBounds.MathlibTM2.Mult.SourceErr

/-! ### The computed source transform -/

section Source

open Complex

/-- The computed source transform of §8.4,
`F̃ u = 2^γ · B̃₀(C̃(Ã u))`: the line maps `A' i` applied along every axis
(`tensorZR`, from `∏ ZMod (s i)` to `∏ ZMod (t i)`), the computed chirp transform
`C̃ x = Q_p(ā' · M'(a', Q_p(ā' · x)))` (`bluesteinApproxD`, with `Q_p = rhoC p`
truncating both components toward zero), the line maps `B' i` along every axis, and the
exact multiplication by `2^γ`. The scaling and the sign-extension removal of the paper
are exact on values: the represented complex numbers are multiplied by `2^γ` and nothing
is rounded. -/
noncomputable def sourceApprox {d : ℕ} (s t : Fin d → ℕ) [∀ i, NeZero (s i)]
    [∀ i, NeZero (t i)] (p γ : ℕ) (A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ)
    (B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ) (a' : ((i : Fin d) → ZMod (t i)) → ℂ)
    (M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ))
    (u : ((i : Fin d) → ZMod (s i)) → ℂ) : ((i : Fin d) → ZMod (s i)) → ℂ :=
  ((2 : ℂ) ^ γ) • tensorZR d t s B' (bluesteinApproxD p a' M' (tensorZR d s t A' u))

/-- The opposite-sign procedure `F̃⁺ z = conj (F̃ (conj z))`. -/
noncomputable def oppApprox {d : ℕ} (s t : Fin d → ℕ) [∀ i, NeZero (s i)]
    [∀ i, NeZero (t i)] (p γ : ℕ) (A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ)
    (B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ) (a' : ((i : Fin d) → ZMod (t i)) → ℂ)
    (M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ))
    (z : ((i : Fin d) → ZMod (s i)) → ℂ) : ((i : Fin d) → ZMod (s i)) → ℂ :=
  fun k => starRingEnd ℂ (sourceApprox s t p γ A' B' a' M' (fun j => starRingEnd ℂ (z j)) k)

/-- The scale by `2^γ` is exact on grid values: `Q_p (2^γ v) = 2^γ v`. -/
theorem rhoC_two_pow_mul_of_isFixed {p γ : ℕ} {v : ℂ} (hv : IsFixed p v) :
    rhoC p ((2 : ℂ) ^ γ * v) = (2 : ℂ) ^ γ * v := by
  have h := hv.natMul (2 ^ γ)
  push_cast at h
  exact rhoC_of_isFixed h

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

omit [∀ i, NeZero (s i)] in
theorem opNorm_permQCLM_le : ‖permQCLM s t‖ ≤ 1 :=
  opNorm_tensorRCLM_le _ fun _ => opNorm_permTCLM_le

/-- The source transform with general component errors. If the exact factorization
`R F_s = 2^γ ℬ Q F_t 𝒜` holds with linewise contractions `𝒜 = ⊗ Aℓ i`, `ℬ = ⊗ Bℓ i`, the
line maps approximate `Aℓ i`, `Bℓ i` within `εA`, `εB` and keep the unit ball, the kernel
`a'` approximates `conj (chirpW t s)` within `εa`, and `M'` approximates `convNormD t`
within `εM` with outputs of norm at most `μ ≤ 1` whenever its second operand has norm at
most `ρ`, where `1/2 + d εA 2^{-p} ≤ ρ ≤ 1`, then on inputs of norm at most `1/2` the
computed source transform errs by at most `2^γ (d εB + (εM + 3 εa + 4) + d εA)`. -/
theorem sourceApprox_err {p γ : ℕ} (heven : ∀ i, 2 ∣ t i)
    (Aℓ : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (t i) → ℂ))
    (Bℓ : ∀ i, (ZMod (t i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hfact : permRCLM s t ∘L dftDCLM s = ((2 : ℂ) ^ γ) •
      (tensorRCLM Bℓ ∘L permQCLM s t ∘L dftDCLM t ∘L tensorRCLM Aℓ))
    (hAℓ : ∀ i, ‖Aℓ i‖ ≤ 1) (hBℓ : ∀ i, ‖Bℓ i‖ ≤ 1)
    {A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ} {B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ}
    {εA εB εa εM ρ μ : ℝ}
    (hA' : ∀ i, ApproxMap p (A' i) (Aℓ i) εA) (hA'1 : ∀ i u, ‖u‖ ≤ 1 → ‖A' i u‖ ≤ 1)
    (hB' : ∀ i, ApproxMap p (B' i) (Bℓ i) εB) (hB'1 : ∀ i w, ‖w‖ ≤ 1 → ‖B' i w‖ ≤ 1)
    {a' : ((i : Fin d) → ZMod (t i)) → ℂ}
    (ha' : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW t s j)‖ ≤ εa) (ha'1 : ∀ j, ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)}
    (hM' : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ ρ →
      2 ^ p * ‖M' f g - convNormD t f g‖ ≤ εM ∧ ‖M' f g‖ ≤ μ)
    (hμ : μ ≤ 1) (hρ : 1 / 2 + d * εA / 2 ^ p ≤ ρ) (hρ1 : ρ ≤ 1) :
    ApproxOn p (sourceApprox s t p γ A' B' a' M') (permRCLM s t ∘L dftDCLM s) (1 / 2)
      (2 ^ γ * (d * εB + (εM + 3 * εa + 4) + d * εA)) := by
  -- the linewise maps
  have hAt : ApproxMap p (tensorZR d s t A') (tensorRCLM Aℓ) (d * εA) := by
    rw [← tensorZRCLM_eq_tensorRCLM]
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      approxMap_tensorZR d s t A' Aℓ (fun _ => εA) hAℓ hA' hA'1
  have hBt : ApproxMap p (tensorZR d t s B') (tensorRCLM Bℓ) (d * εB) := by
    rw [← tensorZRCLM_eq_tensorRCLM]
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      approxMap_tensorZR d t s B' Bℓ (fun _ => εB) hBℓ hB' hB'1
  have hAn : ‖tensorRCLM Aℓ‖ ≤ 1 := opNorm_tensorRCLM_le _ hAℓ
  have hBn : ‖tensorRCLM Bℓ‖ ≤ 1 := opNorm_tensorRCLM_le _ hBℓ
  have hFn : ‖permQCLM s t ∘L dftDCLM t‖ ≤ 1 :=
    opNorm_comp_le_one opNorm_permQCLM_le (opNorm_dftDCLM_le t)
  -- the chirp step on the `ρ`-ball
  obtain ⟨hC, hCball⟩ := approxOn_chirp (p := p) heven s ha' ha'1 hM' hμ hρ1
  -- disk margin after the expansion
  have hAball : ∀ u : ((i : Fin d) → ZMod (s i)) → ℂ, ‖u‖ ≤ 1 / 2 →
      ‖tensorZR d s t A' u‖ ≤ ρ := fun u hu =>
    ((approxOn_of_approxMap hAt (by norm_num)).norm_le hAn hu).trans (by
      have : ‖u‖ + d * εA / 2 ^ p ≤ 1 / 2 + d * εA / 2 ^ p := by linarith
      exact this.trans hρ)
  exact prop52_on hBn hFn (approxOn_of_approxMap hAt (by norm_num)) hC hBt hAball
    (fun x hx => (hCball x hx).trans hμ) (by rw [hfact]; rfl)

end Source

/-! ### The opposite procedure by conjugation -/

section Conj

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem norm_conj_fun (z : ι → ℂ) : ‖fun k => starRingEnd ℂ (z k)‖ = ‖z‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    rw [Complex.norm_conj]
    exact norm_le_pi_norm z k
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    have h := norm_le_pi_norm (fun k => starRingEnd ℂ (z k)) k
    rwa [Complex.norm_conj] at h

theorem norm_conj_fun_sub (f g : ι → ℂ) :
    ‖(fun k => starRingEnd ℂ (f k)) - fun k => starRingEnd ℂ (g k)‖ = ‖f - g‖ := by
  have e : ((fun k => starRingEnd ℂ (f k)) - fun k => starRingEnd ℂ (g k)) =
      fun k => starRingEnd ℂ ((f - g) k) := by
    funext k
    simp
  rw [e, norm_conj_fun]

/-- Conjugation keeps an approximation: if `F'` approximates `F` on the `r`-ball and
`G = conj ∘ F ∘ conj`, then `conj ∘ F' ∘ conj` approximates `G` on the `r`-ball with the same
error. -/
theorem ApproxOn.conj {p : ℕ} {F' : (ι → ℂ) → (κ → ℂ)} {F G : (ι → ℂ) →L[ℂ] (κ → ℂ)}
    {r ε : ℝ} (h : ApproxOn p F' F r ε)
    (hG : ∀ z, G z = fun k => starRingEnd ℂ (F (fun j => starRingEnd ℂ (z j)) k)) :
    ApproxOn p (fun z k => starRingEnd ℂ (F' (fun j => starRingEnd ℂ (z j)) k)) G r ε := by
  intro z hz
  rw [hG, norm_conj_fun_sub]
  exact h _ (by rw [norm_conj_fun]; exact hz)

end Conj

section Opposite

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

omit [∀ i, NeZero (t i)] in
/-- The exact opposite transform: `R F_s⁺ z = conj (R F_s (conj z))`. -/
theorem permRCLM_dftDPlusCLM_eq_conj (z : ((i : Fin d) → ZMod (s i)) → ℂ) :
    (permRCLM s t ∘L dftDPlusCLM s) z = fun k =>
      starRingEnd ℂ ((permRCLM s t ∘L dftDCLM s) (fun j => starRingEnd ℂ (z j)) k) := by
  funext k
  simp only [ContinuousLinearMap.comp_apply, permRCLM_apply, dftDPlusCLM_eq_conj]

/-- The opposite procedure `F̃⁺ z = conj (F̃ (conj z))` approximates `R F_s⁺` on
the `r`-ball whenever `F̃` approximates `R F_s` there, with the same error. -/
theorem oppApprox_approxOn {p γ : ℕ} {A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ}
    {B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ} {a' : ((i : Fin d) → ZMod (t i)) → ℂ}
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)} {r ε : ℝ}
    (h : ApproxOn p (sourceApprox s t p γ A' B' a' M') (permRCLM s t ∘L dftDCLM s) r ε) :
    ApproxOn p (oppApprox s t p γ A' B' a' M') (permRCLM s t ∘L dftDPlusCLM s) r ε :=
  h.conj permRCLM_dftDPlusCLM_eq_conj

/-- Output margin: an approximation of a contraction on the `r`-ball stays within
`r + ε 2^{-p}`. -/
theorem norm_le_of_approxOn {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {p : ℕ} {F' : V → W} {F : V →L[ℂ] W} {r ε : ℝ}
    (hF : ‖F‖ ≤ 1) (h : ApproxOn p F' F r ε) {v : V} (hv : ‖v‖ ≤ r) :
    ‖F' v‖ ≤ r + ε / 2 ^ p :=
  (h.norm_le hF hv).trans (by linarith)

end Opposite

/-! ### Paper constants: `E_s = 9 · 2^γ T L` -/

section Paper

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- The source transform and its opposite with the paper's constants (eq. `source-error`).
The line maps approximate `resampA`, `resampB₀` within `p²` and keep the unit ball, the
per-line exact factorization holds with left inverses `J i` (as produced by
`Resampling.TabledMaps.permuted_numeric_tabled` or `NLogN.permuted_numeric_manuscript`),
the chirp kernel is within `2` of `conj (chirpW t s)` in the unit disk, and the computed
convolution errs by at most `6 T L` with outputs of norm at most `.701` when its second
operand has norm at most `.7`. With `2 d p² ≤ T L` and `E_s ≤ 2^p / 100`
(the hypothesis `hEs` of `ExactRecovery.exact_product`), the computed source transform
and its opposite approximate `R F_s` and `R F_s⁺` on the `1/2`-ball within
`E_s = 9 · 2^γ T L`, `γ = d (2⌈α²⌉ + 2)`. -/
theorem sourceErr_of_components (heven : ∀ i, 2 ∣ t i) {p L : ℕ} {α : ℝ}
    (J : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, permSCLM (t i) ∘L dftCLM (s i) = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
      (resampB₀ (s i) (t i) α (J i) ∘L permTCLM (s i) ∘L dftCLM (t i) ∘L
        resampA (s i) (t i) α))
    (hAn : ∀ i, ‖resampA (s i) (t i) α‖ ≤ 1) (hBn : ∀ i, ‖resampB₀ (s i) (t i) α (J i)‖ ≤ 1)
    {A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ} {B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ}
    (hA' : ∀ i, ApproxMap p (A' i) (resampA (s i) (t i) α) ((p : ℝ) ^ 2))
    (hA'1 : ∀ i u, ‖u‖ ≤ 1 → ‖A' i u‖ ≤ 1)
    (hB' : ∀ i, ApproxMap p (B' i) (resampB₀ (s i) (t i) α (J i)) ((p : ℝ) ^ 2))
    (hB'1 : ∀ i w, ‖w‖ ≤ 1 → ‖B' i w‖ ≤ 1)
    {a' : ((i : Fin d) → ZMod (t i)) → ℂ}
    (ha' : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW t s j)‖ ≤ 2 ∧ ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)}
    (hM' : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖M' f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
        ‖M' f g‖ ≤ 701 / 1000)
    (hd : 0 < d) (hp : 2 ≤ p) (hsmall : 2 * d * p ^ 2 ≤ (∏ i, t i) * L)
    (hEs : 9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p / 100) :
    ApproxOn p (sourceApprox s t p (d * (2 * ⌈α ^ 2⌉₊ + 2)) A' B' a' M')
        (permRCLM s t ∘L dftDCLM s) (1 / 2)
        (9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L) ∧
      ApproxOn p (oppApprox s t p (d * (2 * ⌈α ^ 2⌉₊ + 2)) A' B' a' M')
        (permRCLM s t ∘L dftDPlusCLM s) (1 / 2)
        (9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L) := by
  set γ := d * (2 * ⌈α ^ 2⌉₊ + 2) with hγ
  set X : ℝ := ((∏ i, t i : ℕ) : ℝ) * L with hX
  have hfact := permuted_factorization_multi α J hJ
  have hpos : (0 : ℝ) < 2 ^ p := by positivity
  have hg1 : (1 : ℝ) ≤ 2 ^ γ := one_le_pow₀ (by norm_num)
  have hsm : 2 * (d : ℝ) * (p : ℝ) ^ 2 ≤ X := by
    rw [hX]; exact_mod_cast hsmall
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hX8 : 8 ≤ X := by nlinarith
  have hXp : 900 * X ≤ 2 ^ p := by
    have : 9 * 2 ^ γ * ((∏ i, t i : ℕ) : ℝ) * L = 9 * 2 ^ γ * X := by rw [hX]; ring
    rw [this] at hEs
    nlinarith
  have hρ : 1 / 2 + d * (p : ℝ) ^ 2 / 2 ^ p ≤ 7 / 10 := by
    have : d * (p : ℝ) ^ 2 / 2 ^ p ≤ 1 / 5 := by
      rw [div_le_iff₀ hpos]; nlinarith
    linarith
  have hF := sourceApprox_err (γ := γ) heven _ _ hfact hAn hBn hA' hA'1 hB' hB'1
    (fun j => (ha' j).1) (fun j => (ha' j).2) hM' (by norm_num) hρ (by norm_num)
  have hF9 := hF.mono le_rfl (by
    show 2 ^ γ * (d * (p : ℝ) ^ 2 + (6 * ((∏ i, t i : ℕ) : ℝ) * L + 3 * 2 + 4) +
      d * (p : ℝ) ^ 2) ≤ 9 * 2 ^ γ * ((∏ i, t i : ℕ) : ℝ) * L
    have e : 9 * (2 : ℝ) ^ γ * ((∏ i, t i : ℕ) : ℝ) * L = 2 ^ γ * (9 * X) := by rw [hX]; ring
    rw [e]
    gcongr
    rw [hX] at hsm hX8 ⊢
    linarith)
  exact ⟨hF9, oppApprox_approxOn hF9⟩

end Paper

/-! ### Disk margins (§8 "Scales and disk margins") -/

section Margins

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- The intermediate margins of the source transform on an input of norm at most `1/2`:
the chirp input `x = Ã u` and the data operand `x₀ = Q_p(ā' · x)` have norm at most `.6`,
and the convolution output `y₀ = M'(a', x₀)` and the chirp output `C̃ x` have norm at most
`.701`, so every call is made inside the disk where its hypothesis holds. -/
theorem sourceApprox_margins {p L : ℕ} {α : ℝ}
    (hAn : ∀ i, ‖resampA (s i) (t i) α‖ ≤ 1)
    {A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ}
    (hA' : ∀ i, ApproxMap p (A' i) (resampA (s i) (t i) α) ((p : ℝ) ^ 2))
    (hA'1 : ∀ i u, ‖u‖ ≤ 1 → ‖A' i u‖ ≤ 1)
    {a' : ((i : Fin d) → ZMod (t i)) → ℂ} (ha'1 : ∀ j, ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)}
    (hM' : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 → ‖M' f g‖ ≤ 701 / 1000)
    (hsmall : 2 * d * p ^ 2 ≤ (∏ i, t i) * L)
    (hEs : 9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p / 100)
    {u : ((i : Fin d) → ZMod (s i)) → ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖tensorZR d s t A' u‖ ≤ 6 / 10 ∧
      ‖fun j => rhoC p (starRingEnd ℂ (a' j) * tensorZR d s t A' u j)‖ ≤ 6 / 10 ∧
      ‖M' a' (fun j => rhoC p (starRingEnd ℂ (a' j) * tensorZR d s t A' u j))‖ ≤ 701 / 1000 ∧
      ‖bluesteinApproxD p a' M' (tensorZR d s t A' u)‖ ≤ 701 / 1000 := by
  set γ := d * (2 * ⌈α ^ 2⌉₊ + 2)
  have hpos : (0 : ℝ) < 2 ^ p := by positivity
  have hg1 : (1 : ℝ) ≤ 2 ^ γ := one_le_pow₀ (by norm_num)
  have hX0 : (0 : ℝ) ≤ ((∏ i, t i : ℕ) : ℝ) * L := by positivity
  have hsm : 2 * (d : ℝ) * (p : ℝ) ^ 2 ≤ ((∏ i, t i : ℕ) : ℝ) * L := by exact_mod_cast hsmall
  have hXp : 900 * (((∏ i, t i : ℕ) : ℝ) * L) ≤ 2 ^ p := by
    have e : 9 * 2 ^ γ * ((∏ i, t i : ℕ) : ℝ) * L = 9 * 2 ^ γ * (((∏ i, t i : ℕ) : ℝ) * L) := by
      ring
    rw [e] at hEs
    have := mul_le_mul_of_nonneg_right hg1 hX0
    linarith
  have hAt : ApproxMap p (tensorZR d s t A') (tensorRCLM fun i => resampA (s i) (t i) α)
      (d * (p : ℝ) ^ 2) := by
    rw [← tensorZRCLM_eq_tensorRCLM]
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      approxMap_tensorZR d s t A' _ (fun _ => (p : ℝ) ^ 2) hAn hA' hA'1
  have hx : ‖tensorZR d s t A' u‖ ≤ 6 / 10 := by
    have h0 : ApproxOn p (tensorZR d s t A') (tensorRCLM fun i => resampA (s i) (t i) α) (1 / 2)
        (d * (p : ℝ) ^ 2) := approxOn_of_approxMap hAt (by norm_num)
    have h1 := ApproxOn.norm_le (opNorm_tensorRCLM_le (fun i => resampA (s i) (t i) α) hAn) h0 hu
    have h2 : d * (p : ℝ) ^ 2 / 2 ^ p ≤ 1 / 10 := by
      rw [div_le_iff₀ hpos]; linarith
    linarith
  have hx0 : ‖fun j => rhoC p (starRingEnd ℂ (a' j) * tensorZR d s t A' u j)‖ ≤ 6 / 10 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_
    refine (norm_rhoC_le _ _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    calc ‖a' j‖ * ‖tensorZR d s t A' u j‖ ≤ 1 * (6 / 10) :=
          mul_le_mul (ha'1 j) ((norm_le_pi_norm _ j).trans hx) (norm_nonneg _) zero_le_one
      _ = 6 / 10 := one_mul _
  have ha1 : ‖a'‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 ha'1
  have hy0 := hM' a' _ ha1 (hx0.trans (by norm_num))
  refine ⟨hx, hx0, hy0, ?_⟩
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun k => ?_
  refine (norm_rhoC_le _ _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  calc ‖a' k‖ * ‖M' a' (fun j => rhoC p (starRingEnd ℂ (a' j) * tensorZR d s t A' u j)) k‖
      ≤ 1 * (701 / 1000) := mul_le_mul (ha'1 k) ((norm_le_pi_norm _ k).trans hy0)
        (norm_nonneg _) zero_le_one
    _ = 701 / 1000 := one_mul _

omit [∀ i, NeZero (t i)] in
/-- The output margin after the exact scale `2^γ`: with `E_s ≤ 2^p / 100`, the computed
source transform and its opposite stay in the disk of radius `.51` on inputs of norm at most
`1/2`, so the exact numerator scaling needs no clipping and the sign-extension removal of
the paper loses no bits. -/
theorem sourceApprox_norm_le {p : ℕ} {Es : ℝ} {F' G' : (((i : Fin d) → ZMod (s i)) → ℂ) →
      (((i : Fin d) → ZMod (s i)) → ℂ)}
    (hF' : ApproxOn p F' (permRCLM s t ∘L dftDCLM s) (1 / 2) Es)
    (hG' : ApproxOn p G' (permRCLM s t ∘L dftDPlusCLM s) (1 / 2) Es)
    (hEs : Es ≤ 2 ^ p / 100) {u : ((i : Fin d) → ZMod (s i)) → ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖F' u‖ ≤ 51 / 100 ∧ ‖G' u‖ ≤ 51 / 100 := by
  have hpos : (0 : ℝ) < 2 ^ p := by positivity
  have hE : Es / 2 ^ p ≤ 1 / 100 := by rw [div_le_iff₀ hpos]; linarith
  have h1 := norm_le_of_approxOn
    (opNorm_comp_le_one (opNorm_permRCLM_le s t) (opNorm_dftDCLM_le s)) hF' hu
  have h2 := norm_le_of_approxOn
    (opNorm_comp_le_one (opNorm_permRCLM_le s t) opNorm_dftDPlusCLM_le) hG' hu
  constructor <;> linarith

end Margins

/-! ### Composition with the layout map `Φ` and exact recovery -/

section CRT

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
  (hs : Pairwise (Nat.Coprime on s))

/-- The computed source transform on coefficient arrays: `F̃ ∘ Φ`, `u ↦ F̃ (u ∘ Φ⁻¹)`. -/
noncomputable def crtSourceApprox (p γ : ℕ) (A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ)
    (B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ) (a' : ((i : Fin d) → ZMod (t i)) → ℂ)
    (M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ))
    (u : ZMod (∏ i, s i) → ℂ) : ((i : Fin d) → ZMod (s i)) → ℂ :=
  sourceApprox s t p γ A' B' a' M' (u ∘ (crtPhi s hs).symm)

/-- The computed opposite transform on coefficient arrays: `Φ⁻¹ ∘ F̃⁺`, `y ↦ F̃⁺ y ∘ Φ`. -/
noncomputable def crtOppApprox (p γ : ℕ) (A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ)
    (B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ) (a' : ((i : Fin d) → ZMod (t i)) → ℂ)
    (M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ))
    (y : ((i : Fin d) → ZMod (s i)) → ℂ) : ZMod (∏ i, s i) → ℂ :=
  oppApprox s t p γ A' B' a' M' y ∘ crtPhi s hs

omit [∀ i, NeZero (t i)] in
/-- Reindexing by `Φ⁻¹` is isometric, so `F̃ ∘ Φ` keeps the error of `F̃`. -/
theorem crtSource_err {p : ℕ} {r ε : ℝ}
    {F' : (((i : Fin d) → ZMod (s i)) → ℂ) → (((i : Fin d) → ZMod (s i)) → ℂ)}
    (h : ApproxOn p F' (permRCLM s t ∘L dftDCLM s) r ε) (u : ZMod (∏ i, s i) → ℂ)
    (hu : ‖u‖ ≤ r) :
    2 ^ p * ‖F' (u ∘ (crtPhi s hs).symm) - crtSourceCLM s t hs u‖ ≤ ε := by
  have e : crtSourceCLM s t hs u = (permRCLM s t ∘L dftDCLM s) (u ∘ (crtPhi s hs).symm) := rfl
  rw [e]
  exact h _ ((norm_comp_le_pi_norm _ u).trans hu)

omit [∀ i, NeZero (t i)] in
/-- Reindexing by `Φ` does not increase the error of `F̃⁺`. -/
theorem crtOpp_err {p : ℕ} {r ε : ℝ}
    {G' : (((i : Fin d) → ZMod (s i)) → ℂ) → (((i : Fin d) → ZMod (s i)) → ℂ)}
    (h : ApproxOn p G' (permRCLM s t ∘L dftDPlusCLM s) r ε)
    (y : ((i : Fin d) → ZMod (s i)) → ℂ) (hy : ‖y‖ ≤ r) :
    2 ^ p * ‖G' y ∘ crtPhi s hs - crtOppositeCLM s t hs y‖ ≤ ε := by
  have e : G' y ∘ crtPhi s hs - crtOppositeCLM s t hs y =
      (G' y - (permRCLM s t ∘L dftDPlusCLM s) y) ∘ crtPhi s hs := rfl
  rw [e]
  exact (mul_le_mul_of_nonneg_left (norm_comp_le_pi_norm _ _) (by positivity)).trans (h y hy)

/-- The analytic core without its tape layer: the components of §8.4 (line maps, chirp
table, computed convolution) with the paper's constants, the size conditions
`2 d p² ≤ T L`, `E_s ≤ 2^p/100` and the final-error condition of
`ExactRecovery.exact_product` give the exact product from the computed procedures
`F̃ ∘ Φ` and `Φ⁻¹ ∘ F̃⁺`. -/
theorem exact_product_of_components (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (heven : ∀ i, 2 ∣ t i) {p L : ℕ} {α : ℝ}
    (J : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, permSCLM (t i) ∘L dftCLM (s i) = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
      (resampB₀ (s i) (t i) α (J i) ∘L permTCLM (s i) ∘L dftCLM (t i) ∘L
        resampA (s i) (t i) α))
    (hAn : ∀ i, ‖resampA (s i) (t i) α‖ ≤ 1) (hBn : ∀ i, ‖resampB₀ (s i) (t i) α (J i)‖ ≤ 1)
    {A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ} {B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ}
    (hA' : ∀ i, ApproxMap p (A' i) (resampA (s i) (t i) α) ((p : ℝ) ^ 2))
    (hA'1 : ∀ i u, ‖u‖ ≤ 1 → ‖A' i u‖ ≤ 1)
    (hB' : ∀ i, ApproxMap p (B' i) (resampB₀ (s i) (t i) α (J i)) ((p : ℝ) ^ 2))
    (hB'1 : ∀ i w, ‖w‖ ≤ 1 → ‖B' i w‖ ≤ 1)
    {a' : ((i : Fin d) → ZMod (t i)) → ℂ}
    (ha' : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW t s j)‖ ≤ 2 ∧ ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)}
    (hM' : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖M' f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
        ‖M' f g‖ ≤ 701 / 1000)
    (hd : 0 < d) (hp : 2 ≤ p) (hsmall : 2 * d * p ^ 2 ≤ (∏ i, t i) * L)
    (hEs : 9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p / 100)
    {k : ℕ} (hk : 0 < k) {x y : List Bool}
    (hS : (digitsOf k x).length + (digitsOf k y).length ≤ (∏ i, s i) + 1)
    (hfinal : (2 : ℝ) ^ (2 * k + 4) * ((∏ i, s i : ℕ) : ℝ) ^ 2 *
      (3 * (9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L) + 2) <
        2 ^ p / 2) :
    evalBase (2 ^ k) (List.ofFn fun i : Fin (∏ i, s i) =>
      (round (((2 : ℂ) ^ (2 * k) * ((∏ i, s i : ℕ) : ℂ)) *
        ExactRecovery.computedConv (p := p) (k := k)
          (crtSourceApprox hs p (d * (2 * ⌈α ^ 2⌉₊ + 2)) A' B' a' M')
          (crtOppApprox hs p (d * (2 * ⌈α ^ 2⌉₊ + 2)) A' B' a' M') x y
          (i.val : ZMod (∏ i, s i))).re).toNat) =
      IntegerMultBounds.Machine.binaryValue x * IntegerMultBounds.Machine.binaryValue y := by
  obtain ⟨hF, hG⟩ := sourceErr_of_components heven J hJ hAn hBn hA' hA'1 hB' hB'1 ha' hM'
    hd hp hsmall hEs
  exact exact_product_crt s t hs hcop _ _ hk hS (crtSource_err hs hF) (crtOpp_err hs hG) hEs
    hfinal

end CRT

/-! ### The instance with tabled line maps -/

section Tables

open IntegerMultBounds.Resampling.WindowSum (termW)
open IntegerMultBounds.Resampling.TabledMaps (resampB₀NumW permuted_numeric_tabled)

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- `sourceErr_of_components` with the table-driven line maps of
`Resampling.TabledMaps.permuted_numeric_tabled` (integer weight tables within two units),
which discharge the line-map hypotheses and supply the left inverses `J`. -/
theorem sourceErr_of_tables (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (heven : ∀ i, 2 ∣ t i) {α : ℝ} (hα : 2 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / s i - 1)) {p m L : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p)
    (WA : ∀ i, ZMod (t i) → ℤ → ℤ) (WE : ∀ i, ZMod (s i) → ℤ → ℤ) (WD : ∀ i, ZMod (s i) → ℤ)
    (hWA : ∀ i k j, |(WA i k j : ℝ) - 2 ^ p * resampWeight (s i) (t i) α k j| ≤ 2)
    (hWE : ∀ i ℓ h, |(WE i ℓ h : ℝ) - 2 ^ p * Real.exp (normExp (s i) (t i) α ℓ.val h)| ≤ 2)
    (hWD : ∀ i ℓ, |(WD i ℓ : ℝ) - 2 ^ p * dPrime (s i) (t i) α ℓ| ≤ 2)
    (hWD1 : ∀ i ℓ, 0 ≤ WD i ℓ ∧ WD i ℓ ≤ 2 ^ p)
    {a' : ((i : Fin d) → ZMod (t i)) → ℂ}
    (ha' : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW t s j)‖ ≤ 2 ∧ ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)}
    (hM' : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖M' f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
        ‖M' f g‖ ≤ 701 / 1000)
    (hd : 0 < d) (hsmall : 2 * d * p ^ 2 ≤ (∏ i, t i) * L)
    (hEs : 9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p / 100) :
    ApproxOn p (sourceApprox s t p (d * (2 * ⌈α ^ 2⌉₊ + 2))
        (fun i => resampANum (s i) (t i) m (termW p fun k j => (WA i k j : ℝ) / 2 ^ p))
        (fun i => resampB₀NumW p (sqrtWindow p) (fun ℓ h => (WE i ℓ h : ℝ) / 2 ^ p)
          fun ℓ => (WD i ℓ : ℝ) / 2 ^ p) a' M')
        (permRCLM s t ∘L dftDCLM s) (1 / 2)
        (9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L) ∧
      ApproxOn p (oppApprox s t p (d * (2 * ⌈α ^ 2⌉₊ + 2))
        (fun i => resampANum (s i) (t i) m (termW p fun k j => (WA i k j : ℝ) / 2 ^ p))
        (fun i => resampB₀NumW p (sqrtWindow p) (fun ℓ h => (WE i ℓ h : ℝ) / 2 ^ p)
          fun ℓ => (WD i ℓ : ℝ) / 2 ^ p) a' M')
        (permRCLM s t ∘L dftDPlusCLM s) (1 / 2)
        (9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L) := by
  choose J hJ hAn hBn hA' hB' hεA hεB hA'1 hB'1 using fun i =>
    permuted_numeric_tabled (hst i) (hcop i) hα (hθ i) hαp hm hm1 hmp hp (WA i) (WE i) (WD i)
      (hWA i) (hWE i) (hWD i) (hWD1 i)
  exact sourceErr_of_components heven J hJ hAn hBn
    (fun i v hv => (hA' i v hv).trans (hεA i).le) hA'1
    (fun i v hv => (hB' i v hv).trans (hεB i).le) hB'1 ha' hM' hd (by omega) hsmall hEs

end Tables

end IntegerMultBounds.MathlibTM2.Mult.SourceErr
