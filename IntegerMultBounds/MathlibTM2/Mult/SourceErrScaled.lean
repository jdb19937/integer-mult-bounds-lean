module

public import IntegerMultBounds.MathlibTM2.Mult.SourceErr
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The source transform with scaled line maps

`sourceErr_of_components` with the per-line exponent `c` and the line operators `Aℓ`, `Bℓ`
given by a factorization `P_s F_s = 2^c Bℓ P_t F_t Aℓ` on every axis, so `γ = d c`. A line map
that approximates a scaled operator `2^-j ℬ₀` (the banded `B̃₀`) enters with `Bℓ = 2^-j ℬ₀` and
`c = 2⌈α²⌉ + 2 + j` (`sourceErr_of_componentsC`, `exact_product_of_componentsC`).
-/

@[expose] public section

open IntegerMultBounds IntegerMultBounds.NLogN
open scoped Function

namespace IntegerMultBounds.MathlibTM2.Mult.SourceErr

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- The tensor factorization from per-line factorizations with exponent `c`. -/
theorem factorization_multiC (c : ℕ) (Aℓ : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (t i) → ℂ))
    (Bℓ : ∀ i, (ZMod (t i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, permSCLM (t i) ∘L dftCLM (s i) = ((2 : ℂ) ^ c) •
      (Bℓ i ∘L permTCLM (s i) ∘L dftCLM (t i) ∘L Aℓ i)) :
    permRCLM s t ∘L dftDCLM s = ((2 : ℂ) ^ (d * c)) •
      (tensorRCLM Bℓ ∘L permQCLM s t ∘L dftDCLM t ∘L tensorRCLM Aℓ) := by
  unfold permRCLM permQCLM
  rw [dftDCLM_eq_tensor, dftDCLM_eq_tensor, ← tensorRCLM_comp]
  have e : (fun i => permSCLM (t i) ∘L dftCLM (s i)) = fun i =>
      ((2 : ℂ) ^ c) • (Bℓ i ∘L permTCLM (s i) ∘L dftCLM (t i) ∘L Aℓ i) :=
    funext hJ
  rw [e, tensorRCLM_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
    mul_comm c d, tensorRCLM_comp Bℓ (fun i => permTCLM (s i) ∘L dftCLM (t i) ∘L Aℓ i),
    tensorRCLM_comp (fun i => permTCLM (s i)) (fun i => dftCLM (t i) ∘L Aℓ i),
    tensorRCLM_comp (fun i => dftCLM (t i)) Aℓ]

/-- **The source transform with line operators of exponent `c`.** -/
theorem sourceErr_of_componentsC (heven : ∀ i, 2 ∣ t i) {p L c : ℕ}
    (Aℓ : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (t i) → ℂ))
    (Bℓ : ∀ i, (ZMod (t i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, permSCLM (t i) ∘L dftCLM (s i) = ((2 : ℂ) ^ c) •
      (Bℓ i ∘L permTCLM (s i) ∘L dftCLM (t i) ∘L Aℓ i))
    (hAn : ∀ i, ‖Aℓ i‖ ≤ 1) (hBn : ∀ i, ‖Bℓ i‖ ≤ 1)
    {A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ} {B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ}
    (hA' : ∀ i, ApproxMap p (A' i) (Aℓ i) ((p : ℝ) ^ 2))
    (hA'1 : ∀ i u, ‖u‖ ≤ 1 → ‖A' i u‖ ≤ 1)
    (hB' : ∀ i, ApproxMap p (B' i) (Bℓ i) ((p : ℝ) ^ 2))
    (hB'1 : ∀ i w, ‖w‖ ≤ 1 → ‖B' i w‖ ≤ 1)
    {a' : ((i : Fin d) → ZMod (t i)) → ℂ}
    (ha' : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW t s j)‖ ≤ 2 ∧ ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)}
    (hM' : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖M' f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
        ‖M' f g‖ ≤ 701 / 1000)
    (hd : 0 < d) (hp : 2 ≤ p) (hsmall : 2 * d * p ^ 2 ≤ (∏ i, t i) * L)
    (hEs : 9 * (2 : ℝ) ^ (d * c) * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p / 100) :
    ApproxOn p (sourceApprox s t p (d * c) A' B' a' M')
        (permRCLM s t ∘L dftDCLM s) (1 / 2)
        (9 * (2 : ℝ) ^ (d * c) * ((∏ i, t i : ℕ) : ℝ) * L) ∧
      ApproxOn p (oppApprox s t p (d * c) A' B' a' M')
        (permRCLM s t ∘L dftDPlusCLM s) (1 / 2)
        (9 * (2 : ℝ) ^ (d * c) * ((∏ i, t i : ℕ) : ℝ) * L) := by
  set γ := d * c with hγ
  set X : ℝ := ((∏ i, t i : ℕ) : ℝ) * L with hX
  have hfact := factorization_multiC c Aℓ Bℓ hJ
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

variable (hs : Pairwise (Nat.Coprime on s))

/-- **The exact product with line operators of exponent `c`.** -/
theorem exact_product_of_componentsC (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (heven : ∀ i, 2 ∣ t i) {p L c : ℕ}
    (Aℓ : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (t i) → ℂ))
    (Bℓ : ∀ i, (ZMod (t i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, permSCLM (t i) ∘L dftCLM (s i) = ((2 : ℂ) ^ c) •
      (Bℓ i ∘L permTCLM (s i) ∘L dftCLM (t i) ∘L Aℓ i))
    (hAn : ∀ i, ‖Aℓ i‖ ≤ 1) (hBn : ∀ i, ‖Bℓ i‖ ≤ 1)
    {A' : ∀ i, (ZMod (s i) → ℂ) → ZMod (t i) → ℂ} {B' : ∀ i, (ZMod (t i) → ℂ) → ZMod (s i) → ℂ}
    (hA' : ∀ i, ApproxMap p (A' i) (Aℓ i) ((p : ℝ) ^ 2))
    (hA'1 : ∀ i u, ‖u‖ ≤ 1 → ‖A' i u‖ ≤ 1)
    (hB' : ∀ i, ApproxMap p (B' i) (Bℓ i) ((p : ℝ) ^ 2))
    (hB'1 : ∀ i w, ‖w‖ ≤ 1 → ‖B' i w‖ ≤ 1)
    {a' : ((i : Fin d) → ZMod (t i)) → ℂ}
    (ha' : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW t s j)‖ ≤ 2 ∧ ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)}
    (hM' : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖M' f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
        ‖M' f g‖ ≤ 701 / 1000)
    (hd : 0 < d) (hp : 2 ≤ p) (hsmall : 2 * d * p ^ 2 ≤ (∏ i, t i) * L)
    (hEs : 9 * (2 : ℝ) ^ (d * c) * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p / 100)
    {k : ℕ} (hk : 0 < k) {x y : List Bool}
    (hS : (digitsOf k x).length + (digitsOf k y).length ≤ (∏ i, s i) + 1)
    (hfinal : (2 : ℝ) ^ (2 * k + 4) * ((∏ i, s i : ℕ) : ℝ) ^ 2 *
      (3 * (9 * (2 : ℝ) ^ (d * c) * ((∏ i, t i : ℕ) : ℝ) * L) + 2) < 2 ^ p / 2) :
    evalBase (2 ^ k) (List.ofFn fun i : Fin (∏ i, s i) =>
      (round (((2 : ℂ) ^ (2 * k) * ((∏ i, s i : ℕ) : ℂ)) *
        ExactRecovery.computedConv (p := p) (k := k)
          (crtSourceApprox hs p (d * c) A' B' a' M')
          (crtOppApprox hs p (d * c) A' B' a' M') x y
          (i.val : ZMod (∏ i, s i))).re).toNat) =
      IntegerMultBounds.Machine.binaryValue x * IntegerMultBounds.Machine.binaryValue y := by
  obtain ⟨hF, hG⟩ := sourceErr_of_componentsC heven Aℓ Bℓ hJ hAn hBn hA' hA'1 hB' hB'1 ha' hM'
    hd hp hsmall hEs
  exact exact_product_crt s t hs hcop _ _ hk hS (crtSource_err hs hF) (crtOpp_err hs hG) hEs
    hfinal

end IntegerMultBounds.MathlibTM2.Mult.SourceErr
