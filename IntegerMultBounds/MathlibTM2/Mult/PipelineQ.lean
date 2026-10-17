module

public import IntegerMultBounds.MathlibTM2.Mult.Pipeline
public import IntegerMultBounds.MathlibTM2.Mult.SynthErrQ

/-!
# The box convolution with approximate rounds

`boxConvSuccQ` is `boxConvSucc` with `M̃_r = synthMrQ F O`: computed forward and opposite rounds
within `etaQ p τ` of the exact rounds. `boxConvQ` is its form for any number of axes, with a pair
of rounds `RoundPairs` on the box (nothing on the empty box), and `convBoxQ n` the instance on the
pipeline box. `convBoxQ_spec`: for `0 ≤ τ ≤ 1/8` it has the guarantee `BoxConvSpec` of the source
transforms, so `pipeline_correctG` applies.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.Pipeline

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Mult.Rounds ComplexConv

/-- The axis exponents of the box without its last axis. -/
noncomputable def boxAx {D : ℕ} (t : Fin (D + 1) → ℕ) : Fin D → ℕ := fun i => Nat.log 2 (t i.castSucc)

/-- A forward and an opposite computed round on the box `t`, within `etaQ p τ`. -/
def RoundPairs (p : ℕ) (τ : ℝ) : (D : ℕ) → (t : Fin D → ℕ) → (∀ i, NeZero (t i)) → Type
  | 0, _, _ => Unit
  | D + 1, t, inst =>
    haveI : NeZero (t (Fin.last D)) := inst _
    RoundOp (r := t (Fin.last D)) (List.ofFn (boxAx t)).sum p (fwdRound (List.ofFn (boxAx t)))
        (etaQ p τ) ×
      RoundOp (r := t (Fin.last D)) (List.ofFn (boxAx t)).sum p (oppRound (List.ofFn (boxAx t)))
        (etaQ p τ)

/-- `boxConvSucc` with the computed rounds `F`, `O`. -/
noncomputable def boxConvSuccQ (p D : ℕ) (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] {τ : ℝ}
    (FO : RoundPairs p τ (D + 1) t inferInstance) :
    (((i : Fin (D + 1)) → ZMod (t i)) → ℂ) → (((i : Fin (D + 1)) → ZMod (t i)) → ℂ) →
      (((i : Fin (D + 1)) → ZMod (t i)) → ℂ) :=
  cconvApproxVia (boxSplit t rfl) p (twistPlus p (t (Fin.last D)))
    (twistMinus p (t (Fin.last D)))
    (synthMrQ (boxAx t) (fun i => t i.castSucc) FO.1 FO.2)

/-- `boxConvSuccQ` for any number of axes (`0` on the empty box). -/
noncomputable def boxConvQ (p : ℕ) {τ : ℝ} : (D : ℕ) → (t : Fin D → ℕ) → (inst : ∀ i, NeZero (t i)) →
    RoundPairs p τ D t inst →
    (((i : Fin D) → ZMod (t i)) → ℂ) → (((i : Fin D) → ZMod (t i)) → ℂ) →
      (((i : Fin D) → ZMod (t i)) → ℂ)
  | 0, _, _, _ => fun _ _ => 0
  | D + 1, t, _, FO => boxConvSuccQ p D t FO

theorem boxConvSuccQ_spec {p D : ℕ} (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] {ℓ0 L : ℕ} {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ8 : τ ≤ 1 / 8) (FO : RoundPairs p τ (D + 1) t inferInstance)
    (hr2 : 2 ≤ t (Fin.last D)) (hpow : ∀ i, t i = 2 ^ Nat.log 2 (t i))
    (hdvd : ∀ i, t i ∣ 2 * t (Fin.last D)) (hlog : ∀ i, Nat.log 2 (t i) ≤ ℓ0) (hℓ0 : 1 ≤ ℓ0)
    (hℓL : ℓ0 ≤ L) (h9 : 9 ≤ ((∏ i, t i : ℕ) : ℝ) * L)
    (hE : 5000 * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p)
    (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 7 / 10) :
    2 ^ p * ‖boxConvSuccQ p D t FO f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
      ‖boxConvSuccQ p D t FO f g‖ ≤ 701 / 1000 := by
  have hA : nRounds (boxAx t) ≤ ℓ0 := Finset.sup_le fun i _ => hlog _
  have hprod : ((t (Fin.last D) * ∏ i, (fun i : Fin D => t i.castSucc) i : ℕ) : ℝ) =
      ((∏ i, t i : ℕ) : ℝ) := by
    rw [Fin.prod_univ_castSucc, mul_comm]
  have hlt := eSynthQ_lt (r := t (Fin.last D)) (boxAx t) (fun i => t i.castSucc) hr2 hA hℓ0 hℓL
    hτ hτ8
  rw [hprod] at hlt
  have hθ := twist_phaseApprox p (t (Fin.last D))
  have hR := synthMrQ_ringApprox (r := t (Fin.last D)) (boxAx t) (fun i => t i.castSucc)
    (fun i => hpow i.castSucc) (fun i => (hpow i.castSucc) ▸ hdvd i.castSucc) FO.1 FO.2
  have h := cconvApprox_box t rfl hθ.1 hθ.2 hR (by linarith) f g hf hg
  refine ⟨h.1.trans (by linarith), h.2⟩

theorem boxConvQ_spec {p : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (hτ8 : τ ≤ 1 / 8) :
    ∀ {D : ℕ} (t : Fin D → ℕ) [inst : ∀ i, NeZero (t i)] (FO : RoundPairs p τ D t inst)
    {ℓ0 L R : ℕ},
    0 < D → (∀ i : Fin D, (i : ℕ) + 1 = D → t i = R) → 2 ≤ R →
    (∀ i, t i = 2 ^ Nat.log 2 (t i)) → (∀ i, t i ∣ 2 * R) → (∀ i, Nat.log 2 (t i) ≤ ℓ0) →
    1 ≤ ℓ0 → ℓ0 ≤ L → 9 ≤ ((∏ i, t i : ℕ) : ℝ) * L →
    5000 * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p →
    ∀ f g : ((i : Fin D) → ZMod (t i)) → ℂ, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖boxConvQ p D t inst FO f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
        ‖boxConvQ p D t inst FO f g‖ ≤ 701 / 1000
  | 0, _, _, _, _, _, _, hD, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hD (lt_irrefl 0)
  | D + 1, t, _, FO, ℓ0, L, R, _, hlast, hR, hpow, hdvd, hlog, hℓ0, hℓL, h9, hE, f, g, hf, hg => by
    have hl : t (Fin.last D) = R := hlast _ rfl
    subst hl
    exact boxConvSuccQ_spec t hτ hτ8 FO hR hpow hdvd hlog hℓ0 hℓL h9 hE f g hf hg

section Sizes

open Sizes

variable {n : ℕ}

/-- The computed complex convolution with computed rounds on the pipeline box. -/
noncomputable def convBoxQ (n : ℕ) {τ : ℝ} (FO : RoundPairs (p n) τ (d n) (t n) inferInstance) :
    BoxConvOf n :=
  boxConvQ (p n) (d n) (t n) inferInstance FO

/-- **The guarantee of the box convolution with computed rounds.** -/
theorem convBoxQ_spec (h : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * T n * logT n ≤ 2 ^ p n / 100) {τ : ℝ} (hτ : 0 ≤ τ)
    (hτ8 : τ ≤ 1 / 8) (FO : RoundPairs (p n) τ (d n) (t n) inferInstance) :
    BoxConvSpec n (convBoxQ n FO) := by
  intro f g hf hg
  have hd1 := h.one_le_d
  have hpT : ∏ i, t n i = T n := prod_t hd1
  have h9 : 9 ≤ ((∏ i, t n i : ℕ) : ℝ) * logT n := by
    have hp := h.thirteen_le_p
    have hD := h.2
    have : 9 ≤ (∏ i, t n i) * logT n := by
      rw [hpT]
      have : 9 ≤ 2 * d n * p n ^ 2 := by nlinarith
      omega
    exact_mod_cast this
  have hE : 5000 * ((∏ i, t n i : ℕ) : ℝ) * logT n ≤ 2 ^ p n := by
    have hg4 : (16 : ℝ) ≤ 2 ^ gamma n :=
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ gamma n := pow_le_pow_right₀ (by norm_num) (four_le_gamma h)
    have hX : (0 : ℝ) ≤ (T n : ℝ) * logT n := by positivity
    rw [hpT]
    nlinarith
  exact boxConvQ_spec hτ hτ8 (t n) FO (by omega) (t_of_last h) (two_le_r h) (t_pow_log n)
    (t_dvd_two_r n) (log_t_le n) (by have := h.two_le_ℓ; omega) (ℓ_le_logT h) h9 hE f g hf hg

end Sizes

end IntegerMultBounds.MathlibTM2.Mult.Pipeline
