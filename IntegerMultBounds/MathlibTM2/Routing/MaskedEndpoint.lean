module

public import IntegerMultBounds.MathlibTM2.Routing.MaskedSchedule

/-!
# Complete masked schedule endpoint

The frozen-source argument reuses the existing no-carry compact arithmetic and
later-source identity. Dynamic source reads will be frozen only by the checked
preservation of the complete source observation after each early pass.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par)

/-- Two masked early passes with an arbitrary fixed source bit list restore all
borrowed fields and toggle exactly the active requested targets. -/
theorem selectiveRun_frozen_good (active : Fin p.n → Bool) (src : ℕ → ℕ)
    (hsrc : ∀ c, src c = 0 ∨ src c = 1) {v : V} (hv : Fits p v)
    (hgood : Good p v) (hG : 0 < p.G) (hK : 1 ≤ p.K) :
    selectiveRun p active (fun _ _ => src) prog v =
      { v with y := togY p (activeSource p active src) v.y } := by
  have ht := fun c hc => (hgood c hc).1
  have hu := fun c hc => (hgood c hc).2.1
  have hg := fun c hc => (hgood c hc).2.2
  let z (c : ℕ) := zc p c (maskedView p active v)
  let y₁ := togY p z v.y
  have hz : ∀ c, z c = 0 ∨ z c = 1 := fun c => zc_cases c _
  have hp₁ := togY_parts hv.y hz hg hK
  have hE₁ : maskedRun p active E v = { v with y := y₁ } :=
    maskedRun_E p active hv hG ht hg hK
  let u₁ (c : ℕ) := cdig p.G c v.u + src c
  have hu₁ : ∀ c < p.n, u₁ c < 2 ^ p.G := by
    intro c hc
    have hu' := hu c hc
    have hs := hsrc c
    dsimp [u₁]
    omega
  have hu₀ : v.u = casm p.G p.n (fun c => cdig p.G c v.u) := eq_casm p.G p.n v.u hv.u
  have hload : rotv p.wc false (casm p.G p.n src) v.u = casm p.G p.n u₁ := by
    conv_lhs => rw [hu₀]
    exact rotv_pos_casm hu₁
  let v₂ : V := { v with y := y₁, u := casm p.G p.n u₁ }
  have hv₂ : Fits p v₂ := ⟨hv.b, hv.t, casm_lt hu₁, hp₁.1⟩
  have hg₁ : ∀ c < p.n, seg p.ρ p.K c y₁ / 2 + 2 ^ p.G < 2 ^ (p.K - 1) := by
    intro c hc
    rw [hp₁.2.2.2 c hc, tog_div_two (hz c)]
    exact hg c hc
  have hE₂ := maskedRun_E p active hv₂ hG ht hg₁ hK
  have hy₂ : togY p (fun c => zc p c (maskedView p active v₂)) y₁ =
      togY p (activeSource p active src) v.y := by
    unfold togY
    rw [hp₁.2.1, hp₁.2.2.1]
    apply asm_congr
    intro c hc
    rw [hp₁.2.2.2 c hc]
    change tog (tog (seg p.ρ p.K c v.y) (zc p c (maskedView p active v)))
      (zc p c (maskedView p active v₂)) = _
    rw [zc_maskedView p hG active v ⟨c, hc⟩, zc_maskedView p hG active v₂ ⟨c, hc⟩]
    have hc₁ : cdig p.G c (casm p.G p.n u₁) = u₁ c := cdig_casm hu₁ hc
    by_cases ha : active ⟨c, hc⟩ = true
    · simp only [ha, ite_true]
      change tog (tog (seg p.ρ p.K c v.y) (cdig p.G c v.u % 2))
        (cdig p.G c (casm p.G p.n u₁) % 2) = _
      rw [hc₁]
      simpa [u₁, activeSource, hc, ha] using
        tog_tog (seg p.ρ p.K c v.y) (cdig p.G c v.u) (src c) (hsrc c)
    · simp [ha, activeSource, hc, tog_zero]
  have hunload : rotv p.wc true (casm p.G p.n src) (casm p.G p.n u₁) = v.u := by
    rw [rotv_neg_casm hu₁ (fun c _ => Nat.le_add_left _ _), hu₀]
    exact casm_congr fun c _ => by simp [u₁]
  rw [selectiveRun_prog, hE₁]
  dsimp only
  rw [hload]
  change ({ maskedRun p active E v₂ with
    u := rotv p.wc true (casm p.G p.n src) (maskedRun p active E v₂).u } : V) = _
  rw [hE₂]
  dsimp only
  rw [hy₂, hunload]

end IntegerMultBounds.MathlibTM2.Routing
