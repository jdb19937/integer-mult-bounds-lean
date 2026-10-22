module

public import IntegerMultBounds.MathlibTM2.Routing.MaskedEndpoint

/-!
# Complete masked schedule with actual intermediate source reads

The read is a function of the complete preserved target observation and an
unchanged spectator word. Both load and unload read their actual current state;
freezing is a theorem derived from the early-pass source-preservation proof.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par)

def slotRead (active : Fin p.n → Bool)
    (read : (ℕ × (Fin p.n → ℕ) × ℕ) → ℕ → ℕ → ℕ) (y x : ℕ) : ℕ → ℕ :=
  read (slotView p active y) x

/-- The actual intermediate load and unload read the original source observation.
No source copy, initialized borrowed value or assumed callback run is used. -/
theorem selectiveRun_freeze (active : Fin p.n → Bool)
    (read : (ℕ × (Fin p.n → ℕ) × ℕ) → ℕ → ℕ → ℕ)
    {v : V} (hv : Fits p v) (hgood : Good p v) (hG : 0 < p.G) (hK : 1 ≤ p.K) :
    selectiveRun p active (slotRead p active read) prog v =
      selectiveRun p active (fun _ _ => slotRead p active read v.y v.x) prog v := by
  let src := slotRead p active read v.y v.x
  let v₁ := maskedRun p active E v
  have hv₁ := (maskedRun_E_good active hv hG hgood hK).1
  have hg₁ := (maskedRun_E_good active hv hG hgood hK).2
  have hview₁ := maskedRun_E_view active hv hG
    (fun c hc => (hgood c hc).1) (fun c hc => (hgood c hc).2.2) hK
  have hx₁ : v₁.x = v.x := by
    have hE := maskedRun_E p active hv hG
      (fun c hc => (hgood c hc).1) (fun c hc => (hgood c hc).2.2) hK
    simpa only using congrArg V.x hE
  have hread₁ : slotRead p active read v₁.y v₁.x = src := by
    unfold slotRead
    rw [hview₁, hx₁]
    rfl
  let v₂ : V := { v₁ with u := rotv p.wc false (casm p.G p.n src) v₁.u }
  have hv₂ : Fits p v₂ := ⟨hv₁.b, hv₁.t, by exact rotv_lt p.wc false (casm p.G p.n src) v₁.u, hv₁.y⟩
  have ht₂ : ∀ c < p.n, cdig p.G c v₂.t + 1 < 2 ^ p.G := fun c hc => (hg₁ c hc).1
  have hg₂ : ∀ c < p.n, seg p.ρ p.K c v₂.y / 2 + 2 ^ p.G < 2 ^ (p.K - 1) :=
    fun c hc => (hg₁ c hc).2.2
  let v₃ := maskedRun p active E v₂
  have hview₃ := maskedRun_E_view active hv₂ hG ht₂ hg₂ hK
  have hx₃ : v₃.x = v₁.x := by
    simpa only using congrArg V.x (maskedRun_E p active hv₂ hG ht₂ hg₂ hK)
  have hread₃ : slotRead p active read v₃.y v₃.x = src := by
    unfold slotRead
    rw [hview₃, hx₃]
    exact hread₁
  rw [selectiveRun_prog, selectiveRun_prog]
  dsimp only
  rw [hread₁]
  change ({ v₃ with u := rotv p.wc true (casm p.G p.n
    (slotRead p active read v₃.y v₃.x)) v₃.u } : V) =
      { v₃ with u := rotv p.wc true (casm p.G p.n src) v₃.u }
  rw [hread₃]

/-- The complete actual-source selective schedule restores the borrowed fields,
keeps all spectators, and toggles only active target coordinates. -/
theorem selectiveRun_dynamic_good (active : Fin p.n → Bool)
    (read : (ℕ × (Fin p.n → ℕ) × ℕ) → ℕ → ℕ → ℕ)
    (hbits : ∀ obs x c, read obs x c = 0 ∨ read obs x c = 1)
    {v : V} (hv : Fits p v) (hgood : Good p v) (hG : 0 < p.G) (hK : 1 ≤ p.K) :
    selectiveRun p active (slotRead p active read) prog v =
      { v with y := togY p (activeSource p active (slotRead p active read v.y v.x)) v.y } := by
  rw [selectiveRun_freeze p active read hv hgood hG hK]
  exact selectiveRun_frozen_good p active _ (hbits _ _) hv hgood hG hK

end IntegerMultBounds.MathlibTM2.Routing
