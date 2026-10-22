module

public import IntegerMultBounds.MathlibTM2.Routing.MaskedGadget

/-!
# Preserved source observation of a masked early pass

The observation includes prefix and suffix spectators, all upper bits at active
targets, and complete inactive target digits. Actual source reads can depend on
this whole observation and therefore remain valid after either early pass.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par}

/-- Parts and range of a segmentwise parity toggle under the existing guards. -/
theorem togY_parts {y : ℕ} {z : ℕ → ℕ} (hy : y < 2 ^ p.wy)
    (hz : ∀ c, z c = 0 ∨ z c = 1)
    (hg : ∀ c < p.n, seg p.ρ p.K c y / 2 + 2 ^ p.G < 2 ^ (p.K - 1)) (hK : 1 ≤ p.K) :
    togY p z y < 2 ^ p.wy ∧
      togY p z y % 2 ^ p.ρ = y % 2 ^ p.ρ ∧
      togY p z y / 2 ^ (p.ρ + p.n * p.K) = y / 2 ^ (p.ρ + p.n * p.K) ∧
      ∀ c < p.n, seg p.ρ p.K c (togY p z y) = tog (seg p.ρ p.K c y) (z c) := by
  have hL : 2 ^ p.K = 2 * 2 ^ (p.K - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hs : ∀ c < p.n, tog (seg p.ρ p.K c y) (z c) < 2 ^ p.K := fun c hc => by
    rw [hL]
    exact tog_lt (hz c)
      (lt_of_le_of_lt (Nat.add_le_add_left Nat.one_le_two_pow _) (hg c hc))
  exact ⟨asm_lt (low_lt y) hs (top_lt hy), asm_mod (low_lt y),
    asm_div (low_lt y) hs, fun c hc => seg_asm (low_lt y) hs hc⟩

/-- The complete target information permitted to influence a source read. -/
def slotView (p : Par) (active : Fin p.n → Bool) (y : ℕ) :
    ℕ × (Fin p.n → ℕ) × ℕ :=
  (y % 2 ^ p.ρ,
    (fun c => if active c then seg p.ρ p.K c.val y / 2 else seg p.ρ p.K c.val y),
    y / 2 ^ (p.ρ + p.n * p.K))

/-- An early pass preserves complete spectators and every admissible source bit. -/
theorem maskedRun_E_view (active : Fin p.n → Bool) {v : V} (hv : Fits p v)
    (hG : 0 < p.G)
    (ht : ∀ c < p.n, cdig p.G c v.t + 1 < 2 ^ p.G)
    (hg : ∀ c < p.n, seg p.ρ p.K c v.y / 2 + 2 ^ p.G < 2 ^ (p.K - 1)) (hK : 1 ≤ p.K) :
    slotView p active (maskedRun p active E v).y = slotView p active v.y := by
  rw [maskedRun_E p active hv hG ht hg hK]
  have hz := fun c => zc_cases (p := p) c (maskedView p active v)
  have hp := togY_parts hv.y hz hg hK
  unfold slotView
  simp only
  rw [hp.2.1, hp.2.2.1]
  apply congrArg (fun f : Fin p.n → ℕ => (v.y % 2 ^ p.ρ, f, v.y / 2 ^ (p.ρ + p.n * p.K)))
  funext c
  rw [hp.2.2.2 c.val c.isLt]
  by_cases ha : active c = true
  · simp only [ha, ite_true]
    exact tog_div_two (hz c.val)
  · have hz0 : zc p c.val (maskedView p active v) = 0 := by
      rw [zc_maskedView p hG active v c]
      simp [ha]
    simp [ha, hz0, tog_zero]

/-- Range and guards survive a complete masked early pass. -/
theorem maskedRun_E_good (active : Fin p.n → Bool) {v : V} (hv : Fits p v)
    (hG : 0 < p.G) (hgood : Good p v) (hK : 1 ≤ p.K) :
    Fits p (maskedRun p active E v) ∧ Good p (maskedRun p active E v) := by
  have ht := fun c hc => (hgood c hc).1
  have hg := fun c hc => (hgood c hc).2.2
  rw [maskedRun_E p active hv hG ht hg hK]
  have hz := fun c => zc_cases (p := p) c (maskedView p active v)
  have hp := togY_parts hv.y hz hg hK
  refine ⟨⟨hv.b, hv.t, hv.u, hp.1⟩, fun c hc => ⟨(hgood c hc).1, (hgood c hc).2.1, ?_⟩⟩
  rw [hp.2.2.2 c hc, tog_div_two (hz c)]
  exact hg c hc

end IntegerMultBounds.MathlibTM2.Routing
