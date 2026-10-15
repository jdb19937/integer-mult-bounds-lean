module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectSource
public import IntegerMultBounds.MathlibTM2.Cost.CRTDirectFull

/-! # Cost matching for the executable direct CRT entry -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast
noncomputable section

/-- The exact entry program budget, uniformly in the chosen direction. -/
theorem crtDirectEntry_pipeline_le (Tm cw K : ℕ) :
    ∀ᶠ n in atTop, ∀ m c : ℕ, ∀ a s μ : Fin (m + 1) → ℕ,
      m + 1 = d n → (∑ j, a j) = logT n →
      (∀ j, a j = ℓ n ∨ a j = ℓ n - 1) →
      (∀ j, s j ≤ 2 ^ a j) → (∀ j, μ j ≤ s j) → c ≤ cw * p n →
      ∀ fwd : Bool, (crtDirectEntryCost (K := K) fwd Tm c a s μ : ℝ) ≤
        mtCrtDirectEntryC Tm cw * totDirectCRT n := by
  filter_upwards [crtDirectMachineEntry_pipeline_le Tm cw K] with n h m c a s μ
      hdim hL ha hs hμ hc fwd
  obtain ⟨hf, hi⟩ := h m 0 c a s μ hdim hL ha hs hμ (Nat.zero_le _) hc
  simp only [crtDirectSetupStream_length] at hf hi
  have hwidth : crtPre a (m + 1) = logT n := (crtControl_fullWidth a).trans hL
  cases fwd
  · simpa only [crtDirectEntryCost, Bool.false_eq_true, ↓reduceIte, hwidth,
      crtControl_fullWidth, hL, Nat.add_assoc] using hi
  · simpa only [crtDirectEntryCost, ↓reduceIte, hwidth,
      crtControl_fullWidth, hL, Nat.add_assoc] using hf

/-- The source-stage budget also matches for arbitrary runtime dimensions. -/
theorem crtDirectSource_pipeline_le (Tm cw K : ℕ) :
    ∀ᶠ n in atTop, ∀ k c : ℕ, ∀ a s μ : Fin k → ℕ,
      k = d n → (∑ j, a j) = logT n →
      (∀ j, a j = ℓ n ∨ a j = ℓ n - 1) →
      (∀ j, s j ≤ 2 ^ a j) → (∀ j, μ j ≤ s j) → c ≤ cw * p n →
      ∀ fwd : Bool, (crtDirectSourceCost (K := K) fwd Tm c a s μ : ℝ) ≤
        mtCrtDirectEntryC Tm cw * totDirectCRT n := by
  filter_upwards [crtDirectEntry_pipeline_le Tm cw K, eventually_big] with n h hb
    k c a s μ hdim hL ha hs hμ hc fwd
  cases k with
  | zero => have := hb.one_le_d; omega
  | succ k => exact h k c a s μ hdim hL ha hs hμ hc fwd

end
end IntegerMultBounds.MathlibTM2.Cost
