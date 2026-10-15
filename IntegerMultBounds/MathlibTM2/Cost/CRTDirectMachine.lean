module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectMachine
public import IntegerMultBounds.MathlibTM2.Cost.CRTControlTarget

/-! # Cost matching for the concrete direct CRT loops

The exact weighted target budgets are retained. Unary metadata traversal,
including the zero-target identity branch and loop tests, is absorbed into one
additional volume; no maximum target cost is multiplied by the dimension.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast

noncomputable section

/-- Separate the actual nonzero targets from every unary traversal charge. -/
theorem crtDirectMachineLoopCost_eq {d K : ℕ} (Tm B w c : ℕ)
    (a s μ : Fin (d + 1) → ℕ) :
    crtDirectMachineLoopCost (K := K) Tm B w c a s μ =
      (∑ i ∈ Finset.univ.erase (0 : Fin (d + 1)), crtControlTargetCost (K := K) Tm B w c a s i (μ i)) +
      12 * (∑ i, a i) + 4 * (∑ i, s i) + 4 * (∑ i, μ i) + 37 * (d + 1) + 3 := by
  have hsum := Finset.sum_erase_add (s := Finset.univ) (a := (0 : Fin (d + 1)))
    (f := crtDirectMachineBudget (K := K) Tm B w c a s μ) (by simp)
  have hnonzero : (∑ i ∈ Finset.univ.erase (0 : Fin (d + 1)),
      crtDirectMachineBudget (K := K) Tm B w c a s μ i) =
      ∑ i ∈ Finset.univ.erase (0 : Fin (d + 1)), crtControlTargetCost (K := K) Tm B w c a s i (μ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [crtDirectMachineBudget, (Finset.mem_erase.mp hi).1]
  rw [hnonzero] at hsum
  have hz : crtDirectMachineBudget (K := K) Tm B w c a s μ 0 = 1 := by
    simp [crtDirectMachineBudget]
  rw [hz] at hsum
  unfold crtDirectMachineLoopCost
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  omega

/-- Every unary bookkeeping term in the actual loop is eventually at most
one padded volume, uniformly over the permitted runtime parameter streams. -/
theorem crtDirectMachineMetadata_pipeline_le :
    ∀ᶠ n in atTop, ∀ m : ℕ, ∀ a s μ : Fin (m + 1) → ℕ,
      m + 1 = d n → (∑ j, a j) = logT n →
      (∀ j, a j ≤ ℓ n) → (∀ j, s j ≤ 2 ^ a j) → (∀ j, μ j ≤ s j) →
      12 * (∑ i, a i) + 4 * (∑ i, s i) + 4 * (∑ i, μ i) + 37 * (m + 1) + 3 ≤ T n := by
  filter_upwards [mt_poly_r_le_T 64 1, eventually_big] with n hpoly hb m a s μ hdim hL ha hs hμ
  have hrad : ∀ i, s i ≤ r n := fun i => (hs i).trans (Nat.pow_le_pow_right (by decide) (ha i))
  have hmu : ∀ i, μ i ≤ r n := fun i => (hμ i).trans (hrad i)
  have hsumS : (∑ i, s i) ≤ d n * r n := by
    calc
      _ ≤ ∑ _ : Fin (m + 1), r n := Finset.sum_le_sum fun i _ => hrad i
      _ = _ := by simp [hdim]
  have hsumM : (∑ i, μ i) ≤ d n * r n := by
    calc
      _ ≤ ∑ _ : Fin (m + 1), r n := Finset.sum_le_sum fun i _ => hmu i
      _ = _ := by simp [hdim]
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hb1 : 1 ≤ b n := by have := hb.sixteen_le_b; omega
  have hbR : b n ≤ b n * r n := Nat.le_mul_of_pos_right _ hr1
  have hd := d_le_b n
  have hL' := mt_logT_le_b hb
  have hdr : d n * r n ≤ b n * r n := Nat.mul_le_mul_right _ hd
  rw [hL]
  simp only [pow_one] at hpoly
  nlinarith

/-- The constant for an actual concrete forward or inverse target loop. -/
def mtCrtDirectMachineLoopC (Tm cw : ℕ) : ℝ := mtCrtControlTargetC Tm cw + 2

/-- Both executable target loops satisfy the linear-axis CRT envelope. The
remaining full-wrapper setup, padding/deletion, and reversal are separate. -/
theorem crtDirectMachineLoop_pipeline_le (Tm cw K : ℕ) :
    ∀ᶠ n in atTop, ∀ m w c : ℕ, ∀ a s μ : Fin (m + 1) → ℕ,
      m + 1 = d n → (∑ j, a j) = logT n →
      (∀ j, a j = ℓ n ∨ a j = ℓ n - 1) →
      (∀ j, s j ≤ 2 ^ a j) → (∀ j, μ j ≤ s j) →
      w ≤ 3 * logT n + 1 → c ≤ cw * p n →
      (crtDirectMachineLoopCost (K := K) Tm (logT n) w c a s μ : ℝ) ≤
      mtCrtDirectMachineLoopC Tm cw * totDirectCRT n := by
  filter_upwards [crtControlTarget_pipeline_le Tm cw K,
    crtDirectMachineMetadata_pipeline_le, eventually_big] with n htarget hmeta hb m w c a s μ
      hdim hL ha hs hμ hw hc
  have htargets := htarget m w c a s μ hdim hL ha hs hμ hw hc
  have hmeta' := hmeta m a s μ hdim hL (by intro i; rcases ha i with h | h <;> omega) hs hμ
  have hmetaReal := (Nat.cast_le (α := ℝ)).2 hmeta'
  have hT : (T n : ℝ) ≤ totDirectCRT n := by
    have hd : (1 : ℝ) ≤ d n := by exact_mod_cast hb.one_le_d
    have hdt := mt_directCRT_dT_le hb
    have ht0 : (0 : ℝ) ≤ T n := Nat.cast_nonneg _
    nlinarith
  rw [crtDirectMachineLoopCost_eq]
  push_cast at htargets hmetaReal ⊢
  unfold mtCrtDirectMachineLoopC
  nlinarith

end
end IntegerMultBounds.MathlibTM2.Cost
