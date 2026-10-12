module

public import IntegerMultBounds.Resampling.Script
public import IntegerMultBounds.Machine.BinaryInterchangeBudget

/-! The cost of one swap record of the tensor driver: at most a constant times
the array length times the larger field width to the power `τ`
(`swapCost_le`), from the interchange's uniform budget. -/

@[expose] public section

namespace IntegerMultBounds.Resampling.SwapCost
noncomputable section

open Machine Schoenhage AxisDriver Script

theorem advance_length : ∀ (n : ℕ) (bs : List Bool), (GrowingCounterData.advance n bs).length ≤ bs.length + n
  | 0, _ => by simp [GrowingCounterData.advance]
  | n + 1, bs => by
    have := advance_length n (GrowingCounterData.increment bs)
    have h2 := (GrowingCounterData.increment_length bs).2
    simp only [GrowingCounterData.advance]; omega

theorem bin_length (n : ℕ) : (bin n).length ≤ n := by
  have := advance_length n []; simpa [bin] using this

theorem words_swIn (hs : List (List Bool)) (A : List Bool) (i : Fin 6) :
    SwapPrim.words (swIn hs A) i = if i.val < 5 then hs.getD i.val [] else A := by
  simp only [SwapPrim.words, swIn, SwapPrim.slot_val]
  have := i.isLt
  by_cases h5 : i.val < 5
  · simp [h5, reg]
  · have : i.val = 5 := by omega
    simp [this, reg]

theorem swapCost_le : ∃ C : ℝ, 0 < C ∧ ∀ (P G h d B : ℕ) (A : List Bool), 0 < P → 0 < G → 0 < B →
    h ≤ d + 1 → d ≤ h + 1 → A.length = P * 2 ^ h * G * 2 ^ d * B →
    (swapCost (swapHdrsG P G h d B) A : ℝ) ≤ C * A.length * ((max 1 (max h d) : ℕ) : ℝ) ^ Parameters.tau := by
  obtain ⟨C0, hC0, hb⟩ := BinaryInterchangeRun.uniform_bound
  refine ⟨C0 + 2000, by linarith, fun P G h d B A hP hG hB hhd hdh hl => ?_⟩
  set hs := swapHdrsG P G h d B
  set N := A.length
  have h2h : 0 < 2 ^ h := by positivity
  have h2d : 0 < 2 ^ d := by positivity
  have hN : 1 ≤ N := by rw [hl]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hPN : P ≤ N := by rw [hl, show P * 2 ^ h * G * 2 ^ d * B = P * (2 ^ h * G * 2 ^ d * B) by ring]
                         exact Nat.le_mul_of_pos_right _ (by positivity)
  have hGN : G ≤ N := by rw [hl, show P * 2 ^ h * G * 2 ^ d * B = G * (P * 2 ^ h * 2 ^ d * B) by ring]
                         exact Nat.le_mul_of_pos_right _ (by positivity)
  have hBN : B ≤ N := by rw [hl, show P * 2 ^ h * G * 2 ^ d * B = B * (P * 2 ^ h * G * 2 ^ d) by ring]
                         exact Nat.le_mul_of_pos_right _ (by positivity)
  have hhN : h ≤ N := by
    have := Nat.lt_two_pow_self (n := h)
    rw [hl, show P * 2 ^ h * G * 2 ^ d * B = 2 ^ h * (P * G * 2 ^ d * B) by ring]
    have := Nat.le_mul_of_pos_right (2 ^ h) (show 0 < P * G * 2 ^ d * B by positivity); omega
  have hdN : d ≤ N := by
    have := Nat.lt_two_pow_self (n := d)
    rw [hl, show P * 2 ^ h * G * 2 ^ d * B = 2 ^ d * (P * 2 ^ h * G * B) by ring]
    have := Nat.le_mul_of_pos_right (2 ^ d) (show 0 < P * 2 ^ h * G * B by positivity); omega
  have hlen : ∀ x ∈ hs, x.length ≤ N := by
    intro x hx
    simp only [hs, swapHdrsG, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact (bin_length _).trans (by assumption)
  have hw := words_swIn hs A
  have hv : ∀ i : Fin 5, SwapPrim.vals (swIn hs A) i = BinaryInterchangeRun.values P G B h d i := by
    intro i
    simp only [SwapPrim.vals, SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [hs, swapHdrsG, value_bin, BinaryInterchangeRun.values]
  have hcan : ∀ i : Fin 5, GrowingCounterData.Canonical (SwapPrim.hdr (SwapPrim.words (swIn hs A)) i) := by
    intro i
    simp only [SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [hs, swapHdrsG, canonical_bin]
  have hbir := hb P G B h d (SwapPrim.hdr (SwapPrim.words (swIn hs A))) hP hG hB hhd hdh (fun i => hv i) hcan
  rw [show (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B : ℝ) = N by
    simp [BinaryAdjacentWidthInterchange.volume, N, hl]] at hbir
  have hsw : (SwapPrim.swapped (swIn hs A)).length = N := by
    simp only [SwapPrim.swapped, AxisRounds.length_swapList, hv, BinaryInterchangeRun.values]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, N, hl]
    simp only [Fin.succ_one_eq_two, Matrix.cons_val_succ]
    rw [show (![B, h, d] 2) = d from rfl, show (![G, B, h, d] 2) = h from rfl]
    ring
  have l0 := bin_length P
  have l1 := bin_length G
  have l2 := bin_length B
  have l3 := bin_length h
  have l4 := bin_length d
  have hnat : swapCost hs A ≤ 2000 * N + BinaryInterchangeRun.cost P G B h d
      (SwapPrim.hdr (SwapPrim.words (swIn hs A))) := by
    have e1 : SwapPrim.cost (swIn hs A) = SwapPrim.inCost (SwapPrim.words (swIn hs A)) + 1 +
        (BinaryInterchangeRun.cost P G B h d (SwapPrim.hdr (SwapPrim.words (swIn hs A))) + 1 +
          SwapPrim.outCost (Function.update (SwapPrim.words (swIn hs A)) 5 (SwapPrim.swapped (swIn hs A)))) := by
      simp only [SwapPrim.cost, hv, BinaryInterchangeRun.values]; rfl
    simp only [swapCost, e1, SwapPrim.inCost, SwapPrim.outCost, hw, Function.update_apply]
    simp (config := {decide := true}) only [hs, swapHdrsG, loadCost, clen, List.getD_cons_zero,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ite_true, ite_false,
      Fin.val_zero, Fin.isValue]
    simp
    have hsw' : (SwapPrim.swapped (swIn [bin P, bin G, bin B, bin h, bin d] A)).length = A.length := hsw
    omega
  have hM : (1 : ℝ) ≤ ((max 1 (max h d) : ℕ) : ℝ) ^ Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left _ _) (by norm_num [Parameters.tau])
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcast : (swapCost hs A : ℝ) ≤ 2000 * N + (BinaryInterchangeRun.cost P G B h d
      (SwapPrim.hdr (SwapPrim.words (swIn hs A))) : ℝ) := by exact_mod_cast hnat
  calc (swapCost hs A : ℝ) ≤ 2000 * N + C0 * N * ((max 1 (max h d) : ℕ) : ℝ) ^ Parameters.tau := by linarith
    _ ≤ (C0 + 2000) * N * ((max 1 (max h d) : ℕ) : ℝ) ^ Parameters.tau := by nlinarith

end
end IntegerMultBounds.Resampling.SwapCost
