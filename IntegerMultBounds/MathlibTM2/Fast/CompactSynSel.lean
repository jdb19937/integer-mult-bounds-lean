module

import IntegerMultBounds.MathlibTM2.Fast.SynSel
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecPieces
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Reserved active pieces reuse a common row depth even when reservation reduces
active width. These are semantic validity and precision contracts for actual records;
they do not yet replace the running layer. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
noncomputable section

theorem compactSynPcs_ok (ds : ComplexFramedExecution.Directions) {K a D oS n w' J : ℕ}
    (hlevels : synJ D D - 1 ≤ J)
    (hfit : oS + K * D ≤ n)
    (hw : synE (gateCount (program ds)) (factorCount (program ds)) D D + D ≤ w') :
    ∀ pc ∈ synPcs K a D oS J D,
      pc.Ok ds K n w' (rowsAt (2 ^ a) J) := by
  intro pc hpc
  obtain ⟨j, hj, h0, rfl⟩ := mem_synPcs hpc
  have hpos := synDg_pos_div h0
  have hJ := lt_synJ hj hpos
  refine ⟨Nat.pos_of_ne_zero h0, ?_, ?_, ?_, ?_⟩
  · simp only [synPc, rowsAt_eq]
    have : 0 < NW := Nat.pos_of_ne_zero (NeZero.ne _)
    exact Nat.mul_pos (pow_pos this _) (by positivity)
  · simp only [synPc, rowsAt_eq]
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  · intro i hi
    simp only [synPc] at hi ⊢
    rw [expZ_eq_expSeq]
    have h1 := expSeq_le_add (gateCount (program ds)) (factorCount (program ds)) (synDg D j) hi
    have h2 := synE_ge (gateCount (program ds)) (factorCount (program ds)) D hj h0
    have h3 := synDg_le D j
    omega
  · simp only [synPc, bits_eq_mul]
    have h1 : D % m ^ j + synDg D j * m ^ j ≤ D := by
      rw [← mod_pow_succ_dg]; exact Nat.mod_le _ _
    have h2 : K * (D % m ^ j) + K * (synDg D j * m ^ j) ≤ K * D := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h1
    omega


theorem compactReservedPcs_ok (ds : ComplexFramedExecution.Directions)
    {K a oS B activeOffset J D n w : ℕ}
    (hlevels : synJ D D - 1 ≤ J) (hback : oS + K*B ≤ n)
    (hactive : activeOffset + K*D ≤ n)
    (hw : synE (gateCount (program ds)) (factorCount (program ds)) D D + D ≤ w) :
    ∀ pc ∈ compactReservedPcs K a oS B activeOffset J D,
      pc.Ok ds K n w (rowsAt (2^a) J) := by
  intro pc hp
  unfold compactReservedPcs at hp
  rcases List.mem_append.mp hp with hb | ha
  · by_cases hB : B=0
    · simp [hB] at hb
    · simp only [ite_eq_right hB, List.mem_singleton] at hb
      subst pc
      refine ⟨Nat.pos_of_ne_zero hB, ?_, rfl, ?_, ?_⟩
      · rw [rowsAt_eq]
        exact Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne NW)) _) (by positivity)
      · intro i hi
        exact (Nat.not_lt_zero i hi).elim
      · simpa only [bits] using hback
  · exact compactSynPcs_ok ds hlevels hactive hw pc ha

theorem compactReservedPcs_exp_sum (ds : ComplexFramedExecution.Directions)
    (K a oS B activeOffset J D : ℕ) :
    ((compactReservedPcs K a oS B activeOffset J D).map fun pc => expZ pc.u ds pc.j).sum =
      B + synE (gateCount (program ds)) (factorCount (program ds)) D D := by
  unfold compactReservedPcs
  rw [List.map_append, List.sum_append, synPcs_exp_sum]
  by_cases hB : B=0 <;> simp [hB, expZ]

end
end IntegerMultBounds.MathlibTM2.Fast
