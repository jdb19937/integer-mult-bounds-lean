module

import IntegerMultBounds.Machine.ActivePrefixStageFullBudget
public import IntegerMultBounds.Machine.ActivePrefixStageFullLateRun
public import IntegerMultBounds.Machine.ActivePrefixStageFullEarlyRun
import IntegerMultBounds.Machine.ActivePrefixStageHeadersBudget
import Mathlib.Tactic.Positivity.Finset

/-! # Compact stage bank and host simulation costs

The original thirteen descriptors and raw array have linear total word length.
This pays host-bank normalization without adding a dimension factor to the
existing complete native stage bounds. Layout reservation remains an explicit
requirement of the native stage inputs.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData

noncomputable section

/-- Initial nonblank words: thirteen retained original headers and the raw array. -/
def compactStageBankSize {s : Shape} (d : Inputs s) : ℕ :=
  (∑ i : Fin 13, (1 + (RecursiveChildQuotientsConstant.bits
    (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)).length)) +
    d.rows * s.recordWidth

theorem compactStageBankSize_le {s : Shape} (d : Inputs s)
    (order : ActivePrefixStageHeadersData.Order)
    (horder : ActivePrefixStageHeadersSchedule.Ordered order d.stage) :
    compactStageBankSize d ≤ 40 * (d.rows * s.recordWidth) := by
  have hpos : 0 < d.rows * s.recordWidth := by
    have hp : 0 < s.payload := by have := d.hrecord; omega
    exact Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)
  have ho := (ActivePrefixStageHeadersBudget.original_bounds order d.stage d.rows
    d.hG d.hGK horder d.hr d.hrecord).1
  have hsum : (∑ i : Fin 13, (1 + (RecursiveChildQuotientsConstant.bits
      (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)).length)) ≤
      ∑ _i : Fin 13, 3 * (d.rows * s.recordWidth) := by
    apply Finset.sum_le_sum
    intro i _
    have hb := ActiveRepairRankHeadersCommands.bits_length
      (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)
    have hi := ho i
    omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold compactStageBankSize
  omega

/-- Explicit normalized host budget, with the original bank-size charge. -/
def compactStageHostCost (T N H cost bankSize : ℕ) : ℕ :=
  (T + 12 * N + 5) * cost + 6 * bankSize + 2 * T + 6 * N + H + 10

/-- A native compact-width bound survives normalization at fixed host/bank size. -/
theorem compactStageHostCost_le {T N H cost bankSize V h : ℕ} {C : ℝ}
    (hV : 1 ≤ V) (hbank : bankSize ≤ 40 * V)
    (hcost : (cost : ℝ) ≤ C * V * ((max 1 h : ℕ) : ℝ) ^ Parameters.tau) :
    (compactStageHostCost T N H cost bankSize : ℝ) ≤
      ((T + 12 * N + 5 : ℕ) * C + (240 + 2*T + 6*N + H + 10 : ℕ)) *
        V * ((max 1 h : ℕ) : ℝ) ^ Parameters.tau := by
  have hp : (1 : ℝ) ≤ ((max 1 h : ℕ) : ℝ) ^ Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 h)
      (by norm_num [Parameters.tau])
  have hn : 6 * bankSize + 2*T + 6*N + H + 10 ≤
      (240 + 2*T + 6*N + H + 10) * V := by
    have := Nat.mul_le_mul_left (2*T + 6*N + H + 10) hV
    nlinarith
  have hnR : ((6 * bankSize + 2*T + 6*N + H + 10 : ℕ) : ℝ) ≤
      ((240 + 2*T + 6*N + H + 10 : ℕ) : ℝ) * V := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg (α := ℝ) (T + 12*N + 5))
  have he := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ ((240 + 2*T + 6*N + H + 10 : ℕ) : ℝ) * V by positivity)
  unfold compactStageHostCost
  push_cast at hm hnR he ⊢
  nlinarith only [hm, hnR, he]

/-- Complete earlier-source native stage, including host simulation and bank cleanup. -/
theorem compactStageEarlyHost_uniform (T N D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Shape) (d : Inputs s)
      (horder : d.stage.source.val < d.stage.target.val),
      (compactStageHostCost T N 13 (ActivePrefixStageFullEarlyRun.cost D d horder)
        (compactStageBankSize d) : ℝ) ≤ C * (d.rows * s.recordWidth : ℕ) *
          ((max 1 ((d.stage.f - 1) * s.guard) : ℕ) : ℝ) ^ Parameters.tau := by
  obtain ⟨C, hC, hbound⟩ := ActivePrefixStageFullBudget.early_uniform_bound D
  refine ⟨(T + 12*N + 5 : ℕ) * C + (240 + 2*T + 6*N + 13 + 10 : ℕ),
    by positivity, ?_⟩
  intro s d horder
  have hV : 1 ≤ d.rows * s.recordWidth := by
    have hp : 0 < s.payload := by have := d.hrecord; omega
    exact Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)
  exact compactStageHostCost_le hV (compactStageBankSize_le d .early horder)
    (hbound s d horder)

/-- Complete later-source native stage at its explicit nontrivial-width cutoff. -/
theorem compactStageLateHost_uniform (T N D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Shape) (d : Inputs s)
      (horder : d.stage.target.val < d.stage.source.val)
      (hn : 0 < d.stage.f - 1) (hb : 2 ≤ s.guard),
      (compactStageHostCost T N 13 (ActivePrefixStageFullLateRun.cost D d horder hn hb)
        (compactStageBankSize d) : ℝ) ≤ C * (d.rows * s.recordWidth : ℕ) *
          ((max 1 ((d.stage.f - 1) * s.guard) : ℕ) : ℝ) ^ Parameters.tau := by
  obtain ⟨C, hC, hbound⟩ := ActivePrefixStageFullBudget.late_uniform_bound D
  refine ⟨(T + 12*N + 5 : ℕ) * C + (240 + 2*T + 6*N + 13 + 10 : ℕ),
    by positivity, ?_⟩
  intro s d horder hn hb
  have hV : 1 ≤ d.rows * s.recordWidth := by
    have hp : 0 < s.payload := by have := d.hrecord; omega
    exact Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)
  exact compactStageHostCost_le hV (compactStageBankSize_le d .late horder)
    (hbound s d horder hn hb)

end
end IntegerMultBounds.MathlibTM2.Cost
