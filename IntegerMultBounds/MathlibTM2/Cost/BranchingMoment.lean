module

public import IntegerMultBounds.MathlibTM2.Cost.Branching

/-!
# The layer branching bound as an occurrence moment

A node of the layer machine runs `F = factorCount (program ds)` child calls, each one level down,
so each child occurrence has size ratio `1/m`, and the normalized cost charges weight `1/NW` per
occurrence. The layer moment `Σ_i (1/NW) (1/m)^σ` is the uniform instance of the occurrence
moment `Σ_i w_i (r_i/m)^σ` of `Layer.OccurrenceRecurrence` (every rank is `1`).

`layerMoment_lt_iff_logb` shows a moment below one is exactly the hypothesis
`log_m (F/NW) < λ` used by `Recurrence.recurrence_closed`; `br_layerMoment_lt` is the
h=25 supplier instance. A variable-rank supplier (`Layer.SelectedMoments`) needs a layer
machine with per-occurrence child sizes before its moment can enter here.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Layer

/-- Occurrence moment of one layer node: weight `1/NW` and size ratio `1/m` per child call. -/
noncomputable def layerMoment (ds : ComplexFramedExecution.Directions) (σ : ℝ) : ℝ :=
  ∑ _i : Fin (factorCount (program ds)), (1 / (NW : ℝ)) * (((1 : ℕ) : ℝ) / (m : ℝ)) ^ σ

theorem layerMoment_eq (ds : ComplexFramedExecution.Directions) (σ : ℝ) :
    layerMoment ds σ = ((factorCount (program ds) : ℝ) / NW) / (m : ℝ) ^ σ := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [layerMoment, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_one, one_div (m : ℝ), Real.inv_rpow hm]
  ring

/-- A layer moment below one is the logarithmic branching hypothesis. -/
theorem layerMoment_lt_iff_logb (ds : ComplexFramedExecution.Directions) {lam : ℝ}
    (hlam : 0 < lam) :
    layerMoment ds lam < 1 ↔ Real.logb (m : ℝ) ((factorCount (program ds) : ℝ) / NW) < lam := by
  have hm : (1 : ℝ) < m := by norm_num [m]
  have hpow : (0 : ℝ) < (m : ℝ) ^ lam := Real.rpow_pos_of_pos (by linarith) _
  rw [layerMoment_eq, div_lt_one hpow]
  have ha : (0 : ℝ) ≤ (factorCount (program ds) : ℝ) / NW :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rcases ha.eq_or_lt with h | h
  · rw [← h, Real.logb_zero]
    exact ⟨fun _ => hlam, fun _ => hpow⟩
  · exact (Real.logb_lt_iff_lt_rpow hm h).symm

theorem logb_lt_of_layerMoment (ds : ComplexFramedExecution.Directions) {lam : ℝ}
    (hlam : 0 < lam) (hmom : layerMoment ds lam < 1) :
    Real.logb (m : ℝ) ((factorCount (program ds) : ℝ) / NW) < lam :=
  (layerMoment_lt_iff_logb ds hlam).1 hmom

/-- The h=25 supplier: its layer moment at `λ` is below one, from `F/NW < m^σ` and `σ < λ`. -/
theorem br_layerMoment_lt : layerMoment brDirs Parameters.lam < 1 := by
  have hlam : 0 < Parameters.lam := by norm_num [Parameters.lam]
  rw [layerMoment_lt_iff_logb _ hlam]
  have hm : (1 : ℝ) < m := by norm_num [m]
  have hσ : Parameters.sigma < Parameters.lam := by
    norm_num [Parameters.sigma, Parameters.lam]
  have ha : (0 : ℝ) ≤ (factorCount (program brDirs) : ℝ) / NW :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rcases ha.eq_or_lt with h | h
  · rw [← h, Real.logb_zero]
    exact hlam
  · exact ((Real.logb_lt_iff_lt_rpow hm h).mpr br_branching).trans hσ

end IntegerMultBounds.MathlibTM2.Cost
