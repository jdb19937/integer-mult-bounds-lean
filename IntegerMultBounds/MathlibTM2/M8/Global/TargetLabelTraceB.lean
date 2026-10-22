module

public import IntegerMultBounds.MathlibTM2.M8.Global.ReadoutZeroB
public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.Kernel
public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.HintChecked

/-! The kernel-friendly target labels describe the actual stage, including repeats. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Checked block hints preserve the exact numeric-key readout trace. -/
theorem target_readoutLabels_eq (t : Nat) :
    TargetGeometryB.readoutLabels t =
      ((AssignmentB.readoutOrder.filter fun s => (CovarianceB.slotMask s).testBit t).map AssignmentB.sigmaLabel) := by
  rw [TargetGeometryB.readoutLabels, TargetGeometryB.fastLabels_eq _ TargetGeometryB.hints_checked,
    TargetGeometryB.hints_slots]

theorem late_target_label_trace (t : Nat) (ht : t < leafCount) :
    (targetReadouts assignment.readoutOrder t).map assignment.sigma =
      (TargetGeometryB.readoutLabels t).map frameOfLabel := by
  rw [target_readoutLabels_eq]
  simp [targetReadouts, ht, assignment, List.map_map, Function.comp_def]

def targetZeroPrefix (t : Nat) : List LMat :=
  (targetReadouts nowSlots t).map assignment.sigma ++
    ((List.finRange 23).filter fun c => decide (t ∈ centreTargets c)).map (fun _ => 0)

theorem targetZeroPrefix_zero (t : Nat) :
    (targetZeroPrefix t).all (fun F => decide (F = 0)) = true := by
  unfold targetZeroPrefix
  rw [List.all_append, now_target_trace_zero]
  simp

/-- Exact first-stage target trace: a zero prefix, checked signed labels, and output reads. -/
theorem firstStage_target_label_trace (t : Nat) (ht : t < leafCount) :
    fseq (.inl (.y t)) firstStage = targetZeroPrefix t ++
      (TargetGeometryB.readoutLabels t).map frameOfLabel ++
      (outputRoots.filter fun j => decide (t ∈ targets j)).map assignment.output := by
  rw [firstStage, stage_target_trace, lateSlots_materialized]
  simp only [readout_incidence]
  change _ ++ _ ++ (targetReadouts assignment.readoutOrder t).map assignment.sigma ++ _ = _
  rw [late_target_label_trace t ht]
  rfl

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
