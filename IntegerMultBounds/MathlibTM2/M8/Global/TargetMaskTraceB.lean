module

public import IntegerMultBounds.MathlibTM2.M8.Global.CovarianceB
public import IntegerMultBounds.MathlibTM2.M8.Global.ReadoutOrderB
public import IntegerMultBounds.MathlibTM2.M8.Global.TargetTraceB

/-! Exact target traces expressed by the checked masks and concrete readout order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical
open CovarianceB MaskWeightsB

theorem coeff_eq_one (m t : Nat) : coeff m t = 1 ↔ m.testBit t = true := by
  cases ht : m.testBit t <;> simp [coeff, ht]

/-- The readout incidence predicate is a checked mask bit. -/
theorem readout_incidence (s t : Nat) :
    decide (t < leafCount ∧ dagB.cov targets s t = 1) =
      (decide (t < leafCount) && (slotMask s).testBit t) := by
  rw [covariance_eq_slotMask]
  simp [coeff_eq_one]

/-- Target readout slots in the supplied order, retaining all repetitions of frames. -/
def targetReadouts (ss : List Nat) (t : Nat) : List Nat :=
  ss.filter fun s => decide (t < leafCount) && (slotMask s).testBit t

theorem readBlocks_target_mask_trace (F : FrameAssignment) (ss : List Nat) (t : Nat) :
    fseq (.inl (.y t)) (readBlocks F ss).flatten = (targetReadouts ss t).map F.sigma := by
  rw [readBlocks_target_trace]
  simp only [readout_incidence, targetReadouts]

/-- The actual first-stage target trace is now expressed in the concrete key and
mask data, with the zero and nonzero readout phases explicitly separated. -/
theorem firstStage_target_mask_trace (t : Nat) :
    fseq (.inl (.y t)) firstStage =
      (targetReadouts nowSlots t).map assignment.sigma ++
      ((List.finRange 23).filter fun c => decide (t ∈ centreTargets c)).map (fun _ => 0) ++
      (targetReadouts (planB.defS.filter KeyOrderB.zeroReadout) t).map assignment.sigma ++
      (targetReadouts (planB.defS.filter (fun s => !KeyOrderB.zeroReadout s)) t).map assignment.sigma ++
      (outputRoots.filter fun j => decide (t ∈ targets j)).map assignment.output := by
  rw [firstStage, stage_target_trace, lateSlots_materialized, readout_order_partition]
  simp only [readout_incidence, targetReadouts, List.filter_append, List.map_append, List.append_assoc]

/-- The first late-readout phase consists entirely of zero frames. -/
theorem zero_readouts_trace (t : Nat) :
    ((targetReadouts (planB.defS.filter KeyOrderB.zeroReadout) t).map assignment.sigma).all
      (fun F => decide (F = 0)) = true := by
  apply List.all_eq_true.mpr
  intro F hF
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hF
  have hz : KeyOrderB.zeroReadout s = true :=
    (List.mem_filter.mp (List.mem_filter.mp hs).1).2
  have he : AssignmentB.sigmaLabel s = Signed.Frame.zero := of_decide_eq_true hz
  simp [assignment, he, frameOfLabel, Signed.Frame.eval]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
