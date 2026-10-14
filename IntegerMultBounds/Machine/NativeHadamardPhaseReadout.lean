module

public import IntegerMultBounds.Machine.NativeEndpointCharacterReadout
public import IntegerMultBounds.Networks.GaussianHadamardPhase

/-! The existing physical aggregate phase scanner with unit weights computes
exactly the source and sink diagonal correction for normalized Hadamard. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardPhaseReadout
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageRuntimeOrdinal (highCoordinates reverseAxis)
open NativeEndpointCharacterAddress (reverseSlot)
open NativeEndpointCharacterReadout (coordinates)
open Networks
variable {shape : Shape}

/-- Unit weights are compiled once; each slot contributes its original bit. -/
def weights (slotCount : ℕ) : List (ZMod 4) := List.replicate slotCount 1

theorem weights_length (slotCount : ℕ) : (weights slotCount).length=slotCount := by simp [weights]

theorem accumulator (stage : Stage shape) {rows : ℕ} (index : Fin (rows*shape.recordWidth)) :
    ((AllAxisPhaseFlagsCaller.phase stage stage.slots (weights stage.slots)
      (BinaryAddressTableData.row shape.bits (index.val/shape.payload))).val : ZMod 4) =
      ∑ column : Fin stage.f, BinaryPhase.weightPhase (coordinates stage index column) := by
  unfold AllAxisPhaseFlagsCaller.phase
  rw [RepeatedWeightedPhaseAccumulator.accumulate_cast,RepeatedWeightedPhaseTensor.total_eq_fin_sum]
  simp only [Fin.val_zero,Nat.cast_zero,zero_add]
  rw [weights_length]
  change (∑ slot : Fin stage.slots, ∑ column : Fin stage.f,
    if (AllAxisPhaseFlagsCaller.controls stage stage.slots
      (BinaryAddressTableData.row shape.bits (index.val/shape.payload))).getD
        (slot.val*stage.f+column.val) false
    then (weights stage.slots).getD slot.val 0 else 0) = _
  rw [Finset.sum_comm]
  have columnSum (column : Fin stage.f) :
      (∑ slot : Fin stage.slots,
        if (AllAxisPhaseFlagsCaller.controls stage stage.slots
          (BinaryAddressTableData.row shape.bits (index.val/shape.payload))).getD
            (slot.val*stage.f+column.val) false
        then (weights stage.slots).getD slot.val 0 else 0) =
          BinaryPhase.weightPhase (coordinates stage index (reverseAxis column)) := by
    have slotBit (slot : Fin stage.slots) :
        (if (AllAxisPhaseFlagsCaller.controls stage stage.slots
          (BinaryAddressTableData.row shape.bits (index.val/shape.payload))).getD
            (slot.val*stage.f+column.val) false
        then (weights stage.slots).getD slot.val 0 else 0) =
          BinaryPhase.bitLift (BinaryRowColumns.scalar
            (highCoordinates stage index (reverseAxis column) (reverseSlot stage slot))) := by
      rw [NativeEndpointCharacterAddress.selected]
      rw [List.getD_eq_getElem _ _ (by simpa only [weights_length] using slot.isLt)]
      simp only [weights,List.getElem_replicate]
      cases highCoordinates stage index (reverseAxis column) (reverseSlot stage slot) <;>
        simp [BinaryRowColumns.scalar]
    simp_rw [slotBit]
    have reversal := (CompactAllAxisPhaseReadout.reversal stage.slots).sum_comp
      (fun slot => BinaryPhase.bitLift (BinaryRowColumns.scalar
        (highCoordinates stage index (reverseAxis column) slot)))
    change (∑ slot : Fin stage.slots, BinaryPhase.bitLift (BinaryRowColumns.scalar
      (highCoordinates stage index (reverseAxis column) (reverseSlot stage slot)))) = _ at reversal
    simpa only [coordinates,BinaryRowColumns.coordinates,BinaryPhase.weightPhase] using reversal
  simp_rw [columnSum]
  exact (CompactAllAxisPhaseReadout.reversal stage.f).sum_comp
    (fun column => BinaryPhase.weightPhase (coordinates stage index column))

/-- Literal scanner flags compute the entire original tensor phase correction. -/
theorem tensor_action (stage : Stage shape) {rows : ℕ} (index : Fin (rows*shape.recordWidth))
    (input : BinaryColumns.Arrays stage.slots stage.f) :
    BinaryPhase.phase ((AllAxisPhaseFlagsCaller.phase stage stage.slots (weights stage.slots)
      (BinaryAddressTableData.row shape.bits (index.val/shape.payload))).val : ZMod 4) *
        input (coordinates stage index) =
      GaussianHadamardPhase.tensorPhase stage.f input (coordinates stage index) := by
  rw [accumulator,BinaryPhase.phase_sum,GaussianHadamardPhase.tensorPhase_apply]

end
end IntegerMultBounds.Machine.NativeHadamardPhaseReadout
