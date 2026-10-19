module

public import IntegerMultBounds.Machine.ActiveTargetHighestLayoutCompose
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutSourceFrames
public import IntegerMultBounds.Machine.ActivePrefixStageSingletonData
import Mathlib.Tactic.Positivity.Finset

/-! Exact singleton selected-XOR semantics on original array addresses. The
single physically read source bit is the complete selection when f=1; no low
packed operation, repair permutation, or assumed low-word specification occurs. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActivePrefixStageSingletonSelected
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Address)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageSingletonData
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlGlobalSwap (index)
open ActiveTargetHighestLayoutWords
open ActiveTargetHighestLayoutCompose (targetWord)
open ActiveRepairLayoutPermutationFiber (sourceWord)
open BinaryAddressTableData (row row_length)
variable {s : Shape}

def earlyDestination (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (x : Address s (params d) d.rows) :=
  ActiveTargetHighestLayoutEarlyCoordinates.destination s (params d) (earlyOffset d.stage) d.rows
    (early_fits d.stage horder) (early_high_positive d.stage horder) x

def lateDestination (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
    (x : Address s (params d) d.rows) :=
  ActiveTargetHighestLayoutLateCoordinates.destination s (params d) (lateOffset d.stage) d.rows
    (late_fits d.stage horder) (positive_before d.stage) x

theorem early_entry (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (array : Array s d.rows) (x : Address s (params d) d.rows) :
    earlyResult d horder array (index s (params d) (earlyDestination d horder x))=array (index s (params d) x) :=
  ActiveTargetHighestLayoutGlobal.early_entry s (params d) (earlyOffset d.stage) d.rows
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG)
    d.hr (by have := d.hrecord; omega) array x

theorem late_entry (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
    (array : Array s d.rows) (x : Address s (params d) d.rows) :
    lateResult d horder array (index s (params d) (lateDestination d horder x))=array (index s (params d) x) :=
  ActiveTargetHighestLayoutGlobal.late_entry s (params d) (lateOffset d.stage) d.rows
    (late_fits d.stage horder) (positive_before d.stage) (positive_H d.stage d.hG)
    d.hr (by have := d.hrecord; omega) array x

private theorem empty_target (d : Inputs s) (x : Address s (params d) d.rows) :
    row ((params d).n*(params d).q) x.target.val=[] := by
  apply List.length_eq_zero_iff.mp
  rw [row_length,zero_low,zero_mul]

theorem early_target_word (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (x : Address s (params d) d.rows) (lo : List Bool) :
    targetWord s (params d) d.rows lo (earlyDestination d horder x)=
      List.zipWith xor (targetWord s (params d) d.rows lo x)
        (List.replicate lo.length false++
          (earlyControl s (params d) (earlyOffset d.stage) d.rows x::List.replicate ((params d).before-1) false)) := by
  have h := ActiveTargetHighestLayoutCompose.early_after_low_word s (params d) (earlyOffset d.stage) d.rows
    (early_fits d.stage horder) (early_high_positive d.stage horder) x x lo []
    (zero_low d).symm rfl (by rw [empty_target]; rfl)
  simpa only [earlyDestination,Compact.PowerTwo.toggleMask,List.map_nil,List.flatten_nil,List.append_nil] using h

theorem late_target_word (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
    (x : Address s (params d) d.rows) (lo : List Bool) :
    targetWord s (params d) d.rows lo (lateDestination d horder x)=
      List.zipWith xor (targetWord s (params d) d.rows lo x)
        (List.replicate lo.length false++
          (lateControl s (params d) (lateOffset d.stage) d.rows x::List.replicate ((params d).before-1) false)) := by
  have h := ActiveTargetHighestLayoutCompose.late_after_low_word s (params d) (lateOffset d.stage) d.rows
    (late_fits d.stage horder) (positive_before d.stage) x x lo []
    (zero_low d).symm rfl rfl (by rw [empty_target]; rfl)
  simpa only [lateDestination,Compact.PowerTwo.toggleMask,List.map_nil,List.flatten_nil,List.append_nil] using h

/-- The control read by the machine is the entire original one-bit source
selection, extracted from its complete original slot. -/
theorem early_selected (d : Inputs s) (x : Address s (params d) d.rows) :
    SelectedSourceBitsData.selected
      (sourceWord (params d).before (params d).after (earlyOffset d.stage) ((params d).f*(params d).q)
        .before (x.activeBefore,x.activeAfter)) (params d).q (params d).rho 1=
      [earlyControl s (params d) (earlyOffset d.stage) d.rows x] := by
  have h := ActiveTargetHighestLayoutWords.early_selected s (params d) (earlyOffset d.stage) d.rows x
  simpa only [zero_low,Nat.zero_add,ActiveRepairLayoutPermutationFiber.controlWord,
    SelectedSourceBitsData.selected_zero,List.nil_append] using h

theorem late_selected (d : Inputs s) (x : Address s (params d) d.rows) :
    SelectedSourceBitsData.selected
      (sourceWord (params d).before (params d).after (lateOffset d.stage) ((params d).f*(params d).q)
        .after (x.activeBefore,x.activeAfter)) (params d).q (params d).rho 1=
      [lateControl s (params d) (lateOffset d.stage) d.rows x] := by
  have h := ActiveTargetHighestLayoutWords.late_selected s (params d) (lateOffset d.stage) d.rows x
  simpa only [zero_low,Nat.zero_add,ActiveRepairLayoutPermutationFiber.controlWord,
    SelectedSourceBitsData.selected_zero,List.nil_append] using h

theorem early_source (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (x : Address s (params d) d.rows) :
    Gather.field (row (params d).before (earlyDestination d horder x).activeBefore.val)
      (earlyOffset d.stage) ((params d).f*(params d).q)=
    Gather.field (row (params d).before x.activeBefore.val) (earlyOffset d.stage) ((params d).f*(params d).q) :=
  ActiveTargetHighestLayoutSourceFrames.early_source s (params d) (earlyOffset d.stage) d.rows
    (early_fits d.stage horder) (early_high_positive d.stage horder) (early_disjoint d.stage) x

theorem late_source (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
    (x : Address s (params d) d.rows) : (lateDestination d horder x).activeAfter=x.activeAfter := rfl

theorem early_fields (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (x : Address s (params d) d.rows) :
    earlyDestination d horder x={x with activeBefore:=(earlyDestination d horder x).activeBefore} := rfl

theorem late_fields (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
    (x : Address s (params d) d.rows) :
    lateDestination d horder x={x with activeBefore:=(lateDestination d horder x).activeBefore} := rfl

end
end IntegerMultBounds.Machine.ActivePrefixStageSingletonSelected
