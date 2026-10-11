import IntegerMultBounds.Machine.ActivePrefixStageNativePairCoordinates

/-! Actual native basis words retain the complete front and back address
spectators. These projections come from the literal runtime destination and
its canonical row ordinal, not from a supplied array permutation contract. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativeFrameCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (Address geometry)
open ActivePrefixStageRuntimeOrdinal (front word_value index_factored quotient)
open ActivePrefixStageRuntimeWord (word word_length)
open ActivePrefixStageRuntimeSelected (destination fields)
open ActivePrefixDirtyControlGlobalSwap (index)
open ActivePrefixStageNativeRows (ordinal)
open Networks.BinaryRowProgram (Op)
variable {sh : Shape}

/-- Bits below the complete active field, including the dirty back reserve. -/
def backOrdinal (sh : Shape) {rows : ℕ} (i : Fin (rows*sh.recordWidth)) : ℕ :=
  i.val/sh.payload%2^(sh.H+sh.B)

/-- Bits above the complete active field, including the original outer row. -/
def frontOrdinal (sh : Shape) {rows : ℕ} (i : Fin (rows*sh.recordWidth)) : ℕ :=
  i.val/sh.payload/2^(sh.active*sh.chunk+sh.H+sh.B)

private theorem index_record (d : Inputs sh) (i : Address d) :
    (index sh (geometry d) i).val/sh.payload=
      (front d i*2^(sh.active*sh.chunk)+Counter.value (word d i))*2^(sh.H+sh.B)+i.back.val := by
  rw [index_factored]
  exact quotient _ _ _ (by have := d.hrecord; omega) i.payload.isLt

private theorem word_lt (d : Inputs sh) (i : Address d) :
    Counter.value (word d i)<2^(sh.active*sh.chunk) := by
  simpa only [word_length] using Counter.value_lt (word d i)

theorem back_at_index (d : Inputs sh) (i : Address d) :
    backOrdinal sh (index sh (geometry d) i)=i.back.val := by
  unfold backOrdinal
  rw [index_record,Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt i.back.isLt

theorem front_at_index (d : Inputs sh) (i : Address d) :
    frontOrdinal sh (index sh (geometry d) i)=front d i := by
  unfold frontOrdinal
  rw [index_record]
  have he : sh.active*sh.chunk+sh.H+sh.B=sh.active*sh.chunk+(sh.H+sh.B) := by omega
  have hp : 2^(sh.active*sh.chunk+sh.H+sh.B)=2^(sh.H+sh.B)*2^(sh.active*sh.chunk) := by
    rw [he,pow_add,Nat.mul_comm]
  rw [hp,←Nat.div_div_eq_div_mul,quotient _ _ _ (by positivity) i.back.isLt]
  exact quotient _ _ _ (by positivity) (word_lt d i)

private theorem front_destination (d : Inputs sh) (i : Address d) :
    front d (destination d i)=front d i := by
  rw [fields]
  rfl

private theorem back_destination (d : Inputs sh) (i : Address d) :
    (destination d i).back=i.back := by
  rw [fields]

/-- A real physical row-addition stage leaves all front and back spectators
unchanged, independently of which original source/target pair it uses. -/
theorem step_frame (d : Inputs sh) (op : Op (Fin d.stage.slots))
    (i : Fin (d.rows*sh.recordWidth)) :
    frontOrdinal sh (ActivePrefixStagePairCoordinates.destination d op i)=frontOrdinal sh i ∧
    backOrdinal sh (ActivePrefixStagePairCoordinates.destination d op i)=backOrdinal sh i := by
  let input := ActivePrefixStagePairData.changePair d op
  let a := (ActivePrefixStagePairCoordinates.addressEquiv input).symm i
  have hi : index sh (geometry input) a=i := ActivePrefixStagePairCoordinates.index_decode input i
  change frontOrdinal sh (index sh (geometry input) (destination input a))=frontOrdinal sh i ∧
    backOrdinal sh (index sh (geometry input) (destination input a))=backOrdinal sh i
  rw [←hi,front_at_index,front_at_index,back_at_index,back_at_index]
  exact ⟨front_destination input a,congrArg Fin.val (back_destination input a)⟩

/-- The literal chronological native word retains the same address frame
through every target-pair change. -/
theorem run_frame (d : Inputs sh) (ops : List (Op (Fin d.stage.slots)))
    (i : Fin (d.rows*sh.recordWidth)) :
    frontOrdinal sh (ActivePrefixStagePairCoordinates.run d ops i)=frontOrdinal sh i ∧
    backOrdinal sh (ActivePrefixStagePairCoordinates.run d ops i)=backOrdinal sh i := by
  induction ops generalizing i with
  | nil => exact ⟨rfl,rfl⟩
  | cons op ops ih =>
    have hs := step_frame d op i
    have hr := ih (ActivePrefixStagePairCoordinates.destination d op i)
    exact ⟨hr.1.trans hs.1,hr.2.trans hs.2⟩

/-- At the actual native row ordinal, front and back projections contain no
codec-payload factor. The expanded polynomial payload does not change them. -/
theorem native_frame (d : Inputs sh) (ops : List (Op (Fin d.stage.slots)))
    (r : Fin (ActivePrefixStageTripleWords.count d)) :
    (ActivePrefixStageNativePairCoordinates.run d ops r).val/
      2^(sh.active*sh.chunk+sh.H+sh.B)=r.val/2^(sh.active*sh.chunk+sh.H+sh.B) ∧
    (ActivePrefixStageNativePairCoordinates.run d ops r).val%2^(sh.H+sh.B)=
      r.val%2^(sh.H+sh.B) := by
  have hp : 0<sh.payload := by have hr := d.hrecord; omega
  have h := run_frame d ops (ActivePrefixStageNativePairCoordinates.start d r)
  rw [ActivePrefixStageNativePairCoordinates.run_start] at h
  simpa only [frontOrdinal,backOrdinal,ActivePrefixStageNativePairCoordinates.start,
    Nat.mul_div_cancel _ hp] using h

/-- The actual native row permutation retains the original outer row as
well as every address spectator, even with an expanded polynomial codec. -/
theorem native_outer_row (d : Inputs sh) (ops : List (Op (Fin d.stage.slots)))
    (r : Fin (ActivePrefixStageTripleWords.count d)) :
    (ActivePrefixStageNativePairCoordinates.run d ops r).val/2^sh.bits=r.val/2^sh.bits := by
  have hf := (native_frame d ops r).1
  have hb : sh.active*sh.chunk+sh.H+sh.B≤sh.bits := by unfold Shape.bits; omega
  have he : 2^sh.bits=2^(sh.active*sh.chunk+sh.H+sh.B)*
      2^(sh.bits-(sh.active*sh.chunk+sh.H+sh.B)) := by
    rw [←pow_add,Nat.add_sub_of_le hb]
  calc
    _ = (ActivePrefixStageNativePairCoordinates.run d ops r).val/
        (2^(sh.active*sh.chunk+sh.H+sh.B)*2^(sh.bits-(sh.active*sh.chunk+sh.H+sh.B))) :=
      congrArg (fun n => (ActivePrefixStageNativePairCoordinates.run d ops r).val/n) he
    _ = ((ActivePrefixStageNativePairCoordinates.run d ops r).val/
        2^(sh.active*sh.chunk+sh.H+sh.B))/2^(sh.bits-(sh.active*sh.chunk+sh.H+sh.B)) :=
      (Nat.div_div_eq_div_mul _ _ _).symm
    _ = (r.val/2^(sh.active*sh.chunk+sh.H+sh.B))/2^(sh.bits-(sh.active*sh.chunk+sh.H+sh.B)) :=
      congrArg (fun n => n/2^(sh.bits-(sh.active*sh.chunk+sh.H+sh.B))) hf
    _ = r.val/(2^(sh.active*sh.chunk+sh.H+sh.B)*2^(sh.bits-(sh.active*sh.chunk+sh.H+sh.B))) :=
      Nat.div_div_eq_div_mul _ _ _
    _ = _ := congrArg (fun n => r.val/n) he.symm

end
end IntegerMultBounds.Machine.ActivePrefixStageNativeFrameCoordinates
